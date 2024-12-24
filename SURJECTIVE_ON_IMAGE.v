Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_ON_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
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
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem5037683 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term0 A B v u f) : term0 A B v u f.
Proof. exact (h1). Qed.
Lemma lem5037684 {B : Type'} (y : B) (v : B -> Prop) (h1 : @IN B y v) : @IN B y v.
Proof. exact (h1). Qed.
Lemma lem5037685 {A B : Type'} (y : B) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term0 A B v u f) : term1 A B v u f y.
Proof. exact (@lem5037683 A B v u f h1 (@INSERT B y (@EMPTY B))). Qed.
Lemma lem5037686 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term1 A B v u f y) = (term2 A B v u f y).
Proof. exact (eq_refl (term1 A B v u f y)). Qed.
Lemma lem5037687 {A B : Type'} (y : B) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term0 A B v u f) : term2 A B v u f y.
Proof. exact (EQ_MP (@lem5037686 A B v u f y) (@lem5037685 A B y v u f h1)). Qed.
Lemma lem5037688 (t1 : Prop) : term3 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5037689 (t1 : Prop) : (term3 t1) = (term4 t1).
Proof. exact (eq_refl (term3 t1)). Qed.
Lemma lem5037690 (t1 : Prop) : term4 t1.
Proof. exact (EQ_MP (@lem5037689 t1) (@lem5037688 t1)). Qed.
Lemma lem5037691 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (@lem5037690 t1 t2). Qed.
Lemma lem5037692 (t1 : Prop) (t2 : Prop) : (term5 t1 t2) = (term6 t1 t2).
Proof. exact (eq_refl (term5 t1 t2)). Qed.
Lemma lem5037693 (t1 : Prop) (t2 : Prop) : term6 t1 t2.
Proof. exact (EQ_MP (@lem5037692 t1 t2) (@lem5037691 t1 t2)). Qed.
Lemma lem5037694 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term7 t1 t2 t3.
Proof. exact (@lem5037693 t1 t2 t3). Qed.
Lemma lem5037695 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term7 t1 t2 t3) = ((term8 t1 t2 t3) = (term9 t1 t2 t3)).
Proof. exact (eq_refl (term7 t1 t2 t3)). Qed.
Lemma lem5037696 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term8 t1 t2 t3) = (term9 t1 t2 t3).
Proof. exact (EQ_MP (@lem5037695 t1 t2 t3) (@lem5037694 t1 t2 t3)). Qed.
Lemma lem5037697 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term9 t1 t2 t3) = (term8 t1 t2 t3).
Proof. exact (SYM (@lem5037696 t1 t2 t3)). Qed.
Lemma lem5037705 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5037706 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term10 B s t).
Proof. exact (@lem5037705 B s t). Qed.
Lemma lem5037707 {B : Type'} (y : B) (v : B -> Prop) : (term11 B y v) = (term12 B y v).
Proof. exact (@lem5037706 B (@INSERT B y (@EMPTY B)) v). Qed.
Lemma lem5037714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037715 {B : Type'} (y : B) (v : B -> Prop) : (term13 B y v) = (term14 B y v).
Proof. exact (MK_COMB (@lem5037714) (@lem5037707 B y v)). Qed.
Lemma lem5037723 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5037724 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem5037723 A s t). Qed.
Lemma lem5037725 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@SUBSET A s u) = (term10 A s u).
Proof. exact (@lem5037724 A s u). Qed.
Lemma lem5037732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037733 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term15 A s u) = (term16 A s u).
Proof. exact (MK_COMB (@lem5037732) (@lem5037725 A s u)). Qed.
Lemma lem5037737 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5037738 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term17 B s t).
Proof. exact (@lem5037737 B s t). Qed.
Lemma lem5037739 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : ((@IMAGE A B f s) = (@INSERT B y (@EMPTY B))) = (term18 A B f s y).
Proof. exact (@lem5037738 B (@IMAGE A B f s) (@INSERT B y (@EMPTY B))). Qed.
Lemma lem5037748 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term19 A B u f s y) = (term20 A B u f s y).
Proof. exact (MK_COMB (@lem5037733 A s u) (@lem5037739 A B f s y)). Qed.
Lemma lem5037751 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term21 A B u f y) = (term22 A B u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5037748 A B u f s y)). Qed.
Lemma lem5037752 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5037753 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term23 A B u f y) = (term24 A B u f y).
Proof. exact (MK_COMB (@lem5037752 A) (@lem5037751 A B u f y)). Qed.
Lemma lem5037758 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term2 A B v u f y) = (term25 A B v u f y).
Proof. exact (MK_COMB (@lem5037715 B y v) (@lem5037753 A B u f y)). Qed.
Lemma lem5037761 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037762 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term26 A B v u f y) = (term27 A B v u f y).
Proof. exact (MK_COMB (@lem5037761) (@lem5037758 A B v u f y)). Qed.
Lemma lem5037773 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term28 A B u f y) = (term28 A B u f y).
Proof. exact (eq_refl (term28 A B u f y)). Qed.
Lemma lem5037774 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term29 A B v u f y) = (term30 A B v u f y).
Proof. exact (MK_COMB (@lem5037762 A B v u f y) (@lem5037773 A B u f y)). Qed.
Lemma lem5037777 {B : Type'} (y : B) (v : B -> Prop) : (term31 B y v) = (term31 B y v).
Proof. exact (eq_refl (term31 B y v)). Qed.
Lemma lem5037778 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term32 A B v u f y) = (term33 A B v u f y).
Proof. exact (MK_COMB (@lem5037777 B y v) (@lem5037774 A B v u f y)). Qed.
Lemma lem5037781 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term33 A B v u f y) = (term32 A B v u f y).
Proof. exact (SYM (@lem5037778 A B v u f y)). Qed.
Lemma lem5037785 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5037786 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5037785 B P x). Qed.
Lemma lem5037787 {B : Type'} (v : B -> Prop) (y : B) : (@IN B y v) = (v y).
Proof. exact (@lem5037786 B v y). Qed.
Lemma lem5037788 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037789 {B : Type'} (v : B -> Prop) (y : B) : (term31 B y v) = (term34 B v y).
Proof. exact (MK_COMB (@lem5037788) (@lem5037787 B v y)). Qed.
Lemma lem5037801 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term35 A x y s) = (term36 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5037802 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term35 B x y s) = (term36 B y x s).
Proof. exact (@lem5037801 B y x s). Qed.
Lemma lem5037803 {B : Type'} (y : B) (x : B) : (term37 B x y) = (term38 B y x).
Proof. exact (@lem5037802 B y x (@EMPTY B)). Qed.
Lemma lem5037809 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5037810 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem5037809 B x). Qed.
Lemma lem5037811 {B : Type'} (x : B) (y : B) : (term39 B x y) = (term39 B x y).
Proof. exact (eq_refl (term39 B x y)). Qed.
Lemma lem5037812 {B : Type'} (x : B) (y : B) : (term38 B y x) = (term40 B x y).
Proof. exact (MK_COMB (@lem5037811 B x y) (@lem5037810 B x)). Qed.
Lemma lem5037814 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5037815 {B : Type'} (x : B) (y : B) : (term40 B x y) = (x = y).
Proof. exact (@lem5037814 (x = y)). Qed.
Lemma lem5037818 {B : Type'} (x : B) (y : B) : (term38 B y x) = (x = y).
Proof. exact (TRANS (@lem5037812 B x y) (@lem5037815 B x y)). Qed.
Lemma lem5037819 {B : Type'} (x : B) (y : B) : (term37 B x y) = (x = y).
Proof. exact (TRANS (@lem5037803 B y x) (@lem5037818 B x y)). Qed.
Lemma lem5037820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037821 {B : Type'} (x : B) (y : B) : (term41 B x y) = (term42 B x y).
Proof. exact (MK_COMB (@lem5037820) (@lem5037819 B x y)). Qed.
Lemma lem5037823 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5037824 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5037823 B P x). Qed.
Lemma lem5037825 {B : Type'} (v : B -> Prop) (x : B) : (@IN B x v) = (v x).
Proof. exact (@lem5037824 B v x). Qed.
Lemma lem5037826 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term43 B y x v) = (term44 B y v x).
Proof. exact (MK_COMB (@lem5037821 B x y) (@lem5037825 B v x)). Qed.
Lemma lem5037831 {B : Type'} (y : B) (v : B -> Prop) : (term45 B y v) = (term46 B y v).
Proof. exact (fun_ext (fun x : B => @lem5037826 B y v x)). Qed.
Lemma lem5037832 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5037833 {B : Type'} (y : B) (v : B -> Prop) : (term12 B y v) = (term47 B y v).
Proof. exact (MK_COMB (@lem5037832 B) (@lem5037831 B y v)). Qed.
Lemma lem5037838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037839 {B : Type'} (y : B) (v : B -> Prop) : (term14 B y v) = (term48 B y v).
Proof. exact (MK_COMB (@lem5037838) (@lem5037833 B y v)). Qed.
Lemma lem5037853 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5037854 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5037853 A P x). Qed.
Lemma lem5037855 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5037854 A s x). Qed.
Lemma lem5037856 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037857 {A : Type'} (s : A -> Prop) (x : A) : (term31 A x s) = (term34 A s x).
Proof. exact (MK_COMB (@lem5037856) (@lem5037855 A s x)). Qed.
Lemma lem5037859 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5037860 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5037859 A P x). Qed.
Lemma lem5037861 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5037860 A u x). Qed.
Lemma lem5037862 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term49 A s x u) = (term50 A s u x).
Proof. exact (MK_COMB (@lem5037857 A s x) (@lem5037861 A u x)). Qed.
Lemma lem5037865 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term51 A s u) = (term52 A s u).
Proof. exact (fun_ext (fun x : A => @lem5037862 A s u x)). Qed.
Lemma lem5037866 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037867 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term10 A s u) = (term53 A s u).
Proof. exact (MK_COMB (@lem5037866 A) (@lem5037865 A s u)). Qed.
Lemma lem5037872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037873 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term16 A s u) = (term54 A s u).
Proof. exact (MK_COMB (@lem5037872) (@lem5037867 A s u)). Qed.
Lemma lem5037881 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term55 A B y f s) = (term56 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5037882 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term55 A B y f s) = (term56 A B y f s).
Proof. exact (@lem5037881 A B y f s). Qed.
Lemma lem5037883 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term55 A B x f s) = (term56 A B x f s).
Proof. exact (@lem5037882 A B x f s). Qed.
Lemma lem5037893 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5037894 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5037893 A P x). Qed.
Lemma lem5037895 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5037894 A s x). Qed.
Lemma lem5037896 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term57 A B x f x') = (term57 A B x f x').
Proof. exact (eq_refl (term57 A B x f x')). Qed.
Lemma lem5037897 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term58 A B x f x' s) = (term59 A B x f s x').
Proof. exact (MK_COMB (@lem5037896 A B x f x') (@lem5037895 A s x')). Qed.
Lemma lem5037900 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term60 A B x f s) = (term61 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5037897 A B x f s x')). Qed.
Lemma lem5037901 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5037902 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term56 A B x f s) = (term62 A B x f s).
Proof. exact (MK_COMB (@lem5037901 A) (@lem5037900 A B x f s)). Qed.
Lemma lem5037907 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term55 A B x f s) = (term62 A B x f s).
Proof. exact (TRANS (@lem5037883 A B x f s) (@lem5037902 A B x f s)). Qed.
Lemma lem5037908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5037909 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term63 A B x f s) = (term64 A B x f s).
Proof. exact (MK_COMB (@lem5037908) (@lem5037907 A B x f s)). Qed.
Lemma lem5037911 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term35 A x y s) = (term36 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5037912 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term35 B x y s) = (term36 B y x s).
Proof. exact (@lem5037911 B y x s). Qed.
Lemma lem5037913 {B : Type'} (y : B) (x : B) : (term37 B x y) = (term38 B y x).
Proof. exact (@lem5037912 B y x (@EMPTY B)). Qed.
Lemma lem5037919 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5037920 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem5037919 B x). Qed.
Lemma lem5037921 {B : Type'} (x : B) (y : B) : (term39 B x y) = (term39 B x y).
Proof. exact (eq_refl (term39 B x y)). Qed.
Lemma lem5037922 {B : Type'} (x : B) (y : B) : (term38 B y x) = (term40 B x y).
Proof. exact (MK_COMB (@lem5037921 B x y) (@lem5037920 B x)). Qed.
Lemma lem5037924 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5037925 {B : Type'} (x : B) (y : B) : (term40 B x y) = (x = y).
Proof. exact (@lem5037924 (x = y)). Qed.
Lemma lem5037928 {B : Type'} (x : B) (y : B) : (term38 B y x) = (x = y).
Proof. exact (TRANS (@lem5037922 B x y) (@lem5037925 B x y)). Qed.
Lemma lem5037929 {B : Type'} (x : B) (y : B) : (term37 B x y) = (x = y).
Proof. exact (TRANS (@lem5037913 B y x) (@lem5037928 B x y)). Qed.
Lemma lem5037930 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : ((term55 A B x f s) = (term37 B x y)) = ((term62 A B x f s) = (x = y)).
Proof. exact (MK_COMB (@lem5037909 A B x f s) (@lem5037929 B x y)). Qed.
Lemma lem5037933 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term65 A B f s y) = (term66 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5037930 A B f s x y)). Qed.
Lemma lem5037934 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5037935 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term18 A B f s y) = (term67 A B f s y).
Proof. exact (MK_COMB (@lem5037934 B) (@lem5037933 A B f s y)). Qed.
Lemma lem5037940 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term20 A B u f s y) = (term68 A B u f s y).
Proof. exact (MK_COMB (@lem5037873 A s u) (@lem5037935 A B f s y)). Qed.
Lemma lem5037943 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term22 A B u f y) = (term69 A B u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5037940 A B u f s y)). Qed.
Lemma lem5037944 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5037945 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term24 A B u f y) = (term70 A B u f y).
Proof. exact (MK_COMB (@lem5037944 A) (@lem5037943 A B u f y)). Qed.
Lemma lem5037950 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term25 A B v u f y) = (term71 A B v u f y).
Proof. exact (MK_COMB (@lem5037839 B y v) (@lem5037945 A B u f y)). Qed.
Lemma lem5037953 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037954 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term27 A B v u f y) = (term72 A B v u f y).
Proof. exact (MK_COMB (@lem5037953) (@lem5037950 A B v u f y)). Qed.
Lemma lem5037962 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5037963 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5037962 A P x). Qed.
Lemma lem5037964 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5037963 A u x). Qed.
Lemma lem5037965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037966 {A : Type'} (u : A -> Prop) (x : A) : (term73 A x u) = (term74 A u x).
Proof. exact (MK_COMB (@lem5037965) (@lem5037964 A u x)). Qed.
Lemma lem5037969 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem5037970 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term75 A B u f x y) = (term76 A B u f x y).
Proof. exact (MK_COMB (@lem5037966 A u x) (@lem5037969 A B f x y)). Qed.
Lemma lem5037973 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term77 A B u f y) = (term78 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5037970 A B u f x y)). Qed.
Lemma lem5037974 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5037975 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term28 A B u f y) = (term79 A B u f y).
Proof. exact (MK_COMB (@lem5037974 A) (@lem5037973 A B u f y)). Qed.
Lemma lem5037980 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term30 A B v u f y) = (term80 A B v u f y).
Proof. exact (MK_COMB (@lem5037954 A B v u f y) (@lem5037975 A B u f y)). Qed.
Lemma lem5037983 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term33 A B v u f y) = (term81 A B v u f y).
Proof. exact (MK_COMB (@lem5037789 B v y) (@lem5037980 A B v u f y)). Qed.
Lemma lem5037986 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term81 A B v u f y) = (term33 A B v u f y).
Proof. exact (SYM (@lem5037983 A B v u f y)). Qed.
Lemma lem5037988 (p : Prop) : p = (term82 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5037989 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term81 A B v u f y) = (term83 A B v u f y).
Proof. exact (@lem5037988 (term81 A B v u f y)). Qed.
Lemma lem5037990 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term83 A B v u f y) = (term81 A B v u f y).
Proof. exact (SYM (@lem5037989 A B v u f y)). Qed.
Lemma lem5037991 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term84 A B v u f y) : term84 A B v u f y.
Proof. exact (h1). Qed.
Lemma lem5037994 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term83 A B v u f y) : term83 A B v u f y.
Proof. exact (h1). Qed.
Lemma lem5037995 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term85 A B v u f y.
Proof. exact (fun h0 : term83 A B v u f y => @lem5037994 A B v u f y h0). Qed.
Lemma lem5037996 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term85 A B v u f y) : term85 A B v u f y.
Proof. exact (h1). Qed.
Lemma lem5037997 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term83 A B v u f y) : term83 A B v u f y.
Proof. exact (h1). Qed.
Lemma lem5037998 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term83 A B v u f y) (h2 : term85 A B v u f y) : term83 A B v u f y.
Proof. exact (@lem5037996 A B v u f y h2 (@lem5037997 A B v u f y h1)). Qed.
Lemma lem5037999 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term83 A B v u f y) : term86 A B v u f y.
Proof. exact (fun h0 : term85 A B v u f y => @lem5037998 A B v u f y h1 h0). Qed.
Lemma lem5038000 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term85 A B v u f y) : term85 A B v u f y.
Proof. exact (h1). Qed.
Lemma lem5038001 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term83 A B v u f y) (h2 : term85 A B v u f y) : term83 A B v u f y.
Proof. exact (@lem5037999 A B v u f y h1 (@lem5038000 A B v u f y h2)). Qed.
Lemma lem5038002 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term85 A B v u f y) : term85 A B v u f y.
Proof. exact (fun h0 : term83 A B v u f y => @lem5038001 A B v u f y h0 h1). Qed.
Lemma lem5038003 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term87 A B v u f y.
Proof. exact (fun h0 : term85 A B v u f y => @lem5038002 A B v u f y h0). Qed.
Lemma lem5038006 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term85 A B v u f y.
Proof. exact (@lem5038003 A B v u f y (@lem5037995 A B v u f y)). Qed.
Lemma lem5038007 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term85 A B v u f y.
Proof. exact (@lem5038006 A B v u f y). Qed.
Lemma lem5038025 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5038026 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term83 A B v u f y) = (term88 A B v u f y).
Proof. exact (@lem5038025 (term84 A B v u f y)). Qed.
Lemma lem5038028 (t : Prop) : (term89 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5038029 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term88 A B v u f y) = (term81 A B v u f y).
Proof. exact (@lem5038028 (term81 A B v u f y)). Qed.
Lemma lem5038032 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term83 A B v u f y) = (term81 A B v u f y).
Proof. exact (TRANS (@lem5038026 A B v u f y) (@lem5038029 A B v u f y)). Qed.
Lemma lem5038167 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term90 A B u f y) = (term91 A B u f y).
Proof. exact (fun_ext (fun v : B -> Prop => @lem5038032 A B v u f y)). Qed.
Lemma lem5038168 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5038169 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term92 A B u f y) = (term93 A B u f y).
Proof. exact (MK_COMB (@lem5038168 B) (@lem5038167 A B u f y)). Qed.
Lemma lem5038174 {A B : Type'} (f : A -> B) (y : B) : (term94 A B f y) = (term95 A B f y).
Proof. exact (fun_ext (fun u : A -> Prop => @lem5038169 A B u f y)). Qed.
Lemma lem5038175 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5038176 {A B : Type'} (f : A -> B) (y : B) : (term96 A B f y) = (term97 A B f y).
Proof. exact (MK_COMB (@lem5038175 A) (@lem5038174 A B f y)). Qed.
Lemma lem5038181 {A B : Type'} (y : B) : (term98 A B y) = (term99 A B y).
Proof. exact (fun_ext (fun f : A -> B => @lem5038176 A B f y)). Qed.
Lemma lem5038182 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5038183 {A B : Type'} (y : B) : (term100 A B y) = (term101 A B y).
Proof. exact (MK_COMB (@lem5038182 A B) (@lem5038181 A B y)). Qed.
Lemma lem5038188 {A B : Type'} : (term102 A B) = (term103 A B).
Proof. exact (fun_ext (fun y : B => @lem5038183 A B y)). Qed.
Lemma lem5038189 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038198 {A B : Type'} : (term104 A B) = (term105 A B).
Proof. exact (MK_COMB (@lem5038189 B) (@lem5038188 A B)). Qed.
Lemma lem5038203 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term76 A B u f x y) = (term76 A B u f x y).
Proof. exact (eq_refl (term76 A B u f x y)). Qed.
Lemma lem5038204 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term78 A B u f y) = (term78 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5038203 A B u f x y)). Qed.
Lemma lem5038205 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5038206 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term79 A B u f y) = (term79 A B u f y).
Proof. exact (MK_COMB (@lem5038205 A) (@lem5038204 A B u f y)). Qed.
Lemma lem5038207 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5038212 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term59 A B x f s x') = (term59 A B x f s x').
Proof. exact (eq_refl (term59 A B x f s x')). Qed.
Lemma lem5038213 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term61 A B x f s) = (term61 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5038212 A B x f s x')). Qed.
Lemma lem5038214 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5038215 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term62 A B x f s) = (term62 A B x f s).
Proof. exact (MK_COMB (@lem5038214 A) (@lem5038213 A B x f s)). Qed.
Lemma lem5038216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038217 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term64 A B x f s) = (term64 A B x f s).
Proof. exact (MK_COMB (@lem5038216) (@lem5038215 A B x f s)). Qed.
Lemma lem5038218 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : ((term62 A B x f s) = (x = y)) = ((term62 A B x f s) = (x = y)).
Proof. exact (MK_COMB (@lem5038217 A B x f s) (@lem5038207 B x y)). Qed.
Lemma lem5038219 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term66 A B f s y) = (term66 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5038218 A B f s x y)). Qed.
Lemma lem5038220 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038221 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term67 A B f s y) = (term67 A B f s y).
Proof. exact (MK_COMB (@lem5038220 B) (@lem5038219 A B f s y)). Qed.
Lemma lem5038226 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term50 A s u x) = (term50 A s u x).
Proof. exact (eq_refl (term50 A s u x)). Qed.
Lemma lem5038227 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term52 A s u) = (term52 A s u).
Proof. exact (fun_ext (fun x : A => @lem5038226 A s u x)). Qed.
Lemma lem5038228 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5038229 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term53 A s u) = (term53 A s u).
Proof. exact (MK_COMB (@lem5038228 A) (@lem5038227 A s u)). Qed.
Lemma lem5038230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5038231 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term54 A s u) = (term54 A s u).
Proof. exact (MK_COMB (@lem5038230) (@lem5038229 A s u)). Qed.
Lemma lem5038232 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term68 A B u f s y) = (term68 A B u f s y).
Proof. exact (MK_COMB (@lem5038231 A s u) (@lem5038221 A B f s y)). Qed.
Lemma lem5038233 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term69 A B u f y) = (term69 A B u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5038232 A B u f s y)). Qed.
Lemma lem5038234 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5038235 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term70 A B u f y) = (term70 A B u f y).
Proof. exact (MK_COMB (@lem5038234 A) (@lem5038233 A B u f y)). Qed.
Lemma lem5038240 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term44 B y v x) = (term44 B y v x).
Proof. exact (eq_refl (term44 B y v x)). Qed.
Lemma lem5038241 {B : Type'} (y : B) (v : B -> Prop) : (term46 B y v) = (term46 B y v).
Proof. exact (fun_ext (fun x : B => @lem5038240 B y v x)). Qed.
Lemma lem5038242 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038243 {B : Type'} (y : B) (v : B -> Prop) : (term47 B y v) = (term47 B y v).
Proof. exact (MK_COMB (@lem5038242 B) (@lem5038241 B y v)). Qed.
Lemma lem5038244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5038245 {B : Type'} (y : B) (v : B -> Prop) : (term48 B y v) = (term48 B y v).
Proof. exact (MK_COMB (@lem5038244) (@lem5038243 B y v)). Qed.
Lemma lem5038246 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term71 A B v u f y) = (term71 A B v u f y).
Proof. exact (MK_COMB (@lem5038245 B y v) (@lem5038235 A B u f y)). Qed.
Lemma lem5038247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5038248 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term72 A B v u f y) = (term72 A B v u f y).
Proof. exact (MK_COMB (@lem5038247) (@lem5038246 A B v u f y)). Qed.
Lemma lem5038249 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term80 A B v u f y) = (term80 A B v u f y).
Proof. exact (MK_COMB (@lem5038248 A B v u f y) (@lem5038206 A B u f y)). Qed.
Lemma lem5038252 {B : Type'} (v : B -> Prop) (y : B) : (term34 B v y) = (term34 B v y).
Proof. exact (eq_refl (term34 B v y)). Qed.
Lemma lem5038253 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term81 A B v u f y) = (term81 A B v u f y).
Proof. exact (MK_COMB (@lem5038252 B v y) (@lem5038249 A B v u f y)). Qed.
Lemma lem5038254 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term91 A B u f y) = (term91 A B u f y).
Proof. exact (fun_ext (fun v : B -> Prop => @lem5038253 A B v u f y)). Qed.
Lemma lem5038255 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5038256 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term93 A B u f y) = (term93 A B u f y).
Proof. exact (MK_COMB (@lem5038255 B) (@lem5038254 A B u f y)). Qed.
Lemma lem5038257 {A B : Type'} (f : A -> B) (y : B) : (term95 A B f y) = (term95 A B f y).
Proof. exact (fun_ext (fun u : A -> Prop => @lem5038256 A B u f y)). Qed.
Lemma lem5038258 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5038259 {A B : Type'} (f : A -> B) (y : B) : (term97 A B f y) = (term97 A B f y).
Proof. exact (MK_COMB (@lem5038258 A) (@lem5038257 A B f y)). Qed.
Lemma lem5038260 {A B : Type'} (y : B) : (term99 A B y) = (term99 A B y).
Proof. exact (fun_ext (fun f : A -> B => @lem5038259 A B f y)). Qed.
Lemma lem5038261 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5038262 {A B : Type'} (y : B) : (term101 A B y) = (term101 A B y).
Proof. exact (MK_COMB (@lem5038261 A B) (@lem5038260 A B y)). Qed.
Lemma lem5038263 {A B : Type'} : (term103 A B) = (term103 A B).
Proof. exact (fun_ext (fun y : B => @lem5038262 A B y)). Qed.
Lemma lem5038264 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038265 {A B : Type'} : (term105 A B) = (term105 A B).
Proof. exact (MK_COMB (@lem5038264 B) (@lem5038263 A B)). Qed.
Lemma lem5038344 {A B : Type'} : (term104 A B) = (term105 A B).
Proof. exact (TRANS (@lem5038198 A B) (@lem5038265 A B)). Qed.
Lemma lem5038345 {A B : Type'} : (term105 A B) = (term104 A B).
Proof. exact (SYM (@lem5038344 A B)). Qed.
Lemma lem5038347 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term71 A B v u f y) : term71 A B v u f y.
Proof. exact (h1). Qed.
Lemma lem5038349 (p : Prop) : p = (term82 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5038350 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term79 A B u f y) = (term106 A B u f y).
Proof. exact (@lem5038349 (term79 A B u f y)). Qed.
Lemma lem5038351 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term106 A B u f y) = (term79 A B u f y).
Proof. exact (SYM (@lem5038350 A B u f y)). Qed.
Lemma lem5038352 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term107 A B u f y.
Proof. exact (h1). Qed.
Lemma lem5038358 {B : Type'} (v : B -> Prop) (y : B) (h1 : v y) : v y.
Proof. exact (h1). Qed.
Lemma lem5038365 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term108 B y v x) = (term109 B y v x).
Proof. exact (@lem17362 (x = y) (v x)). Qed.
Lemma lem5038366 {B : Type'} (P : B -> Prop) : (term110 B P) = (term111 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5038367 {B : Type'} (y : B) (v : B -> Prop) : (term112 B y v) = (term113 B y v).
Proof. exact (@lem5038366 B (term46 B y v)). Qed.
Lemma lem5038368 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term114 B y v x) = (term44 B y v x).
Proof. exact (eq_refl (term114 B y v x)). Qed.
Lemma lem5038369 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5038370 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term115 B y v x) = (term108 B y v x).
Proof. exact (MK_COMB (@lem5038369) (@lem5038368 B y v x)). Qed.
Lemma lem5038371 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term115 B y v x) = (term109 B y v x).
Proof. exact (TRANS (@lem5038370 B y v x) (@lem5038365 B y v x)). Qed.
Lemma lem5038372 {B : Type'} (y : B) (v : B -> Prop) : (term116 B y v) = (term117 B y v).
Proof. exact (fun_ext (fun x : B => @lem5038371 B y v x)). Qed.
Lemma lem5038373 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5038374 {B : Type'} (y : B) (v : B -> Prop) : (term113 B y v) = (term118 B y v).
Proof. exact (MK_COMB (@lem5038373 B) (@lem5038372 B y v)). Qed.
Lemma lem5038375 {B : Type'} (y : B) (v : B -> Prop) : (term112 B y v) = (term118 B y v).
Proof. exact (TRANS (@lem5038367 B y v) (@lem5038374 B y v)). Qed.
Lemma lem5038382 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term50 A s u x) = (term119 A s u x).
Proof. exact (@lem17265 (s x) (u x)). Qed.
Lemma lem5038383 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term52 A s u) = (term120 A s u).
Proof. exact (fun_ext (fun x : A => @lem5038382 A s u x)). Qed.
Lemma lem5038384 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5038385 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term53 A s u) = (term121 A s u).
Proof. exact (MK_COMB (@lem5038384 A) (@lem5038383 A s u)). Qed.
Lemma lem5038394 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term122 A B x f s x') = (term123 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem5038397 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term59 A B x f s x') = (term59 A B x f s x').
Proof. exact (eq_refl (term59 A B x f s x')). Qed.
Lemma lem5038398 {A : Type'} (P : A -> Prop) : (term124 A P) = (term125 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5038399 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term126 A B x f s) = (term127 A B x f s).
Proof. exact (@lem5038398 A (term61 A B x f s)). Qed.
Lemma lem5038400 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term128 A B x f s x') = (term59 A B x f s x').
Proof. exact (eq_refl (term128 A B x f s x')). Qed.
Lemma lem5038401 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5038402 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term129 A B x f s x') = (term122 A B x f s x').
Proof. exact (MK_COMB (@lem5038401) (@lem5038400 A B x f s x')). Qed.
Lemma lem5038403 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term129 A B x f s x') = (term123 A B x f s x').
Proof. exact (TRANS (@lem5038402 A B x f s x') (@lem5038394 A B x f s x')). Qed.
Lemma lem5038404 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term130 A B x f s) = (term131 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5038403 A B x f s x')). Qed.
Lemma lem5038405 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5038406 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term127 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem5038405 A) (@lem5038404 A B x f s)). Qed.
Lemma lem5038407 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term126 A B x f s) = (term132 A B x f s).
Proof. exact (TRANS (@lem5038399 A B x f s) (@lem5038406 A B x f s)). Qed.
Lemma lem5038408 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term61 A B x f s) = (term61 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5038397 A B x f s x')). Qed.
Lemma lem5038409 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5038410 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term62 A B x f s) = (term62 A B x f s).
Proof. exact (MK_COMB (@lem5038409 A) (@lem5038408 A B x f s)). Qed.
Lemma lem5038411 {B : Type'} (x : B) (y : B) : (term133 B x y) = (term133 B x y).
Proof. exact (eq_refl (term133 B x y)). Qed.
Lemma lem5038412 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5038413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5038414 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term134 A B x f s) = (term135 A B x f s).
Proof. exact (MK_COMB (@lem5038413) (@lem5038407 A B x f s)). Qed.
Lemma lem5038415 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term136 A B f s x y) = (term137 A B f s x y).
Proof. exact (MK_COMB (@lem5038414 A B x f s) (@lem5038412 B x y)). Qed.
Lemma lem5038416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5038417 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term138 A B x f s) = (term138 A B x f s).
Proof. exact (MK_COMB (@lem5038416) (@lem5038410 A B x f s)). Qed.
Lemma lem5038418 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term139 A B f s x y) = (term139 A B f s x y).
Proof. exact (MK_COMB (@lem5038417 A B x f s) (@lem5038411 B x y)). Qed.
Lemma lem5038419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5038420 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term140 A B f s x y) = (term140 A B f s x y).
Proof. exact (MK_COMB (@lem5038419) (@lem5038418 A B f s x y)). Qed.
Lemma lem5038421 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term141 A B f s x y) = (term142 A B f s x y).
Proof. exact (MK_COMB (@lem5038420 A B f s x y) (@lem5038415 A B f s x y)). Qed.
Lemma lem5038422 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : ((term62 A B x f s) = (x = y)) = (term141 A B f s x y).
Proof. exact (@lem17784 (term62 A B x f s) (x = y)). Qed.
Lemma lem5038423 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : ((term62 A B x f s) = (x = y)) = (term142 A B f s x y).
Proof. exact (TRANS (@lem5038422 A B f s x y) (@lem5038421 A B f s x y)). Qed.
Lemma lem5038424 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term66 A B f s y) = (term143 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5038423 A B f s x y)). Qed.
Lemma lem5038425 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038426 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term67 A B f s y) = (term144 A B f s y).
Proof. exact (MK_COMB (@lem5038425 B) (@lem5038424 A B f s y)). Qed.
Lemma lem5038427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5038428 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term54 A s u) = (term145 A s u).
Proof. exact (MK_COMB (@lem5038427) (@lem5038385 A s u)). Qed.
Lemma lem5038429 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term68 A B u f s y) = (term146 A B u f s y).
Proof. exact (MK_COMB (@lem5038428 A s u) (@lem5038426 A B f s y)). Qed.
Lemma lem5038430 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term69 A B u f y) = (term147 A B u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5038429 A B u f s y)). Qed.
Lemma lem5038431 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5038432 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term70 A B u f y) = (term148 A B u f y).
Proof. exact (MK_COMB (@lem5038431 A) (@lem5038430 A B u f y)). Qed.
Lemma lem5038433 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5038434 {B : Type'} (y : B) (v : B -> Prop) : (term149 B y v) = (term150 B y v).
Proof. exact (MK_COMB (@lem5038433) (@lem5038375 B y v)). Qed.
Lemma lem5038435 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term151 A B v u f y) = (term152 A B v u f y).
Proof. exact (MK_COMB (@lem5038434 B y v) (@lem5038432 A B u f y)). Qed.
Lemma lem5038436 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term71 A B v u f y) = (term151 A B v u f y).
Proof. exact (@lem17265 (term47 B y v) (term70 A B u f y)). Qed.
Lemma lem5038437 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term71 A B v u f y) = (term152 A B v u f y).
Proof. exact (TRANS (@lem5038436 A B v u f y) (@lem5038435 A B v u f y)). Qed.
Lemma lem5038567 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term154 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5038568 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term153 B P Q) = (term154 B P Q).
Proof. exact (@lem5038567 B P Q). Qed.
Lemma lem5038569 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term155 A B f s y) = (term156 A B f s y).
Proof. exact (@lem5038568 B (term157 A B f s y) (term158 A B f s y)). Qed.
Lemma lem5038570 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term159 A B f s y x) = (term139 A B f s x y).
Proof. exact (eq_refl (term159 A B f s y x)). Qed.
Lemma lem5038571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5038572 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term160 A B f s y x) = (term140 A B f s x y).
Proof. exact (MK_COMB (@lem5038571) (@lem5038570 A B f s x y)). Qed.
Lemma lem5038573 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term161 A B f s y x) = (term137 A B f s x y).
Proof. exact (eq_refl (term161 A B f s y x)). Qed.
Lemma lem5038574 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term162 A B f s y x) = (term142 A B f s x y).
Proof. exact (MK_COMB (@lem5038572 A B f s x y) (@lem5038573 A B f s x y)). Qed.
Lemma lem5038575 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term163 A B f s y) = (term143 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5038574 A B f s x y)). Qed.
Lemma lem5038576 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038577 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term155 A B f s y) = (term144 A B f s y).
Proof. exact (MK_COMB (@lem5038576 B) (@lem5038575 A B f s y)). Qed.
Lemma lem5038578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038579 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term164 A B f s y) = (term165 A B f s y).
Proof. exact (MK_COMB (@lem5038578) (@lem5038577 A B f s y)). Qed.
Lemma lem5038580 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term159 A B f s y x) = (term139 A B f s x y).
Proof. exact (eq_refl (term159 A B f s y x)). Qed.
Lemma lem5038581 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term166 A B f s y) = (term157 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5038580 A B f s x y)). Qed.
Lemma lem5038582 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038583 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term167 A B f s y) = (term168 A B f s y).
Proof. exact (MK_COMB (@lem5038582 B) (@lem5038581 A B f s y)). Qed.
Lemma lem5038584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5038585 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term169 A B f s y) = (term170 A B f s y).
Proof. exact (MK_COMB (@lem5038584) (@lem5038583 A B f s y)). Qed.
Lemma lem5038586 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term161 A B f s y x) = (term137 A B f s x y).
Proof. exact (eq_refl (term161 A B f s y x)). Qed.
Lemma lem5038587 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term171 A B f s y) = (term158 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5038586 A B f s x y)). Qed.
Lemma lem5038588 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038589 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term172 A B f s y) = (term173 A B f s y).
Proof. exact (MK_COMB (@lem5038588 B) (@lem5038587 A B f s y)). Qed.
Lemma lem5038590 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term156 A B f s y) = (term174 A B f s y).
Proof. exact (MK_COMB (@lem5038585 A B f s y) (@lem5038589 A B f s y)). Qed.
Lemma lem5038591 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : ((term155 A B f s y) = (term156 A B f s y)) = ((term144 A B f s y) = (term174 A B f s y)).
Proof. exact (MK_COMB (@lem5038579 A B f s y) (@lem5038590 A B f s y)). Qed.
Lemma lem5038592 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term144 A B f s y) = (term174 A B f s y).
Proof. exact (EQ_MP (@lem5038591 A B f s y) (@lem5038569 A B f s y)). Qed.
Lemma lem5038769 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term145 A s u) = (term145 A s u).
Proof. exact (eq_refl (term145 A s u)). Qed.
Lemma lem5038770 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term146 A B u f s y) = (term175 A B u f s y).
Proof. exact (MK_COMB (@lem5038769 A s u) (@lem5038592 A B f s y)). Qed.
Lemma lem5038771 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term147 A B u f y) = (term176 A B u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5038770 A B u f s y)). Qed.
Lemma lem5038772 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5038773 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term148 A B u f y) = (term177 A B u f y).
Proof. exact (MK_COMB (@lem5038772 A) (@lem5038771 A B u f y)). Qed.
Lemma lem5038822 {B : Type'} (y : B) (v : B -> Prop) : (term150 B y v) = (term150 B y v).
Proof. exact (eq_refl (term150 B y v)). Qed.
Lemma lem5038823 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term152 A B v u f y) = (term178 A B v u f y).
Proof. exact (MK_COMB (@lem5038822 B y v) (@lem5038773 A B u f y)). Qed.
Lemma lem5038825 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5038826 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (@lem5038825 A P Q). Qed.
Lemma lem5038827 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term181 A B f s x y) = (term182 A B f s x y).
Proof. exact (@lem5038826 A (term61 A B x f s) (term133 B x y)). Qed.
Lemma lem5038828 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term128 A B x f s x') = (term59 A B x f s x').
Proof. exact (eq_refl (term128 A B x f s x')). Qed.
Lemma lem5038829 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term183 A B x f s) = (term61 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5038828 A B x f s x')). Qed.
Lemma lem5038830 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5038831 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term184 A B x f s) = (term62 A B x f s).
Proof. exact (MK_COMB (@lem5038830 A) (@lem5038829 A B x f s)). Qed.
Lemma lem5038832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5038833 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term185 A B x f s) = (term138 A B x f s).
Proof. exact (MK_COMB (@lem5038832) (@lem5038831 A B x f s)). Qed.
Lemma lem5038834 {B : Type'} (x : B) (y : B) : (term133 B x y) = (term133 B x y).
Proof. exact (eq_refl (term133 B x y)). Qed.
Lemma lem5038835 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term181 A B f s x y) = (term139 A B f s x y).
Proof. exact (MK_COMB (@lem5038833 A B x f s) (@lem5038834 B x y)). Qed.
Lemma lem5038836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038837 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term186 A B f s x y) = (term187 A B f s x y).
Proof. exact (MK_COMB (@lem5038836) (@lem5038835 A B f s x y)). Qed.
Lemma lem5038838 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term128 A B x f s x') = (term59 A B x f s x').
Proof. exact (eq_refl (term128 A B x f s x')). Qed.
Lemma lem5038839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5038840 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term188 A B x f s x') = (term189 A B x f s x').
Proof. exact (MK_COMB (@lem5038839) (@lem5038838 A B x f s x')). Qed.
Lemma lem5038841 {B : Type'} (x : B) (y : B) : (term133 B x y) = (term133 B x y).
Proof. exact (eq_refl (term133 B x y)). Qed.
Lemma lem5038842 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (x' : B) (y : B) : (term190 A B f s x x' y) = (term191 A B f s x x' y).
Proof. exact (MK_COMB (@lem5038840 A B x' f s x) (@lem5038841 B x' y)). Qed.
Lemma lem5038843 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term192 A B f s x y) = (term193 A B f s x y).
Proof. exact (fun_ext (fun x' : A => @lem5038842 A B f s x' x y)). Qed.
Lemma lem5038844 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5038845 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term182 A B f s x y) = (term194 A B f s x y).
Proof. exact (MK_COMB (@lem5038844 A) (@lem5038843 A B f s x y)). Qed.
Lemma lem5038846 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : ((term181 A B f s x y) = (term182 A B f s x y)) = ((term139 A B f s x y) = (term194 A B f s x y)).
Proof. exact (MK_COMB (@lem5038837 A B f s x y) (@lem5038845 A B f s x y)). Qed.
Lemma lem5038847 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term139 A B f s x y) = (term194 A B f s x y).
Proof. exact (EQ_MP (@lem5038846 A B f s x y) (@lem5038827 A B f s x y)). Qed.
Lemma lem5038848 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term157 A B f s y) = (term195 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5038847 A B f s x y)). Qed.
Lemma lem5038849 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038850 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term168 A B f s y) = (term196 A B f s y).
Proof. exact (MK_COMB (@lem5038849 B) (@lem5038848 A B f s y)). Qed.
Lemma lem5038852 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5038853 {A B : Type'} (P : type1470 A B) : (term199 A B P) = (term200 A B P).
Proof. exact (@lem5038852 B A P). Qed.
Lemma lem5038854 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term201 A B f s y) = (term202 A B f s y).
Proof. exact (@lem5038853 A B (term203 A B f s y)). Qed.
Lemma lem5038855 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term204 A B f s y x) = (term193 A B f s x y).
Proof. exact (eq_refl (term204 A B f s y x)). Qed.
Lemma lem5038856 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5038857 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) (x' : A) : (term205 A B f s y x x') = (term206 A B f s x y x').
Proof. exact (MK_COMB (@lem5038855 A B f s x y) (@lem5038856 A x')). Qed.
Lemma lem5038858 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (x' : B) (y : B) : (term206 A B f s x' y x) = (term191 A B f s x x' y).
Proof. exact (eq_refl (term206 A B f s x' y x)). Qed.
Lemma lem5038859 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (x' : B) (y : B) : (term205 A B f s y x' x) = (term191 A B f s x x' y).
Proof. exact (TRANS (@lem5038857 A B f s x' y x) (@lem5038858 A B f s x x' y)). Qed.
Lemma lem5038860 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term207 A B f s y x) = (term193 A B f s x y).
Proof. exact (fun_ext (fun x' : A => @lem5038859 A B f s x' x y)). Qed.
Lemma lem5038861 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5038862 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term208 A B f s y x) = (term194 A B f s x y).
Proof. exact (MK_COMB (@lem5038861 A) (@lem5038860 A B f s x y)). Qed.
Lemma lem5038863 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term209 A B f s y) = (term195 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5038862 A B f s x y)). Qed.
Lemma lem5038864 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038865 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term201 A B f s y) = (term196 A B f s y).
Proof. exact (MK_COMB (@lem5038864 B) (@lem5038863 A B f s y)). Qed.
Lemma lem5038866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038867 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term210 A B f s y) = (term211 A B f s y).
Proof. exact (MK_COMB (@lem5038866) (@lem5038865 A B f s y)). Qed.
Lemma lem5038868 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term204 A B f s y x) = (term193 A B f s x y).
Proof. exact (eq_refl (term204 A B f s y x)). Qed.
Lemma lem5038869 {A B : Type'} (x : B -> A) (x' : B) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem5038870 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) (x : B -> A) (x' : B) : (term212 A B f s y x x') = (term213 A B f s y x x').
Proof. exact (MK_COMB (@lem5038868 A B f s x' y) (@lem5038869 A B x x')). Qed.
Lemma lem5038871 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B -> A) (x' : B) (y : B) : (term213 A B f s y x x') = (term214 A B f s x x' y).
Proof. exact (eq_refl (term213 A B f s y x x')). Qed.
Lemma lem5038872 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B -> A) (x' : B) (y : B) : (term212 A B f s y x x') = (term214 A B f s x x' y).
Proof. exact (TRANS (@lem5038870 A B f s y x x') (@lem5038871 A B f s x x' y)). Qed.
Lemma lem5038873 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B -> A) (y : B) : (term215 A B f s y x) = (term216 A B f s x y).
Proof. exact (fun_ext (fun x' : B => @lem5038872 A B f s x x' y)). Qed.
Lemma lem5038874 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5038875 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B -> A) (y : B) : (term217 A B f s y x) = (term218 A B f s x y).
Proof. exact (MK_COMB (@lem5038874 B) (@lem5038873 A B f s x y)). Qed.
Lemma lem5038876 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term219 A B f s y) = (term220 A B f s y).
Proof. exact (fun_ext (fun x : B -> A => @lem5038875 A B f s x y)). Qed.
Lemma lem5038877 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5038878 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term202 A B f s y) = (term221 A B f s y).
Proof. exact (MK_COMB (@lem5038877 A B) (@lem5038876 A B f s y)). Qed.
Lemma lem5038879 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : ((term201 A B f s y) = (term202 A B f s y)) = ((term196 A B f s y) = (term221 A B f s y)).
Proof. exact (MK_COMB (@lem5038867 A B f s y) (@lem5038878 A B f s y)). Qed.
Lemma lem5038880 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term196 A B f s y) = (term221 A B f s y).
Proof. exact (EQ_MP (@lem5038879 A B f s y) (@lem5038854 A B f s y)). Qed.
Lemma lem5038881 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term168 A B f s y) = (term221 A B f s y).
Proof. exact (TRANS (@lem5038850 A B f s y) (@lem5038880 A B f s y)). Qed.
Lemma lem5038882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5038883 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term170 A B f s y) = (term222 A B f s y).
Proof. exact (MK_COMB (@lem5038882) (@lem5038881 A B f s y)). Qed.
Lemma lem5038884 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term173 A B f s y) = (term173 A B f s y).
Proof. exact (eq_refl (term173 A B f s y)). Qed.
Lemma lem5038885 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term174 A B f s y) = (term223 A B f s y).
Proof. exact (MK_COMB (@lem5038883 A B f s y) (@lem5038884 A B f s y)). Qed.
Lemma lem5038887 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5038888 {A B : Type'} (P : type805 A B) (Q : Prop) : (term226 A B P Q) = (term227 A B P Q).
Proof. exact (@lem5038887 (B -> A) P Q). Qed.
Lemma lem5038889 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term228 A B f s y) = (term229 A B f s y).
Proof. exact (@lem5038888 A B (term220 A B f s y) (term173 A B f s y)). Qed.
Lemma lem5038890 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B -> A) (y : B) : (term230 A B f s y x) = (term218 A B f s x y).
Proof. exact (eq_refl (term230 A B f s y x)). Qed.
Lemma lem5038891 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term231 A B f s y) = (term220 A B f s y).
Proof. exact (fun_ext (fun x : B -> A => @lem5038890 A B f s x y)). Qed.
Lemma lem5038892 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5038893 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term232 A B f s y) = (term221 A B f s y).
Proof. exact (MK_COMB (@lem5038892 A B) (@lem5038891 A B f s y)). Qed.
Lemma lem5038894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5038895 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term233 A B f s y) = (term222 A B f s y).
Proof. exact (MK_COMB (@lem5038894) (@lem5038893 A B f s y)). Qed.
Lemma lem5038896 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term173 A B f s y) = (term173 A B f s y).
Proof. exact (eq_refl (term173 A B f s y)). Qed.
Lemma lem5038897 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term228 A B f s y) = (term223 A B f s y).
Proof. exact (MK_COMB (@lem5038895 A B f s y) (@lem5038896 A B f s y)). Qed.
Lemma lem5038898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038899 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term234 A B f s y) = (term235 A B f s y).
Proof. exact (MK_COMB (@lem5038898) (@lem5038897 A B f s y)). Qed.
Lemma lem5038900 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B -> A) (y : B) : (term230 A B f s y x) = (term218 A B f s x y).
Proof. exact (eq_refl (term230 A B f s y x)). Qed.
Lemma lem5038901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5038902 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B -> A) (y : B) : (term236 A B f s y x) = (term237 A B f s x y).
Proof. exact (MK_COMB (@lem5038901) (@lem5038900 A B f s x y)). Qed.
Lemma lem5038903 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term173 A B f s y) = (term173 A B f s y).
Proof. exact (eq_refl (term173 A B f s y)). Qed.
Lemma lem5038904 {A B : Type'} (x : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term238 A B x f s y) = (term239 A B x f s y).
Proof. exact (MK_COMB (@lem5038902 A B f s x y) (@lem5038903 A B f s y)). Qed.
Lemma lem5038905 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term240 A B f s y) = (term241 A B f s y).
Proof. exact (fun_ext (fun x : B -> A => @lem5038904 A B x f s y)). Qed.
Lemma lem5038906 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5038907 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term229 A B f s y) = (term242 A B f s y).
Proof. exact (MK_COMB (@lem5038906 A B) (@lem5038905 A B f s y)). Qed.
Lemma lem5038908 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : ((term228 A B f s y) = (term229 A B f s y)) = ((term223 A B f s y) = (term242 A B f s y)).
Proof. exact (MK_COMB (@lem5038899 A B f s y) (@lem5038907 A B f s y)). Qed.
Lemma lem5038909 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term223 A B f s y) = (term242 A B f s y).
Proof. exact (EQ_MP (@lem5038908 A B f s y) (@lem5038889 A B f s y)). Qed.
Lemma lem5038910 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term174 A B f s y) = (term242 A B f s y).
Proof. exact (TRANS (@lem5038885 A B f s y) (@lem5038909 A B f s y)). Qed.
Lemma lem5038911 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term145 A s u) = (term145 A s u).
Proof. exact (eq_refl (term145 A s u)). Qed.
Lemma lem5038912 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term175 A B u f s y) = (term243 A B u f s y).
Proof. exact (MK_COMB (@lem5038911 A s u) (@lem5038910 A B f s y)). Qed.
Lemma lem5038914 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5038915 {A B : Type'} (P : Prop) (Q : type805 A B) : (term246 A B P Q) = (term247 A B P Q).
Proof. exact (@lem5038914 (B -> A) P Q). Qed.
Lemma lem5038916 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term248 A B u f s y) = (term249 A B u f s y).
Proof. exact (@lem5038915 A B (term121 A s u) (term241 A B f s y)). Qed.
Lemma lem5038917 {A B : Type'} (x : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term250 A B f s y x) = (term239 A B x f s y).
Proof. exact (eq_refl (term250 A B f s y x)). Qed.
Lemma lem5038918 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term251 A B f s y) = (term241 A B f s y).
Proof. exact (fun_ext (fun x : B -> A => @lem5038917 A B x f s y)). Qed.
Lemma lem5038919 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5038920 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term252 A B f s y) = (term242 A B f s y).
Proof. exact (MK_COMB (@lem5038919 A B) (@lem5038918 A B f s y)). Qed.
Lemma lem5038921 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term145 A s u) = (term145 A s u).
Proof. exact (eq_refl (term145 A s u)). Qed.
Lemma lem5038922 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term248 A B u f s y) = (term243 A B u f s y).
Proof. exact (MK_COMB (@lem5038921 A s u) (@lem5038920 A B f s y)). Qed.
Lemma lem5038923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038924 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term253 A B u f s y) = (term254 A B u f s y).
Proof. exact (MK_COMB (@lem5038923) (@lem5038922 A B u f s y)). Qed.
Lemma lem5038925 {A B : Type'} (x : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term250 A B f s y x) = (term239 A B x f s y).
Proof. exact (eq_refl (term250 A B f s y x)). Qed.
Lemma lem5038926 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term145 A s u) = (term145 A s u).
Proof. exact (eq_refl (term145 A s u)). Qed.
Lemma lem5038927 {A B : Type'} (u : A -> Prop) (x : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term255 A B u f s y x) = (term256 A B u x f s y).
Proof. exact (MK_COMB (@lem5038926 A s u) (@lem5038925 A B x f s y)). Qed.
Lemma lem5038928 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term257 A B u f s y) = (term258 A B u f s y).
Proof. exact (fun_ext (fun x : B -> A => @lem5038927 A B u x f s y)). Qed.
Lemma lem5038929 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5038930 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term249 A B u f s y) = (term259 A B u f s y).
Proof. exact (MK_COMB (@lem5038929 A B) (@lem5038928 A B u f s y)). Qed.
Lemma lem5038931 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : ((term248 A B u f s y) = (term249 A B u f s y)) = ((term243 A B u f s y) = (term259 A B u f s y)).
Proof. exact (MK_COMB (@lem5038924 A B u f s y) (@lem5038930 A B u f s y)). Qed.
Lemma lem5038932 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term243 A B u f s y) = (term259 A B u f s y).
Proof. exact (EQ_MP (@lem5038931 A B u f s y) (@lem5038916 A B u f s y)). Qed.
Lemma lem5038933 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term175 A B u f s y) = (term259 A B u f s y).
Proof. exact (TRANS (@lem5038912 A B u f s y) (@lem5038932 A B u f s y)). Qed.
Lemma lem5038934 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term176 A B u f y) = (term260 A B u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5038933 A B u f s y)). Qed.
Lemma lem5038935 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5038936 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term177 A B u f y) = (term261 A B u f y).
Proof. exact (MK_COMB (@lem5038935 A) (@lem5038934 A B u f y)). Qed.
Lemma lem5038937 {B : Type'} (y : B) (v : B -> Prop) : (term150 B y v) = (term150 B y v).
Proof. exact (eq_refl (term150 B y v)). Qed.
Lemma lem5038938 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term178 A B v u f y) = (term262 A B v u f y).
Proof. exact (MK_COMB (@lem5038937 B y v) (@lem5038936 A B u f y)). Qed.
Lemma lem5038942 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5038943 {B : Type'} (P : B -> Prop) (Q : Prop) : (term179 B P Q) = (term180 B P Q).
Proof. exact (@lem5038942 B P Q). Qed.
Lemma lem5038944 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term263 A B v u f y) = (term264 A B v u f y).
Proof. exact (@lem5038943 B (term117 B y v) (term261 A B u f y)). Qed.
Lemma lem5038945 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term265 B y v x) = (term109 B y v x).
Proof. exact (eq_refl (term265 B y v x)). Qed.
Lemma lem5038946 {B : Type'} (y : B) (v : B -> Prop) : (term266 B y v) = (term117 B y v).
Proof. exact (fun_ext (fun x : B => @lem5038945 B y v x)). Qed.
Lemma lem5038947 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5038948 {B : Type'} (y : B) (v : B -> Prop) : (term267 B y v) = (term118 B y v).
Proof. exact (MK_COMB (@lem5038947 B) (@lem5038946 B y v)). Qed.
Lemma lem5038949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5038950 {B : Type'} (y : B) (v : B -> Prop) : (term268 B y v) = (term150 B y v).
Proof. exact (MK_COMB (@lem5038949) (@lem5038948 B y v)). Qed.
Lemma lem5038951 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term261 A B u f y) = (term261 A B u f y).
Proof. exact (eq_refl (term261 A B u f y)). Qed.
Lemma lem5038952 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term263 A B v u f y) = (term262 A B v u f y).
Proof. exact (MK_COMB (@lem5038950 B y v) (@lem5038951 A B u f y)). Qed.
Lemma lem5038953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038954 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term269 A B v u f y) = (term270 A B v u f y).
Proof. exact (MK_COMB (@lem5038953) (@lem5038952 A B v u f y)). Qed.
Lemma lem5038955 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term265 B y v x) = (term109 B y v x).
Proof. exact (eq_refl (term265 B y v x)). Qed.
Lemma lem5038956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5038957 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term271 B y v x) = (term272 B y v x).
Proof. exact (MK_COMB (@lem5038956) (@lem5038955 B y v x)). Qed.
Lemma lem5038958 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term261 A B u f y) = (term261 A B u f y).
Proof. exact (eq_refl (term261 A B u f y)). Qed.
Lemma lem5038959 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term273 A B v x u f y) = (term274 A B v x u f y).
Proof. exact (MK_COMB (@lem5038957 B y v x) (@lem5038958 A B u f y)). Qed.
Lemma lem5038960 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term275 A B v u f y) = (term276 A B v u f y).
Proof. exact (fun_ext (fun x : B => @lem5038959 A B v x u f y)). Qed.
Lemma lem5038961 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5038962 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term264 A B v u f y) = (term277 A B v u f y).
Proof. exact (MK_COMB (@lem5038961 B) (@lem5038960 A B v u f y)). Qed.
Lemma lem5038963 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : ((term263 A B v u f y) = (term264 A B v u f y)) = ((term262 A B v u f y) = (term277 A B v u f y)).
Proof. exact (MK_COMB (@lem5038954 A B v u f y) (@lem5038962 A B v u f y)). Qed.
Lemma lem5038964 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term262 A B v u f y) = (term277 A B v u f y).
Proof. exact (EQ_MP (@lem5038963 A B v u f y) (@lem5038944 A B v u f y)). Qed.
Lemma lem5038966 {A : Type'} (P : Prop) (Q : A -> Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5038967 {A : Type'} (P : Prop) (Q : type686 A) : (term280 A P Q) = (term281 A P Q).
Proof. exact (@lem5038966 (A -> Prop) P Q). Qed.
Lemma lem5038968 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term282 A B v x u f y) = (term283 A B v x u f y).
Proof. exact (@lem5038967 A (term109 B y v x) (term260 A B u f y)). Qed.
Lemma lem5038969 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term284 A B u f y s) = (term259 A B u f s y).
Proof. exact (eq_refl (term284 A B u f y s)). Qed.
Lemma lem5038970 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term285 A B u f y) = (term260 A B u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5038969 A B u f s y)). Qed.
Lemma lem5038971 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5038972 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term286 A B u f y) = (term261 A B u f y).
Proof. exact (MK_COMB (@lem5038971 A) (@lem5038970 A B u f y)). Qed.
Lemma lem5038973 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term272 B y v x) = (term272 B y v x).
Proof. exact (eq_refl (term272 B y v x)). Qed.
Lemma lem5038974 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term282 A B v x u f y) = (term274 A B v x u f y).
Proof. exact (MK_COMB (@lem5038973 B y v x) (@lem5038972 A B u f y)). Qed.
Lemma lem5038975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038976 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term287 A B v x u f y) = (term288 A B v x u f y).
Proof. exact (MK_COMB (@lem5038975) (@lem5038974 A B v x u f y)). Qed.
Lemma lem5038977 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term284 A B u f y s) = (term259 A B u f s y).
Proof. exact (eq_refl (term284 A B u f y s)). Qed.
Lemma lem5038978 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term272 B y v x) = (term272 B y v x).
Proof. exact (eq_refl (term272 B y v x)). Qed.
Lemma lem5038979 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term289 A B v x u f y s) = (term290 A B v x u f s y).
Proof. exact (MK_COMB (@lem5038978 B y v x) (@lem5038977 A B u f s y)). Qed.
Lemma lem5038980 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term291 A B v x u f y) = (term292 A B v x u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5038979 A B v x u f s y)). Qed.
Lemma lem5038981 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5038982 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term283 A B v x u f y) = (term293 A B v x u f y).
Proof. exact (MK_COMB (@lem5038981 A) (@lem5038980 A B v x u f y)). Qed.
Lemma lem5038983 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : ((term282 A B v x u f y) = (term283 A B v x u f y)) = ((term274 A B v x u f y) = (term293 A B v x u f y)).
Proof. exact (MK_COMB (@lem5038976 A B v x u f y) (@lem5038982 A B v x u f y)). Qed.
Lemma lem5038984 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term274 A B v x u f y) = (term293 A B v x u f y).
Proof. exact (EQ_MP (@lem5038983 A B v x u f y) (@lem5038968 A B v x u f y)). Qed.
Lemma lem5038986 {A : Type'} (P : Prop) (Q : A -> Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5038987 {A B : Type'} (P : Prop) (Q : type805 A B) : (term294 A B P Q) = (term295 A B P Q).
Proof. exact (@lem5038986 (B -> A) P Q). Qed.
Lemma lem5038988 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term296 A B v x u f s y) = (term297 A B v x u f s y).
Proof. exact (@lem5038987 A B (term109 B y v x) (term258 A B u f s y)). Qed.
Lemma lem5038989 {A B : Type'} (u : A -> Prop) (x : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term298 A B u f s y x) = (term256 A B u x f s y).
Proof. exact (eq_refl (term298 A B u f s y x)). Qed.
Lemma lem5038990 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term299 A B u f s y) = (term258 A B u f s y).
Proof. exact (fun_ext (fun x : B -> A => @lem5038989 A B u x f s y)). Qed.
Lemma lem5038991 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5038992 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term300 A B u f s y) = (term259 A B u f s y).
Proof. exact (MK_COMB (@lem5038991 A B) (@lem5038990 A B u f s y)). Qed.
Lemma lem5038993 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term272 B y v x) = (term272 B y v x).
Proof. exact (eq_refl (term272 B y v x)). Qed.
Lemma lem5038994 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term296 A B v x u f s y) = (term290 A B v x u f s y).
Proof. exact (MK_COMB (@lem5038993 B y v x) (@lem5038992 A B u f s y)). Qed.
Lemma lem5038995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5038996 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term301 A B v x u f s y) = (term302 A B v x u f s y).
Proof. exact (MK_COMB (@lem5038995) (@lem5038994 A B v x u f s y)). Qed.
Lemma lem5038997 {A B : Type'} (u : A -> Prop) (x : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term298 A B u f s y x) = (term256 A B u x f s y).
Proof. exact (eq_refl (term298 A B u f s y x)). Qed.
Lemma lem5038998 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term272 B y v x) = (term272 B y v x).
Proof. exact (eq_refl (term272 B y v x)). Qed.
Lemma lem5038999 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term303 A B v x u f s y x') = (term304 A B v x u x' f s y).
Proof. exact (MK_COMB (@lem5038998 B y v x) (@lem5038997 A B u x' f s y)). Qed.
Lemma lem5039000 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term305 A B v x u f s y) = (term306 A B v x u f s y).
Proof. exact (fun_ext (fun x' : B -> A => @lem5038999 A B v x u x' f s y)). Qed.
Lemma lem5039001 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5039002 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term297 A B v x u f s y) = (term307 A B v x u f s y).
Proof. exact (MK_COMB (@lem5039001 A B) (@lem5039000 A B v x u f s y)). Qed.
Lemma lem5039003 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : ((term296 A B v x u f s y) = (term297 A B v x u f s y)) = ((term290 A B v x u f s y) = (term307 A B v x u f s y)).
Proof. exact (MK_COMB (@lem5038996 A B v x u f s y) (@lem5039002 A B v x u f s y)). Qed.
Lemma lem5039004 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) : (term290 A B v x u f s y) = (term307 A B v x u f s y).
Proof. exact (EQ_MP (@lem5039003 A B v x u f s y) (@lem5038988 A B v x u f s y)). Qed.
Lemma lem5039005 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term292 A B v x u f y) = (term308 A B v x u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5039004 A B v x u f s y)). Qed.
Lemma lem5039006 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5039007 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term293 A B v x u f y) = (term309 A B v x u f y).
Proof. exact (MK_COMB (@lem5039006 A) (@lem5039005 A B v x u f y)). Qed.
Lemma lem5039008 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) : (term274 A B v x u f y) = (term309 A B v x u f y).
Proof. exact (TRANS (@lem5038984 A B v x u f y) (@lem5039007 A B v x u f y)). Qed.
Lemma lem5039009 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term276 A B v u f y) = (term310 A B v u f y).
Proof. exact (fun_ext (fun x : B => @lem5039008 A B v x u f y)). Qed.
Lemma lem5039010 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5039011 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term277 A B v u f y) = (term311 A B v u f y).
Proof. exact (MK_COMB (@lem5039010 B) (@lem5039009 A B v u f y)). Qed.
Lemma lem5039012 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term262 A B v u f y) = (term311 A B v u f y).
Proof. exact (TRANS (@lem5038964 A B v u f y) (@lem5039011 A B v u f y)). Qed.
Lemma lem5039013 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term178 A B v u f y) = (term311 A B v u f y).
Proof. exact (TRANS (@lem5038938 A B v u f y) (@lem5039012 A B v u f y)). Qed.
Lemma lem5039014 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term152 A B v u f y) = (term311 A B v u f y).
Proof. exact (TRANS (@lem5038823 A B v u f y) (@lem5039013 A B v u f y)). Qed.
Lemma lem5039015 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term71 A B v u f y) = (term311 A B v u f y).
Proof. exact (TRANS (@lem5038437 A B v u f y) (@lem5039014 A B v u f y)). Qed.
Lemma lem5039016 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term71 A B v u f y) : term311 A B v u f y.
Proof. exact (EQ_MP (@lem5039015 A B v u f y) (@lem5038347 A B v u f y h1)). Qed.
Lemma lem5039023 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term312 A B u f x y) = (term313 A B u f x y).
Proof. exact (@lem17045 (u x) ((f x) = y)). Qed.
Lemma lem5039024 {A : Type'} (P : A -> Prop) : (term124 A P) = (term125 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5039025 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term107 A B u f y) = (term314 A B u f y).
Proof. exact (@lem5039024 A (term78 A B u f y)). Qed.
Lemma lem5039026 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term315 A B u f y x) = (term76 A B u f x y).
Proof. exact (eq_refl (term315 A B u f y x)). Qed.
Lemma lem5039027 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5039028 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term316 A B u f y x) = (term312 A B u f x y).
Proof. exact (MK_COMB (@lem5039027) (@lem5039026 A B u f x y)). Qed.
Lemma lem5039029 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term316 A B u f y x) = (term313 A B u f x y).
Proof. exact (TRANS (@lem5039028 A B u f x y) (@lem5039023 A B u f x y)). Qed.
Lemma lem5039030 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term317 A B u f y) = (term318 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5039029 A B u f x y)). Qed.
Lemma lem5039031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039032 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term314 A B u f y) = (term319 A B u f y).
Proof. exact (MK_COMB (@lem5039031 A) (@lem5039030 A B u f y)). Qed.
Lemma lem5039085 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term107 A B u f y) = (term319 A B u f y).
Proof. exact (TRANS (@lem5039025 A B u f y) (@lem5039032 A B u f y)). Qed.
Lemma lem5039086 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term319 A B u f y.
Proof. exact (EQ_MP (@lem5039085 A B u f y) (@lem5038352 A B u f y h1)). Qed.
Lemma lem5039087 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term309 A B v x u f y) : term309 A B v x u f y.
Proof. exact (h1). Qed.
Lemma lem5039088 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term307 A B v x u f s y) : term307 A B v x u f s y.
Proof. exact (h1). Qed.
Lemma lem5039089 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term304 A B v x u x' f s y) : term304 A B v x u x' f s y.
Proof. exact (h1). Qed.
Lemma lem5039093 {B : Type'} (v : B -> Prop) (y : B) (h1 : v y) : v y.
Proof. exact (h1). Qed.
Lemma lem5039110 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term313 A B u f x y) = (term313 A B u f x y).
Proof. exact (eq_refl (term313 A B u f x y)). Qed.
Lemma lem5039111 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term318 A B u f y) = (term318 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5039110 A B u f x y)). Qed.
Lemma lem5039112 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039113 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term319 A B u f y) = (term319 A B u f y).
Proof. exact (MK_COMB (@lem5039112 A) (@lem5039111 A B u f y)). Qed.
Lemma lem5039114 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term319 A B u f y.
Proof. exact (EQ_MP (@lem5039113 A B u f y) (@lem5039086 A B u f y h1)). Qed.
Lemma lem5039119 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5039136 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term123 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term123 A B x f s x')). Qed.
Lemma lem5039137 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term131 A B x f s) = (term131 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5039136 A B x f s x')). Qed.
Lemma lem5039138 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039139 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem5039138 A) (@lem5039137 A B x f s)). Qed.
Lemma lem5039140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5039141 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term135 A B x f s) = (term135 A B x f s).
Proof. exact (MK_COMB (@lem5039140) (@lem5039139 A B x f s)). Qed.
Lemma lem5039142 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term137 A B f s x y) = (term137 A B f s x y).
Proof. exact (MK_COMB (@lem5039141 A B x f s) (@lem5039119 B x y)). Qed.
Lemma lem5039143 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term158 A B f s y) = (term158 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5039142 A B f s x y)). Qed.
Lemma lem5039144 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5039145 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term173 A B f s y) = (term173 A B f s y).
Proof. exact (MK_COMB (@lem5039144 B) (@lem5039143 A B f s y)). Qed.
Lemma lem5039172 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (x : B) (y : B) : (term214 A B f s x' x y) = (term214 A B f s x' x y).
Proof. exact (eq_refl (term214 A B f s x' x y)). Qed.
Lemma lem5039173 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (y : B) : (term216 A B f s x' y) = (term216 A B f s x' y).
Proof. exact (fun_ext (fun x : B => @lem5039172 A B f s x' x y)). Qed.
Lemma lem5039174 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5039175 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (y : B) : (term218 A B f s x' y) = (term218 A B f s x' y).
Proof. exact (MK_COMB (@lem5039174 B) (@lem5039173 A B f s x' y)). Qed.
Lemma lem5039176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5039177 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (y : B) : (term237 A B f s x' y) = (term237 A B f s x' y).
Proof. exact (MK_COMB (@lem5039176) (@lem5039175 A B f s x' y)). Qed.
Lemma lem5039178 {A B : Type'} (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term239 A B x' f s y) = (term239 A B x' f s y).
Proof. exact (MK_COMB (@lem5039177 A B f s x' y) (@lem5039145 A B f s y)). Qed.
Lemma lem5039189 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term119 A s u x) = (term119 A s u x).
Proof. exact (eq_refl (term119 A s u x)). Qed.
Lemma lem5039190 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term120 A s u) = (term120 A s u).
Proof. exact (fun_ext (fun x : A => @lem5039189 A s u x)). Qed.
Lemma lem5039191 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039192 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term121 A s u) = (term121 A s u).
Proof. exact (MK_COMB (@lem5039191 A) (@lem5039190 A s u)). Qed.
Lemma lem5039193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5039194 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term145 A s u) = (term145 A s u).
Proof. exact (MK_COMB (@lem5039193) (@lem5039192 A s u)). Qed.
Lemma lem5039195 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term256 A B u x' f s y) = (term256 A B u x' f s y).
Proof. exact (MK_COMB (@lem5039194 A s u) (@lem5039178 A B x' f s y)). Qed.
Lemma lem5039210 {B : Type'} (y : B) (v : B -> Prop) (x : B) : (term272 B y v x) = (term272 B y v x).
Proof. exact (eq_refl (term272 B y v x)). Qed.
Lemma lem5039211 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) : (term304 A B v x u x' f s y) = (term304 A B v x u x' f s y).
Proof. exact (MK_COMB (@lem5039210 B y v x) (@lem5039195 A B u x' f s y)). Qed.
Lemma lem5039212 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term304 A B v x u x' f s y) : term304 A B v x u x' f s y.
Proof. exact (EQ_MP (@lem5039211 A B v x u x' f s y) (@lem5039089 A B v x u x' f s y h1)). Qed.
Lemma lem5039213 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : term109 B y v x) : term109 B y v x.
Proof. exact (h1). Qed.
Lemma lem5039214 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term256 A B u x' f s y.
Proof. exact (h1). Qed.
Lemma lem5039217 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term239 A B x' f s y.
Proof. exact (proj2 (@lem5039214 A B u x' f s y h1)). Qed.
Lemma lem5039218 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term121 A s u.
Proof. exact (proj1 (@lem5039214 A B u x' f s y h1)). Qed.
Lemma lem5039219 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term173 A B f s y.
Proof. exact (proj2 (@lem5039217 A B u x' f s y h1)). Qed.
Lemma lem5039220 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term218 A B f s x' y.
Proof. exact (proj1 (@lem5039217 A B u x' f s y h1)). Qed.
Lemma lem5039224 {B : Type'} (v : B -> Prop) (y : B) (h1 : v y) : v y.
Proof. exact (h1). Qed.
Lemma lem5039257 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term313 A B u f x y) = (term313 A B u f x y).
Proof. exact (eq_refl (term313 A B u f x y)). Qed.
Lemma lem5039258 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term318 A B u f y) = (term318 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5039257 A B u f x y)). Qed.
Lemma lem5039259 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039261 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term319 A B u f y) = (term319 A B u f y).
Proof. exact (MK_COMB (@lem5039259 A) (@lem5039258 A B u f y)). Qed.
Lemma lem5039262 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term319 A B u f y.
Proof. exact (EQ_MP (@lem5039261 A B u f y) (@lem5039114 A B u f y h1)). Qed.
Lemma lem5039270 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term119 A s u x) = (term119 A s u x).
Proof. exact (eq_refl (term119 A s u x)). Qed.
Lemma lem5039271 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term120 A s u) = (term120 A s u).
Proof. exact (fun_ext (fun x : A => @lem5039270 A s u x)). Qed.
Lemma lem5039272 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039274 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term121 A s u) = (term121 A s u).
Proof. exact (MK_COMB (@lem5039272 A) (@lem5039271 A s u)). Qed.
Lemma lem5039275 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term121 A s u.
Proof. exact (EQ_MP (@lem5039274 A s u) (@lem5039218 A B u x' f s y h1)). Qed.
Lemma lem5039293 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (x : B) (y : B) : (term214 A B f s x' x y) = (term320 A B f s x' x y).
Proof. exact (@lem19699 (x = (term321 A B f x' x)) (term322 A B s x' x) (term133 B x y)). Qed.
Lemma lem5039294 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (y : B) : (term216 A B f s x' y) = (term323 A B f s x' y).
Proof. exact (fun_ext (fun x : B => @lem5039293 A B f s x' x y)). Qed.
Lemma lem5039295 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5039297 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (y : B) : (term218 A B f s x' y) = (term324 A B f s x' y).
Proof. exact (MK_COMB (@lem5039295 B) (@lem5039294 A B f s x' y)). Qed.
Lemma lem5039298 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term324 A B f s x' y.
Proof. exact (EQ_MP (@lem5039297 A B f s x' y) (@lem5039220 A B u x' f s y h1)). Qed.
Lemma lem5039300 {A : Type'} (P : A -> Prop) (Q : Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5039301 {A : Type'} (P : A -> Prop) (Q : Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (@lem5039300 A P Q). Qed.
Lemma lem5039302 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term327 A B f s x y) = (term328 A B f s x y).
Proof. exact (@lem5039301 A (term131 A B x f s) (x = y)). Qed.
Lemma lem5039303 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term329 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term329 A B x f s x')). Qed.
Lemma lem5039304 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term330 A B x f s) = (term131 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5039303 A B x f s x')). Qed.
Lemma lem5039305 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039306 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term331 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem5039305 A) (@lem5039304 A B x f s)). Qed.
Lemma lem5039307 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5039308 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term332 A B x f s) = (term135 A B x f s).
Proof. exact (MK_COMB (@lem5039307) (@lem5039306 A B x f s)). Qed.
Lemma lem5039309 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5039310 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term327 A B f s x y) = (term137 A B f s x y).
Proof. exact (MK_COMB (@lem5039308 A B x f s) (@lem5039309 B x y)). Qed.
Lemma lem5039311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5039312 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term333 A B f s x y) = (term334 A B f s x y).
Proof. exact (MK_COMB (@lem5039311) (@lem5039310 A B f s x y)). Qed.
Lemma lem5039313 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term329 A B x f s x') = (term123 A B x f s x').
Proof. exact (eq_refl (term329 A B x f s x')). Qed.
Lemma lem5039314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5039315 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term335 A B x f s x') = (term336 A B x f s x').
Proof. exact (MK_COMB (@lem5039314) (@lem5039313 A B x f s x')). Qed.
Lemma lem5039316 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5039317 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (x' : B) (y : B) : (term337 A B f s x x' y) = (term338 A B f s x x' y).
Proof. exact (MK_COMB (@lem5039315 A B x' f s x) (@lem5039316 B x' y)). Qed.
Lemma lem5039318 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term339 A B f s x y) = (term340 A B f s x y).
Proof. exact (fun_ext (fun x' : A => @lem5039317 A B f s x' x y)). Qed.
Lemma lem5039319 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039320 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term328 A B f s x y) = (term341 A B f s x y).
Proof. exact (MK_COMB (@lem5039319 A) (@lem5039318 A B f s x y)). Qed.
Lemma lem5039321 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : ((term327 A B f s x y) = (term328 A B f s x y)) = ((term137 A B f s x y) = (term341 A B f s x y)).
Proof. exact (MK_COMB (@lem5039312 A B f s x y) (@lem5039320 A B f s x y)). Qed.
Lemma lem5039322 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term137 A B f s x y) = (term341 A B f s x y).
Proof. exact (EQ_MP (@lem5039321 A B f s x y) (@lem5039302 A B f s x y)). Qed.
Lemma lem5039323 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term158 A B f s y) = (term342 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5039322 A B f s x y)). Qed.
Lemma lem5039324 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5039325 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term173 A B f s y) = (term343 A B f s y).
Proof. exact (MK_COMB (@lem5039324 B) (@lem5039323 A B f s y)). Qed.
Lemma lem5039338 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (x' : B) (y : B) : (term338 A B f s x x' y) = (term338 A B f s x x' y).
Proof. exact (eq_refl (term338 A B f s x x' y)). Qed.
Lemma lem5039339 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term340 A B f s x y) = (term340 A B f s x y).
Proof. exact (fun_ext (fun x' : A => @lem5039338 A B f s x' x y)). Qed.
Lemma lem5039340 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5039341 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (y : B) : (term341 A B f s x y) = (term341 A B f s x y).
Proof. exact (MK_COMB (@lem5039340 A) (@lem5039339 A B f s x y)). Qed.
Lemma lem5039342 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term342 A B f s y) = (term342 A B f s y).
Proof. exact (fun_ext (fun x : B => @lem5039341 A B f s x y)). Qed.
Lemma lem5039343 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5039344 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term343 A B f s y) = (term343 A B f s y).
Proof. exact (MK_COMB (@lem5039343 B) (@lem5039342 A B f s y)). Qed.
Lemma lem5039345 {A B : Type'} (f : A -> B) (s : A -> Prop) (y : B) : (term173 A B f s y) = (term343 A B f s y).
Proof. exact (TRANS (@lem5039325 A B f s y) (@lem5039344 A B f s y)). Qed.
Lemma lem5039346 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term343 A B f s y.
Proof. exact (EQ_MP (@lem5039345 A B f s y) (@lem5039219 A B u x' f s y h1)). Qed.
Lemma lem5039350 {A B : Type'} (_64735 : A) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term344 A B u f y _64735.
Proof. exact (@lem5039262 A B u f y h1 _64735). Qed.
Lemma lem5039351 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64735 : A) (y : B) : (term344 A B u f y _64735) = (term313 A B u f _64735 y).
Proof. exact (eq_refl (term344 A B u f y _64735)). Qed.
Lemma lem5039353 {A B : Type'} (_64736 : A) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term345 A s u _64736.
Proof. exact (@lem5039275 A B u x' f s y h1 _64736). Qed.
Lemma lem5039354 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64736 : A) : (term345 A s u _64736) = (term119 A s u _64736).
Proof. exact (eq_refl (term345 A s u _64736)). Qed.
Lemma lem5039356 {A B : Type'} (_64737 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term346 A B f s x' y _64737.
Proof. exact (@lem5039298 A B u x' f s y h1 _64737). Qed.
Lemma lem5039357 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (_64737 : B) (y : B) : (term346 A B f s x' y _64737) = (term320 A B f s x' _64737 y).
Proof. exact (eq_refl (term346 A B f s x' y _64737)). Qed.
Lemma lem5039358 {A B : Type'} (_64737 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term320 A B f s x' _64737 y.
Proof. exact (EQ_MP (@lem5039357 A B f s x' _64737 y) (@lem5039356 A B _64737 u x' f s y h1)). Qed.
Lemma lem5039359 {A B : Type'} (_64738 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term347 A B f s y _64738.
Proof. exact (@lem5039346 A B u x' f s y h1 _64738). Qed.
Lemma lem5039360 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64738 : B) (y : B) : (term347 A B f s y _64738) = (term341 A B f s _64738 y).
Proof. exact (eq_refl (term347 A B f s y _64738)). Qed.
Lemma lem5039361 {A B : Type'} (_64738 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term341 A B f s _64738 y.
Proof. exact (EQ_MP (@lem5039360 A B f s _64738 y) (@lem5039359 A B _64738 u x' f s y h1)). Qed.
Lemma lem5039362 {A B : Type'} (_64738 : B) (_64739 : A) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term348 A B f s _64738 y _64739.
Proof. exact (@lem5039361 A B _64738 u x' f s y h1 _64739). Qed.
Lemma lem5039363 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64739 : A) (_64738 : B) (y : B) : (term348 A B f s _64738 y _64739) = (term338 A B f s _64739 _64738 y).
Proof. exact (eq_refl (term348 A B f s _64738 y _64739)). Qed.
Lemma lem5039364 {A B : Type'} (_64739 : A) (_64738 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term338 A B f s _64739 _64738 y.
Proof. exact (EQ_MP (@lem5039363 A B f s _64739 _64738 y) (@lem5039362 A B _64738 _64739 u x' f s y h1)). Qed.
Lemma lem5039368 {B : Type'} (v : B -> Prop) (y : B) (h1 : v y) : v y.
Proof. exact (h1). Qed.
Lemma lem5039376 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : term109 B y v x) : x = y.
Proof. exact (proj1 (@lem5039213 B y v x h1)). Qed.
Lemma lem5039378 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : term109 B y v x) : term349 B v x.
Proof. exact (proj2 (@lem5039213 B y v x h1)). Qed.
Lemma lem5039386 {A B : Type'} (_64735 : A) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term313 A B u f _64735 y.
Proof. exact (EQ_MP (@lem5039351 A B u f _64735 y) (@lem5039350 A B _64735 u f y h1)). Qed.
Lemma lem5039392 {A B : Type'} (_64736 : A) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term119 A s u _64736.
Proof. exact (EQ_MP (@lem5039354 A s u _64736) (@lem5039353 A B _64736 u x' f s y h1)). Qed.
Lemma lem5039403 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64739 : A) (_64738 : B) (y : B) : (term338 A B f s _64739 _64738 y) = (term350 A B f s _64739 _64738 y).
Proof. exact (@lem5037697 (term351 A B _64738 f _64739) (term349 A s _64739) (_64738 = y)). Qed.
Lemma lem5039404 {A B : Type'} (_64739 : A) (_64738 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term350 A B f s _64739 _64738 y.
Proof. exact (EQ_MP (@lem5039403 A B f s _64739 _64738 y) (@lem5039364 A B _64739 _64738 u x' f s y h1)). Qed.
Lemma lem5039416 {A B : Type'} (_64737 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term352 A B s x' _64737 y.
Proof. exact (proj2 (@lem5039358 A B _64737 u x' f s y h1)). Qed.
Lemma lem5039444 {B : Type'} (v : B -> Prop) (y : B) (h1 : v y) : v y.
Proof. exact (h1). Qed.
Lemma lem5039459 {B : Type'} (v : B -> Prop) : (term353 B v) = (term353 B v).
Proof. exact (eq_refl (term353 B v)). Qed.
Lemma lem5039460 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : term109 B y v x) : (term354 B v x) = (term354 B v y).
Proof. exact (MK_COMB (@lem5039459 B v) (@lem5039376 B y v x h1)). Qed.
Lemma lem5039461 {B : Type'} (v : B -> Prop) (y : B) : (term354 B v y) = (term349 B v y).
Proof. exact (eq_refl (term354 B v y)). Qed.
Lemma lem5039462 {B : Type'} (v : B -> Prop) (x : B) : (term355 B v x) = (term355 B v x).
Proof. exact (eq_refl (term355 B v x)). Qed.
Lemma lem5039463 {B : Type'} (x : B) (v : B -> Prop) (y : B) : ((term354 B v x) = (term354 B v y)) = ((term354 B v x) = (term349 B v y)).
Proof. exact (MK_COMB (@lem5039462 B v x) (@lem5039461 B v y)). Qed.
Lemma lem5039464 {B : Type'} (v : B -> Prop) (x : B) : (term354 B v x) = (term349 B v x).
Proof. exact (eq_refl (term354 B v x)). Qed.
Lemma lem5039465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5039466 {B : Type'} (v : B -> Prop) (x : B) : (term355 B v x) = (term356 B v x).
Proof. exact (MK_COMB (@lem5039465) (@lem5039464 B v x)). Qed.
Lemma lem5039467 {B : Type'} (v : B -> Prop) (y : B) : (term349 B v y) = (term349 B v y).
Proof. exact (eq_refl (term349 B v y)). Qed.
Lemma lem5039468 {B : Type'} (x : B) (v : B -> Prop) (y : B) : ((term354 B v x) = (term349 B v y)) = ((term349 B v x) = (term349 B v y)).
Proof. exact (MK_COMB (@lem5039466 B v x) (@lem5039467 B v y)). Qed.
Lemma lem5039469 {B : Type'} (x : B) (v : B -> Prop) (y : B) : ((term354 B v x) = (term354 B v y)) = ((term349 B v x) = (term349 B v y)).
Proof. exact (TRANS (@lem5039463 B x v y) (@lem5039468 B x v y)). Qed.
Lemma lem5039470 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : term109 B y v x) : (term349 B v x) = (term349 B v y).
Proof. exact (EQ_MP (@lem5039469 B x v y) (@lem5039460 B y v x h1)). Qed.
Lemma lem5039471 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : term109 B y v x) : term349 B v y.
Proof. exact (EQ_MP (@lem5039470 B y v x h1) (@lem5039378 B y v x h1)). Qed.
Lemma lem5039509 {B : Type'} (v : B -> Prop) (y : B) (h1 : v y) : v y.
Proof. exact (h1). Qed.
Lemma lem5039510 {B : Type'} (v : B -> Prop) (y : B) (h1 : v y) : term357 B v y.
Proof. exact (fun h0 : term349 B v y => @lem5039509 B v y h1). Qed.
Lemma lem5039512 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039513 {B : Type'} (v : B -> Prop) (y : B) : (term357 B v y) = (v y).
Proof. exact (@lem5039512 (v y)). Qed.
Lemma lem5039514 {B : Type'} (v : B -> Prop) (y : B) (h1 : v y) : v y.
Proof. exact (EQ_MP (@lem5039513 B v y) (@lem5039510 B v y h1)). Qed.
Lemma lem5039517 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5039519 {B : Type'} (v : B -> Prop) (y : B) : (term349 B v y) = (term359 B v y).
Proof. exact (@lem5039517 (v y)). Qed.
Lemma lem5039522 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : term109 B y v x) : term359 B v y.
Proof. exact (EQ_MP (@lem5039519 B v y) (@lem5039471 B y v x h1)). Qed.
Lemma lem5039525 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : False.
Proof. exact (@lem5039522 B y v x h2 (@lem5039514 B v y h1)). Qed.
Lemma lem5039526 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : term360.
Proof. exact (fun h0 : ~ False => @lem5039525 B y v x h1 h2). Qed.
Lemma lem5039528 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039529 : term360 = False.
Proof. exact (@lem5039528 False). Qed.
Lemma lem5039530 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : False.
Proof. exact (EQ_MP (@lem5039529) (@lem5039526 B y v x h1 h2)). Qed.
Lemma lem5039588 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5039589 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5039588 B x). Qed.
Lemma lem5039590 {B : Type'} (y : B) : y = y.
Proof. exact (@lem5039589 B y). Qed.
Lemma lem5039591 {B : Type'} (y : B) : term361 B y.
Proof. exact (fun h0 : term362 B y => @lem5039590 B y). Qed.
Lemma lem5039593 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039594 {B : Type'} (y : B) : (term361 B y) = (y = y).
Proof. exact (@lem5039593 (y = y)). Qed.
Lemma lem5039595 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem5039594 B y) (@lem5039591 B y)). Qed.
Lemma lem5039597 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5039598 {A B : Type'} (y : B) (s : A -> Prop) (x' : B -> A) (_64737 : B) : (term352 A B s x' _64737 y) = (term364 A B y s x' _64737).
Proof. exact (@lem5039597 (term133 B _64737 y) (term322 A B s x' _64737)). Qed.
Lemma lem5039600 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5039601 {B : Type'} (_64737 : B) (y : B) : (term365 B _64737 y) = (_64737 = y).
Proof. exact (@lem5039600 (_64737 = y)). Qed.
Lemma lem5039602 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5039603 {B : Type'} (_64737 : B) (y : B) : (term366 B _64737 y) = (term42 B _64737 y).
Proof. exact (MK_COMB (@lem5039602) (@lem5039601 B _64737 y)). Qed.
Lemma lem5039604 {A B : Type'} (s : A -> Prop) (x' : B -> A) (_64737 : B) : (term322 A B s x' _64737) = (term322 A B s x' _64737).
Proof. exact (eq_refl (term322 A B s x' _64737)). Qed.
Lemma lem5039605 {A B : Type'} (y : B) (s : A -> Prop) (x' : B -> A) (_64737 : B) : (term364 A B y s x' _64737) = (term367 A B y s x' _64737).
Proof. exact (MK_COMB (@lem5039603 B _64737 y) (@lem5039604 A B s x' _64737)). Qed.
Lemma lem5039606 {A B : Type'} (y : B) (s : A -> Prop) (x' : B -> A) (_64737 : B) : (term352 A B s x' _64737 y) = (term367 A B y s x' _64737).
Proof. exact (TRANS (@lem5039598 A B y s x' _64737) (@lem5039605 A B y s x' _64737)). Qed.
Lemma lem5039609 {A B : Type'} (_64737 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term367 A B y s x' _64737.
Proof. exact (EQ_MP (@lem5039606 A B y s x' _64737) (@lem5039416 A B _64737 u x' f s y h1)). Qed.
Lemma lem5039610 {A B : Type'} (_64737 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term367 A B y s x' _64737.
Proof. exact (@lem5039609 A B _64737 u x' f s y h1). Qed.
Lemma lem5039611 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term368 A B s x' y.
Proof. exact (@lem5039610 A B y u x' f s y h1). Qed.
Lemma lem5039614 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term322 A B s x' y.
Proof. exact (@lem5039611 A B u x' f s y h1 (@lem5039595 B y)). Qed.
Lemma lem5039615 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term369 A B s x' y.
Proof. exact (fun h0 : term370 A B s x' y => @lem5039614 A B u x' f s y h1). Qed.
Lemma lem5039617 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039618 {A B : Type'} (s : A -> Prop) (x' : B -> A) (y : B) : (term369 A B s x' y) = (term322 A B s x' y).
Proof. exact (@lem5039617 (term322 A B s x' y)). Qed.
Lemma lem5039619 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term322 A B s x' y.
Proof. exact (EQ_MP (@lem5039618 A B s x' y) (@lem5039615 A B u x' f s y h1)). Qed.
Lemma lem5039625 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5039626 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64736 : A) : (term119 A s u _64736) = (term371 A u s _64736).
Proof. exact (@lem5039625 (u _64736) (term349 A s _64736)). Qed.
Lemma lem5039632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5039633 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64736 : A) : (term372 A s u _64736) = (term373 A u s _64736).
Proof. exact (MK_COMB (@lem5039632) (@lem5039626 A u s _64736)). Qed.
Lemma lem5039639 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64736 : A) : (term371 A u s _64736) = (term371 A u s _64736).
Proof. exact (eq_refl (term371 A u s _64736)). Qed.
Lemma lem5039640 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64736 : A) : ((term119 A s u _64736) = (term371 A u s _64736)) = ((term371 A u s _64736) = (term371 A u s _64736)).
Proof. exact (MK_COMB (@lem5039633 A u s _64736) (@lem5039639 A u s _64736)). Qed.
Lemma lem5039642 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5039643 (x : Prop) : (x = x) = True.
Proof. exact (@lem5039642 Prop x). Qed.
Lemma lem5039644 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64736 : A) : ((term371 A u s _64736) = (term371 A u s _64736)) = True.
Proof. exact (@lem5039643 (term371 A u s _64736)). Qed.
Lemma lem5039645 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64736 : A) : ((term119 A s u _64736) = (term371 A u s _64736)) = True.
Proof. exact (TRANS (@lem5039640 A u s _64736) (@lem5039644 A u s _64736)). Qed.
Lemma lem5039646 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64736 : A) : True = ((term119 A s u _64736) = (term371 A u s _64736)).
Proof. exact (SYM (@lem5039645 A u s _64736)). Qed.
Lemma lem5039647 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64736 : A) : (term119 A s u _64736) = (term371 A u s _64736).
Proof. exact (EQ_MP (@lem5039646 A u s _64736) (@lem0)). Qed.
Lemma lem5039648 {A B : Type'} (_64736 : A) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term371 A u s _64736.
Proof. exact (EQ_MP (@lem5039647 A u s _64736) (@lem5039392 A B _64736 u x' f s y h1)). Qed.
Lemma lem5039650 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5039651 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64736 : A) : (term371 A u s _64736) = (term374 A s u _64736).
Proof. exact (@lem5039650 (term349 A s _64736) (u _64736)). Qed.
Lemma lem5039653 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5039654 {A : Type'} (s : A -> Prop) (_64736 : A) : (term375 A s _64736) = (s _64736).
Proof. exact (@lem5039653 (s _64736)). Qed.
Lemma lem5039655 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5039656 {A : Type'} (s : A -> Prop) (_64736 : A) : (term376 A s _64736) = (term34 A s _64736).
Proof. exact (MK_COMB (@lem5039655) (@lem5039654 A s _64736)). Qed.
Lemma lem5039657 {A : Type'} (u : A -> Prop) (_64736 : A) : (u _64736) = (u _64736).
Proof. exact (eq_refl (u _64736)). Qed.
Lemma lem5039658 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64736 : A) : (term374 A s u _64736) = (term50 A s u _64736).
Proof. exact (MK_COMB (@lem5039656 A s _64736) (@lem5039657 A u _64736)). Qed.
Lemma lem5039659 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64736 : A) : (term371 A u s _64736) = (term50 A s u _64736).
Proof. exact (TRANS (@lem5039651 A s u _64736) (@lem5039658 A s u _64736)). Qed.
Lemma lem5039662 {A B : Type'} (_64736 : A) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term50 A s u _64736.
Proof. exact (EQ_MP (@lem5039659 A s u _64736) (@lem5039648 A B _64736 u x' f s y h1)). Qed.
Lemma lem5039663 {A B : Type'} (_64736 : A) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term50 A s u _64736.
Proof. exact (@lem5039662 A B _64736 u x' f s y h1). Qed.
Lemma lem5039664 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term377 A B s u x' y.
Proof. exact (@lem5039663 A B (x' y) u x' f s y h1). Qed.
Lemma lem5039667 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term322 A B u x' y.
Proof. exact (@lem5039664 A B u x' f s y h1 (@lem5039619 A B u x' f s y h1)). Qed.
Lemma lem5039668 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term369 A B u x' y.
Proof. exact (fun h0 : term370 A B u x' y => @lem5039667 A B u x' f s y h1). Qed.
Lemma lem5039670 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039671 {A B : Type'} (u : A -> Prop) (x' : B -> A) (y : B) : (term369 A B u x' y) = (term322 A B u x' y).
Proof. exact (@lem5039670 (term322 A B u x' y)). Qed.
Lemma lem5039672 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term322 A B u x' y.
Proof. exact (EQ_MP (@lem5039671 A B u x' y) (@lem5039668 A B u x' f s y h1)). Qed.
Lemma lem5039674 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5039675 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5039674 B x). Qed.
Lemma lem5039676 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term321 A B f x' y) = (term321 A B f x' y).
Proof. exact (@lem5039675 B (term321 A B f x' y)). Qed.
Lemma lem5039677 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : term378 A B f x' y.
Proof. exact (fun h0 : term379 A B f x' y => @lem5039676 A B f x' y). Qed.
Lemma lem5039679 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039680 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term378 A B f x' y) = ((term321 A B f x' y) = (term321 A B f x' y)).
Proof. exact (@lem5039679 ((term321 A B f x' y) = (term321 A B f x' y))). Qed.
Lemma lem5039681 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term321 A B f x' y) = (term321 A B f x' y).
Proof. exact (EQ_MP (@lem5039680 A B f x' y) (@lem5039677 A B f x' y)). Qed.
Lemma lem5039683 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5039684 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5039683 B x). Qed.
Lemma lem5039685 {B : Type'} (y : B) : y = y.
Proof. exact (@lem5039684 B y). Qed.
Lemma lem5039686 {B : Type'} (y : B) : term361 B y.
Proof. exact (fun h0 : term362 B y => @lem5039685 B y). Qed.
Lemma lem5039688 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039689 {B : Type'} (y : B) : (term361 B y) = (y = y).
Proof. exact (@lem5039688 (y = y)). Qed.
Lemma lem5039690 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem5039689 B y) (@lem5039686 B y)). Qed.
Lemma lem5039692 {A B : Type'} (_64737 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term367 A B y s x' _64737.
Proof. exact (EQ_MP (@lem5039606 A B y s x' _64737) (@lem5039416 A B _64737 u x' f s y h1)). Qed.
Lemma lem5039693 {A B : Type'} (_64737 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term367 A B y s x' _64737.
Proof. exact (@lem5039692 A B _64737 u x' f s y h1). Qed.
Lemma lem5039694 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term368 A B s x' y.
Proof. exact (@lem5039693 A B y u x' f s y h1). Qed.
Lemma lem5039697 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term322 A B s x' y.
Proof. exact (@lem5039694 A B u x' f s y h1 (@lem5039690 B y)). Qed.
Lemma lem5039698 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term369 A B s x' y.
Proof. exact (fun h0 : term370 A B s x' y => @lem5039697 A B u x' f s y h1). Qed.
Lemma lem5039700 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039701 {A B : Type'} (s : A -> Prop) (x' : B -> A) (y : B) : (term369 A B s x' y) = (term322 A B s x' y).
Proof. exact (@lem5039700 (term322 A B s x' y)). Qed.
Lemma lem5039702 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term322 A B s x' y.
Proof. exact (EQ_MP (@lem5039701 A B s x' y) (@lem5039698 A B u x' f s y h1)). Qed.
Lemma lem5039708 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5039709 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64739 : A) (_64738 : B) (y : B) : (term350 A B f s _64739 _64738 y) = (term380 A B s f _64739 _64738 y).
Proof. exact (@lem5039708 (term349 A s _64739) (term351 A B _64738 f _64739) (_64738 = y)). Qed.
Lemma lem5039723 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5039724 {A B : Type'} (y : B) (_64738 : B) (f : A -> B) (_64739 : A) : (term381 A B f _64739 _64738 y) = (term382 A B y _64738 f _64739).
Proof. exact (@lem5039723 (_64738 = y) (term351 A B _64738 f _64739)). Qed.
Lemma lem5039734 {A : Type'} (s : A -> Prop) (_64739 : A) : (term383 A s _64739) = (term383 A s _64739).
Proof. exact (eq_refl (term383 A s _64739)). Qed.
Lemma lem5039735 {A B : Type'} (s : A -> Prop) (y : B) (_64738 : B) (f : A -> B) (_64739 : A) : (term380 A B s f _64739 _64738 y) = (term384 A B s y _64738 f _64739).
Proof. exact (MK_COMB (@lem5039734 A s _64739) (@lem5039724 A B y _64738 f _64739)). Qed.
Lemma lem5039739 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5039740 {A B : Type'} (y : B) (s : A -> Prop) (_64738 : B) (f : A -> B) (_64739 : A) : (term384 A B s y _64738 f _64739) = (term385 A B y s _64738 f _64739).
Proof. exact (@lem5039739 (_64738 = y) (term349 A s _64739) (term351 A B _64738 f _64739)). Qed.
Lemma lem5039760 {A B : Type'} (y : B) (s : A -> Prop) (_64738 : B) (f : A -> B) (_64739 : A) : (term380 A B s f _64739 _64738 y) = (term385 A B y s _64738 f _64739).
Proof. exact (TRANS (@lem5039735 A B s y _64738 f _64739) (@lem5039740 A B y s _64738 f _64739)). Qed.
Lemma lem5039761 {A B : Type'} (y : B) (s : A -> Prop) (_64738 : B) (f : A -> B) (_64739 : A) : (term350 A B f s _64739 _64738 y) = (term385 A B y s _64738 f _64739).
Proof. exact (TRANS (@lem5039709 A B s f _64739 _64738 y) (@lem5039760 A B y s _64738 f _64739)). Qed.
Lemma lem5039762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5039763 {A B : Type'} (y : B) (s : A -> Prop) (_64738 : B) (f : A -> B) (_64739 : A) : (term386 A B f s _64739 _64738 y) = (term387 A B y s _64738 f _64739).
Proof. exact (MK_COMB (@lem5039762) (@lem5039761 A B y s _64738 f _64739)). Qed.
Lemma lem5039779 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5039780 {A B : Type'} (s : A -> Prop) (_64738 : B) (f : A -> B) (_64739 : A) : (term123 A B _64738 f s _64739) = (term388 A B s _64738 f _64739).
Proof. exact (@lem5039779 (term349 A s _64739) (term351 A B _64738 f _64739)). Qed.
Lemma lem5039788 {B : Type'} (_64738 : B) (y : B) : (term39 B _64738 y) = (term39 B _64738 y).
Proof. exact (eq_refl (term39 B _64738 y)). Qed.
Lemma lem5039789 {A B : Type'} (y : B) (s : A -> Prop) (_64738 : B) (f : A -> B) (_64739 : A) : (term389 A B y _64738 f s _64739) = (term385 A B y s _64738 f _64739).
Proof. exact (MK_COMB (@lem5039788 B _64738 y) (@lem5039780 A B s _64738 f _64739)). Qed.
Lemma lem5039800 {A B : Type'} (y : B) (s : A -> Prop) (_64738 : B) (f : A -> B) (_64739 : A) : ((term350 A B f s _64739 _64738 y) = (term389 A B y _64738 f s _64739)) = ((term385 A B y s _64738 f _64739) = (term385 A B y s _64738 f _64739)).
Proof. exact (MK_COMB (@lem5039763 A B y s _64738 f _64739) (@lem5039789 A B y s _64738 f _64739)). Qed.
Lemma lem5039802 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5039803 (x : Prop) : (x = x) = True.
Proof. exact (@lem5039802 Prop x). Qed.
Lemma lem5039804 {A B : Type'} (y : B) (s : A -> Prop) (_64738 : B) (f : A -> B) (_64739 : A) : ((term385 A B y s _64738 f _64739) = (term385 A B y s _64738 f _64739)) = True.
Proof. exact (@lem5039803 (term385 A B y s _64738 f _64739)). Qed.
Lemma lem5039805 {A B : Type'} (y : B) (_64738 : B) (f : A -> B) (s : A -> Prop) (_64739 : A) : ((term350 A B f s _64739 _64738 y) = (term389 A B y _64738 f s _64739)) = True.
Proof. exact (TRANS (@lem5039800 A B y s _64738 f _64739) (@lem5039804 A B y s _64738 f _64739)). Qed.
Lemma lem5039806 {A B : Type'} (y : B) (_64738 : B) (f : A -> B) (s : A -> Prop) (_64739 : A) : True = ((term350 A B f s _64739 _64738 y) = (term389 A B y _64738 f s _64739)).
Proof. exact (SYM (@lem5039805 A B y _64738 f s _64739)). Qed.
Lemma lem5039807 {A B : Type'} (y : B) (_64738 : B) (f : A -> B) (s : A -> Prop) (_64739 : A) : (term350 A B f s _64739 _64738 y) = (term389 A B y _64738 f s _64739).
Proof. exact (EQ_MP (@lem5039806 A B y _64738 f s _64739) (@lem0)). Qed.
Lemma lem5039808 {A B : Type'} (_64738 : B) (_64739 : A) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term389 A B y _64738 f s _64739.
Proof. exact (EQ_MP (@lem5039807 A B y _64738 f s _64739) (@lem5039404 A B _64739 _64738 u x' f s y h1)). Qed.
Lemma lem5039810 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5039811 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64739 : A) (_64738 : B) (y : B) : (term389 A B y _64738 f s _64739) = (term390 A B f s _64739 _64738 y).
Proof. exact (@lem5039810 (term123 A B _64738 f s _64739) (_64738 = y)). Qed.
Lemma lem5039813 (a : Prop) (b : Prop) : (term391 a b) = (term392 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5039814 {A B : Type'} (_64738 : B) (f : A -> B) (s : A -> Prop) (_64739 : A) : (term393 A B _64738 f s _64739) = (term394 A B _64738 f s _64739).
Proof. exact (@lem5039813 (term351 A B _64738 f _64739) (term349 A s _64739)). Qed.
Lemma lem5039816 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5039817 {A B : Type'} (_64738 : B) (f : A -> B) (_64739 : A) : (term395 A B _64738 f _64739) = (_64738 = (f _64739)).
Proof. exact (@lem5039816 (_64738 = (f _64739))). Qed.
Lemma lem5039818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5039819 {A B : Type'} (_64738 : B) (f : A -> B) (_64739 : A) : (term396 A B _64738 f _64739) = (term57 A B _64738 f _64739).
Proof. exact (MK_COMB (@lem5039818) (@lem5039817 A B _64738 f _64739)). Qed.
Lemma lem5039821 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5039822 {A : Type'} (s : A -> Prop) (_64739 : A) : (term375 A s _64739) = (s _64739).
Proof. exact (@lem5039821 (s _64739)). Qed.
Lemma lem5039823 {A B : Type'} (_64738 : B) (f : A -> B) (s : A -> Prop) (_64739 : A) : (term394 A B _64738 f s _64739) = (term59 A B _64738 f s _64739).
Proof. exact (MK_COMB (@lem5039819 A B _64738 f _64739) (@lem5039822 A s _64739)). Qed.
Lemma lem5039824 {A B : Type'} (_64738 : B) (f : A -> B) (s : A -> Prop) (_64739 : A) : (term393 A B _64738 f s _64739) = (term59 A B _64738 f s _64739).
Proof. exact (TRANS (@lem5039814 A B _64738 f s _64739) (@lem5039823 A B _64738 f s _64739)). Qed.
Lemma lem5039825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5039826 {A B : Type'} (_64738 : B) (f : A -> B) (s : A -> Prop) (_64739 : A) : (term397 A B _64738 f s _64739) = (term398 A B _64738 f s _64739).
Proof. exact (MK_COMB (@lem5039825) (@lem5039824 A B _64738 f s _64739)). Qed.
Lemma lem5039827 {B : Type'} (_64738 : B) (y : B) : (_64738 = y) = (_64738 = y).
Proof. exact (eq_refl (_64738 = y)). Qed.
Lemma lem5039828 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64739 : A) (_64738 : B) (y : B) : (term390 A B f s _64739 _64738 y) = (term399 A B f s _64739 _64738 y).
Proof. exact (MK_COMB (@lem5039826 A B _64738 f s _64739) (@lem5039827 B _64738 y)). Qed.
Lemma lem5039829 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64739 : A) (_64738 : B) (y : B) : (term389 A B y _64738 f s _64739) = (term399 A B f s _64739 _64738 y).
Proof. exact (TRANS (@lem5039811 A B f s _64739 _64738 y) (@lem5039828 A B f s _64739 _64738 y)). Qed.
Lemma lem5039831 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term400 A B f s x' y.
Proof. exact (conj (@lem5039681 A B f x' y) (@lem5039702 A B u x' f s y h1)). Qed.
Lemma lem5039833 {A B : Type'} (_64739 : A) (_64738 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term399 A B f s _64739 _64738 y.
Proof. exact (EQ_MP (@lem5039829 A B f s _64739 _64738 y) (@lem5039808 A B _64738 _64739 u x' f s y h1)). Qed.
Lemma lem5039834 {A B : Type'} (_64739 : A) (_64738 : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term399 A B f s _64739 _64738 y.
Proof. exact (@lem5039833 A B _64739 _64738 u x' f s y h1). Qed.
Lemma lem5039835 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term401 A B s f x' y.
Proof. exact (@lem5039834 A B (x' y) (term321 A B f x' y) u x' f s y h1). Qed.
Lemma lem5039838 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : (term321 A B f x' y) = y.
Proof. exact (@lem5039835 A B u x' f s y h1 (@lem5039831 A B u x' f s y h1)). Qed.
Lemma lem5039839 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term402 A B f x' y.
Proof. exact (fun h0 : term403 A B f x' y => @lem5039838 A B u x' f s y h1). Qed.
Lemma lem5039841 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039842 {A B : Type'} (f : A -> B) (x' : B -> A) (y : B) : (term402 A B f x' y) = ((term321 A B f x' y) = y).
Proof. exact (@lem5039841 ((term321 A B f x' y) = y)). Qed.
Lemma lem5039843 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : (term321 A B f x' y) = y.
Proof. exact (EQ_MP (@lem5039842 A B f x' y) (@lem5039839 A B u x' f s y h1)). Qed.
Lemma lem5039845 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5039846 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64735 : A) (y : B) : (term313 A B u f _64735 y) = (term312 A B u f _64735 y).
Proof. exact (@lem5039845 (u _64735) ((f _64735) = y)). Qed.
Lemma lem5039848 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5039849 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64735 : A) (y : B) : (term312 A B u f _64735 y) = (term406 A B u f _64735 y).
Proof. exact (@lem5039848 (term76 A B u f _64735 y)). Qed.
Lemma lem5039850 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64735 : A) (y : B) : (term313 A B u f _64735 y) = (term406 A B u f _64735 y).
Proof. exact (TRANS (@lem5039846 A B u f _64735 y) (@lem5039849 A B u f _64735 y)). Qed.
Lemma lem5039852 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term256 A B u x' f s y) : term407 A B u f x' y.
Proof. exact (conj (@lem5039672 A B u x' f s y h1) (@lem5039843 A B u x' f s y h1)). Qed.
Lemma lem5039854 {A B : Type'} (_64735 : A) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term406 A B u f _64735 y.
Proof. exact (EQ_MP (@lem5039850 A B u f _64735 y) (@lem5039386 A B _64735 u f y h1)). Qed.
Lemma lem5039855 {A B : Type'} (_64735 : A) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term406 A B u f _64735 y.
Proof. exact (@lem5039854 A B _64735 u f y h1). Qed.
Lemma lem5039856 {A B : Type'} (x' : B -> A) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) : term408 A B u f x' y.
Proof. exact (@lem5039855 A B (x' y) u f y h1). Qed.
Lemma lem5039859 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term107 A B u f y) (h2 : term256 A B u x' f s y) : False.
Proof. exact (@lem5039856 A B x' u f y h1 (@lem5039852 A B u x' f s y h2)). Qed.
Lemma lem5039860 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term107 A B u f y) (h2 : term256 A B u x' f s y) : term360.
Proof. exact (fun h0 : ~ False => @lem5039859 A B u x' f s y h1 h2). Qed.
Lemma lem5039862 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5039863 : term360 = False.
Proof. exact (@lem5039862 False). Qed.
Lemma lem5039864 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term107 A B u f y) (h2 : term256 A B u x' f s y) : False.
Proof. exact (EQ_MP (@lem5039863) (@lem5039860 A B u x' f s y h1 h2)). Qed.
Lemma lem5039865 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : (v y) = False.
Proof. exact (prop_ext (fun h3 : v y => @lem5039530 B y v x h1 h2) (fun h3 : False => @lem5039444 B v y h1)). Qed.
Lemma lem5039867 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : False.
Proof. exact (EQ_MP (@lem5039865 B y v x h1 h2) (@lem5039444 B v y h1)). Qed.
Lemma lem5039868 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : (v y) = False.
Proof. exact (prop_ext (fun h3 : v y => @lem5039867 B y v x h1 h2) (fun h3 : False => @lem5039368 B v y h1)). Qed.
Lemma lem5039869 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : False.
Proof. exact (EQ_MP (@lem5039868 B y v x h1 h2) (@lem5039368 B v y h1)). Qed.
Lemma lem5039870 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : (v y) = False.
Proof. exact (prop_ext (fun h3 : v y => @lem5039869 B y v x h1 h2) (fun h3 : False => @lem5039224 B v y h1)). Qed.
Lemma lem5039871 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : False.
Proof. exact (EQ_MP (@lem5039870 B y v x h1 h2) (@lem5039224 B v y h1)). Qed.
Lemma lem5039872 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : (v y) = False.
Proof. exact (prop_ext (fun h3 : v y => @lem5039871 B y v x h1 h2) (fun h3 : False => @lem5039224 B v y h1)). Qed.
Lemma lem5039873 {B : Type'} (y : B) (v : B -> Prop) (x : B) (h1 : v y) (h2 : term109 B y v x) : False.
Proof. exact (EQ_MP (@lem5039872 B y v x h1 h2) (@lem5039224 B v y h1)). Qed.
Lemma lem5039874 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term304 A B v x u x' f s y) : False.
Proof. exact (or_elim (@lem5039212 A B v x u x' f s y h3) (fun h0 : term109 B y v x => @lem5039873 B y v x h2 h0) (fun h0 : term256 A B u x' f s y => @lem5039864 A B u x' f s y h1 h0)). Qed.
Lemma lem5039875 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term304 A B v x u x' f s y) : (term304 A B v x u x' f s y) = False.
Proof. exact (prop_ext (fun h4 : term304 A B v x u x' f s y => @lem5039874 A B v x u x' f s y h1 h2 h3) (fun h4 : False => @lem5039212 A B v x u x' f s y h3)). Qed.
Lemma lem5039876 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term304 A B v x u x' f s y) : False.
Proof. exact (EQ_MP (@lem5039875 A B v x u x' f s y h1 h2 h3) (@lem5039212 A B v x u x' f s y h3)). Qed.
Lemma lem5039877 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term304 A B v x u x' f s y) : (v y) = False.
Proof. exact (prop_ext (fun h4 : v y => @lem5039876 A B v x u x' f s y h1 h2 h3) (fun h4 : False => @lem5039093 B v y h2)). Qed.
Lemma lem5039878 {A B : Type'} (v : B -> Prop) (x : B) (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term304 A B v x u x' f s y) : False.
Proof. exact (EQ_MP (@lem5039877 A B v x u x' f s y h1 h2 h3) (@lem5039093 B v y h2)). Qed.
Lemma lem5039879 {A B : Type'} (x : B) (s : A -> Prop) (u : A -> Prop) (f : A -> B) (v : B -> Prop) (y : B) (h1 : term307 A B v x u f s y) (h2 : term107 A B u f y) (h3 : v y) : False.
Proof. exact (ex_elim (@lem5039088 A B v x u f s y h1) (fun x' : B -> A => fun h0 : term306 A B v x u f s y x' => @lem5039878 A B v x u x' f s y h2 h3 h0)). Qed.
Lemma lem5039880 {A B : Type'} (x : B) (u : A -> Prop) (f : A -> B) (v : B -> Prop) (y : B) (h1 : term309 A B v x u f y) (h2 : term107 A B u f y) (h3 : v y) : False.
Proof. exact (ex_elim (@lem5039087 A B v x u f y h1) (fun s : A -> Prop => fun h0 : term308 A B v x u f y s => @lem5039879 A B x s u f v y h0 h2 h3)). Qed.
Lemma lem5039881 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term71 A B v u f y) : False.
Proof. exact (ex_elim (@lem5039016 A B v u f y h3) (fun x : B => fun h0 : term310 A B v u f y x => @lem5039880 A B x u f v y h0 h1 h2)). Qed.
Lemma lem5039882 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term71 A B v u f y) : (v y) = False.
Proof. exact (prop_ext (fun h4 : v y => @lem5039881 A B v u f y h1 h2 h3) (fun h4 : False => @lem5038358 B v y h2)). Qed.
Lemma lem5039883 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term71 A B v u f y) : False.
Proof. exact (EQ_MP (@lem5039882 A B v u f y h1 h2 h3) (@lem5038358 B v y h2)). Qed.
Lemma lem5039884 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term71 A B v u f y) : (term107 A B u f y) = False.
Proof. exact (prop_ext (fun h4 : term107 A B u f y => @lem5039883 A B v u f y h1 h2 h3) (fun h4 : False => @lem5038352 A B u f y h1)). Qed.
Lemma lem5039885 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term107 A B u f y) (h2 : v y) (h3 : term71 A B v u f y) : False.
Proof. exact (EQ_MP (@lem5039884 A B v u f y h1 h2 h3) (@lem5038352 A B u f y h1)). Qed.
Lemma lem5039886 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : v y) (h2 : term71 A B v u f y) : term106 A B u f y.
Proof. exact (fun h0 : term107 A B u f y => @lem5039885 A B v u f y h0 h1 h2). Qed.
Lemma lem5039887 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : v y) (h2 : term71 A B v u f y) : term79 A B u f y.
Proof. exact (EQ_MP (@lem5038351 A B u f y) (@lem5039886 A B v u f y h1 h2)). Qed.
Lemma lem5039888 {A B : Type'} (u : A -> Prop) (f : A -> B) (v : B -> Prop) (y : B) (h1 : v y) : term80 A B v u f y.
Proof. exact (fun h0 : term71 A B v u f y => @lem5039887 A B v u f y h1 h0). Qed.
Lemma lem5039889 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term81 A B v u f y.
Proof. exact (fun h0 : v y => @lem5039888 A B u f v y h0). Qed.
Lemma lem5039894 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : term93 A B u f y.
Proof. exact (fun v : B -> Prop => @lem5039889 A B v u f y). Qed.
Lemma lem5039899 {A B : Type'} (f : A -> B) (y : B) : term97 A B f y.
Proof. exact (fun u : A -> Prop => @lem5039894 A B u f y). Qed.
Lemma lem5039904 {A B : Type'} (y : B) : term101 A B y.
Proof. exact (fun f : A -> B => @lem5039899 A B f y). Qed.
Lemma lem5039909 {A B : Type'} : term105 A B.
Proof. exact (fun y : B => @lem5039904 A B y). Qed.
Lemma lem5039910 {A B : Type'} : term104 A B.
Proof. exact (EQ_MP (@lem5038345 A B) (@lem5039909 A B)). Qed.
Lemma lem5039911 {A B : Type'} (y : B) : term409 A B y.
Proof. exact (@lem5039910 A B y). Qed.
Lemma lem5039912 {A B : Type'} (y : B) : (term409 A B y) = (term100 A B y).
Proof. exact (eq_refl (term409 A B y)). Qed.
Lemma lem5039913 {A B : Type'} (y : B) : term100 A B y.
Proof. exact (EQ_MP (@lem5039912 A B y) (@lem5039911 A B y)). Qed.
Lemma lem5039914 {A B : Type'} (y : B) (f : A -> B) : term410 A B y f.
Proof. exact (@lem5039913 A B y f). Qed.
Lemma lem5039915 {A B : Type'} (f : A -> B) (y : B) : (term410 A B y f) = (term96 A B f y).
Proof. exact (eq_refl (term410 A B y f)). Qed.
Lemma lem5039916 {A B : Type'} (f : A -> B) (y : B) : term96 A B f y.
Proof. exact (EQ_MP (@lem5039915 A B f y) (@lem5039914 A B y f)). Qed.
Lemma lem5039917 {A B : Type'} (f : A -> B) (y : B) (u : A -> Prop) : term411 A B f y u.
Proof. exact (@lem5039916 A B f y u). Qed.
Lemma lem5039918 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term411 A B f y u) = (term92 A B u f y).
Proof. exact (eq_refl (term411 A B f y u)). Qed.
Lemma lem5039919 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : term92 A B u f y.
Proof. exact (EQ_MP (@lem5039918 A B u f y) (@lem5039917 A B f y u)). Qed.
Lemma lem5039920 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) (v : B -> Prop) : term412 A B u f y v.
Proof. exact (@lem5039919 A B u f y v). Qed.
Lemma lem5039921 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term412 A B u f y v) = (term83 A B v u f y).
Proof. exact (eq_refl (term412 A B u f y v)). Qed.
Lemma lem5039922 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term83 A B v u f y.
Proof. exact (EQ_MP (@lem5039921 A B v u f y) (@lem5039920 A B u f y v)). Qed.
Lemma lem5039924 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term83 A B v u f y.
Proof. exact (@lem5038007 A B v u f y (@lem5039922 A B v u f y)). Qed.
Lemma lem5039925 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term84 A B v u f y) : False.
Proof. exact (@lem5039924 A B v u f y (@lem5037991 A B v u f y h1)). Qed.
Lemma lem5039926 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term84 A B v u f y) : (term84 A B v u f y) = False.
Proof. exact (prop_ext (fun h2 : term84 A B v u f y => @lem5039925 A B v u f y h1) (fun h2 : False => @lem5037991 A B v u f y h1)). Qed.
Lemma lem5039927 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (h1 : term84 A B v u f y) : False.
Proof. exact (EQ_MP (@lem5039926 A B v u f y h1) (@lem5037991 A B v u f y h1)). Qed.
Lemma lem5039928 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term83 A B v u f y.
Proof. exact (fun h0 : term84 A B v u f y => @lem5039927 A B v u f y h0). Qed.
Lemma lem5039929 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term81 A B v u f y.
Proof. exact (EQ_MP (@lem5037990 A B v u f y) (@lem5039928 A B v u f y)). Qed.
Lemma lem5039930 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term33 A B v u f y.
Proof. exact (EQ_MP (@lem5037986 A B v u f y) (@lem5039929 A B v u f y)). Qed.
Lemma lem5039931 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : term32 A B v u f y.
Proof. exact (EQ_MP (@lem5037781 A B v u f y) (@lem5039930 A B v u f y)). Qed.
Lemma lem5039932 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) (v : B -> Prop) (h1 : @IN B y v) : term29 A B v u f y.
Proof. exact (@lem5039931 A B v u f y (@lem5037684 B y v h1)). Qed.
Lemma lem5039933 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) (v : B -> Prop) (h1 : term0 A B v u f) (h2 : @IN B y v) : term28 A B u f y.
Proof. exact (@lem5039932 A B u f y v h2 (@lem5037687 A B y v u f h1)). Qed.
Lemma lem5039934 {A B : Type'} (y : B) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term0 A B v u f) : term413 A B v u f y.
Proof. exact (fun h0 : @IN B y v => @lem5039933 A B u f y v h1 h0). Qed.
Lemma lem5039939 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term0 A B v u f) : term414 A B v u f.
Proof. exact (fun y : B => @lem5039934 A B y v u f h1). Qed.
Lemma lem5039940 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : term415 A B v u f.
Proof. exact (fun h0 : term0 A B v u f => @lem5039939 A B v u f h0). Qed.
Lemma lem5039941 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term414 A B v u f) : term414 A B v u f.
Proof. exact (h1). Qed.
Lemma lem5039942 {B : Type'} (t : B -> Prop) (v : B -> Prop) (h1 : @SUBSET B t v) : @SUBSET B t v.
Proof. exact (h1). Qed.
Lemma lem5039953 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (v : B -> Prop) (h1 : term414 A B v u f) (h2 : @SUBSET B t v) : term416 A B t v u f.
Proof. exact (conj (@lem5039942 B t v h2) (@lem5039941 A B v u f h1)). Qed.
Lemma lem5039959 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5039960 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term10 B s t).
Proof. exact (@lem5039959 B s t). Qed.
Lemma lem5039961 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (@SUBSET B t v) = (term10 B t v).
Proof. exact (@lem5039960 B t v). Qed.
Lemma lem5039968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5039969 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term15 B t v) = (term16 B t v).
Proof. exact (MK_COMB (@lem5039968) (@lem5039961 B t v)). Qed.
Lemma lem5039986 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term414 A B v u f) = (term414 A B v u f).
Proof. exact (eq_refl (term414 A B v u f)). Qed.
Lemma lem5039987 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term416 A B t v u f) = (term417 A B t v u f).
Proof. exact (MK_COMB (@lem5039969 B t v) (@lem5039986 A B v u f)). Qed.
Lemma lem5039990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5039991 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term418 A B t v u f) = (term419 A B t v u f).
Proof. exact (MK_COMB (@lem5039990) (@lem5039987 A B t v u f)). Qed.
Lemma lem5039995 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5039996 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (@lem5039995 A s t). Qed.
Lemma lem5039997 {A B : Type'} (f : A -> B) (t : B -> Prop) (u : A -> Prop) : (term420 A B f t u) = (term421 A B f t u).
Proof. exact (@lem5039996 A (term422 A B u f t) u). Qed.
Lemma lem5040010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040011 {A B : Type'} (f : A -> B) (t : B -> Prop) (u : A -> Prop) : (term423 A B f t u) = (term424 A B f t u).
Proof. exact (MK_COMB (@lem5040010) (@lem5039997 A B f t u)). Qed.
Lemma lem5040015 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5040016 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term17 B s t).
Proof. exact (@lem5040015 B s t). Qed.
Lemma lem5040017 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term425 A B u f t) = t) = (term426 A B u f t).
Proof. exact (@lem5040016 B (term425 A B u f t) t). Qed.
Lemma lem5040032 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term427 A B u f t) = (term428 A B u f t).
Proof. exact (MK_COMB (@lem5040011 A B f t u) (@lem5040017 A B u f t)). Qed.
Lemma lem5040035 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term429 A B v u f t) = (term430 A B v u f t).
Proof. exact (MK_COMB (@lem5039991 A B t v u f) (@lem5040032 A B u f t)). Qed.
Lemma lem5040038 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term430 A B v u f t) = (term429 A B v u f t).
Proof. exact (SYM (@lem5040035 A B v u f t)). Qed.
Lemma lem5040050 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040051 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5040050 B P x). Qed.
Lemma lem5040052 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5040051 B t x). Qed.
Lemma lem5040053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5040054 {B : Type'} (t : B -> Prop) (x : B) : (term31 B x t) = (term34 B t x).
Proof. exact (MK_COMB (@lem5040053) (@lem5040052 B t x)). Qed.
Lemma lem5040056 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040057 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5040056 B P x). Qed.
Lemma lem5040058 {B : Type'} (v : B -> Prop) (x : B) : (@IN B x v) = (v x).
Proof. exact (@lem5040057 B v x). Qed.
Lemma lem5040059 {B : Type'} (t : B -> Prop) (v : B -> Prop) (x : B) : (term49 B t x v) = (term50 B t v x).
Proof. exact (MK_COMB (@lem5040054 B t x) (@lem5040058 B v x)). Qed.
Lemma lem5040062 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term51 B t v) = (term52 B t v).
Proof. exact (fun_ext (fun x : B => @lem5040059 B t v x)). Qed.
Lemma lem5040063 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040064 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term10 B t v) = (term53 B t v).
Proof. exact (MK_COMB (@lem5040063 B) (@lem5040062 B t v)). Qed.
Lemma lem5040069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040070 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term16 B t v) = (term54 B t v).
Proof. exact (MK_COMB (@lem5040069) (@lem5040064 B t v)). Qed.
Lemma lem5040078 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040079 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5040078 B P x). Qed.
Lemma lem5040080 {B : Type'} (v : B -> Prop) (y : B) : (@IN B y v) = (v y).
Proof. exact (@lem5040079 B v y). Qed.
Lemma lem5040081 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5040082 {B : Type'} (v : B -> Prop) (y : B) : (term31 B y v) = (term34 B v y).
Proof. exact (MK_COMB (@lem5040081) (@lem5040080 B v y)). Qed.
Lemma lem5040090 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040091 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5040090 A P x). Qed.
Lemma lem5040092 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5040091 A u x). Qed.
Lemma lem5040093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040094 {A : Type'} (u : A -> Prop) (x : A) : (term73 A x u) = (term74 A u x).
Proof. exact (MK_COMB (@lem5040093) (@lem5040092 A u x)). Qed.
Lemma lem5040097 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem5040098 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term75 A B u f x y) = (term76 A B u f x y).
Proof. exact (MK_COMB (@lem5040094 A u x) (@lem5040097 A B f x y)). Qed.
Lemma lem5040101 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term77 A B u f y) = (term78 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5040098 A B u f x y)). Qed.
Lemma lem5040102 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040103 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term28 A B u f y) = (term79 A B u f y).
Proof. exact (MK_COMB (@lem5040102 A) (@lem5040101 A B u f y)). Qed.
Lemma lem5040108 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term413 A B v u f y) = (term431 A B v u f y).
Proof. exact (MK_COMB (@lem5040082 B v y) (@lem5040103 A B u f y)). Qed.
Lemma lem5040111 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term432 A B v u f) = (term433 A B v u f).
Proof. exact (fun_ext (fun y : B => @lem5040108 A B v u f y)). Qed.
Lemma lem5040112 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040113 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term414 A B v u f) = (term434 A B v u f).
Proof. exact (MK_COMB (@lem5040112 B) (@lem5040111 A B v u f)). Qed.
Lemma lem5040118 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term417 A B t v u f) = (term435 A B t v u f).
Proof. exact (MK_COMB (@lem5040070 B t v) (@lem5040113 A B v u f)). Qed.
Lemma lem5040121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5040122 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term419 A B t v u f) = (term436 A B t v u f).
Proof. exact (MK_COMB (@lem5040121) (@lem5040118 A B t v u f)). Qed.
Lemma lem5040132 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term437 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5040133 {A : Type'} (p : A -> Prop) (x : A) : (term437 A x p) = (p x).
Proof. exact (@lem5040132 A p x). Qed.
Lemma lem5040134 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term438 A B x u f t) = (term439 A B u f t x).
Proof. exact (@lem5040133 A (term440 A B u f t) x). Qed.
Lemma lem5040135 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term439 A B u f t x) = (term441 A B u f x t).
Proof. exact (eq_refl (term439 A B u f t x)). Qed.
Lemma lem5040136 {A : Type'} (GEN_PVAR_219 : A) : (@SETSPEC A GEN_PVAR_219) = (@SETSPEC A GEN_PVAR_219).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_219)). Qed.
Lemma lem5040137 {A B : Type'} (GEN_PVAR_219 : A) (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term442 A B GEN_PVAR_219 u f t x) = (term443 A B GEN_PVAR_219 u f x t).
Proof. exact (MK_COMB (@lem5040136 A GEN_PVAR_219) (@lem5040135 A B u f x t)). Qed.
Lemma lem5040138 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5040139 {A B : Type'} (GEN_PVAR_219 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term444 A B GEN_PVAR_219 u f t x) = (term445 A B GEN_PVAR_219 u f t x).
Proof. exact (MK_COMB (@lem5040137 A B GEN_PVAR_219 u f x t) (@lem5040138 A x)). Qed.
Lemma lem5040140 {A B : Type'} (GEN_PVAR_219 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term446 A B GEN_PVAR_219 u f t) = (term447 A B GEN_PVAR_219 u f t).
Proof. exact (fun_ext (fun x : A => @lem5040139 A B GEN_PVAR_219 u f t x)). Qed.
Lemma lem5040141 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040142 {A B : Type'} (GEN_PVAR_219 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term448 A B GEN_PVAR_219 u f t) = (term449 A B GEN_PVAR_219 u f t).
Proof. exact (MK_COMB (@lem5040141 A) (@lem5040140 A B GEN_PVAR_219 u f t)). Qed.
Lemma lem5040143 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term450 A B u f t) = (term451 A B u f t).
Proof. exact (fun_ext (fun GEN_PVAR_219 : A => @lem5040142 A B GEN_PVAR_219 u f t)). Qed.
Lemma lem5040144 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5040145 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term452 A B u f t) = (term422 A B u f t).
Proof. exact (MK_COMB (@lem5040144 A) (@lem5040143 A B u f t)). Qed.
Lemma lem5040146 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5040147 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term438 A B x u f t) = (term453 A B x u f t).
Proof. exact (MK_COMB (@lem5040146 A x) (@lem5040145 A B u f t)). Qed.
Lemma lem5040148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5040149 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term454 A B x u f t) = (term455 A B x u f t).
Proof. exact (MK_COMB (@lem5040148) (@lem5040147 A B x u f t)). Qed.
Lemma lem5040150 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term439 A B u f t x) = (term441 A B u f x t).
Proof. exact (eq_refl (term439 A B u f t x)). Qed.
Lemma lem5040151 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : ((term438 A B x u f t) = (term439 A B u f t x)) = ((term453 A B x u f t) = (term441 A B u f x t)).
Proof. exact (MK_COMB (@lem5040149 A B x u f t) (@lem5040150 A B u f x t)). Qed.
Lemma lem5040152 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term453 A B x u f t) = (term441 A B u f x t).
Proof. exact (EQ_MP (@lem5040151 A B u f x t) (@lem5040134 A B u f t x)). Qed.
Lemma lem5040156 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040157 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5040156 A P x). Qed.
Lemma lem5040158 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5040157 A u x). Qed.
Lemma lem5040159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040160 {A : Type'} (u : A -> Prop) (x : A) : (term73 A x u) = (term74 A u x).
Proof. exact (MK_COMB (@lem5040159) (@lem5040158 A u x)). Qed.
Lemma lem5040162 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040163 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5040162 B P x). Qed.
Lemma lem5040164 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term456 A B f x t) = (term457 A B t f x).
Proof. exact (@lem5040163 B t (f x)). Qed.
Lemma lem5040165 {A B : Type'} (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term441 A B u f x t) = (term458 A B u t f x).
Proof. exact (MK_COMB (@lem5040160 A u x) (@lem5040164 A B t f x)). Qed.
Lemma lem5040168 {A B : Type'} (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term453 A B x u f t) = (term458 A B u t f x).
Proof. exact (TRANS (@lem5040152 A B u f x t) (@lem5040165 A B u t f x)). Qed.
Lemma lem5040169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5040170 {A B : Type'} (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term459 A B x u f t) = (term460 A B u t f x).
Proof. exact (MK_COMB (@lem5040169) (@lem5040168 A B u t f x)). Qed.
Lemma lem5040172 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040173 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5040172 A P x). Qed.
Lemma lem5040174 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5040173 A u x). Qed.
Lemma lem5040175 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term461 A B f t x u) = (term462 A B t f u x).
Proof. exact (MK_COMB (@lem5040170 A B u t f x) (@lem5040174 A u x)). Qed.
Lemma lem5040178 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term463 A B f t u) = (term464 A B t f u).
Proof. exact (fun_ext (fun x : A => @lem5040175 A B t f u x)). Qed.
Lemma lem5040179 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5040180 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term421 A B f t u) = (term465 A B t f u).
Proof. exact (MK_COMB (@lem5040179 A) (@lem5040178 A B t f u)). Qed.
Lemma lem5040185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040186 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term424 A B f t u) = (term466 A B t f u).
Proof. exact (MK_COMB (@lem5040185) (@lem5040180 A B t f u)). Qed.
Lemma lem5040194 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term55 A B y f s) = (term56 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5040195 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term55 A B y f s) = (term56 A B y f s).
Proof. exact (@lem5040194 A B y f s). Qed.
Lemma lem5040196 {A B : Type'} (x : B) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term467 A B x u f t) = (term468 A B x u f t).
Proof. exact (@lem5040195 A B x f (term422 A B u f t)). Qed.
Lemma lem5040206 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term437 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5040207 {A : Type'} (p : A -> Prop) (x : A) : (term437 A x p) = (p x).
Proof. exact (@lem5040206 A p x). Qed.
Lemma lem5040208 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term438 A B x u f t) = (term439 A B u f t x).
Proof. exact (@lem5040207 A (term440 A B u f t) x). Qed.
Lemma lem5040209 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term439 A B u f t x) = (term441 A B u f x t).
Proof. exact (eq_refl (term439 A B u f t x)). Qed.
Lemma lem5040210 {A : Type'} (GEN_PVAR_219 : A) : (@SETSPEC A GEN_PVAR_219) = (@SETSPEC A GEN_PVAR_219).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_219)). Qed.
Lemma lem5040211 {A B : Type'} (GEN_PVAR_219 : A) (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term442 A B GEN_PVAR_219 u f t x) = (term443 A B GEN_PVAR_219 u f x t).
Proof. exact (MK_COMB (@lem5040210 A GEN_PVAR_219) (@lem5040209 A B u f x t)). Qed.
Lemma lem5040212 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5040213 {A B : Type'} (GEN_PVAR_219 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term444 A B GEN_PVAR_219 u f t x) = (term445 A B GEN_PVAR_219 u f t x).
Proof. exact (MK_COMB (@lem5040211 A B GEN_PVAR_219 u f x t) (@lem5040212 A x)). Qed.
Lemma lem5040214 {A B : Type'} (GEN_PVAR_219 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term446 A B GEN_PVAR_219 u f t) = (term447 A B GEN_PVAR_219 u f t).
Proof. exact (fun_ext (fun x : A => @lem5040213 A B GEN_PVAR_219 u f t x)). Qed.
Lemma lem5040215 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040216 {A B : Type'} (GEN_PVAR_219 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term448 A B GEN_PVAR_219 u f t) = (term449 A B GEN_PVAR_219 u f t).
Proof. exact (MK_COMB (@lem5040215 A) (@lem5040214 A B GEN_PVAR_219 u f t)). Qed.
Lemma lem5040217 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term450 A B u f t) = (term451 A B u f t).
Proof. exact (fun_ext (fun GEN_PVAR_219 : A => @lem5040216 A B GEN_PVAR_219 u f t)). Qed.
Lemma lem5040218 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5040219 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term452 A B u f t) = (term422 A B u f t).
Proof. exact (MK_COMB (@lem5040218 A) (@lem5040217 A B u f t)). Qed.
Lemma lem5040220 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5040221 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term438 A B x u f t) = (term453 A B x u f t).
Proof. exact (MK_COMB (@lem5040220 A x) (@lem5040219 A B u f t)). Qed.
Lemma lem5040222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5040223 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term454 A B x u f t) = (term455 A B x u f t).
Proof. exact (MK_COMB (@lem5040222) (@lem5040221 A B x u f t)). Qed.
Lemma lem5040224 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term439 A B u f t x) = (term441 A B u f x t).
Proof. exact (eq_refl (term439 A B u f t x)). Qed.
Lemma lem5040225 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : ((term438 A B x u f t) = (term439 A B u f t x)) = ((term453 A B x u f t) = (term441 A B u f x t)).
Proof. exact (MK_COMB (@lem5040223 A B x u f t) (@lem5040224 A B u f x t)). Qed.
Lemma lem5040226 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term453 A B x u f t) = (term441 A B u f x t).
Proof. exact (EQ_MP (@lem5040225 A B u f x t) (@lem5040208 A B u f t x)). Qed.
Lemma lem5040230 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040231 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5040230 A P x). Qed.
Lemma lem5040232 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5040231 A u x). Qed.
Lemma lem5040233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040234 {A : Type'} (u : A -> Prop) (x : A) : (term73 A x u) = (term74 A u x).
Proof. exact (MK_COMB (@lem5040233) (@lem5040232 A u x)). Qed.
Lemma lem5040236 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040237 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5040236 B P x). Qed.
Lemma lem5040238 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term456 A B f x t) = (term457 A B t f x).
Proof. exact (@lem5040237 B t (f x)). Qed.
Lemma lem5040239 {A B : Type'} (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term441 A B u f x t) = (term458 A B u t f x).
Proof. exact (MK_COMB (@lem5040234 A u x) (@lem5040238 A B t f x)). Qed.
Lemma lem5040242 {A B : Type'} (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term453 A B x u f t) = (term458 A B u t f x).
Proof. exact (TRANS (@lem5040226 A B u f x t) (@lem5040239 A B u t f x)). Qed.
Lemma lem5040243 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term57 A B x f x') = (term57 A B x f x').
Proof. exact (eq_refl (term57 A B x f x')). Qed.
Lemma lem5040244 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term469 A B x x' u f t) = (term470 A B x u t f x').
Proof. exact (MK_COMB (@lem5040243 A B x f x') (@lem5040242 A B u t f x')). Qed.
Lemma lem5040247 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term471 A B x u f t) = (term472 A B x u t f).
Proof. exact (fun_ext (fun x' : A => @lem5040244 A B x u t f x')). Qed.
Lemma lem5040248 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040249 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term468 A B x u f t) = (term473 A B x u t f).
Proof. exact (MK_COMB (@lem5040248 A) (@lem5040247 A B x u t f)). Qed.
Lemma lem5040254 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term467 A B x u f t) = (term473 A B x u t f).
Proof. exact (TRANS (@lem5040196 A B x u f t) (@lem5040249 A B x u t f)). Qed.
Lemma lem5040255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5040256 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term474 A B x u f t) = (term475 A B x u t f).
Proof. exact (MK_COMB (@lem5040255) (@lem5040254 A B x u t f)). Qed.
Lemma lem5040258 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5040259 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem5040258 B P x). Qed.
Lemma lem5040260 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem5040259 B t x). Qed.
Lemma lem5040261 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : ((term467 A B x u f t) = (@IN B x t)) = ((term473 A B x u t f) = (t x)).
Proof. exact (MK_COMB (@lem5040256 A B x u t f) (@lem5040260 B t x)). Qed.
Lemma lem5040264 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term476 A B u f t) = (term477 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5040261 A B u f t x)). Qed.
Lemma lem5040265 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040266 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term426 A B u f t) = (term478 A B u f t).
Proof. exact (MK_COMB (@lem5040265 B) (@lem5040264 A B u f t)). Qed.
Lemma lem5040271 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term428 A B u f t) = (term479 A B u f t).
Proof. exact (MK_COMB (@lem5040186 A B t f u) (@lem5040266 A B u f t)). Qed.
Lemma lem5040274 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term430 A B v u f t) = (term480 A B v u f t).
Proof. exact (MK_COMB (@lem5040122 A B t v u f) (@lem5040271 A B u f t)). Qed.
Lemma lem5040277 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term480 A B v u f t) = (term430 A B v u f t).
Proof. exact (SYM (@lem5040274 A B v u f t)). Qed.
Lemma lem5040279 (p : Prop) : p = (term82 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5040280 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term480 A B v u f t) = (term481 A B v u f t).
Proof. exact (@lem5040279 (term480 A B v u f t)). Qed.
Lemma lem5040281 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term481 A B v u f t) = (term480 A B v u f t).
Proof. exact (SYM (@lem5040280 A B v u f t)). Qed.
Lemma lem5040282 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term482 A B v u f t) : term482 A B v u f t.
Proof. exact (h1). Qed.
Lemma lem5040285 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term481 A B v u f t) : term481 A B v u f t.
Proof. exact (h1). Qed.
Lemma lem5040286 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term483 A B v u f t.
Proof. exact (fun h0 : term481 A B v u f t => @lem5040285 A B v u f t h0). Qed.
Lemma lem5040287 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term483 A B v u f t) : term483 A B v u f t.
Proof. exact (h1). Qed.
Lemma lem5040288 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term481 A B v u f t) : term481 A B v u f t.
Proof. exact (h1). Qed.
Lemma lem5040289 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term481 A B v u f t) (h2 : term483 A B v u f t) : term481 A B v u f t.
Proof. exact (@lem5040287 A B v u f t h2 (@lem5040288 A B v u f t h1)). Qed.
Lemma lem5040290 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term481 A B v u f t) : term484 A B v u f t.
Proof. exact (fun h0 : term483 A B v u f t => @lem5040289 A B v u f t h1 h0). Qed.
Lemma lem5040291 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term483 A B v u f t) : term483 A B v u f t.
Proof. exact (h1). Qed.
Lemma lem5040292 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term481 A B v u f t) (h2 : term483 A B v u f t) : term481 A B v u f t.
Proof. exact (@lem5040290 A B v u f t h1 (@lem5040291 A B v u f t h2)). Qed.
Lemma lem5040293 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term483 A B v u f t) : term483 A B v u f t.
Proof. exact (fun h0 : term481 A B v u f t => @lem5040292 A B v u f t h0 h1). Qed.
Lemma lem5040294 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term485 A B v u f t.
Proof. exact (fun h0 : term483 A B v u f t => @lem5040293 A B v u f t h0). Qed.
Lemma lem5040297 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term483 A B v u f t.
Proof. exact (@lem5040294 A B v u f t (@lem5040286 A B v u f t)). Qed.
Lemma lem5040298 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term483 A B v u f t.
Proof. exact (@lem5040297 A B v u f t). Qed.
Lemma lem5040316 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5040317 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term481 A B v u f t) = (term486 A B v u f t).
Proof. exact (@lem5040316 (term482 A B v u f t)). Qed.
Lemma lem5040319 (t : Prop) : (term89 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5040320 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term486 A B v u f t) = (term480 A B v u f t).
Proof. exact (@lem5040319 (term480 A B v u f t)). Qed.
Lemma lem5040323 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term481 A B v u f t) = (term480 A B v u f t).
Proof. exact (TRANS (@lem5040317 A B v u f t) (@lem5040320 A B v u f t)). Qed.
Lemma lem5040434 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term487 A B u f t) = (term488 A B u f t).
Proof. exact (fun_ext (fun v : B -> Prop => @lem5040323 A B v u f t)). Qed.
Lemma lem5040435 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5040436 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term489 A B u f t) = (term490 A B u f t).
Proof. exact (MK_COMB (@lem5040435 B) (@lem5040434 A B u f t)). Qed.
Lemma lem5040441 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term491 A B f t) = (term492 A B f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem5040436 A B u f t)). Qed.
Lemma lem5040442 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5040443 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term493 A B f t) = (term494 A B f t).
Proof. exact (MK_COMB (@lem5040442 A) (@lem5040441 A B f t)). Qed.
Lemma lem5040448 {A B : Type'} (t : B -> Prop) : (term495 A B t) = (term496 A B t).
Proof. exact (fun_ext (fun f : A -> B => @lem5040443 A B f t)). Qed.
Lemma lem5040449 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5040450 {A B : Type'} (t : B -> Prop) : (term497 A B t) = (term498 A B t).
Proof. exact (MK_COMB (@lem5040449 A B) (@lem5040448 A B t)). Qed.
Lemma lem5040455 {A B : Type'} : (term499 A B) = (term500 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5040450 A B t)). Qed.
Lemma lem5040456 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5040465 {A B : Type'} : (term501 A B) = (term502 A B).
Proof. exact (MK_COMB (@lem5040456 B) (@lem5040455 A B)). Qed.
Lemma lem5040466 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem5040475 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term470 A B x u t f x') = (term470 A B x u t f x').
Proof. exact (eq_refl (term470 A B x u t f x')). Qed.
Lemma lem5040476 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term472 A B x u t f) = (term472 A B x u t f).
Proof. exact (fun_ext (fun x' : A => @lem5040475 A B x u t f x')). Qed.
Lemma lem5040477 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040478 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term473 A B x u t f) = (term473 A B x u t f).
Proof. exact (MK_COMB (@lem5040477 A) (@lem5040476 A B x u t f)). Qed.
Lemma lem5040479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5040480 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term475 A B x u t f) = (term475 A B x u t f).
Proof. exact (MK_COMB (@lem5040479) (@lem5040478 A B x u t f)). Qed.
Lemma lem5040481 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : ((term473 A B x u t f) = (t x)) = ((term473 A B x u t f) = (t x)).
Proof. exact (MK_COMB (@lem5040480 A B x u t f) (@lem5040466 B t x)). Qed.
Lemma lem5040482 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term477 A B u f t) = (term477 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5040481 A B u f t x)). Qed.
Lemma lem5040483 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040484 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term478 A B u f t) = (term478 A B u f t).
Proof. exact (MK_COMB (@lem5040483 B) (@lem5040482 A B u f t)). Qed.
Lemma lem5040493 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term462 A B t f u x) = (term462 A B t f u x).
Proof. exact (eq_refl (term462 A B t f u x)). Qed.
Lemma lem5040494 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term464 A B t f u) = (term464 A B t f u).
Proof. exact (fun_ext (fun x : A => @lem5040493 A B t f u x)). Qed.
Lemma lem5040495 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5040496 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term465 A B t f u) = (term465 A B t f u).
Proof. exact (MK_COMB (@lem5040495 A) (@lem5040494 A B t f u)). Qed.
Lemma lem5040497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040498 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term466 A B t f u) = (term466 A B t f u).
Proof. exact (MK_COMB (@lem5040497) (@lem5040496 A B t f u)). Qed.
Lemma lem5040499 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term479 A B u f t) = (term479 A B u f t).
Proof. exact (MK_COMB (@lem5040498 A B t f u) (@lem5040484 A B u f t)). Qed.
Lemma lem5040504 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term76 A B u f x y) = (term76 A B u f x y).
Proof. exact (eq_refl (term76 A B u f x y)). Qed.
Lemma lem5040505 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term78 A B u f y) = (term78 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5040504 A B u f x y)). Qed.
Lemma lem5040506 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040507 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term79 A B u f y) = (term79 A B u f y).
Proof. exact (MK_COMB (@lem5040506 A) (@lem5040505 A B u f y)). Qed.
Lemma lem5040510 {B : Type'} (v : B -> Prop) (y : B) : (term34 B v y) = (term34 B v y).
Proof. exact (eq_refl (term34 B v y)). Qed.
Lemma lem5040511 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term431 A B v u f y) = (term431 A B v u f y).
Proof. exact (MK_COMB (@lem5040510 B v y) (@lem5040507 A B u f y)). Qed.
Lemma lem5040512 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term433 A B v u f) = (term433 A B v u f).
Proof. exact (fun_ext (fun y : B => @lem5040511 A B v u f y)). Qed.
Lemma lem5040513 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040514 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term434 A B v u f) = (term434 A B v u f).
Proof. exact (MK_COMB (@lem5040513 B) (@lem5040512 A B v u f)). Qed.
Lemma lem5040519 {B : Type'} (t : B -> Prop) (v : B -> Prop) (x : B) : (term50 B t v x) = (term50 B t v x).
Proof. exact (eq_refl (term50 B t v x)). Qed.
Lemma lem5040520 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term52 B t v) = (term52 B t v).
Proof. exact (fun_ext (fun x : B => @lem5040519 B t v x)). Qed.
Lemma lem5040521 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040522 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term53 B t v) = (term53 B t v).
Proof. exact (MK_COMB (@lem5040521 B) (@lem5040520 B t v)). Qed.
Lemma lem5040523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040524 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term54 B t v) = (term54 B t v).
Proof. exact (MK_COMB (@lem5040523) (@lem5040522 B t v)). Qed.
Lemma lem5040525 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term435 A B t v u f) = (term435 A B t v u f).
Proof. exact (MK_COMB (@lem5040524 B t v) (@lem5040514 A B v u f)). Qed.
Lemma lem5040526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5040527 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term436 A B t v u f) = (term436 A B t v u f).
Proof. exact (MK_COMB (@lem5040526) (@lem5040525 A B t v u f)). Qed.
Lemma lem5040528 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term480 A B v u f t) = (term480 A B v u f t).
Proof. exact (MK_COMB (@lem5040527 A B t v u f) (@lem5040499 A B u f t)). Qed.
Lemma lem5040529 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term488 A B u f t) = (term488 A B u f t).
Proof. exact (fun_ext (fun v : B -> Prop => @lem5040528 A B v u f t)). Qed.
Lemma lem5040530 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5040531 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term490 A B u f t) = (term490 A B u f t).
Proof. exact (MK_COMB (@lem5040530 B) (@lem5040529 A B u f t)). Qed.
Lemma lem5040532 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term492 A B f t) = (term492 A B f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem5040531 A B u f t)). Qed.
Lemma lem5040533 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5040534 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term494 A B f t) = (term494 A B f t).
Proof. exact (MK_COMB (@lem5040533 A) (@lem5040532 A B f t)). Qed.
Lemma lem5040535 {A B : Type'} (t : B -> Prop) : (term496 A B t) = (term496 A B t).
Proof. exact (fun_ext (fun f : A -> B => @lem5040534 A B f t)). Qed.
Lemma lem5040536 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5040537 {A B : Type'} (t : B -> Prop) : (term498 A B t) = (term498 A B t).
Proof. exact (MK_COMB (@lem5040536 A B) (@lem5040535 A B t)). Qed.
Lemma lem5040538 {A B : Type'} : (term500 A B) = (term500 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5040537 A B t)). Qed.
Lemma lem5040539 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5040540 {A B : Type'} : (term502 A B) = (term502 A B).
Proof. exact (MK_COMB (@lem5040539 B) (@lem5040538 A B)). Qed.
Lemma lem5040623 {A B : Type'} : (term501 A B) = (term502 A B).
Proof. exact (TRANS (@lem5040465 A B) (@lem5040540 A B)). Qed.
Lemma lem5040624 {A B : Type'} : (term502 A B) = (term501 A B).
Proof. exact (SYM (@lem5040623 A B)). Qed.
Lemma lem5040625 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term435 A B t v u f) : term435 A B t v u f.
Proof. exact (h1). Qed.
Lemma lem5040627 (p : Prop) : p = (term82 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5040628 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term479 A B u f t) = (term503 A B u f t).
Proof. exact (@lem5040627 (term479 A B u f t)). Qed.
Lemma lem5040629 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term503 A B u f t) = (term479 A B u f t).
Proof. exact (SYM (@lem5040628 A B u f t)). Qed.
Lemma lem5040630 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term504 A B u f t) : term504 A B u f t.
Proof. exact (h1). Qed.
Lemma lem5040637 {B : Type'} (t : B -> Prop) (v : B -> Prop) (x : B) : (term50 B t v x) = (term119 B t v x).
Proof. exact (@lem17265 (t x) (v x)). Qed.
Lemma lem5040638 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term52 B t v) = (term120 B t v).
Proof. exact (fun_ext (fun x : B => @lem5040637 B t v x)). Qed.
Lemma lem5040639 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040640 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term53 B t v) = (term121 B t v).
Proof. exact (MK_COMB (@lem5040639 B) (@lem5040638 B t v)). Qed.
Lemma lem5040646 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term76 A B u f x y) = (term76 A B u f x y).
Proof. exact (eq_refl (term76 A B u f x y)). Qed.
Lemma lem5040647 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term78 A B u f y) = (term78 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5040646 A B u f x y)). Qed.
Lemma lem5040648 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040649 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term79 A B u f y) = (term79 A B u f y).
Proof. exact (MK_COMB (@lem5040648 A) (@lem5040647 A B u f y)). Qed.
Lemma lem5040651 {B : Type'} (v : B -> Prop) (y : B) : (term383 B v y) = (term383 B v y).
Proof. exact (eq_refl (term383 B v y)). Qed.
Lemma lem5040652 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term505 A B v u f y) = (term505 A B v u f y).
Proof. exact (MK_COMB (@lem5040651 B v y) (@lem5040649 A B u f y)). Qed.
Lemma lem5040653 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term431 A B v u f y) = (term505 A B v u f y).
Proof. exact (@lem17265 (v y) (term79 A B u f y)). Qed.
Lemma lem5040654 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term431 A B v u f y) = (term505 A B v u f y).
Proof. exact (TRANS (@lem5040653 A B v u f y) (@lem5040652 A B v u f y)). Qed.
Lemma lem5040655 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term433 A B v u f) = (term506 A B v u f).
Proof. exact (fun_ext (fun y : B => @lem5040654 A B v u f y)). Qed.
Lemma lem5040656 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040657 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term434 A B v u f) = (term507 A B v u f).
Proof. exact (MK_COMB (@lem5040656 B) (@lem5040655 A B v u f)). Qed.
Lemma lem5040658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040659 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term54 B t v) = (term145 B t v).
Proof. exact (MK_COMB (@lem5040658) (@lem5040640 B t v)). Qed.
Lemma lem5040660 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term435 A B t v u f) = (term508 A B t v u f).
Proof. exact (MK_COMB (@lem5040659 B t v) (@lem5040657 A B v u f)). Qed.
Lemma lem5040771 {A : Type'} (P : Prop) (Q : A -> Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5040772 {A : Type'} (P : Prop) (Q : A -> Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (@lem5040771 A P Q). Qed.
Lemma lem5040773 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term509 A B v u f y) = (term510 A B v u f y).
Proof. exact (@lem5040772 A (term349 B v y) (term78 A B u f y)). Qed.
Lemma lem5040774 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term315 A B u f y x) = (term76 A B u f x y).
Proof. exact (eq_refl (term315 A B u f y x)). Qed.
Lemma lem5040775 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term511 A B u f y) = (term78 A B u f y).
Proof. exact (fun_ext (fun x : A => @lem5040774 A B u f x y)). Qed.
Lemma lem5040776 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040777 {A B : Type'} (u : A -> Prop) (f : A -> B) (y : B) : (term512 A B u f y) = (term79 A B u f y).
Proof. exact (MK_COMB (@lem5040776 A) (@lem5040775 A B u f y)). Qed.
Lemma lem5040778 {B : Type'} (v : B -> Prop) (y : B) : (term383 B v y) = (term383 B v y).
Proof. exact (eq_refl (term383 B v y)). Qed.
Lemma lem5040779 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term509 A B v u f y) = (term505 A B v u f y).
Proof. exact (MK_COMB (@lem5040778 B v y) (@lem5040777 A B u f y)). Qed.
Lemma lem5040780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5040781 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term513 A B v u f y) = (term514 A B v u f y).
Proof. exact (MK_COMB (@lem5040780) (@lem5040779 A B v u f y)). Qed.
Lemma lem5040782 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term315 A B u f y x) = (term76 A B u f x y).
Proof. exact (eq_refl (term315 A B u f y x)). Qed.
Lemma lem5040783 {B : Type'} (v : B -> Prop) (y : B) : (term383 B v y) = (term383 B v y).
Proof. exact (eq_refl (term383 B v y)). Qed.
Lemma lem5040784 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term515 A B v u f y x) = (term516 A B v u f x y).
Proof. exact (MK_COMB (@lem5040783 B v y) (@lem5040782 A B u f x y)). Qed.
Lemma lem5040785 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term517 A B v u f y) = (term518 A B v u f y).
Proof. exact (fun_ext (fun x : A => @lem5040784 A B v u f x y)). Qed.
Lemma lem5040786 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040787 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term510 A B v u f y) = (term519 A B v u f y).
Proof. exact (MK_COMB (@lem5040786 A) (@lem5040785 A B v u f y)). Qed.
Lemma lem5040788 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : ((term509 A B v u f y) = (term510 A B v u f y)) = ((term505 A B v u f y) = (term519 A B v u f y)).
Proof. exact (MK_COMB (@lem5040781 A B v u f y) (@lem5040787 A B v u f y)). Qed.
Lemma lem5040789 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term505 A B v u f y) = (term519 A B v u f y).
Proof. exact (EQ_MP (@lem5040788 A B v u f y) (@lem5040773 A B v u f y)). Qed.
Lemma lem5040790 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term506 A B v u f) = (term520 A B v u f).
Proof. exact (fun_ext (fun y : B => @lem5040789 A B v u f y)). Qed.
Lemma lem5040791 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040792 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term507 A B v u f) = (term521 A B v u f).
Proof. exact (MK_COMB (@lem5040791 B) (@lem5040790 A B v u f)). Qed.
Lemma lem5040794 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5040795 {A B : Type'} (P : type1470 A B) : (term199 A B P) = (term200 A B P).
Proof. exact (@lem5040794 B A P). Qed.
Lemma lem5040796 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term522 A B v u f) = (term523 A B v u f).
Proof. exact (@lem5040795 A B (term524 A B v u f)). Qed.
Lemma lem5040797 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term525 A B v u f y) = (term518 A B v u f y).
Proof. exact (eq_refl (term525 A B v u f y)). Qed.
Lemma lem5040798 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5040799 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) (x : A) : (term526 A B v u f y x) = (term527 A B v u f y x).
Proof. exact (MK_COMB (@lem5040797 A B v u f y) (@lem5040798 A x)). Qed.
Lemma lem5040800 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term527 A B v u f y x) = (term516 A B v u f x y).
Proof. exact (eq_refl (term527 A B v u f y x)). Qed.
Lemma lem5040801 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : A) (y : B) : (term526 A B v u f y x) = (term516 A B v u f x y).
Proof. exact (TRANS (@lem5040799 A B v u f y x) (@lem5040800 A B v u f x y)). Qed.
Lemma lem5040802 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term528 A B v u f y) = (term518 A B v u f y).
Proof. exact (fun_ext (fun x : A => @lem5040801 A B v u f x y)). Qed.
Lemma lem5040803 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040804 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term529 A B v u f y) = (term519 A B v u f y).
Proof. exact (MK_COMB (@lem5040803 A) (@lem5040802 A B v u f y)). Qed.
Lemma lem5040805 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term530 A B v u f) = (term520 A B v u f).
Proof. exact (fun_ext (fun y : B => @lem5040804 A B v u f y)). Qed.
Lemma lem5040806 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040807 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term522 A B v u f) = (term521 A B v u f).
Proof. exact (MK_COMB (@lem5040806 B) (@lem5040805 A B v u f)). Qed.
Lemma lem5040808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5040809 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term531 A B v u f) = (term532 A B v u f).
Proof. exact (MK_COMB (@lem5040808) (@lem5040807 A B v u f)). Qed.
Lemma lem5040810 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (y : B) : (term525 A B v u f y) = (term518 A B v u f y).
Proof. exact (eq_refl (term525 A B v u f y)). Qed.
Lemma lem5040811 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5040812 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term533 A B v u f x y) = (term534 A B v u f x y).
Proof. exact (MK_COMB (@lem5040810 A B v u f y) (@lem5040811 A B x y)). Qed.
Lemma lem5040813 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term534 A B v u f x y) = (term535 A B v u f x y).
Proof. exact (eq_refl (term534 A B v u f x y)). Qed.
Lemma lem5040814 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term533 A B v u f x y) = (term535 A B v u f x y).
Proof. exact (TRANS (@lem5040812 A B v u f x y) (@lem5040813 A B v u f x y)). Qed.
Lemma lem5040815 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : B -> A) : (term536 A B v u f x) = (term537 A B v u f x).
Proof. exact (fun_ext (fun y : B => @lem5040814 A B v u f x y)). Qed.
Lemma lem5040816 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5040817 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : B -> A) : (term538 A B v u f x) = (term539 A B v u f x).
Proof. exact (MK_COMB (@lem5040816 B) (@lem5040815 A B v u f x)). Qed.
Lemma lem5040818 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term540 A B v u f) = (term541 A B v u f).
Proof. exact (fun_ext (fun x : B -> A => @lem5040817 A B v u f x)). Qed.
Lemma lem5040819 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5040820 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term523 A B v u f) = (term542 A B v u f).
Proof. exact (MK_COMB (@lem5040819 A B) (@lem5040818 A B v u f)). Qed.
Lemma lem5040821 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : ((term522 A B v u f) = (term523 A B v u f)) = ((term521 A B v u f) = (term542 A B v u f)).
Proof. exact (MK_COMB (@lem5040809 A B v u f) (@lem5040820 A B v u f)). Qed.
Lemma lem5040822 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term521 A B v u f) = (term542 A B v u f).
Proof. exact (EQ_MP (@lem5040821 A B v u f) (@lem5040796 A B v u f)). Qed.
Lemma lem5040823 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term507 A B v u f) = (term542 A B v u f).
Proof. exact (TRANS (@lem5040792 A B v u f) (@lem5040822 A B v u f)). Qed.
Lemma lem5040824 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term145 B t v) = (term145 B t v).
Proof. exact (eq_refl (term145 B t v)). Qed.
Lemma lem5040825 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term508 A B t v u f) = (term543 A B t v u f).
Proof. exact (MK_COMB (@lem5040824 B t v) (@lem5040823 A B v u f)). Qed.
Lemma lem5040827 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5040828 {A B : Type'} (P : Prop) (Q : type805 A B) : (term246 A B P Q) = (term247 A B P Q).
Proof. exact (@lem5040827 (B -> A) P Q). Qed.
Lemma lem5040829 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term544 A B t v u f) = (term545 A B t v u f).
Proof. exact (@lem5040828 A B (term121 B t v) (term541 A B v u f)). Qed.
Lemma lem5040830 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : B -> A) : (term546 A B v u f x) = (term539 A B v u f x).
Proof. exact (eq_refl (term546 A B v u f x)). Qed.
Lemma lem5040831 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term547 A B v u f) = (term541 A B v u f).
Proof. exact (fun_ext (fun x : B -> A => @lem5040830 A B v u f x)). Qed.
Lemma lem5040832 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5040833 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term548 A B v u f) = (term542 A B v u f).
Proof. exact (MK_COMB (@lem5040832 A B) (@lem5040831 A B v u f)). Qed.
Lemma lem5040834 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term145 B t v) = (term145 B t v).
Proof. exact (eq_refl (term145 B t v)). Qed.
Lemma lem5040835 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term544 A B t v u f) = (term543 A B t v u f).
Proof. exact (MK_COMB (@lem5040834 B t v) (@lem5040833 A B v u f)). Qed.
Lemma lem5040836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5040837 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term549 A B t v u f) = (term550 A B t v u f).
Proof. exact (MK_COMB (@lem5040836) (@lem5040835 A B t v u f)). Qed.
Lemma lem5040838 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : B -> A) : (term546 A B v u f x) = (term539 A B v u f x).
Proof. exact (eq_refl (term546 A B v u f x)). Qed.
Lemma lem5040839 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term145 B t v) = (term145 B t v).
Proof. exact (eq_refl (term145 B t v)). Qed.
Lemma lem5040840 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x : B -> A) : (term551 A B t v u f x) = (term552 A B t v u f x).
Proof. exact (MK_COMB (@lem5040839 B t v) (@lem5040838 A B v u f x)). Qed.
Lemma lem5040841 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term553 A B t v u f) = (term554 A B t v u f).
Proof. exact (fun_ext (fun x : B -> A => @lem5040840 A B t v u f x)). Qed.
Lemma lem5040842 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5040843 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term545 A B t v u f) = (term555 A B t v u f).
Proof. exact (MK_COMB (@lem5040842 A B) (@lem5040841 A B t v u f)). Qed.
Lemma lem5040844 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : ((term544 A B t v u f) = (term545 A B t v u f)) = ((term543 A B t v u f) = (term555 A B t v u f)).
Proof. exact (MK_COMB (@lem5040837 A B t v u f) (@lem5040843 A B t v u f)). Qed.
Lemma lem5040845 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term543 A B t v u f) = (term555 A B t v u f).
Proof. exact (EQ_MP (@lem5040844 A B t v u f) (@lem5040829 A B t v u f)). Qed.
Lemma lem5040847 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term508 A B t v u f) = (term555 A B t v u f).
Proof. exact (TRANS (@lem5040825 A B t v u f) (@lem5040845 A B t v u f)). Qed.
Lemma lem5040848 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term435 A B t v u f) = (term555 A B t v u f).
Proof. exact (TRANS (@lem5040660 A B t v u f) (@lem5040847 A B t v u f)). Qed.
Lemma lem5040849 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term435 A B t v u f) : term555 A B t v u f.
Proof. exact (EQ_MP (@lem5040848 A B t v u f) (@lem5040625 A B t v u f h1)). Qed.
Lemma lem5040860 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term556 A B t f u x) = (term557 A B t f u x).
Proof. exact (@lem17362 (term458 A B u t f x) (u x)). Qed.
Lemma lem5040861 {A : Type'} (P : A -> Prop) : (term110 A P) = (term111 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5040862 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term558 A B t f u) = (term559 A B t f u).
Proof. exact (@lem5040861 A (term464 A B t f u)). Qed.
Lemma lem5040863 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term560 A B t f u x) = (term462 A B t f u x).
Proof. exact (eq_refl (term560 A B t f u x)). Qed.
Lemma lem5040864 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5040865 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term561 A B t f u x) = (term556 A B t f u x).
Proof. exact (MK_COMB (@lem5040864) (@lem5040863 A B t f u x)). Qed.
Lemma lem5040866 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term561 A B t f u x) = (term557 A B t f u x).
Proof. exact (TRANS (@lem5040865 A B t f u x) (@lem5040860 A B t f u x)). Qed.
Lemma lem5040867 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term562 A B t f u) = (term563 A B t f u).
Proof. exact (fun_ext (fun x : A => @lem5040866 A B t f u x)). Qed.
Lemma lem5040868 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040869 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term559 A B t f u) = (term564 A B t f u).
Proof. exact (MK_COMB (@lem5040868 A) (@lem5040867 A B t f u)). Qed.
Lemma lem5040870 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term558 A B t f u) = (term564 A B t f u).
Proof. exact (TRANS (@lem5040862 A B t f u) (@lem5040869 A B t f u)). Qed.
Lemma lem5040881 {A B : Type'} (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term565 A B u t f x) = (term566 A B u t f x).
Proof. exact (@lem17045 (u x) (term457 A B t f x)). Qed.
Lemma lem5040886 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term567 A B x f x') = (term567 A B x f x').
Proof. exact (eq_refl (term567 A B x f x')). Qed.
Lemma lem5040887 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term568 A B x u t f x') = (term569 A B x u t f x').
Proof. exact (MK_COMB (@lem5040886 A B x f x') (@lem5040881 A B u t f x')). Qed.
Lemma lem5040888 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term570 A B x u t f x') = (term568 A B x u t f x').
Proof. exact (@lem17045 (x = (f x')) (term458 A B u t f x')). Qed.
Lemma lem5040889 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term570 A B x u t f x') = (term569 A B x u t f x').
Proof. exact (TRANS (@lem5040888 A B x u t f x') (@lem5040887 A B x u t f x')). Qed.
Lemma lem5040892 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term470 A B x u t f x') = (term470 A B x u t f x').
Proof. exact (eq_refl (term470 A B x u t f x')). Qed.
Lemma lem5040893 {A : Type'} (P : A -> Prop) : (term124 A P) = (term125 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5040894 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term571 A B x u t f) = (term572 A B x u t f).
Proof. exact (@lem5040893 A (term472 A B x u t f)). Qed.
Lemma lem5040895 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term573 A B x u t f x') = (term470 A B x u t f x').
Proof. exact (eq_refl (term573 A B x u t f x')). Qed.
Lemma lem5040896 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5040897 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term574 A B x u t f x') = (term570 A B x u t f x').
Proof. exact (MK_COMB (@lem5040896) (@lem5040895 A B x u t f x')). Qed.
Lemma lem5040898 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term574 A B x u t f x') = (term569 A B x u t f x').
Proof. exact (TRANS (@lem5040897 A B x u t f x') (@lem5040889 A B x u t f x')). Qed.
Lemma lem5040899 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term575 A B x u t f) = (term576 A B x u t f).
Proof. exact (fun_ext (fun x' : A => @lem5040898 A B x u t f x')). Qed.
Lemma lem5040900 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5040901 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term572 A B x u t f) = (term577 A B x u t f).
Proof. exact (MK_COMB (@lem5040900 A) (@lem5040899 A B x u t f)). Qed.
Lemma lem5040902 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term571 A B x u t f) = (term577 A B x u t f).
Proof. exact (TRANS (@lem5040894 A B x u t f) (@lem5040901 A B x u t f)). Qed.
Lemma lem5040903 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term472 A B x u t f) = (term472 A B x u t f).
Proof. exact (fun_ext (fun x' : A => @lem5040892 A B x u t f x')). Qed.
Lemma lem5040904 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5040905 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term473 A B x u t f) = (term473 A B x u t f).
Proof. exact (MK_COMB (@lem5040904 A) (@lem5040903 A B x u t f)). Qed.
Lemma lem5040906 {B : Type'} (t : B -> Prop) (x : B) : (term349 B t x) = (term349 B t x).
Proof. exact (eq_refl (term349 B t x)). Qed.
Lemma lem5040907 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem5040908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040909 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term578 A B x u t f) = (term579 A B x u t f).
Proof. exact (MK_COMB (@lem5040908) (@lem5040902 A B x u t f)). Qed.
Lemma lem5040910 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term580 A B u f t x) = (term581 A B u f t x).
Proof. exact (MK_COMB (@lem5040909 A B x u t f) (@lem5040907 B t x)). Qed.
Lemma lem5040911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5040912 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term582 A B x u t f) = (term582 A B x u t f).
Proof. exact (MK_COMB (@lem5040911) (@lem5040905 A B x u t f)). Qed.
Lemma lem5040913 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term583 A B u f t x) = (term583 A B u f t x).
Proof. exact (MK_COMB (@lem5040912 A B x u t f) (@lem5040906 B t x)). Qed.
Lemma lem5040914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5040915 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term584 A B u f t x) = (term584 A B u f t x).
Proof. exact (MK_COMB (@lem5040914) (@lem5040913 A B u f t x)). Qed.
Lemma lem5040916 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term585 A B u f t x) = (term586 A B u f t x).
Proof. exact (MK_COMB (@lem5040915 A B u f t x) (@lem5040910 A B u f t x)). Qed.
Lemma lem5040917 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term587 A B u f t x) = (term585 A B u f t x).
Proof. exact (@lem17646 (term473 A B x u t f) (t x)). Qed.
Lemma lem5040918 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term587 A B u f t x) = (term586 A B u f t x).
Proof. exact (TRANS (@lem5040917 A B u f t x) (@lem5040916 A B u f t x)). Qed.
Lemma lem5040919 {B : Type'} (P : B -> Prop) : (term110 B P) = (term111 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5040920 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term588 A B u f t) = (term589 A B u f t).
Proof. exact (@lem5040919 B (term477 A B u f t)). Qed.
Lemma lem5040921 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term590 A B u f t x) = ((term473 A B x u t f) = (t x)).
Proof. exact (eq_refl (term590 A B u f t x)). Qed.
Lemma lem5040922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5040923 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term591 A B u f t x) = (term587 A B u f t x).
Proof. exact (MK_COMB (@lem5040922) (@lem5040921 A B u f t x)). Qed.
Lemma lem5040924 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term591 A B u f t x) = (term586 A B u f t x).
Proof. exact (TRANS (@lem5040923 A B u f t x) (@lem5040918 A B u f t x)). Qed.
Lemma lem5040925 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term592 A B u f t) = (term593 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5040924 A B u f t x)). Qed.
Lemma lem5040926 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5040927 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term589 A B u f t) = (term594 A B u f t).
Proof. exact (MK_COMB (@lem5040926 B) (@lem5040925 A B u f t)). Qed.
Lemma lem5040928 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term588 A B u f t) = (term594 A B u f t).
Proof. exact (TRANS (@lem5040920 A B u f t) (@lem5040927 A B u f t)). Qed.
Lemma lem5040929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5040930 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term595 A B t f u) = (term596 A B t f u).
Proof. exact (MK_COMB (@lem5040929) (@lem5040870 A B t f u)). Qed.
Lemma lem5040931 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term597 A B u f t) = (term598 A B u f t).
Proof. exact (MK_COMB (@lem5040930 A B t f u) (@lem5040928 A B u f t)). Qed.
Lemma lem5040932 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term504 A B u f t) = (term597 A B u f t).
Proof. exact (@lem17045 (term465 A B t f u) (term478 A B u f t)). Qed.
Lemma lem5040933 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term504 A B u f t) = (term598 A B u f t).
Proof. exact (TRANS (@lem5040932 A B u f t) (@lem5040931 A B u f t)). Qed.
Lemma lem5040983 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term599 A P Q) = (term600 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5040984 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term599 B P Q) = (term600 B P Q).
Proof. exact (@lem5040983 B P Q). Qed.
Lemma lem5040985 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term601 A B u f t) = (term602 A B u f t).
Proof. exact (@lem5040984 B (term603 A B u f t) (term604 A B u f t)). Qed.
Lemma lem5040986 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term605 A B u f t x) = (term583 A B u f t x).
Proof. exact (eq_refl (term605 A B u f t x)). Qed.
Lemma lem5040987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5040988 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term606 A B u f t x) = (term584 A B u f t x).
Proof. exact (MK_COMB (@lem5040987) (@lem5040986 A B u f t x)). Qed.
Lemma lem5040989 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term607 A B u f t x) = (term581 A B u f t x).
Proof. exact (eq_refl (term607 A B u f t x)). Qed.
Lemma lem5040990 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term608 A B u f t x) = (term586 A B u f t x).
Proof. exact (MK_COMB (@lem5040988 A B u f t x) (@lem5040989 A B u f t x)). Qed.
Lemma lem5040991 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term609 A B u f t) = (term593 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5040990 A B u f t x)). Qed.
Lemma lem5040992 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5040993 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term601 A B u f t) = (term594 A B u f t).
Proof. exact (MK_COMB (@lem5040992 B) (@lem5040991 A B u f t)). Qed.
Lemma lem5040994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5040995 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term610 A B u f t) = (term611 A B u f t).
Proof. exact (MK_COMB (@lem5040994) (@lem5040993 A B u f t)). Qed.
Lemma lem5040996 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term605 A B u f t x) = (term583 A B u f t x).
Proof. exact (eq_refl (term605 A B u f t x)). Qed.
Lemma lem5040997 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term612 A B u f t) = (term603 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5040996 A B u f t x)). Qed.
Lemma lem5040998 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5040999 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term613 A B u f t) = (term614 A B u f t).
Proof. exact (MK_COMB (@lem5040998 B) (@lem5040997 A B u f t)). Qed.
Lemma lem5041000 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5041001 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term615 A B u f t) = (term616 A B u f t).
Proof. exact (MK_COMB (@lem5041000) (@lem5040999 A B u f t)). Qed.
Lemma lem5041002 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term607 A B u f t x) = (term581 A B u f t x).
Proof. exact (eq_refl (term607 A B u f t x)). Qed.
Lemma lem5041003 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term617 A B u f t) = (term604 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5041002 A B u f t x)). Qed.
Lemma lem5041004 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041005 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term618 A B u f t) = (term619 A B u f t).
Proof. exact (MK_COMB (@lem5041004 B) (@lem5041003 A B u f t)). Qed.
Lemma lem5041006 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term602 A B u f t) = (term620 A B u f t).
Proof. exact (MK_COMB (@lem5041001 A B u f t) (@lem5041005 A B u f t)). Qed.
Lemma lem5041007 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term601 A B u f t) = (term602 A B u f t)) = ((term594 A B u f t) = (term620 A B u f t)).
Proof. exact (MK_COMB (@lem5040995 A B u f t) (@lem5041006 A B u f t)). Qed.
Lemma lem5041008 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term594 A B u f t) = (term620 A B u f t).
Proof. exact (EQ_MP (@lem5041007 A B u f t) (@lem5040985 A B u f t)). Qed.
Lemma lem5041185 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term596 A B t f u) = (term596 A B t f u).
Proof. exact (eq_refl (term596 A B t f u)). Qed.
Lemma lem5041186 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term598 A B u f t) = (term621 A B u f t).
Proof. exact (MK_COMB (@lem5041185 A B t f u) (@lem5041008 A B u f t)). Qed.
Lemma lem5041188 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5041189 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem5041188 A P Q). Qed.
Lemma lem5041190 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term622 A B u f t x) = (term623 A B u f t x).
Proof. exact (@lem5041189 A (term472 A B x u t f) (term349 B t x)). Qed.
Lemma lem5041191 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term573 A B x u t f x') = (term470 A B x u t f x').
Proof. exact (eq_refl (term573 A B x u t f x')). Qed.
Lemma lem5041192 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term624 A B x u t f) = (term472 A B x u t f).
Proof. exact (fun_ext (fun x' : A => @lem5041191 A B x u t f x')). Qed.
Lemma lem5041193 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041194 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term625 A B x u t f) = (term473 A B x u t f).
Proof. exact (MK_COMB (@lem5041193 A) (@lem5041192 A B x u t f)). Qed.
Lemma lem5041195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5041196 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term626 A B x u t f) = (term582 A B x u t f).
Proof. exact (MK_COMB (@lem5041195) (@lem5041194 A B x u t f)). Qed.
Lemma lem5041197 {B : Type'} (t : B -> Prop) (x : B) : (term349 B t x) = (term349 B t x).
Proof. exact (eq_refl (term349 B t x)). Qed.
Lemma lem5041198 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term622 A B u f t x) = (term583 A B u f t x).
Proof. exact (MK_COMB (@lem5041196 A B x u t f) (@lem5041197 B t x)). Qed.
Lemma lem5041199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5041200 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term627 A B u f t x) = (term628 A B u f t x).
Proof. exact (MK_COMB (@lem5041199) (@lem5041198 A B u f t x)). Qed.
Lemma lem5041201 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term573 A B x u t f x') = (term470 A B x u t f x').
Proof. exact (eq_refl (term573 A B x u t f x')). Qed.
Lemma lem5041202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5041203 {A B : Type'} (x : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x' : A) : (term629 A B x u t f x') = (term630 A B x u t f x').
Proof. exact (MK_COMB (@lem5041202) (@lem5041201 A B x u t f x')). Qed.
Lemma lem5041204 {B : Type'} (t : B -> Prop) (x : B) : (term349 B t x) = (term349 B t x).
Proof. exact (eq_refl (term349 B t x)). Qed.
Lemma lem5041205 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) (x' : B) : (term631 A B u f x t x') = (term632 A B u f x t x').
Proof. exact (MK_COMB (@lem5041203 A B x' u t f x) (@lem5041204 B t x')). Qed.
Lemma lem5041206 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term633 A B u f t x) = (term634 A B u f t x).
Proof. exact (fun_ext (fun x' : A => @lem5041205 A B u f x' t x)). Qed.
Lemma lem5041207 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041208 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term623 A B u f t x) = (term635 A B u f t x).
Proof. exact (MK_COMB (@lem5041207 A) (@lem5041206 A B u f t x)). Qed.
Lemma lem5041209 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : ((term622 A B u f t x) = (term623 A B u f t x)) = ((term583 A B u f t x) = (term635 A B u f t x)).
Proof. exact (MK_COMB (@lem5041200 A B u f t x) (@lem5041208 A B u f t x)). Qed.
Lemma lem5041210 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term583 A B u f t x) = (term635 A B u f t x).
Proof. exact (EQ_MP (@lem5041209 A B u f t x) (@lem5041190 A B u f t x)). Qed.
Lemma lem5041211 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term603 A B u f t) = (term636 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5041210 A B u f t x)). Qed.
Lemma lem5041212 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041213 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term614 A B u f t) = (term637 A B u f t).
Proof. exact (MK_COMB (@lem5041212 B) (@lem5041211 A B u f t)). Qed.
Lemma lem5041214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5041215 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term616 A B u f t) = (term638 A B u f t).
Proof. exact (MK_COMB (@lem5041214) (@lem5041213 A B u f t)). Qed.
Lemma lem5041216 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term619 A B u f t) = (term619 A B u f t).
Proof. exact (eq_refl (term619 A B u f t)). Qed.
Lemma lem5041217 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term620 A B u f t) = (term639 A B u f t).
Proof. exact (MK_COMB (@lem5041215 A B u f t) (@lem5041216 A B u f t)). Qed.
Lemma lem5041219 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term600 A P Q) = (term599 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5041220 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term600 B P Q) = (term599 B P Q).
Proof. exact (@lem5041219 B P Q). Qed.
Lemma lem5041221 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term640 A B u f t) = (term641 A B u f t).
Proof. exact (@lem5041220 B (term636 A B u f t) (term604 A B u f t)). Qed.
Lemma lem5041222 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term642 A B u f t x) = (term635 A B u f t x).
Proof. exact (eq_refl (term642 A B u f t x)). Qed.
Lemma lem5041223 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term643 A B u f t) = (term636 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5041222 A B u f t x)). Qed.
Lemma lem5041224 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041225 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term644 A B u f t) = (term637 A B u f t).
Proof. exact (MK_COMB (@lem5041224 B) (@lem5041223 A B u f t)). Qed.
Lemma lem5041226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5041227 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term645 A B u f t) = (term638 A B u f t).
Proof. exact (MK_COMB (@lem5041226) (@lem5041225 A B u f t)). Qed.
Lemma lem5041228 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term607 A B u f t x) = (term581 A B u f t x).
Proof. exact (eq_refl (term607 A B u f t x)). Qed.
Lemma lem5041229 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term617 A B u f t) = (term604 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5041228 A B u f t x)). Qed.
Lemma lem5041230 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041231 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term618 A B u f t) = (term619 A B u f t).
Proof. exact (MK_COMB (@lem5041230 B) (@lem5041229 A B u f t)). Qed.
Lemma lem5041232 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term640 A B u f t) = (term639 A B u f t).
Proof. exact (MK_COMB (@lem5041227 A B u f t) (@lem5041231 A B u f t)). Qed.
Lemma lem5041233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5041234 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term646 A B u f t) = (term647 A B u f t).
Proof. exact (MK_COMB (@lem5041233) (@lem5041232 A B u f t)). Qed.
Lemma lem5041235 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term642 A B u f t x) = (term635 A B u f t x).
Proof. exact (eq_refl (term642 A B u f t x)). Qed.
Lemma lem5041236 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5041237 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term648 A B u f t x) = (term649 A B u f t x).
Proof. exact (MK_COMB (@lem5041236) (@lem5041235 A B u f t x)). Qed.
Lemma lem5041238 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term607 A B u f t x) = (term581 A B u f t x).
Proof. exact (eq_refl (term607 A B u f t x)). Qed.
Lemma lem5041239 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term650 A B u f t x) = (term651 A B u f t x).
Proof. exact (MK_COMB (@lem5041237 A B u f t x) (@lem5041238 A B u f t x)). Qed.
Lemma lem5041240 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term652 A B u f t) = (term653 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5041239 A B u f t x)). Qed.
Lemma lem5041241 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041242 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term641 A B u f t) = (term654 A B u f t).
Proof. exact (MK_COMB (@lem5041241 B) (@lem5041240 A B u f t)). Qed.
Lemma lem5041243 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term640 A B u f t) = (term641 A B u f t)) = ((term639 A B u f t) = (term654 A B u f t)).
Proof. exact (MK_COMB (@lem5041234 A B u f t) (@lem5041242 A B u f t)). Qed.
Lemma lem5041244 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term639 A B u f t) = (term654 A B u f t).
Proof. exact (EQ_MP (@lem5041243 A B u f t) (@lem5041221 A B u f t)). Qed.
Lemma lem5041246 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5041247 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (@lem5041246 A P Q). Qed.
Lemma lem5041248 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term655 A B u f t x) = (term656 A B u f t x).
Proof. exact (@lem5041247 A (term634 A B u f t x) (term581 A B u f t x)). Qed.
Lemma lem5041249 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) (x' : B) : (term657 A B u f t x' x) = (term632 A B u f x t x').
Proof. exact (eq_refl (term657 A B u f t x' x)). Qed.
Lemma lem5041250 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term658 A B u f t x) = (term634 A B u f t x).
Proof. exact (fun_ext (fun x' : A => @lem5041249 A B u f x' t x)). Qed.
Lemma lem5041251 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041252 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term659 A B u f t x) = (term635 A B u f t x).
Proof. exact (MK_COMB (@lem5041251 A) (@lem5041250 A B u f t x)). Qed.
Lemma lem5041253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5041254 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term660 A B u f t x) = (term649 A B u f t x).
Proof. exact (MK_COMB (@lem5041253) (@lem5041252 A B u f t x)). Qed.
Lemma lem5041255 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term581 A B u f t x) = (term581 A B u f t x).
Proof. exact (eq_refl (term581 A B u f t x)). Qed.
Lemma lem5041256 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term655 A B u f t x) = (term651 A B u f t x).
Proof. exact (MK_COMB (@lem5041254 A B u f t x) (@lem5041255 A B u f t x)). Qed.
Lemma lem5041257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5041258 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term661 A B u f t x) = (term662 A B u f t x).
Proof. exact (MK_COMB (@lem5041257) (@lem5041256 A B u f t x)). Qed.
Lemma lem5041259 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) (x' : B) : (term657 A B u f t x' x) = (term632 A B u f x t x').
Proof. exact (eq_refl (term657 A B u f t x' x)). Qed.
Lemma lem5041260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5041261 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) (x' : B) : (term663 A B u f t x' x) = (term664 A B u f x t x').
Proof. exact (MK_COMB (@lem5041260) (@lem5041259 A B u f x t x')). Qed.
Lemma lem5041262 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term581 A B u f t x) = (term581 A B u f t x).
Proof. exact (eq_refl (term581 A B u f t x)). Qed.
Lemma lem5041263 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term665 A B x u f t x') = (term666 A B x u f t x').
Proof. exact (MK_COMB (@lem5041261 A B u f x t x') (@lem5041262 A B u f t x')). Qed.
Lemma lem5041264 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term667 A B u f t x) = (term668 A B u f t x).
Proof. exact (fun_ext (fun x' : A => @lem5041263 A B x' u f t x)). Qed.
Lemma lem5041265 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041266 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term656 A B u f t x) = (term669 A B u f t x).
Proof. exact (MK_COMB (@lem5041265 A) (@lem5041264 A B u f t x)). Qed.
Lemma lem5041267 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : ((term655 A B u f t x) = (term656 A B u f t x)) = ((term651 A B u f t x) = (term669 A B u f t x)).
Proof. exact (MK_COMB (@lem5041258 A B u f t x) (@lem5041266 A B u f t x)). Qed.
Lemma lem5041268 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term651 A B u f t x) = (term669 A B u f t x).
Proof. exact (EQ_MP (@lem5041267 A B u f t x) (@lem5041248 A B u f t x)). Qed.
Lemma lem5041269 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term653 A B u f t) = (term670 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5041268 A B u f t x)). Qed.
Lemma lem5041270 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041271 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term654 A B u f t) = (term671 A B u f t).
Proof. exact (MK_COMB (@lem5041270 B) (@lem5041269 A B u f t)). Qed.
Lemma lem5041272 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term639 A B u f t) = (term671 A B u f t).
Proof. exact (TRANS (@lem5041244 A B u f t) (@lem5041271 A B u f t)). Qed.
Lemma lem5041273 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term620 A B u f t) = (term671 A B u f t).
Proof. exact (TRANS (@lem5041217 A B u f t) (@lem5041272 A B u f t)). Qed.
Lemma lem5041274 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term596 A B t f u) = (term596 A B t f u).
Proof. exact (eq_refl (term596 A B t f u)). Qed.
Lemma lem5041275 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term621 A B u f t) = (term672 A B u f t).
Proof. exact (MK_COMB (@lem5041274 A B t f u) (@lem5041273 A B u f t)). Qed.
Lemma lem5041279 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5041280 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (@lem5041279 A P Q). Qed.
Lemma lem5041281 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term673 A B u f t) = (term674 A B u f t).
Proof. exact (@lem5041280 A (term563 A B t f u) (term671 A B u f t)). Qed.
Lemma lem5041282 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term675 A B t f u x) = (term557 A B t f u x).
Proof. exact (eq_refl (term675 A B t f u x)). Qed.
Lemma lem5041283 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term676 A B t f u) = (term563 A B t f u).
Proof. exact (fun_ext (fun x : A => @lem5041282 A B t f u x)). Qed.
Lemma lem5041284 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041285 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term677 A B t f u) = (term564 A B t f u).
Proof. exact (MK_COMB (@lem5041284 A) (@lem5041283 A B t f u)). Qed.
Lemma lem5041286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5041287 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) : (term678 A B t f u) = (term596 A B t f u).
Proof. exact (MK_COMB (@lem5041286) (@lem5041285 A B t f u)). Qed.
Lemma lem5041288 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term671 A B u f t) = (term671 A B u f t).
Proof. exact (eq_refl (term671 A B u f t)). Qed.
Lemma lem5041289 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term673 A B u f t) = (term672 A B u f t).
Proof. exact (MK_COMB (@lem5041287 A B t f u) (@lem5041288 A B u f t)). Qed.
Lemma lem5041290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5041291 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term679 A B u f t) = (term680 A B u f t).
Proof. exact (MK_COMB (@lem5041290) (@lem5041289 A B u f t)). Qed.
Lemma lem5041292 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term675 A B t f u x) = (term557 A B t f u x).
Proof. exact (eq_refl (term675 A B t f u x)). Qed.
Lemma lem5041293 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5041294 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term681 A B t f u x) = (term682 A B t f u x).
Proof. exact (MK_COMB (@lem5041293) (@lem5041292 A B t f u x)). Qed.
Lemma lem5041295 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term671 A B u f t) = (term671 A B u f t).
Proof. exact (eq_refl (term671 A B u f t)). Qed.
Lemma lem5041296 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term683 A B x u f t) = (term684 A B x u f t).
Proof. exact (MK_COMB (@lem5041294 A B t f u x) (@lem5041295 A B u f t)). Qed.
Lemma lem5041297 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term685 A B u f t) = (term686 A B u f t).
Proof. exact (fun_ext (fun x : A => @lem5041296 A B x u f t)). Qed.
Lemma lem5041298 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041299 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term674 A B u f t) = (term687 A B u f t).
Proof. exact (MK_COMB (@lem5041298 A) (@lem5041297 A B u f t)). Qed.
Lemma lem5041300 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term673 A B u f t) = (term674 A B u f t)) = ((term672 A B u f t) = (term687 A B u f t)).
Proof. exact (MK_COMB (@lem5041291 A B u f t) (@lem5041299 A B u f t)). Qed.
Lemma lem5041301 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term672 A B u f t) = (term687 A B u f t).
Proof. exact (EQ_MP (@lem5041300 A B u f t) (@lem5041281 A B u f t)). Qed.
Lemma lem5041303 {A : Type'} (P : Prop) (Q : A -> Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5041304 {B : Type'} (P : Prop) (Q : B -> Prop) : (term278 B P Q) = (term279 B P Q).
Proof. exact (@lem5041303 B P Q). Qed.
Lemma lem5041305 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term688 A B x u f t) = (term689 A B x u f t).
Proof. exact (@lem5041304 B (term557 A B t f u x) (term670 A B u f t)). Qed.
Lemma lem5041306 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term690 A B u f t x) = (term669 A B u f t x).
Proof. exact (eq_refl (term690 A B u f t x)). Qed.
Lemma lem5041307 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term691 A B u f t) = (term670 A B u f t).
Proof. exact (fun_ext (fun x : B => @lem5041306 A B u f t x)). Qed.
Lemma lem5041308 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041309 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term692 A B u f t) = (term671 A B u f t).
Proof. exact (MK_COMB (@lem5041308 B) (@lem5041307 A B u f t)). Qed.
Lemma lem5041310 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term682 A B t f u x) = (term682 A B t f u x).
Proof. exact (eq_refl (term682 A B t f u x)). Qed.
Lemma lem5041311 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term688 A B x u f t) = (term684 A B x u f t).
Proof. exact (MK_COMB (@lem5041310 A B t f u x) (@lem5041309 A B u f t)). Qed.
Lemma lem5041312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5041313 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term693 A B x u f t) = (term694 A B x u f t).
Proof. exact (MK_COMB (@lem5041312) (@lem5041311 A B x u f t)). Qed.
Lemma lem5041314 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term690 A B u f t x) = (term669 A B u f t x).
Proof. exact (eq_refl (term690 A B u f t x)). Qed.
Lemma lem5041315 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term682 A B t f u x) = (term682 A B t f u x).
Proof. exact (eq_refl (term682 A B t f u x)). Qed.
Lemma lem5041316 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term695 A B x u f t x') = (term696 A B x u f t x').
Proof. exact (MK_COMB (@lem5041315 A B t f u x) (@lem5041314 A B u f t x')). Qed.
Lemma lem5041317 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term697 A B x u f t) = (term698 A B x u f t).
Proof. exact (fun_ext (fun x' : B => @lem5041316 A B x u f t x')). Qed.
Lemma lem5041318 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041319 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term689 A B x u f t) = (term699 A B x u f t).
Proof. exact (MK_COMB (@lem5041318 B) (@lem5041317 A B x u f t)). Qed.
Lemma lem5041320 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term688 A B x u f t) = (term689 A B x u f t)) = ((term684 A B x u f t) = (term699 A B x u f t)).
Proof. exact (MK_COMB (@lem5041313 A B x u f t) (@lem5041319 A B x u f t)). Qed.
Lemma lem5041321 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term684 A B x u f t) = (term699 A B x u f t).
Proof. exact (EQ_MP (@lem5041320 A B x u f t) (@lem5041305 A B x u f t)). Qed.
Lemma lem5041323 {A : Type'} (P : Prop) (Q : A -> Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5041324 {A : Type'} (P : Prop) (Q : A -> Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (@lem5041323 A P Q). Qed.
Lemma lem5041325 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term700 A B x u f t x') = (term701 A B x u f t x').
Proof. exact (@lem5041324 A (term557 A B t f u x) (term668 A B u f t x')). Qed.
Lemma lem5041326 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term702 A B u f t x' x) = (term666 A B x u f t x').
Proof. exact (eq_refl (term702 A B u f t x' x)). Qed.
Lemma lem5041327 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term703 A B u f t x) = (term668 A B u f t x).
Proof. exact (fun_ext (fun x' : A => @lem5041326 A B x' u f t x)). Qed.
Lemma lem5041328 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041329 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term704 A B u f t x) = (term669 A B u f t x).
Proof. exact (MK_COMB (@lem5041328 A) (@lem5041327 A B u f t x)). Qed.
Lemma lem5041330 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term682 A B t f u x) = (term682 A B t f u x).
Proof. exact (eq_refl (term682 A B t f u x)). Qed.
Lemma lem5041331 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term700 A B x u f t x') = (term696 A B x u f t x').
Proof. exact (MK_COMB (@lem5041330 A B t f u x) (@lem5041329 A B u f t x')). Qed.
Lemma lem5041332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5041333 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term705 A B x u f t x') = (term706 A B x u f t x').
Proof. exact (MK_COMB (@lem5041332) (@lem5041331 A B x u f t x')). Qed.
Lemma lem5041334 {A B : Type'} (x' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x : B) : (term702 A B u f t x x') = (term666 A B x' u f t x).
Proof. exact (eq_refl (term702 A B u f t x x')). Qed.
Lemma lem5041335 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term682 A B t f u x) = (term682 A B t f u x).
Proof. exact (eq_refl (term682 A B t f u x)). Qed.
Lemma lem5041336 {A B : Type'} (x : A) (x' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x'' : B) : (term707 A B x u f t x'' x') = (term708 A B x x' u f t x'').
Proof. exact (MK_COMB (@lem5041335 A B t f u x) (@lem5041334 A B x' u f t x'')). Qed.
Lemma lem5041337 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term709 A B x u f t x') = (term710 A B x u f t x').
Proof. exact (fun_ext (fun x'' : A => @lem5041336 A B x x'' u f t x')). Qed.
Lemma lem5041338 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041339 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term701 A B x u f t x') = (term711 A B x u f t x').
Proof. exact (MK_COMB (@lem5041338 A) (@lem5041337 A B x u f t x')). Qed.
Lemma lem5041340 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : ((term700 A B x u f t x') = (term701 A B x u f t x')) = ((term696 A B x u f t x') = (term711 A B x u f t x')).
Proof. exact (MK_COMB (@lem5041333 A B x u f t x') (@lem5041339 A B x u f t x')). Qed.
Lemma lem5041341 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term696 A B x u f t x') = (term711 A B x u f t x').
Proof. exact (EQ_MP (@lem5041340 A B x u f t x') (@lem5041325 A B x u f t x')). Qed.
Lemma lem5041342 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term698 A B x u f t) = (term712 A B x u f t).
Proof. exact (fun_ext (fun x' : B => @lem5041341 A B x u f t x')). Qed.
Lemma lem5041343 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5041344 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term699 A B x u f t) = (term713 A B x u f t).
Proof. exact (MK_COMB (@lem5041343 B) (@lem5041342 A B x u f t)). Qed.
Lemma lem5041345 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term684 A B x u f t) = (term713 A B x u f t).
Proof. exact (TRANS (@lem5041321 A B x u f t) (@lem5041344 A B x u f t)). Qed.
Lemma lem5041346 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term686 A B u f t) = (term714 A B u f t).
Proof. exact (fun_ext (fun x : A => @lem5041345 A B x u f t)). Qed.
Lemma lem5041347 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5041348 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term687 A B u f t) = (term715 A B u f t).
Proof. exact (MK_COMB (@lem5041347 A) (@lem5041346 A B u f t)). Qed.
Lemma lem5041349 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term672 A B u f t) = (term715 A B u f t).
Proof. exact (TRANS (@lem5041301 A B u f t) (@lem5041348 A B u f t)). Qed.
Lemma lem5041350 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term621 A B u f t) = (term715 A B u f t).
Proof. exact (TRANS (@lem5041275 A B u f t) (@lem5041349 A B u f t)). Qed.
Lemma lem5041351 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term598 A B u f t) = (term715 A B u f t).
Proof. exact (TRANS (@lem5041186 A B u f t) (@lem5041350 A B u f t)). Qed.
Lemma lem5041352 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term504 A B u f t) = (term715 A B u f t).
Proof. exact (TRANS (@lem5040933 A B u f t) (@lem5041351 A B u f t)). Qed.
Lemma lem5041353 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term504 A B u f t) : term715 A B u f t.
Proof. exact (EQ_MP (@lem5041352 A B u f t) (@lem5040630 A B u f t h1)). Qed.
Lemma lem5041354 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term713 A B x u f t) : term713 A B x u f t.
Proof. exact (h1). Qed.
Lemma lem5041355 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term711 A B x u f t x') : term711 A B x u f t x'.
Proof. exact (h1). Qed.
Lemma lem5041356 {A B : Type'} (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term708 A B x x'' u f t x') : term708 A B x x'' u f t x'.
Proof. exact (h1). Qed.
Lemma lem5041357 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term552 A B t v u f x'''.
Proof. exact (h1). Qed.
Lemma lem5041360 {B : Type'} (t : B -> Prop) (x' : B) : (t x') = (t x').
Proof. exact (eq_refl (t x')). Qed.
Lemma lem5041387 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term569 A B x' u t f x) = (term569 A B x' u t f x).
Proof. exact (eq_refl (term569 A B x' u t f x)). Qed.
Lemma lem5041388 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term576 A B x' u t f) = (term576 A B x' u t f).
Proof. exact (fun_ext (fun x : A => @lem5041387 A B x' u t f x)). Qed.
Lemma lem5041389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5041390 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term577 A B x' u t f) = (term577 A B x' u t f).
Proof. exact (MK_COMB (@lem5041389 A) (@lem5041388 A B x' u t f)). Qed.
Lemma lem5041391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5041392 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term579 A B x' u t f) = (term579 A B x' u t f).
Proof. exact (MK_COMB (@lem5041391) (@lem5041390 A B x' u t f)). Qed.
Lemma lem5041393 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term581 A B u f t x') = (term581 A B u f t x').
Proof. exact (MK_COMB (@lem5041392 A B x' u t f) (@lem5041360 B t x')). Qed.
Lemma lem5041424 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) : (term664 A B u f x'' t x') = (term664 A B u f x'' t x').
Proof. exact (eq_refl (term664 A B u f x'' t x')). Qed.
Lemma lem5041425 {A B : Type'} (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term666 A B x'' u f t x') = (term666 A B x'' u f t x').
Proof. exact (MK_COMB (@lem5041424 A B u f x'' t x') (@lem5041393 A B u f t x')). Qed.
Lemma lem5041446 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) : (term682 A B t f u x) = (term682 A B t f u x).
Proof. exact (eq_refl (term682 A B t f u x)). Qed.
Lemma lem5041447 {A B : Type'} (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) : (term708 A B x x'' u f t x') = (term708 A B x x'' u f t x').
Proof. exact (MK_COMB (@lem5041446 A B t f u x) (@lem5041425 A B x'' u f t x')). Qed.
Lemma lem5041448 {A B : Type'} (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term708 A B x x'' u f t x') : term708 A B x x'' u f t x'.
Proof. exact (EQ_MP (@lem5041447 A B x x'' u f t x') (@lem5041356 A B x x'' u f t x' h1)). Qed.
Lemma lem5041473 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (y : B) : (term535 A B v u f x''' y) = (term535 A B v u f x''' y).
Proof. exact (eq_refl (term535 A B v u f x''' y)). Qed.
Lemma lem5041474 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) : (term537 A B v u f x''') = (term537 A B v u f x''').
Proof. exact (fun_ext (fun y : B => @lem5041473 A B v u f x''' y)). Qed.
Lemma lem5041475 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5041476 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) : (term539 A B v u f x''') = (term539 A B v u f x''').
Proof. exact (MK_COMB (@lem5041475 B) (@lem5041474 A B v u f x''')). Qed.
Lemma lem5041487 {B : Type'} (t : B -> Prop) (v : B -> Prop) (x : B) : (term119 B t v x) = (term119 B t v x).
Proof. exact (eq_refl (term119 B t v x)). Qed.
Lemma lem5041488 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term120 B t v) = (term120 B t v).
Proof. exact (fun_ext (fun x : B => @lem5041487 B t v x)). Qed.
Lemma lem5041489 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5041490 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term121 B t v) = (term121 B t v).
Proof. exact (MK_COMB (@lem5041489 B) (@lem5041488 B t v)). Qed.
Lemma lem5041491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5041492 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term145 B t v) = (term145 B t v).
Proof. exact (MK_COMB (@lem5041491) (@lem5041490 B t v)). Qed.
Lemma lem5041493 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) : (term552 A B t v u f x''') = (term552 A B t v u f x''').
Proof. exact (MK_COMB (@lem5041492 B t v) (@lem5041476 A B v u f x''')). Qed.
Lemma lem5041494 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term552 A B t v u f x'''.
Proof. exact (EQ_MP (@lem5041493 A B t v u f x''') (@lem5041357 A B t v u f x''' h1)). Qed.
Lemma lem5041495 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term539 A B v u f x'''.
Proof. exact (proj2 (@lem5041494 A B t v u f x''' h1)). Qed.
Lemma lem5041496 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term121 B t v.
Proof. exact (proj1 (@lem5041494 A B t v u f x''' h1)). Qed.
Lemma lem5041497 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : term557 A B t f u x.
Proof. exact (h1). Qed.
Lemma lem5041498 {A B : Type'} (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term666 A B x'' u f t x') : term666 A B x'' u f t x'.
Proof. exact (h1). Qed.
Lemma lem5041500 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : term458 A B u t f x.
Proof. exact (proj1 (@lem5041497 A B t f u x h1)). Qed.
Lemma lem5041503 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term632 A B u f x'' t x'.
Proof. exact (h1). Qed.
Lemma lem5041504 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term581 A B u f t x'.
Proof. exact (h1). Qed.
Lemma lem5041506 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term470 A B x' u t f x''.
Proof. exact (proj1 (@lem5041503 A B u f x'' t x' h1)). Qed.
Lemma lem5041507 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term458 A B u t f x''.
Proof. exact (proj2 (@lem5041506 A B u f x'' t x' h1)). Qed.
Lemma lem5041512 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term577 A B x' u t f.
Proof. exact (proj1 (@lem5041504 A B u f t x' h1)). Qed.
Lemma lem5041620 {B : Type'} (t : B -> Prop) (v : B -> Prop) (x : B) : (term119 B t v x) = (term119 B t v x).
Proof. exact (eq_refl (term119 B t v x)). Qed.
Lemma lem5041621 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term120 B t v) = (term120 B t v).
Proof. exact (fun_ext (fun x : B => @lem5041620 B t v x)). Qed.
Lemma lem5041622 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5041624 {B : Type'} (t : B -> Prop) (v : B -> Prop) : (term121 B t v) = (term121 B t v).
Proof. exact (MK_COMB (@lem5041622 B) (@lem5041621 B t v)). Qed.
Lemma lem5041625 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term121 B t v.
Proof. exact (EQ_MP (@lem5041624 B t v) (@lem5041496 A B t v u f x''' h1)). Qed.
Lemma lem5041643 {A B : Type'} (u : A -> Prop) (v : B -> Prop) (f : A -> B) (x''' : B -> A) (y : B) : (term535 A B v u f x''' y) = (term716 A B u v f x''' y).
Proof. exact (@lem19490 (term322 A B u x''' y) (term349 B v y) ((term321 A B f x''' y) = y)). Qed.
Lemma lem5041644 {A B : Type'} (u : A -> Prop) (v : B -> Prop) (f : A -> B) (x''' : B -> A) : (term537 A B v u f x''') = (term717 A B u v f x''').
Proof. exact (fun_ext (fun y : B => @lem5041643 A B u v f x''' y)). Qed.
Lemma lem5041645 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5041647 {A B : Type'} (u : A -> Prop) (v : B -> Prop) (f : A -> B) (x''' : B -> A) : (term539 A B v u f x''') = (term718 A B u v f x''').
Proof. exact (MK_COMB (@lem5041645 B) (@lem5041644 A B u v f x''')). Qed.
Lemma lem5041648 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term718 A B u v f x'''.
Proof. exact (EQ_MP (@lem5041647 A B u v f x''') (@lem5041495 A B t v u f x''' h1)). Qed.
Lemma lem5041662 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term569 A B x' u t f x) = (term569 A B x' u t f x).
Proof. exact (eq_refl (term569 A B x' u t f x)). Qed.
Lemma lem5041663 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term576 A B x' u t f) = (term576 A B x' u t f).
Proof. exact (fun_ext (fun x : A => @lem5041662 A B x' u t f x)). Qed.
Lemma lem5041664 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5041666 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) : (term577 A B x' u t f) = (term577 A B x' u t f).
Proof. exact (MK_COMB (@lem5041664 A) (@lem5041663 A B x' u t f)). Qed.
Lemma lem5041667 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term577 A B x' u t f.
Proof. exact (EQ_MP (@lem5041666 A B x' u t f) (@lem5041512 A B u f t x' h1)). Qed.
Lemma lem5041684 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term345 B t v _64768.
Proof. exact (@lem5041625 A B t v u f x''' h1 _64768). Qed.
Lemma lem5041685 {B : Type'} (t : B -> Prop) (v : B -> Prop) (_64768 : B) : (term345 B t v _64768) = (term119 B t v _64768).
Proof. exact (eq_refl (term345 B t v _64768)). Qed.
Lemma lem5041687 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term719 A B u v f x''' _64769.
Proof. exact (@lem5041648 A B t v u f x''' h1 _64769). Qed.
Lemma lem5041688 {A B : Type'} (u : A -> Prop) (v : B -> Prop) (f : A -> B) (x''' : B -> A) (_64769 : B) : (term719 A B u v f x''' _64769) = (term716 A B u v f x''' _64769).
Proof. exact (eq_refl (term719 A B u v f x''' _64769)). Qed.
Lemma lem5041689 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term716 A B u v f x''' _64769.
Proof. exact (EQ_MP (@lem5041688 A B u v f x''' _64769) (@lem5041687 A B _64769 t v u f x''' h1)). Qed.
Lemma lem5041690 {A B : Type'} (_64770 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term720 A B x' u t f _64770.
Proof. exact (@lem5041667 A B u f t x' h1 _64770). Qed.
Lemma lem5041691 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (_64770 : A) : (term720 A B x' u t f _64770) = (term569 A B x' u t f _64770).
Proof. exact (eq_refl (term720 A B x' u t f _64770)). Qed.
Lemma lem5041706 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : term349 A u x.
Proof. exact (proj2 (@lem5041497 A B t f u x h1)). Qed.
Lemma lem5041730 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term349 B t x'.
Proof. exact (proj2 (@lem5041503 A B u f x'' t x' h1)). Qed.
Lemma lem5041732 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : x' = (f x'').
Proof. exact (proj1 (@lem5041506 A B u f x'' t x' h1)). Qed.
Lemma lem5041754 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term119 B t v _64768.
Proof. exact (EQ_MP (@lem5041685 B t v _64768) (@lem5041684 A B _64768 t v u f x''' h1)). Qed.
Lemma lem5041764 {A B : Type'} (_64770 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term569 A B x' u t f _64770.
Proof. exact (EQ_MP (@lem5041691 A B x' u t f _64770) (@lem5041690 A B _64770 u f t x' h1)). Qed.
Lemma lem5041772 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term721 A B v u x''' _64769.
Proof. exact (proj1 (@lem5041689 A B _64769 t v u f x''' h1)). Qed.
Lemma lem5041778 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term722 A B v f x''' _64769.
Proof. exact (proj2 (@lem5041689 A B _64769 t v u f x''' h1)). Qed.
Lemma lem5041807 {B : Type'} (t : B -> Prop) : (term353 B t) = (term353 B t).
Proof. exact (eq_refl (term353 B t)). Qed.
Lemma lem5041808 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : (term354 B t x') = (term723 A B t f x'').
Proof. exact (MK_COMB (@lem5041807 B t) (@lem5041732 A B u f x'' t x' h1)). Qed.
Lemma lem5041809 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : A) : (term723 A B t f x'') = (term724 A B t f x'').
Proof. exact (eq_refl (term723 A B t f x'')). Qed.
Lemma lem5041810 {B : Type'} (t : B -> Prop) (x' : B) : (term355 B t x') = (term355 B t x').
Proof. exact (eq_refl (term355 B t x')). Qed.
Lemma lem5041811 {A B : Type'} (x' : B) (t : B -> Prop) (f : A -> B) (x'' : A) : ((term354 B t x') = (term723 A B t f x'')) = ((term354 B t x') = (term724 A B t f x'')).
Proof. exact (MK_COMB (@lem5041810 B t x') (@lem5041809 A B t f x'')). Qed.
Lemma lem5041812 {B : Type'} (t : B -> Prop) (x' : B) : (term354 B t x') = (term349 B t x').
Proof. exact (eq_refl (term354 B t x')). Qed.
Lemma lem5041813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5041814 {B : Type'} (t : B -> Prop) (x' : B) : (term355 B t x') = (term356 B t x').
Proof. exact (MK_COMB (@lem5041813) (@lem5041812 B t x')). Qed.
Lemma lem5041815 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : A) : (term724 A B t f x'') = (term724 A B t f x'').
Proof. exact (eq_refl (term724 A B t f x'')). Qed.
Lemma lem5041816 {A B : Type'} (x' : B) (t : B -> Prop) (f : A -> B) (x'' : A) : ((term354 B t x') = (term724 A B t f x'')) = ((term349 B t x') = (term724 A B t f x'')).
Proof. exact (MK_COMB (@lem5041814 B t x') (@lem5041815 A B t f x'')). Qed.
Lemma lem5041817 {A B : Type'} (x' : B) (t : B -> Prop) (f : A -> B) (x'' : A) : ((term354 B t x') = (term723 A B t f x'')) = ((term349 B t x') = (term724 A B t f x'')).
Proof. exact (TRANS (@lem5041811 A B x' t f x'') (@lem5041816 A B x' t f x'')). Qed.
Lemma lem5041818 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : (term349 B t x') = (term724 A B t f x'').
Proof. exact (EQ_MP (@lem5041817 A B x' t f x'') (@lem5041808 A B u f x'' t x' h1)). Qed.
Lemma lem5041819 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term724 A B t f x''.
Proof. exact (EQ_MP (@lem5041818 A B u f x'' t x' h1) (@lem5041730 A B u f x'' t x' h1)). Qed.
Lemma lem5041933 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : u x.
Proof. exact (proj1 (@lem5041500 A B t f u x h1)). Qed.
Lemma lem5041934 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : term357 A u x.
Proof. exact (fun h0 : term349 A u x => @lem5041933 A B t f u x h1). Qed.
Lemma lem5041936 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5041937 {A : Type'} (u : A -> Prop) (x : A) : (term357 A u x) = (u x).
Proof. exact (@lem5041936 (u x)). Qed.
Lemma lem5041938 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : u x.
Proof. exact (EQ_MP (@lem5041937 A u x) (@lem5041934 A B t f u x h1)). Qed.
Lemma lem5041941 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5041943 {A : Type'} (u : A -> Prop) (x : A) : (term349 A u x) = (term359 A u x).
Proof. exact (@lem5041941 (u x)). Qed.
Lemma lem5041946 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : term359 A u x.
Proof. exact (EQ_MP (@lem5041943 A u x) (@lem5041706 A B t f u x h1)). Qed.
Lemma lem5041949 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : False.
Proof. exact (@lem5041946 A B t f u x h1 (@lem5041938 A B t f u x h1)). Qed.
Lemma lem5041950 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : term360.
Proof. exact (fun h0 : ~ False => @lem5041949 A B t f u x h1). Qed.
Lemma lem5041952 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5041953 : term360 = False.
Proof. exact (@lem5041952 False). Qed.
Lemma lem5041954 {A B : Type'} (t : B -> Prop) (f : A -> B) (u : A -> Prop) (x : A) (h1 : term557 A B t f u x) : False.
Proof. exact (EQ_MP (@lem5041953) (@lem5041950 A B t f u x h1)). Qed.
Lemma lem5042012 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term457 A B t f x''.
Proof. exact (proj2 (@lem5041507 A B u f x'' t x' h1)). Qed.
Lemma lem5042013 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term725 A B t f x''.
Proof. exact (fun h0 : term724 A B t f x'' => @lem5042012 A B u f x'' t x' h1). Qed.
Lemma lem5042015 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042016 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : A) : (term725 A B t f x'') = (term457 A B t f x'').
Proof. exact (@lem5042015 (term457 A B t f x'')). Qed.
Lemma lem5042017 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term457 A B t f x''.
Proof. exact (EQ_MP (@lem5042016 A B t f x'') (@lem5042013 A B u f x'' t x' h1)). Qed.
Lemma lem5042020 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5042022 {A B : Type'} (t : B -> Prop) (f : A -> B) (x'' : A) : (term724 A B t f x'') = (term726 A B t f x'').
Proof. exact (@lem5042020 (term457 A B t f x'')). Qed.
Lemma lem5042025 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term726 A B t f x''.
Proof. exact (EQ_MP (@lem5042022 A B t f x'') (@lem5041819 A B u f x'' t x' h1)). Qed.
Lemma lem5042028 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : False.
Proof. exact (@lem5042025 A B u f x'' t x' h1 (@lem5042017 A B u f x'' t x' h1)). Qed.
Lemma lem5042029 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : term360.
Proof. exact (fun h0 : ~ False => @lem5042028 A B u f x'' t x' h1). Qed.
Lemma lem5042031 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042032 : term360 = False.
Proof. exact (@lem5042031 False). Qed.
Lemma lem5042046 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5042047 {B : Type'} (_64807 : B) (_64808 : B) (h1 : _64807 = _64808) : _64807 = _64808.
Proof. exact (h1). Qed.
Lemma lem5042048 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) (h1 : _64807 = _64808) : (t _64807) = (t _64808).
Proof. exact (MK_COMB (@lem5042046 B t) (@lem5042047 B _64807 _64808 h1)). Qed.
Lemma lem5042050 (b : Prop) (a : Prop) : term727 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5042051 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : term728 B _64808 t _64807.
Proof. exact (@lem5042050 (t _64808) (t _64807)). Qed.
Lemma lem5042052 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) (h1 : _64807 = _64808) : term729 B _64808 t _64807.
Proof. exact (@lem5042051 B _64808 t _64807 (@lem5042048 B t _64807 _64808 h1)). Qed.
Lemma lem5042053 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : term730 B _64808 t _64807.
Proof. exact (fun h0 : _64807 = _64808 => @lem5042052 B t _64807 _64808 h0). Qed.
Lemma lem5042055 (a : Prop) (b : Prop) : (a -> b) = (term731 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5042056 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : (term730 B _64808 t _64807) = (term732 B _64808 t _64807).
Proof. exact (@lem5042055 (_64807 = _64808) (term729 B _64808 t _64807)). Qed.
Lemma lem5042057 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : term732 B _64808 t _64807.
Proof. exact (EQ_MP (@lem5042056 B _64808 t _64807) (@lem5042053 B _64808 t _64807)). Qed.
Lemma lem5042087 {B : Type'} (x : B) (y : B) (z : B) : term733 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5042091 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : t x'.
Proof. exact (proj2 (@lem5041504 A B u f t x' h1)). Qed.
Lemma lem5042092 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term357 B t x'.
Proof. exact (fun h0 : term349 B t x' => @lem5042091 A B u f t x' h1). Qed.
Lemma lem5042094 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042095 {B : Type'} (t : B -> Prop) (x' : B) : (term357 B t x') = (t x').
Proof. exact (@lem5042094 (t x')). Qed.
Lemma lem5042096 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : t x'.
Proof. exact (EQ_MP (@lem5042095 B t x') (@lem5042092 A B u f t x' h1)). Qed.
Lemma lem5042102 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5042103 {B : Type'} (v : B -> Prop) (t : B -> Prop) (_64768 : B) : (term119 B t v _64768) = (term371 B v t _64768).
Proof. exact (@lem5042102 (v _64768) (term349 B t _64768)). Qed.
Lemma lem5042109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5042110 {B : Type'} (v : B -> Prop) (t : B -> Prop) (_64768 : B) : (term372 B t v _64768) = (term373 B v t _64768).
Proof. exact (MK_COMB (@lem5042109) (@lem5042103 B v t _64768)). Qed.
Lemma lem5042116 {B : Type'} (v : B -> Prop) (t : B -> Prop) (_64768 : B) : (term371 B v t _64768) = (term371 B v t _64768).
Proof. exact (eq_refl (term371 B v t _64768)). Qed.
Lemma lem5042117 {B : Type'} (v : B -> Prop) (t : B -> Prop) (_64768 : B) : ((term119 B t v _64768) = (term371 B v t _64768)) = ((term371 B v t _64768) = (term371 B v t _64768)).
Proof. exact (MK_COMB (@lem5042110 B v t _64768) (@lem5042116 B v t _64768)). Qed.
Lemma lem5042119 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5042120 (x : Prop) : (x = x) = True.
Proof. exact (@lem5042119 Prop x). Qed.
Lemma lem5042121 {B : Type'} (v : B -> Prop) (t : B -> Prop) (_64768 : B) : ((term371 B v t _64768) = (term371 B v t _64768)) = True.
Proof. exact (@lem5042120 (term371 B v t _64768)). Qed.
Lemma lem5042122 {B : Type'} (v : B -> Prop) (t : B -> Prop) (_64768 : B) : ((term119 B t v _64768) = (term371 B v t _64768)) = True.
Proof. exact (TRANS (@lem5042117 B v t _64768) (@lem5042121 B v t _64768)). Qed.
Lemma lem5042123 {B : Type'} (v : B -> Prop) (t : B -> Prop) (_64768 : B) : True = ((term119 B t v _64768) = (term371 B v t _64768)).
Proof. exact (SYM (@lem5042122 B v t _64768)). Qed.
Lemma lem5042124 {B : Type'} (v : B -> Prop) (t : B -> Prop) (_64768 : B) : (term119 B t v _64768) = (term371 B v t _64768).
Proof. exact (EQ_MP (@lem5042123 B v t _64768) (@lem0)). Qed.
Lemma lem5042125 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term371 B v t _64768.
Proof. exact (EQ_MP (@lem5042124 B v t _64768) (@lem5041754 A B _64768 t v u f x''' h1)). Qed.
Lemma lem5042127 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5042128 {B : Type'} (t : B -> Prop) (v : B -> Prop) (_64768 : B) : (term371 B v t _64768) = (term374 B t v _64768).
Proof. exact (@lem5042127 (term349 B t _64768) (v _64768)). Qed.
Lemma lem5042130 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5042131 {B : Type'} (t : B -> Prop) (_64768 : B) : (term375 B t _64768) = (t _64768).
Proof. exact (@lem5042130 (t _64768)). Qed.
Lemma lem5042132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042133 {B : Type'} (t : B -> Prop) (_64768 : B) : (term376 B t _64768) = (term34 B t _64768).
Proof. exact (MK_COMB (@lem5042132) (@lem5042131 B t _64768)). Qed.
Lemma lem5042134 {B : Type'} (v : B -> Prop) (_64768 : B) : (v _64768) = (v _64768).
Proof. exact (eq_refl (v _64768)). Qed.
Lemma lem5042135 {B : Type'} (t : B -> Prop) (v : B -> Prop) (_64768 : B) : (term374 B t v _64768) = (term50 B t v _64768).
Proof. exact (MK_COMB (@lem5042133 B t _64768) (@lem5042134 B v _64768)). Qed.
Lemma lem5042136 {B : Type'} (t : B -> Prop) (v : B -> Prop) (_64768 : B) : (term371 B v t _64768) = (term50 B t v _64768).
Proof. exact (TRANS (@lem5042128 B t v _64768) (@lem5042135 B t v _64768)). Qed.
Lemma lem5042139 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v _64768.
Proof. exact (EQ_MP (@lem5042136 B t v _64768) (@lem5042125 A B _64768 t v u f x''' h1)). Qed.
Lemma lem5042140 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v _64768.
Proof. exact (@lem5042139 A B _64768 t v u f x''' h1). Qed.
Lemma lem5042141 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v x'.
Proof. exact (@lem5042140 A B x' t v u f x''' h1). Qed.
Lemma lem5042144 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : v x'.
Proof. exact (@lem5042141 A B x' t v u f x''' h2 (@lem5042096 A B u f t x' h1)). Qed.
Lemma lem5042145 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term357 B v x'.
Proof. exact (fun h0 : term349 B v x' => @lem5042144 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042147 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042148 {B : Type'} (v : B -> Prop) (x' : B) : (term357 B v x') = (v x').
Proof. exact (@lem5042147 (v x')). Qed.
Lemma lem5042149 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : v x'.
Proof. exact (EQ_MP (@lem5042148 B v x') (@lem5042145 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042155 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5042156 {A B : Type'} (f : A -> B) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : (term722 A B v f x''' _64769) = (term734 A B f x''' v _64769).
Proof. exact (@lem5042155 ((term321 A B f x''' _64769) = _64769) (term349 B v _64769)). Qed.
Lemma lem5042164 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5042165 {A B : Type'} (f : A -> B) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : (term735 A B v f x''' _64769) = (term736 A B f x''' v _64769).
Proof. exact (MK_COMB (@lem5042164) (@lem5042156 A B f x''' v _64769)). Qed.
Lemma lem5042173 {A B : Type'} (f : A -> B) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : (term734 A B f x''' v _64769) = (term734 A B f x''' v _64769).
Proof. exact (eq_refl (term734 A B f x''' v _64769)). Qed.
Lemma lem5042174 {A B : Type'} (f : A -> B) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : ((term722 A B v f x''' _64769) = (term734 A B f x''' v _64769)) = ((term734 A B f x''' v _64769) = (term734 A B f x''' v _64769)).
Proof. exact (MK_COMB (@lem5042165 A B f x''' v _64769) (@lem5042173 A B f x''' v _64769)). Qed.
Lemma lem5042176 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5042177 (x : Prop) : (x = x) = True.
Proof. exact (@lem5042176 Prop x). Qed.
Lemma lem5042178 {A B : Type'} (f : A -> B) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : ((term734 A B f x''' v _64769) = (term734 A B f x''' v _64769)) = True.
Proof. exact (@lem5042177 (term734 A B f x''' v _64769)). Qed.
Lemma lem5042179 {A B : Type'} (f : A -> B) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : ((term722 A B v f x''' _64769) = (term734 A B f x''' v _64769)) = True.
Proof. exact (TRANS (@lem5042174 A B f x''' v _64769) (@lem5042178 A B f x''' v _64769)). Qed.
Lemma lem5042180 {A B : Type'} (f : A -> B) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : True = ((term722 A B v f x''' _64769) = (term734 A B f x''' v _64769)).
Proof. exact (SYM (@lem5042179 A B f x''' v _64769)). Qed.
Lemma lem5042181 {A B : Type'} (f : A -> B) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : (term722 A B v f x''' _64769) = (term734 A B f x''' v _64769).
Proof. exact (EQ_MP (@lem5042180 A B f x''' v _64769) (@lem0)). Qed.
Lemma lem5042182 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term734 A B f x''' v _64769.
Proof. exact (EQ_MP (@lem5042181 A B f x''' v _64769) (@lem5041778 A B _64769 t v u f x''' h1)). Qed.
Lemma lem5042184 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5042185 {A B : Type'} (v : B -> Prop) (f : A -> B) (x''' : B -> A) (_64769 : B) : (term734 A B f x''' v _64769) = (term737 A B v f x''' _64769).
Proof. exact (@lem5042184 (term349 B v _64769) ((term321 A B f x''' _64769) = _64769)). Qed.
Lemma lem5042187 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5042188 {B : Type'} (v : B -> Prop) (_64769 : B) : (term375 B v _64769) = (v _64769).
Proof. exact (@lem5042187 (v _64769)). Qed.
Lemma lem5042189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042190 {B : Type'} (v : B -> Prop) (_64769 : B) : (term376 B v _64769) = (term34 B v _64769).
Proof. exact (MK_COMB (@lem5042189) (@lem5042188 B v _64769)). Qed.
Lemma lem5042191 {A B : Type'} (f : A -> B) (x''' : B -> A) (_64769 : B) : ((term321 A B f x''' _64769) = _64769) = ((term321 A B f x''' _64769) = _64769).
Proof. exact (eq_refl ((term321 A B f x''' _64769) = _64769)). Qed.
Lemma lem5042192 {A B : Type'} (v : B -> Prop) (f : A -> B) (x''' : B -> A) (_64769 : B) : (term737 A B v f x''' _64769) = (term738 A B v f x''' _64769).
Proof. exact (MK_COMB (@lem5042190 B v _64769) (@lem5042191 A B f x''' _64769)). Qed.
Lemma lem5042193 {A B : Type'} (v : B -> Prop) (f : A -> B) (x''' : B -> A) (_64769 : B) : (term734 A B f x''' v _64769) = (term738 A B v f x''' _64769).
Proof. exact (TRANS (@lem5042185 A B v f x''' _64769) (@lem5042192 A B v f x''' _64769)). Qed.
Lemma lem5042196 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term738 A B v f x''' _64769.
Proof. exact (EQ_MP (@lem5042193 A B v f x''' _64769) (@lem5042182 A B _64769 t v u f x''' h1)). Qed.
Lemma lem5042197 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term738 A B v f x''' _64769.
Proof. exact (@lem5042196 A B _64769 t v u f x''' h1). Qed.
Lemma lem5042198 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term738 A B v f x''' x'.
Proof. exact (@lem5042197 A B x' t v u f x''' h1). Qed.
Lemma lem5042201 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : (term321 A B f x''' x') = x'.
Proof. exact (@lem5042198 A B x' t v u f x''' h2 (@lem5042149 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042202 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term402 A B f x''' x'.
Proof. exact (fun h0 : term403 A B f x''' x' => @lem5042201 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042204 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042205 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term402 A B f x''' x') = ((term321 A B f x''' x') = x').
Proof. exact (@lem5042204 ((term321 A B f x''' x') = x')). Qed.
Lemma lem5042206 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : (term321 A B f x''' x') = x'.
Proof. exact (EQ_MP (@lem5042205 A B f x''' x') (@lem5042202 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042208 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5042209 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5042208 B x). Qed.
Lemma lem5042210 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term321 A B f x''' x') = (term321 A B f x''' x').
Proof. exact (@lem5042209 B (term321 A B f x''' x')). Qed.
Lemma lem5042211 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : term378 A B f x''' x'.
Proof. exact (fun h0 : term379 A B f x''' x' => @lem5042210 A B f x''' x'). Qed.
Lemma lem5042213 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042214 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term378 A B f x''' x') = ((term321 A B f x''' x') = (term321 A B f x''' x')).
Proof. exact (@lem5042213 ((term321 A B f x''' x') = (term321 A B f x''' x'))). Qed.
Lemma lem5042215 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term321 A B f x''' x') = (term321 A B f x''' x').
Proof. exact (EQ_MP (@lem5042214 A B f x''' x') (@lem5042211 A B f x''' x')). Qed.
Lemma lem5042233 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5042234 {B : Type'} (y : B) (x : B) (z : B) : (term739 B x y z) = (term740 B y x z).
Proof. exact (@lem5042233 (y = z) (term133 B x z)). Qed.
Lemma lem5042244 {B : Type'} (x : B) (y : B) : (term741 B x y) = (term741 B x y).
Proof. exact (eq_refl (term741 B x y)). Qed.
Lemma lem5042245 {B : Type'} (y : B) (x : B) (z : B) : (term733 B x y z) = (term742 B y x z).
Proof. exact (MK_COMB (@lem5042244 B x y) (@lem5042234 B y x z)). Qed.
Lemma lem5042249 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5042250 {B : Type'} (y : B) (x : B) (z : B) : (term742 B y x z) = (term743 B y x z).
Proof. exact (@lem5042249 (y = z) (term133 B x y) (term133 B x z)). Qed.
Lemma lem5042272 {B : Type'} (y : B) (x : B) (z : B) : (term733 B x y z) = (term743 B y x z).
Proof. exact (TRANS (@lem5042245 B y x z) (@lem5042250 B y x z)). Qed.
Lemma lem5042273 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5042274 {B : Type'} (y : B) (x : B) (z : B) : (term744 B x y z) = (term745 B y x z).
Proof. exact (MK_COMB (@lem5042273) (@lem5042272 B y x z)). Qed.
Lemma lem5042296 {B : Type'} (y : B) (x : B) (z : B) : (term743 B y x z) = (term743 B y x z).
Proof. exact (eq_refl (term743 B y x z)). Qed.
Lemma lem5042297 {B : Type'} (y : B) (x : B) (z : B) : ((term733 B x y z) = (term743 B y x z)) = ((term743 B y x z) = (term743 B y x z)).
Proof. exact (MK_COMB (@lem5042274 B y x z) (@lem5042296 B y x z)). Qed.
Lemma lem5042299 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5042300 (x : Prop) : (x = x) = True.
Proof. exact (@lem5042299 Prop x). Qed.
Lemma lem5042301 {B : Type'} (y : B) (x : B) (z : B) : ((term743 B y x z) = (term743 B y x z)) = True.
Proof. exact (@lem5042300 (term743 B y x z)). Qed.
Lemma lem5042302 {B : Type'} (y : B) (x : B) (z : B) : ((term733 B x y z) = (term743 B y x z)) = True.
Proof. exact (TRANS (@lem5042297 B y x z) (@lem5042301 B y x z)). Qed.
Lemma lem5042303 {B : Type'} (y : B) (x : B) (z : B) : True = ((term733 B x y z) = (term743 B y x z)).
Proof. exact (SYM (@lem5042302 B y x z)). Qed.
Lemma lem5042304 {B : Type'} (y : B) (x : B) (z : B) : (term733 B x y z) = (term743 B y x z).
Proof. exact (EQ_MP (@lem5042303 B y x z) (@lem0)). Qed.
Lemma lem5042305 {B : Type'} (y : B) (x : B) (z : B) : term743 B y x z.
Proof. exact (EQ_MP (@lem5042304 B y x z) (@lem5042087 B x y z)). Qed.
Lemma lem5042307 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5042308 {B : Type'} (x : B) (y : B) (z : B) : (term743 B y x z) = (term746 B x y z).
Proof. exact (@lem5042307 (term747 B y x z) (y = z)). Qed.
Lemma lem5042310 (a : Prop) (b : Prop) : (term391 a b) = (term392 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5042311 {B : Type'} (y : B) (x : B) (z : B) : (term748 B y x z) = (term749 B y x z).
Proof. exact (@lem5042310 (term133 B x y) (term133 B x z)). Qed.
Lemma lem5042313 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5042314 {B : Type'} (x : B) (y : B) : (term365 B x y) = (x = y).
Proof. exact (@lem5042313 (x = y)). Qed.
Lemma lem5042315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5042316 {B : Type'} (x : B) (y : B) : (term750 B x y) = (term751 B x y).
Proof. exact (MK_COMB (@lem5042315) (@lem5042314 B x y)). Qed.
Lemma lem5042318 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5042319 {B : Type'} (x : B) (z : B) : (term365 B x z) = (x = z).
Proof. exact (@lem5042318 (x = z)). Qed.
Lemma lem5042320 {B : Type'} (y : B) (x : B) (z : B) : (term749 B y x z) = (term752 B y x z).
Proof. exact (MK_COMB (@lem5042316 B x y) (@lem5042319 B x z)). Qed.
Lemma lem5042321 {B : Type'} (y : B) (x : B) (z : B) : (term748 B y x z) = (term752 B y x z).
Proof. exact (TRANS (@lem5042311 B y x z) (@lem5042320 B y x z)). Qed.
Lemma lem5042322 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042323 {B : Type'} (y : B) (x : B) (z : B) : (term753 B y x z) = (term754 B y x z).
Proof. exact (MK_COMB (@lem5042322) (@lem5042321 B y x z)). Qed.
Lemma lem5042324 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5042325 {B : Type'} (x : B) (y : B) (z : B) : (term746 B x y z) = (term755 B x y z).
Proof. exact (MK_COMB (@lem5042323 B y x z) (@lem5042324 B y z)). Qed.
Lemma lem5042326 {B : Type'} (x : B) (y : B) (z : B) : (term743 B y x z) = (term755 B x y z).
Proof. exact (TRANS (@lem5042308 B x y z) (@lem5042325 B x y z)). Qed.
Lemma lem5042328 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term756 A B f x''' x'.
Proof. exact (conj (@lem5042206 A B x' t v u f x''' h1 h2) (@lem5042215 A B f x''' x')). Qed.
Lemma lem5042330 {B : Type'} (x : B) (y : B) (z : B) : term755 B x y z.
Proof. exact (EQ_MP (@lem5042326 B x y z) (@lem5042305 B y x z)). Qed.
Lemma lem5042331 {B : Type'} (x : B) (y : B) (z : B) : term755 B x y z.
Proof. exact (@lem5042330 B x y z). Qed.
Lemma lem5042332 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : term757 A B f x''' x'.
Proof. exact (@lem5042331 B (term321 A B f x''' x') x' (term321 A B f x''' x')). Qed.
Lemma lem5042335 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : x' = (term321 A B f x''' x').
Proof. exact (@lem5042332 A B f x''' x' (@lem5042328 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042336 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term758 A B f x''' x'.
Proof. exact (fun h0 : term759 A B f x''' x' => @lem5042335 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042338 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042339 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term758 A B f x''' x') = (x' = (term321 A B f x''' x')).
Proof. exact (@lem5042338 (x' = (term321 A B f x''' x'))). Qed.
Lemma lem5042340 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : x' = (term321 A B f x''' x').
Proof. exact (EQ_MP (@lem5042339 A B f x''' x') (@lem5042336 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042342 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : t x'.
Proof. exact (proj2 (@lem5041504 A B u f t x' h1)). Qed.
Lemma lem5042343 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term357 B t x'.
Proof. exact (fun h0 : term349 B t x' => @lem5042342 A B u f t x' h1). Qed.
Lemma lem5042345 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042346 {B : Type'} (t : B -> Prop) (x' : B) : (term357 B t x') = (t x').
Proof. exact (@lem5042345 (t x')). Qed.
Lemma lem5042347 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : t x'.
Proof. exact (EQ_MP (@lem5042346 B t x') (@lem5042343 A B u f t x' h1)). Qed.
Lemma lem5042349 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v _64768.
Proof. exact (EQ_MP (@lem5042136 B t v _64768) (@lem5042125 A B _64768 t v u f x''' h1)). Qed.
Lemma lem5042350 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v _64768.
Proof. exact (@lem5042349 A B _64768 t v u f x''' h1). Qed.
Lemma lem5042351 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v x'.
Proof. exact (@lem5042350 A B x' t v u f x''' h1). Qed.
Lemma lem5042354 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : v x'.
Proof. exact (@lem5042351 A B x' t v u f x''' h2 (@lem5042347 A B u f t x' h1)). Qed.
Lemma lem5042355 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term357 B v x'.
Proof. exact (fun h0 : term349 B v x' => @lem5042354 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042357 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042358 {B : Type'} (v : B -> Prop) (x' : B) : (term357 B v x') = (v x').
Proof. exact (@lem5042357 (v x')). Qed.
Lemma lem5042359 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : v x'.
Proof. exact (EQ_MP (@lem5042358 B v x') (@lem5042355 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042365 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5042366 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : (term721 A B v u x''' _64769) = (term760 A B u x''' v _64769).
Proof. exact (@lem5042365 (term322 A B u x''' _64769) (term349 B v _64769)). Qed.
Lemma lem5042372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5042373 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : (term761 A B v u x''' _64769) = (term762 A B u x''' v _64769).
Proof. exact (MK_COMB (@lem5042372) (@lem5042366 A B u x''' v _64769)). Qed.
Lemma lem5042379 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : (term760 A B u x''' v _64769) = (term760 A B u x''' v _64769).
Proof. exact (eq_refl (term760 A B u x''' v _64769)). Qed.
Lemma lem5042380 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : ((term721 A B v u x''' _64769) = (term760 A B u x''' v _64769)) = ((term760 A B u x''' v _64769) = (term760 A B u x''' v _64769)).
Proof. exact (MK_COMB (@lem5042373 A B u x''' v _64769) (@lem5042379 A B u x''' v _64769)). Qed.
Lemma lem5042382 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5042383 (x : Prop) : (x = x) = True.
Proof. exact (@lem5042382 Prop x). Qed.
Lemma lem5042384 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : ((term760 A B u x''' v _64769) = (term760 A B u x''' v _64769)) = True.
Proof. exact (@lem5042383 (term760 A B u x''' v _64769)). Qed.
Lemma lem5042385 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : ((term721 A B v u x''' _64769) = (term760 A B u x''' v _64769)) = True.
Proof. exact (TRANS (@lem5042380 A B u x''' v _64769) (@lem5042384 A B u x''' v _64769)). Qed.
Lemma lem5042386 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : True = ((term721 A B v u x''' _64769) = (term760 A B u x''' v _64769)).
Proof. exact (SYM (@lem5042385 A B u x''' v _64769)). Qed.
Lemma lem5042387 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (v : B -> Prop) (_64769 : B) : (term721 A B v u x''' _64769) = (term760 A B u x''' v _64769).
Proof. exact (EQ_MP (@lem5042386 A B u x''' v _64769) (@lem0)). Qed.
Lemma lem5042388 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term760 A B u x''' v _64769.
Proof. exact (EQ_MP (@lem5042387 A B u x''' v _64769) (@lem5041772 A B _64769 t v u f x''' h1)). Qed.
Lemma lem5042390 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5042391 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (x''' : B -> A) (_64769 : B) : (term760 A B u x''' v _64769) = (term763 A B v u x''' _64769).
Proof. exact (@lem5042390 (term349 B v _64769) (term322 A B u x''' _64769)). Qed.
Lemma lem5042393 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5042394 {B : Type'} (v : B -> Prop) (_64769 : B) : (term375 B v _64769) = (v _64769).
Proof. exact (@lem5042393 (v _64769)). Qed.
Lemma lem5042395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042396 {B : Type'} (v : B -> Prop) (_64769 : B) : (term376 B v _64769) = (term34 B v _64769).
Proof. exact (MK_COMB (@lem5042395) (@lem5042394 B v _64769)). Qed.
Lemma lem5042397 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (_64769 : B) : (term322 A B u x''' _64769) = (term322 A B u x''' _64769).
Proof. exact (eq_refl (term322 A B u x''' _64769)). Qed.
Lemma lem5042398 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (x''' : B -> A) (_64769 : B) : (term763 A B v u x''' _64769) = (term764 A B v u x''' _64769).
Proof. exact (MK_COMB (@lem5042396 B v _64769) (@lem5042397 A B u x''' _64769)). Qed.
Lemma lem5042399 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (x''' : B -> A) (_64769 : B) : (term760 A B u x''' v _64769) = (term764 A B v u x''' _64769).
Proof. exact (TRANS (@lem5042391 A B v u x''' _64769) (@lem5042398 A B v u x''' _64769)). Qed.
Lemma lem5042402 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term764 A B v u x''' _64769.
Proof. exact (EQ_MP (@lem5042399 A B v u x''' _64769) (@lem5042388 A B _64769 t v u f x''' h1)). Qed.
Lemma lem5042403 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term764 A B v u x''' _64769.
Proof. exact (@lem5042402 A B _64769 t v u f x''' h1). Qed.
Lemma lem5042404 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term764 A B v u x''' x'.
Proof. exact (@lem5042403 A B x' t v u f x''' h1). Qed.
Lemma lem5042407 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term322 A B u x''' x'.
Proof. exact (@lem5042404 A B x' t v u f x''' h2 (@lem5042359 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042408 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term369 A B u x''' x'.
Proof. exact (fun h0 : term370 A B u x''' x' => @lem5042407 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042410 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042411 {A B : Type'} (u : A -> Prop) (x''' : B -> A) (x' : B) : (term369 A B u x''' x') = (term322 A B u x''' x').
Proof. exact (@lem5042410 (term322 A B u x''' x')). Qed.
Lemma lem5042412 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term322 A B u x''' x'.
Proof. exact (EQ_MP (@lem5042411 A B u x''' x') (@lem5042408 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042414 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : t x'.
Proof. exact (proj2 (@lem5041504 A B u f t x' h1)). Qed.
Lemma lem5042415 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term357 B t x'.
Proof. exact (fun h0 : term349 B t x' => @lem5042414 A B u f t x' h1). Qed.
Lemma lem5042417 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042418 {B : Type'} (t : B -> Prop) (x' : B) : (term357 B t x') = (t x').
Proof. exact (@lem5042417 (t x')). Qed.
Lemma lem5042419 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : t x'.
Proof. exact (EQ_MP (@lem5042418 B t x') (@lem5042415 A B u f t x' h1)). Qed.
Lemma lem5042421 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v _64768.
Proof. exact (EQ_MP (@lem5042136 B t v _64768) (@lem5042125 A B _64768 t v u f x''' h1)). Qed.
Lemma lem5042422 {A B : Type'} (_64768 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v _64768.
Proof. exact (@lem5042421 A B _64768 t v u f x''' h1). Qed.
Lemma lem5042423 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term50 B t v x'.
Proof. exact (@lem5042422 A B x' t v u f x''' h1). Qed.
Lemma lem5042426 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : v x'.
Proof. exact (@lem5042423 A B x' t v u f x''' h2 (@lem5042419 A B u f t x' h1)). Qed.
Lemma lem5042427 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term357 B v x'.
Proof. exact (fun h0 : term349 B v x' => @lem5042426 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042429 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042430 {B : Type'} (v : B -> Prop) (x' : B) : (term357 B v x') = (v x').
Proof. exact (@lem5042429 (v x')). Qed.
Lemma lem5042431 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : v x'.
Proof. exact (EQ_MP (@lem5042430 B v x') (@lem5042427 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042433 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term738 A B v f x''' _64769.
Proof. exact (EQ_MP (@lem5042193 A B v f x''' _64769) (@lem5042182 A B _64769 t v u f x''' h1)). Qed.
Lemma lem5042434 {A B : Type'} (_64769 : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term738 A B v f x''' _64769.
Proof. exact (@lem5042433 A B _64769 t v u f x''' h1). Qed.
Lemma lem5042435 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term552 A B t v u f x''') : term738 A B v f x''' x'.
Proof. exact (@lem5042434 A B x' t v u f x''' h1). Qed.
Lemma lem5042438 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : (term321 A B f x''' x') = x'.
Proof. exact (@lem5042435 A B x' t v u f x''' h2 (@lem5042431 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042439 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term402 A B f x''' x'.
Proof. exact (fun h0 : term403 A B f x''' x' => @lem5042438 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042441 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042442 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term402 A B f x''' x') = ((term321 A B f x''' x') = x').
Proof. exact (@lem5042441 ((term321 A B f x''' x') = x')). Qed.
Lemma lem5042443 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : (term321 A B f x''' x') = x'.
Proof. exact (EQ_MP (@lem5042442 A B f x''' x') (@lem5042439 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042445 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5042446 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5042445 B x). Qed.
Lemma lem5042447 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term321 A B f x''' x') = (term321 A B f x''' x').
Proof. exact (@lem5042446 B (term321 A B f x''' x')). Qed.
Lemma lem5042448 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : term378 A B f x''' x'.
Proof. exact (fun h0 : term379 A B f x''' x' => @lem5042447 A B f x''' x'). Qed.
Lemma lem5042450 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042451 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term378 A B f x''' x') = ((term321 A B f x''' x') = (term321 A B f x''' x')).
Proof. exact (@lem5042450 ((term321 A B f x''' x') = (term321 A B f x''' x'))). Qed.
Lemma lem5042452 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term321 A B f x''' x') = (term321 A B f x''' x').
Proof. exact (EQ_MP (@lem5042451 A B f x''' x') (@lem5042448 A B f x''' x')). Qed.
Lemma lem5042453 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term756 A B f x''' x'.
Proof. exact (conj (@lem5042443 A B x' t v u f x''' h1 h2) (@lem5042452 A B f x''' x')). Qed.
Lemma lem5042455 {B : Type'} (x : B) (y : B) (z : B) : term755 B x y z.
Proof. exact (EQ_MP (@lem5042326 B x y z) (@lem5042305 B y x z)). Qed.
Lemma lem5042456 {B : Type'} (x : B) (y : B) (z : B) : term755 B x y z.
Proof. exact (@lem5042455 B x y z). Qed.
Lemma lem5042457 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : term757 A B f x''' x'.
Proof. exact (@lem5042456 B (term321 A B f x''' x') x' (term321 A B f x''' x')). Qed.
Lemma lem5042460 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : x' = (term321 A B f x''' x').
Proof. exact (@lem5042457 A B f x''' x' (@lem5042453 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042461 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term758 A B f x''' x'.
Proof. exact (fun h0 : term759 A B f x''' x' => @lem5042460 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042463 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042464 {A B : Type'} (f : A -> B) (x''' : B -> A) (x' : B) : (term758 A B f x''' x') = (x' = (term321 A B f x''' x')).
Proof. exact (@lem5042463 (x' = (term321 A B f x''' x'))). Qed.
Lemma lem5042465 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : x' = (term321 A B f x''' x').
Proof. exact (EQ_MP (@lem5042464 A B f x''' x') (@lem5042461 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042467 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : t x'.
Proof. exact (proj2 (@lem5041504 A B u f t x' h1)). Qed.
Lemma lem5042468 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term357 B t x'.
Proof. exact (fun h0 : term349 B t x' => @lem5042467 A B u f t x' h1). Qed.
Lemma lem5042470 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042471 {B : Type'} (t : B -> Prop) (x' : B) : (term357 B t x') = (t x').
Proof. exact (@lem5042470 (t x')). Qed.
Lemma lem5042472 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : t x'.
Proof. exact (EQ_MP (@lem5042471 B t x') (@lem5042468 A B u f t x' h1)). Qed.
Lemma lem5042478 (q : Prop) (p : Prop) (r : Prop) : (term8 p q r) = (term8 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5042479 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : (term732 B _64808 t _64807) = (term765 B _64808 t _64807).
Proof. exact (@lem5042478 (t _64808) (term133 B _64807 _64808) (term349 B t _64807)). Qed.
Lemma lem5042493 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5042494 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) : (term766 B _64808 t _64807) = (term767 B t _64807 _64808).
Proof. exact (@lem5042493 (term349 B t _64807) (term133 B _64807 _64808)). Qed.
Lemma lem5042502 {B : Type'} (t : B -> Prop) (_64808 : B) : (term768 B t _64808) = (term768 B t _64808).
Proof. exact (eq_refl (term768 B t _64808)). Qed.
Lemma lem5042503 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) : (term765 B _64808 t _64807) = (term769 B t _64807 _64808).
Proof. exact (MK_COMB (@lem5042502 B t _64808) (@lem5042494 B t _64807 _64808)). Qed.
Lemma lem5042514 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) : (term732 B _64808 t _64807) = (term769 B t _64807 _64808).
Proof. exact (TRANS (@lem5042479 B _64808 t _64807) (@lem5042503 B t _64807 _64808)). Qed.
Lemma lem5042515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5042516 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) : (term770 B _64808 t _64807) = (term771 B t _64807 _64808).
Proof. exact (MK_COMB (@lem5042515) (@lem5042514 B t _64807 _64808)). Qed.
Lemma lem5042530 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5042531 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) : (term766 B _64808 t _64807) = (term767 B t _64807 _64808).
Proof. exact (@lem5042530 (term349 B t _64807) (term133 B _64807 _64808)). Qed.
Lemma lem5042539 {B : Type'} (t : B -> Prop) (_64808 : B) : (term768 B t _64808) = (term768 B t _64808).
Proof. exact (eq_refl (term768 B t _64808)). Qed.
Lemma lem5042540 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) : (term765 B _64808 t _64807) = (term769 B t _64807 _64808).
Proof. exact (MK_COMB (@lem5042539 B t _64808) (@lem5042531 B t _64807 _64808)). Qed.
Lemma lem5042551 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) : ((term732 B _64808 t _64807) = (term765 B _64808 t _64807)) = ((term769 B t _64807 _64808) = (term769 B t _64807 _64808)).
Proof. exact (MK_COMB (@lem5042516 B t _64807 _64808) (@lem5042540 B t _64807 _64808)). Qed.
Lemma lem5042553 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5042554 (x : Prop) : (x = x) = True.
Proof. exact (@lem5042553 Prop x). Qed.
Lemma lem5042555 {B : Type'} (t : B -> Prop) (_64807 : B) (_64808 : B) : ((term769 B t _64807 _64808) = (term769 B t _64807 _64808)) = True.
Proof. exact (@lem5042554 (term769 B t _64807 _64808)). Qed.
Lemma lem5042556 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : ((term732 B _64808 t _64807) = (term765 B _64808 t _64807)) = True.
Proof. exact (TRANS (@lem5042551 B t _64807 _64808) (@lem5042555 B t _64807 _64808)). Qed.
Lemma lem5042557 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : True = ((term732 B _64808 t _64807) = (term765 B _64808 t _64807)).
Proof. exact (SYM (@lem5042556 B _64808 t _64807)). Qed.
Lemma lem5042558 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : (term732 B _64808 t _64807) = (term765 B _64808 t _64807).
Proof. exact (EQ_MP (@lem5042557 B _64808 t _64807) (@lem0)). Qed.
Lemma lem5042559 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : term765 B _64808 t _64807.
Proof. exact (EQ_MP (@lem5042558 B _64808 t _64807) (@lem5042057 B _64808 t _64807)). Qed.
Lemma lem5042561 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5042562 {B : Type'} (_64807 : B) (t : B -> Prop) (_64808 : B) : (term765 B _64808 t _64807) = (term772 B _64807 t _64808).
Proof. exact (@lem5042561 (term766 B _64808 t _64807) (t _64808)). Qed.
Lemma lem5042564 (a : Prop) (b : Prop) : (term391 a b) = (term392 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5042565 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : (term773 B _64808 t _64807) = (term774 B _64808 t _64807).
Proof. exact (@lem5042564 (term133 B _64807 _64808) (term349 B t _64807)). Qed.
Lemma lem5042567 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5042568 {B : Type'} (_64807 : B) (_64808 : B) : (term365 B _64807 _64808) = (_64807 = _64808).
Proof. exact (@lem5042567 (_64807 = _64808)). Qed.
Lemma lem5042569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5042570 {B : Type'} (_64807 : B) (_64808 : B) : (term750 B _64807 _64808) = (term751 B _64807 _64808).
Proof. exact (MK_COMB (@lem5042569) (@lem5042568 B _64807 _64808)). Qed.
Lemma lem5042572 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5042573 {B : Type'} (t : B -> Prop) (_64807 : B) : (term375 B t _64807) = (t _64807).
Proof. exact (@lem5042572 (t _64807)). Qed.
Lemma lem5042574 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : (term774 B _64808 t _64807) = (term775 B _64808 t _64807).
Proof. exact (MK_COMB (@lem5042570 B _64807 _64808) (@lem5042573 B t _64807)). Qed.
Lemma lem5042575 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : (term773 B _64808 t _64807) = (term775 B _64808 t _64807).
Proof. exact (TRANS (@lem5042565 B _64808 t _64807) (@lem5042574 B _64808 t _64807)). Qed.
Lemma lem5042576 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042577 {B : Type'} (_64808 : B) (t : B -> Prop) (_64807 : B) : (term776 B _64808 t _64807) = (term777 B _64808 t _64807).
Proof. exact (MK_COMB (@lem5042576) (@lem5042575 B _64808 t _64807)). Qed.
Lemma lem5042578 {B : Type'} (t : B -> Prop) (_64808 : B) : (t _64808) = (t _64808).
Proof. exact (eq_refl (t _64808)). Qed.
Lemma lem5042579 {B : Type'} (_64807 : B) (t : B -> Prop) (_64808 : B) : (term772 B _64807 t _64808) = (term778 B _64807 t _64808).
Proof. exact (MK_COMB (@lem5042577 B _64808 t _64807) (@lem5042578 B t _64808)). Qed.
Lemma lem5042580 {B : Type'} (_64807 : B) (t : B -> Prop) (_64808 : B) : (term765 B _64808 t _64807) = (term778 B _64807 t _64808).
Proof. exact (TRANS (@lem5042562 B _64807 t _64808) (@lem5042579 B _64807 t _64808)). Qed.
Lemma lem5042582 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term779 A B f x''' t x'.
Proof. exact (conj (@lem5042465 A B x' t v u f x''' h1 h2) (@lem5042472 A B u f t x' h1)). Qed.
Lemma lem5042584 {B : Type'} (_64807 : B) (t : B -> Prop) (_64808 : B) : term778 B _64807 t _64808.
Proof. exact (EQ_MP (@lem5042580 B _64807 t _64808) (@lem5042559 B _64808 t _64807)). Qed.
Lemma lem5042585 {B : Type'} (_64807 : B) (t : B -> Prop) (_64808 : B) : term778 B _64807 t _64808.
Proof. exact (@lem5042584 B _64807 t _64808). Qed.
Lemma lem5042586 {A B : Type'} (t : B -> Prop) (f : A -> B) (x''' : B -> A) (x' : B) : term780 A B t f x''' x'.
Proof. exact (@lem5042585 B x' t (term321 A B f x''' x')). Qed.
Lemma lem5042589 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term781 A B t f x''' x'.
Proof. exact (@lem5042586 A B t f x''' x' (@lem5042582 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042590 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term782 A B t f x''' x'.
Proof. exact (fun h0 : term783 A B t f x''' x' => @lem5042589 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042592 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042593 {A B : Type'} (t : B -> Prop) (f : A -> B) (x''' : B -> A) (x' : B) : (term782 A B t f x''' x') = (term781 A B t f x''' x').
Proof. exact (@lem5042592 (term781 A B t f x''' x')). Qed.
Lemma lem5042594 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term781 A B t f x''' x'.
Proof. exact (EQ_MP (@lem5042593 A B t f x''' x') (@lem5042590 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042596 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5042597 {A B : Type'} (u : A -> Prop) (t : B -> Prop) (f : A -> B) (_64770 : A) : (term566 A B u t f _64770) = (term565 A B u t f _64770).
Proof. exact (@lem5042596 (u _64770) (term457 A B t f _64770)). Qed.
Lemma lem5042598 {A B : Type'} (x' : B) (f : A -> B) (_64770 : A) : (term567 A B x' f _64770) = (term567 A B x' f _64770).
Proof. exact (eq_refl (term567 A B x' f _64770)). Qed.
Lemma lem5042599 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (_64770 : A) : (term569 A B x' u t f _64770) = (term568 A B x' u t f _64770).
Proof. exact (MK_COMB (@lem5042598 A B x' f _64770) (@lem5042597 A B u t f _64770)). Qed.
Lemma lem5042601 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5042602 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (_64770 : A) : (term568 A B x' u t f _64770) = (term570 A B x' u t f _64770).
Proof. exact (@lem5042601 (x' = (f _64770)) (term458 A B u t f _64770)). Qed.
Lemma lem5042603 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (_64770 : A) : (term569 A B x' u t f _64770) = (term570 A B x' u t f _64770).
Proof. exact (TRANS (@lem5042599 A B x' u t f _64770) (@lem5042602 A B x' u t f _64770)). Qed.
Lemma lem5042605 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5042606 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (_64770 : A) : (term570 A B x' u t f _64770) = (term784 A B x' u t f _64770).
Proof. exact (@lem5042605 (term470 A B x' u t f _64770)). Qed.
Lemma lem5042607 {A B : Type'} (x' : B) (u : A -> Prop) (t : B -> Prop) (f : A -> B) (_64770 : A) : (term569 A B x' u t f _64770) = (term784 A B x' u t f _64770).
Proof. exact (TRANS (@lem5042603 A B x' u t f _64770) (@lem5042606 A B x' u t f _64770)). Qed.
Lemma lem5042609 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term785 A B u t f x''' x'.
Proof. exact (conj (@lem5042412 A B x' t v u f x''' h1 h2) (@lem5042594 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042610 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term786 A B u t f x''' x'.
Proof. exact (conj (@lem5042340 A B x' t v u f x''' h1 h2) (@lem5042609 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042612 {A B : Type'} (_64770 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term784 A B x' u t f _64770.
Proof. exact (EQ_MP (@lem5042607 A B x' u t f _64770) (@lem5041764 A B _64770 u f t x' h1)). Qed.
Lemma lem5042613 {A B : Type'} (_64770 : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term784 A B x' u t f _64770.
Proof. exact (@lem5042612 A B _64770 u f t x' h1). Qed.
Lemma lem5042614 {A B : Type'} (x''' : B -> A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term581 A B u f t x') : term787 A B u t f x''' x'.
Proof. exact (@lem5042613 A B (x''' x') u f t x' h1). Qed.
Lemma lem5042617 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : False.
Proof. exact (@lem5042614 A B x''' u f t x' h1 (@lem5042610 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042618 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : term360.
Proof. exact (fun h0 : ~ False => @lem5042617 A B x' t v u f x''' h1 h2). Qed.
Lemma lem5042620 (p : Prop) : (term358 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5042621 : term360 = False.
Proof. exact (@lem5042620 False). Qed.
Lemma lem5042622 {A B : Type'} (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (x''' : B -> A) (h1 : term581 A B u f t x') (h2 : term552 A B t v u f x''') : False.
Proof. exact (EQ_MP (@lem5042621) (@lem5042618 A B x' t v u f x''' h1 h2)). Qed.
Lemma lem5042623 {A B : Type'} (u : A -> Prop) (f : A -> B) (x'' : A) (t : B -> Prop) (x' : B) (h1 : term632 A B u f x'' t x') : False.
Proof. exact (EQ_MP (@lem5042032) (@lem5042029 A B u f x'' t x' h1)). Qed.
Lemma lem5042624 {A B : Type'} (v : B -> Prop) (x''' : B -> A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term552 A B t v u f x''') (h2 : term666 A B x'' u f t x') : False.
Proof. exact (or_elim (@lem5041498 A B x'' u f t x' h2) (fun h0 : term632 A B u f x'' t x' => @lem5042623 A B u f x'' t x' h0) (fun h0 : term581 A B u f t x' => @lem5042622 A B x' t v u f x''' h0 h1)). Qed.
Lemma lem5042625 {A B : Type'} (v : B -> Prop) (x''' : B -> A) (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term552 A B t v u f x''') (h2 : term708 A B x x'' u f t x') : False.
Proof. exact (or_elim (@lem5041448 A B x x'' u f t x' h2) (fun h0 : term557 A B t f u x => @lem5041954 A B t f u x h0) (fun h0 : term666 A B x'' u f t x' => @lem5042624 A B v x''' x'' u f t x' h1 h0)). Qed.
Lemma lem5042626 {A B : Type'} (v : B -> Prop) (x''' : B -> A) (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term552 A B t v u f x''') (h2 : term708 A B x x'' u f t x') : (term552 A B t v u f x''') = False.
Proof. exact (prop_ext (fun h3 : term552 A B t v u f x''' => @lem5042625 A B v x''' x x'' u f t x' h1 h2) (fun h3 : False => @lem5041494 A B t v u f x''' h1)). Qed.
Lemma lem5042627 {A B : Type'} (v : B -> Prop) (x''' : B -> A) (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term552 A B t v u f x''') (h2 : term708 A B x x'' u f t x') : False.
Proof. exact (EQ_MP (@lem5042626 A B v x''' x x'' u f t x' h1 h2) (@lem5041494 A B t v u f x''' h1)). Qed.
Lemma lem5042628 {A B : Type'} (v : B -> Prop) (x''' : B -> A) (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term552 A B t v u f x''') (h2 : term708 A B x x'' u f t x') : (term708 A B x x'' u f t x') = False.
Proof. exact (prop_ext (fun h3 : term708 A B x x'' u f t x' => @lem5042627 A B v x''' x x'' u f t x' h1 h2) (fun h3 : False => @lem5041448 A B x x'' u f t x' h2)). Qed.
Lemma lem5042629 {A B : Type'} (v : B -> Prop) (x''' : B -> A) (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term552 A B t v u f x''') (h2 : term708 A B x x'' u f t x') : False.
Proof. exact (EQ_MP (@lem5042628 A B v x''' x x'' u f t x' h1 h2) (@lem5041448 A B x x'' u f t x' h2)). Qed.
Lemma lem5042630 {A B : Type'} (v : B -> Prop) (x : A) (x'' : A) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (x' : B) (h1 : term435 A B t v u f) (h2 : term708 A B x x'' u f t x') : False.
Proof. exact (ex_elim (@lem5040849 A B t v u f h1) (fun x''' : B -> A => fun h0 : term554 A B t v u f x''' => @lem5042629 A B v x''' x x'' u f t x' h0 h2)). Qed.
Lemma lem5042631 {A B : Type'} (x : A) (x' : B) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term711 A B x u f t x') (h2 : term435 A B t v u f) : False.
Proof. exact (ex_elim (@lem5041355 A B x u f t x' h1) (fun x'' : A => fun h0 : term710 A B x u f t x' x'' => @lem5042630 A B v x x'' u f t x' h2 h0)). Qed.
Lemma lem5042632 {A B : Type'} (x : A) (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term713 A B x u f t) (h2 : term435 A B t v u f) : False.
Proof. exact (ex_elim (@lem5041354 A B x u f t h1) (fun x' : B => fun h0 : term712 A B x u f t x' => @lem5042631 A B x x' t v u f h0 h2)). Qed.
Lemma lem5042633 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term504 A B u f t) (h2 : term435 A B t v u f) : False.
Proof. exact (ex_elim (@lem5041353 A B u f t h1) (fun x : A => fun h0 : term714 A B u f t x => @lem5042632 A B x t v u f h0 h2)). Qed.
Lemma lem5042634 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term504 A B u f t) (h2 : term435 A B t v u f) : (term504 A B u f t) = False.
Proof. exact (prop_ext (fun h3 : term504 A B u f t => @lem5042633 A B t v u f h1 h2) (fun h3 : False => @lem5040630 A B u f t h1)). Qed.
Lemma lem5042635 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term504 A B u f t) (h2 : term435 A B t v u f) : False.
Proof. exact (EQ_MP (@lem5042634 A B t v u f h1 h2) (@lem5040630 A B u f t h1)). Qed.
Lemma lem5042636 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term435 A B t v u f) : term503 A B u f t.
Proof. exact (fun h0 : term504 A B u f t => @lem5042635 A B t v u f h0 h1). Qed.
Lemma lem5042637 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term435 A B t v u f) : term479 A B u f t.
Proof. exact (EQ_MP (@lem5040629 A B u f t) (@lem5042636 A B t v u f h1)). Qed.
Lemma lem5042638 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term480 A B v u f t.
Proof. exact (fun h0 : term435 A B t v u f => @lem5042637 A B t v u f h0). Qed.
Lemma lem5042643 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term490 A B u f t.
Proof. exact (fun v : B -> Prop => @lem5042638 A B v u f t). Qed.
Lemma lem5042648 {A B : Type'} (f : A -> B) (t : B -> Prop) : term494 A B f t.
Proof. exact (fun u : A -> Prop => @lem5042643 A B u f t). Qed.
Lemma lem5042653 {A B : Type'} (t : B -> Prop) : term498 A B t.
Proof. exact (fun f : A -> B => @lem5042648 A B f t). Qed.
Lemma lem5042658 {A B : Type'} : term502 A B.
Proof. exact (fun t : B -> Prop => @lem5042653 A B t). Qed.
Lemma lem5042659 {A B : Type'} : term501 A B.
Proof. exact (EQ_MP (@lem5040624 A B) (@lem5042658 A B)). Qed.
Lemma lem5042660 {A B : Type'} (t : B -> Prop) : term788 A B t.
Proof. exact (@lem5042659 A B t). Qed.
Lemma lem5042661 {A B : Type'} (t : B -> Prop) : (term788 A B t) = (term497 A B t).
Proof. exact (eq_refl (term788 A B t)). Qed.
Lemma lem5042662 {A B : Type'} (t : B -> Prop) : term497 A B t.
Proof. exact (EQ_MP (@lem5042661 A B t) (@lem5042660 A B t)). Qed.
Lemma lem5042663 {A B : Type'} (t : B -> Prop) (f : A -> B) : term789 A B t f.
Proof. exact (@lem5042662 A B t f). Qed.
Lemma lem5042664 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term789 A B t f) = (term493 A B f t).
Proof. exact (eq_refl (term789 A B t f)). Qed.
Lemma lem5042665 {A B : Type'} (f : A -> B) (t : B -> Prop) : term493 A B f t.
Proof. exact (EQ_MP (@lem5042664 A B f t) (@lem5042663 A B t f)). Qed.
Lemma lem5042666 {A B : Type'} (f : A -> B) (t : B -> Prop) (u : A -> Prop) : term790 A B f t u.
Proof. exact (@lem5042665 A B f t u). Qed.
Lemma lem5042667 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term790 A B f t u) = (term489 A B u f t).
Proof. exact (eq_refl (term790 A B f t u)). Qed.
Lemma lem5042668 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term489 A B u f t.
Proof. exact (EQ_MP (@lem5042667 A B u f t) (@lem5042666 A B f t u)). Qed.
Lemma lem5042669 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (v : B -> Prop) : term791 A B u f t v.
Proof. exact (@lem5042668 A B u f t v). Qed.
Lemma lem5042670 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : (term791 A B u f t v) = (term481 A B v u f t).
Proof. exact (eq_refl (term791 A B u f t v)). Qed.
Lemma lem5042671 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term481 A B v u f t.
Proof. exact (EQ_MP (@lem5042670 A B v u f t) (@lem5042669 A B u f t v)). Qed.
Lemma lem5042673 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term481 A B v u f t.
Proof. exact (@lem5040298 A B v u f t (@lem5042671 A B v u f t)). Qed.
Lemma lem5042674 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term482 A B v u f t) : False.
Proof. exact (@lem5042673 A B v u f t (@lem5040282 A B v u f t h1)). Qed.
Lemma lem5042675 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term482 A B v u f t) : (term482 A B v u f t) = False.
Proof. exact (prop_ext (fun h2 : term482 A B v u f t => @lem5042674 A B v u f t h1) (fun h2 : False => @lem5040282 A B v u f t h1)). Qed.
Lemma lem5042676 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term482 A B v u f t) : False.
Proof. exact (EQ_MP (@lem5042675 A B v u f t h1) (@lem5040282 A B v u f t h1)). Qed.
Lemma lem5042677 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term481 A B v u f t.
Proof. exact (fun h0 : term482 A B v u f t => @lem5042676 A B v u f t h0). Qed.
Lemma lem5042678 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term480 A B v u f t.
Proof. exact (EQ_MP (@lem5040281 A B v u f t) (@lem5042677 A B v u f t)). Qed.
Lemma lem5042679 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term430 A B v u f t.
Proof. exact (EQ_MP (@lem5040277 A B v u f t) (@lem5042678 A B v u f t)). Qed.
Lemma lem5042680 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (t : B -> Prop) : term429 A B v u f t.
Proof. exact (EQ_MP (@lem5040038 A B v u f t) (@lem5042679 A B v u f t)). Qed.
Lemma lem5042681 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (v : B -> Prop) (h1 : term414 A B v u f) (h2 : @SUBSET B t v) : term427 A B u f t.
Proof. exact (@lem5042680 A B v u f t (@lem5039953 A B u f t v h1 h2)). Qed.
Lemma lem5042682 {A B : Type'} (u : A -> Prop) (f : A -> B) (t : B -> Prop) (v : B -> Prop) (h1 : term414 A B v u f) (h2 : @SUBSET B t v) : term792 A B u f t.
Proof. exact (ex_intro (term793 A B u f t) (term422 A B u f t) (@lem5042681 A B u f t v h1 h2)). Qed.
Lemma lem5042683 {A B : Type'} (t : B -> Prop) (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term414 A B v u f) : term794 A B v u f t.
Proof. exact (fun h0 : @SUBSET B t v => @lem5042682 A B u f t v h1 h0). Qed.
Lemma lem5042688 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term414 A B v u f) : term0 A B v u f.
Proof. exact (fun t : B -> Prop => @lem5042683 A B t v u f h1). Qed.
Lemma lem5042689 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : term795 A B v u f.
Proof. exact (fun h0 : term414 A B v u f => @lem5042688 A B v u f h0). Qed.
Lemma lem5042690 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : term796 A B v u f.
Proof. exact (conj (@lem5039940 A B v u f) (@lem5042689 A B v u f)). Qed.
Lemma lem5042691 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term796 A B v u f) = ((term0 A B v u f) = (term414 A B v u f)).
Proof. exact (@lem32 (term0 A B v u f) (term414 A B v u f)). Qed.
Lemma lem5042692 {A B : Type'} (v : B -> Prop) (u : A -> Prop) (f : A -> B) : (term0 A B v u f) = (term414 A B v u f).
Proof. exact (EQ_MP (@lem5042691 A B v u f) (@lem5042690 A B v u f)). Qed.
Lemma lem5042697 {A B : Type'} (u : A -> Prop) (f : A -> B) : term797 A B u f.
Proof. exact (fun v : B -> Prop => @lem5042692 A B v u f). Qed.
Lemma lem5042702 {A B : Type'} (f : A -> B) : term798 A B f.
Proof. exact (fun u : A -> Prop => @lem5042697 A B u f). Qed.
Lemma lem5042707 {A B : Type'} : term799 A B.
Proof. exact (fun f : A -> B => @lem5042702 A B f). Qed.
