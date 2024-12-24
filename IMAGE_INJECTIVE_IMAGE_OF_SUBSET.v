Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_INJECTIVE_IMAGE_OF_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SURJECTIVE_ON_RIGHT_INVERSE_spec.
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
Require Import thm18392_spec.
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
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3588681 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (h1 : (term0 _91307 _91308 t s f) = (term1 _91307 _91308 t s f)) : (term0 _91307 _91308 t s f) = (term1 _91307 _91308 t s f).
Proof. exact (h1). Qed.
Lemma lem3588682 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (h1 : (term0 _91307 _91308 t s f) = (term1 _91307 _91308 t s f)) : (term1 _91307 _91308 t s f) = (term0 _91307 _91308 t s f).
Proof. exact (SYM (@lem3588681 _91307 _91308 t s f h1)). Qed.
Lemma lem3588683 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (h1 : (term1 _91307 _91308 t s f) = (term0 _91307 _91308 t s f)) : (term1 _91307 _91308 t s f) = (term0 _91307 _91308 t s f).
Proof. exact (h1). Qed.
Lemma lem3588684 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (h1 : (term1 _91307 _91308 t s f) = (term0 _91307 _91308 t s f)) : (term0 _91307 _91308 t s f) = (term1 _91307 _91308 t s f).
Proof. exact (SYM (@lem3588683 _91307 _91308 t s f h1)). Qed.
Lemma lem3588685 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term0 _91307 _91308 t s f) = (term1 _91307 _91308 t s f)) = ((term1 _91307 _91308 t s f) = (term0 _91307 _91308 t s f)).
Proof. exact (prop_ext (fun h1 : (term0 _91307 _91308 t s f) = (term1 _91307 _91308 t s f) => @lem3588682 _91307 _91308 t s f h1) (fun h1 : (term1 _91307 _91308 t s f) = (term0 _91307 _91308 t s f) => @lem3588684 _91307 _91308 t s f h1)). Qed.
Lemma lem3588686 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term2 _91307 _91308 s f) = (term3 _91307 _91308 s f).
Proof. exact (fun_ext (fun t : _91308 -> Prop => @lem3588685 _91307 _91308 t s f)). Qed.
Lemma lem3588687 {_91308 : Type'} : (@all (_91308 -> Prop)) = (@all (_91308 -> Prop)).
Proof. exact (eq_refl (@all (_91308 -> Prop))). Qed.
Lemma lem3588688 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term4 _91307 _91308 s f) = (term5 _91307 _91308 s f).
Proof. exact (MK_COMB (@lem3588687 _91308) (@lem3588686 _91307 _91308 s f)). Qed.
Lemma lem3588689 {_91307 _91308 : Type'} (s : _91307 -> Prop) : (term6 _91307 _91308 s) = (term7 _91307 _91308 s).
Proof. exact (fun_ext (fun f : _91307 -> _91308 => @lem3588688 _91307 _91308 s f)). Qed.
Lemma lem3588690 {_91307 _91308 : Type'} : (@all (_91307 -> _91308)) = (@all (_91307 -> _91308)).
Proof. exact (eq_refl (@all (_91307 -> _91308))). Qed.
Lemma lem3588691 {_91307 _91308 : Type'} (s : _91307 -> Prop) : (term8 _91307 _91308 s) = (term9 _91307 _91308 s).
Proof. exact (MK_COMB (@lem3588690 _91307 _91308) (@lem3588689 _91307 _91308 s)). Qed.
Lemma lem3588692 {_91307 _91308 : Type'} (s : _91307 -> Prop) : term9 _91307 _91308 s.
Proof. exact (EQ_MP (@lem3588691 _91307 _91308 s) (@lem3562737 _91307 _91308 s)). Qed.
Lemma lem3588693 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term10 _91307 _91308 s f.
Proof. exact (@lem3588692 _91307 _91308 s f). Qed.
Lemma lem3588694 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term10 _91307 _91308 s f) = (term5 _91307 _91308 s f).
Proof. exact (eq_refl (term10 _91307 _91308 s f)). Qed.
Lemma lem3588695 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term5 _91307 _91308 s f.
Proof. exact (EQ_MP (@lem3588694 _91307 _91308 s f) (@lem3588693 _91307 _91308 s f)). Qed.
Lemma lem3588696 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (t : _91308 -> Prop) : term11 _91307 _91308 s f t.
Proof. exact (@lem3588695 _91307 _91308 s f t). Qed.
Lemma lem3588697 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term11 _91307 _91308 s f t) = ((term1 _91307 _91308 t s f) = (term0 _91307 _91308 t s f)).
Proof. exact (eq_refl (term11 _91307 _91308 s f t)). Qed.
Lemma lem3588699 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term12 A B s f) : term12 A B s f.
Proof. exact (h1). Qed.
Lemma lem3588700 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term13 A B s f g) : term13 A B s f g.
Proof. exact (h1). Qed.
Lemma lem3588702 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term1 _91307 _91308 t s f) = (term0 _91307 _91308 t s f).
Proof. exact (EQ_MP (@lem3588697 _91307 _91308 t s f) (@lem3588696 _91307 _91308 s f t)). Qed.
Lemma lem3588703 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term1 A B t s f) = (term0 A B t s f).
Proof. exact (@lem3588702 A B t s f). Qed.
Lemma lem3588704 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term12 A B s f) = (term14 A B s f).
Proof. exact (@lem3588703 A B (@IMAGE A B f s) s f). Qed.
Lemma lem3588719 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B s f) = (term12 A B s f).
Proof. exact (SYM (@lem3588704 A B s f)). Qed.
Lemma lem3588745 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3588746 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3588745 A B y f s). Qed.
Lemma lem3588756 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3588757 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3588756 A P x). Qed.
Lemma lem3588758 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3588757 A s x). Qed.
Lemma lem3588759 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term17 A B y f x) = (term17 A B y f x).
Proof. exact (eq_refl (term17 A B y f x)). Qed.
Lemma lem3588760 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term18 A B y f x s) = (term19 A B y f s x).
Proof. exact (MK_COMB (@lem3588759 A B y f x) (@lem3588758 A s x)). Qed.
Lemma lem3588763 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term20 A B y f s) = (term21 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3588760 A B y f s x)). Qed.
Lemma lem3588764 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588765 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y f s) = (term22 A B y f s).
Proof. exact (MK_COMB (@lem3588764 A) (@lem3588763 A B y f s)). Qed.
Lemma lem3588770 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term22 A B y f s).
Proof. exact (TRANS (@lem3588746 A B y f s) (@lem3588765 A B y f s)). Qed.
Lemma lem3588771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3588772 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term23 A B y f s) = (term24 A B y f s).
Proof. exact (MK_COMB (@lem3588771) (@lem3588770 A B y f s)). Qed.
Lemma lem3588780 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3588781 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3588780 A P x). Qed.
Lemma lem3588782 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3588781 A s x). Qed.
Lemma lem3588783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3588784 {A : Type'} (s : A -> Prop) (x : A) : (term25 A x s) = (term26 A s x).
Proof. exact (MK_COMB (@lem3588783) (@lem3588782 A s x)). Qed.
Lemma lem3588787 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3588788 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term27 A B s f x y) = (term28 A B s f x y).
Proof. exact (MK_COMB (@lem3588784 A s x) (@lem3588787 A B f x y)). Qed.
Lemma lem3588791 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term29 A B s f y) = (term30 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem3588788 A B s f x y)). Qed.
Lemma lem3588792 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588793 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term31 A B s f y) = (term32 A B s f y).
Proof. exact (MK_COMB (@lem3588792 A) (@lem3588791 A B s f y)). Qed.
Lemma lem3588798 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term33 A B s f y) = (term34 A B s f y).
Proof. exact (MK_COMB (@lem3588772 A B y f s) (@lem3588793 A B s f y)). Qed.
Lemma lem3588801 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term35 A B s f) = (term36 A B s f).
Proof. exact (fun_ext (fun y : B => @lem3588798 A B s f y)). Qed.
Lemma lem3588802 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588803 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B s f) = (term37 A B s f).
Proof. exact (MK_COMB (@lem3588802 B) (@lem3588801 A B s f)). Qed.
Lemma lem3588808 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term37 A B s f) = (term14 A B s f).
Proof. exact (SYM (@lem3588803 A B s f)). Qed.
Lemma lem3588810 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3588811 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term37 A B s f) = (term39 A B s f).
Proof. exact (@lem3588810 (term37 A B s f)). Qed.
Lemma lem3588812 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term39 A B s f) = (term37 A B s f).
Proof. exact (SYM (@lem3588811 A B s f)). Qed.
Lemma lem3588813 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term40 A B s f) : term40 A B s f.
Proof. exact (h1). Qed.
Lemma lem3588816 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term39 A B s f) : term39 A B s f.
Proof. exact (h1). Qed.
Lemma lem3588817 {A B : Type'} (s : A -> Prop) (f : A -> B) : term41 A B s f.
Proof. exact (fun h0 : term39 A B s f => @lem3588816 A B s f h0). Qed.
Lemma lem3588818 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term41 A B s f) : term41 A B s f.
Proof. exact (h1). Qed.
Lemma lem3588819 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term39 A B s f) : term39 A B s f.
Proof. exact (h1). Qed.
Lemma lem3588820 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term39 A B s f) (h2 : term41 A B s f) : term39 A B s f.
Proof. exact (@lem3588818 A B s f h2 (@lem3588819 A B s f h1)). Qed.
Lemma lem3588821 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term39 A B s f) : term42 A B s f.
Proof. exact (fun h0 : term41 A B s f => @lem3588820 A B s f h1 h0). Qed.
Lemma lem3588822 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term41 A B s f) : term41 A B s f.
Proof. exact (h1). Qed.
Lemma lem3588823 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term39 A B s f) (h2 : term41 A B s f) : term39 A B s f.
Proof. exact (@lem3588821 A B s f h1 (@lem3588822 A B s f h2)). Qed.
Lemma lem3588824 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term41 A B s f) : term41 A B s f.
Proof. exact (fun h0 : term39 A B s f => @lem3588823 A B s f h0 h1). Qed.
Lemma lem3588825 {A B : Type'} (s : A -> Prop) (f : A -> B) : term43 A B s f.
Proof. exact (fun h0 : term41 A B s f => @lem3588824 A B s f h0). Qed.
Lemma lem3588828 {A B : Type'} (s : A -> Prop) (f : A -> B) : term41 A B s f.
Proof. exact (@lem3588825 A B s f (@lem3588817 A B s f)). Qed.
Lemma lem3588829 {A B : Type'} (s : A -> Prop) (f : A -> B) : term41 A B s f.
Proof. exact (@lem3588828 A B s f). Qed.
Lemma lem3588839 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3588840 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term39 A B s f) = (term44 A B s f).
Proof. exact (@lem3588839 (term40 A B s f)). Qed.
Lemma lem3588842 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3588843 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term44 A B s f) = (term37 A B s f).
Proof. exact (@lem3588842 (term37 A B s f)). Qed.
Lemma lem3588848 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term39 A B s f) = (term37 A B s f).
Proof. exact (TRANS (@lem3588840 A B s f) (@lem3588843 A B s f)). Qed.
Lemma lem3588915 {A B : Type'} (f : A -> B) : (term46 A B f) = (term47 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3588848 A B s f)). Qed.
Lemma lem3588916 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3588917 {A B : Type'} (f : A -> B) : (term48 A B f) = (term49 A B f).
Proof. exact (MK_COMB (@lem3588916 A) (@lem3588915 A B f)). Qed.
Lemma lem3588922 {A B : Type'} : (term50 A B) = (term51 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3588917 A B f)). Qed.
Lemma lem3588923 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3588932 {A B : Type'} : (term52 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem3588923 A B) (@lem3588922 A B)). Qed.
Lemma lem3588937 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term28 A B s f x y) = (term28 A B s f x y).
Proof. exact (eq_refl (term28 A B s f x y)). Qed.
Lemma lem3588938 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term30 A B s f y) = (term30 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem3588937 A B s f x y)). Qed.
Lemma lem3588939 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588940 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term32 A B s f y) = (term32 A B s f y).
Proof. exact (MK_COMB (@lem3588939 A) (@lem3588938 A B s f y)). Qed.
Lemma lem3588945 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term19 A B y f s x) = (term19 A B y f s x).
Proof. exact (eq_refl (term19 A B y f s x)). Qed.
Lemma lem3588946 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term21 A B y f s) = (term21 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3588945 A B y f s x)). Qed.
Lemma lem3588947 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3588948 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term22 A B y f s) = (term22 A B y f s).
Proof. exact (MK_COMB (@lem3588947 A) (@lem3588946 A B y f s)). Qed.
Lemma lem3588949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3588950 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term24 A B y f s) = (term24 A B y f s).
Proof. exact (MK_COMB (@lem3588949) (@lem3588948 A B y f s)). Qed.
Lemma lem3588951 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term34 A B s f y) = (term34 A B s f y).
Proof. exact (MK_COMB (@lem3588950 A B y f s) (@lem3588940 A B s f y)). Qed.
Lemma lem3588952 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term36 A B s f) = (term36 A B s f).
Proof. exact (fun_ext (fun y : B => @lem3588951 A B s f y)). Qed.
Lemma lem3588953 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3588954 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term37 A B s f) = (term37 A B s f).
Proof. exact (MK_COMB (@lem3588953 B) (@lem3588952 A B s f)). Qed.
Lemma lem3588955 {A B : Type'} (f : A -> B) : (term47 A B f) = (term47 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3588954 A B s f)). Qed.
Lemma lem3588956 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3588957 {A B : Type'} (f : A -> B) : (term49 A B f) = (term49 A B f).
Proof. exact (MK_COMB (@lem3588956 A) (@lem3588955 A B f)). Qed.
Lemma lem3588958 {A B : Type'} : (term51 A B) = (term51 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3588957 A B f)). Qed.
Lemma lem3588959 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3588960 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem3588959 A B) (@lem3588958 A B)). Qed.
Lemma lem3588999 {A B : Type'} : (term52 A B) = (term53 A B).
Proof. exact (TRANS (@lem3588932 A B) (@lem3588960 A B)). Qed.
Lemma lem3589000 {A B : Type'} : (term53 A B) = (term52 A B).
Proof. exact (SYM (@lem3588999 A B)). Qed.
Lemma lem3589001 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (h1 : term22 A B y f s) : term22 A B y f s.
Proof. exact (h1). Qed.
Lemma lem3589003 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3589004 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term32 A B s f y) = (term54 A B s f y).
Proof. exact (@lem3589003 (term32 A B s f y)). Qed.
Lemma lem3589005 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term54 A B s f y) = (term32 A B s f y).
Proof. exact (SYM (@lem3589004 A B s f y)). Qed.
Lemma lem3589006 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term55 A B s f y) : term55 A B s f y.
Proof. exact (h1). Qed.
Lemma lem3589011 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term19 A B y f s x) = (term19 A B y f s x).
Proof. exact (eq_refl (term19 A B y f s x)). Qed.
Lemma lem3589012 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term21 A B y f s) = (term21 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3589011 A B y f s x)). Qed.
Lemma lem3589013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3589050 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term22 A B y f s) = (term22 A B y f s).
Proof. exact (MK_COMB (@lem3589013 A) (@lem3589012 A B y f s)). Qed.
Lemma lem3589051 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (h1 : term22 A B y f s) : term22 A B y f s.
Proof. exact (EQ_MP (@lem3589050 A B y f s) (@lem3589001 A B y f s h1)). Qed.
Lemma lem3589058 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term56 A B s f x y) = (term57 A B s f x y).
Proof. exact (@lem17045 (s x) ((f x) = y)). Qed.
Lemma lem3589059 {A : Type'} (P : A -> Prop) : (term58 A P) = (term59 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3589060 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term55 A B s f y) = (term60 A B s f y).
Proof. exact (@lem3589059 A (term30 A B s f y)). Qed.
Lemma lem3589061 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term61 A B s f y x) = (term28 A B s f x y).
Proof. exact (eq_refl (term61 A B s f y x)). Qed.
Lemma lem3589062 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3589063 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term62 A B s f y x) = (term56 A B s f x y).
Proof. exact (MK_COMB (@lem3589062) (@lem3589061 A B s f x y)). Qed.
Lemma lem3589064 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term62 A B s f y x) = (term57 A B s f x y).
Proof. exact (TRANS (@lem3589063 A B s f x y) (@lem3589058 A B s f x y)). Qed.
Lemma lem3589065 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term63 A B s f y) = (term64 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem3589064 A B s f x y)). Qed.
Lemma lem3589066 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3589067 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term60 A B s f y) = (term65 A B s f y).
Proof. exact (MK_COMB (@lem3589066 A) (@lem3589065 A B s f y)). Qed.
Lemma lem3589120 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term55 A B s f y) = (term65 A B s f y).
Proof. exact (TRANS (@lem3589060 A B s f y) (@lem3589067 A B s f y)). Qed.
Lemma lem3589121 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term55 A B s f y) : term65 A B s f y.
Proof. exact (EQ_MP (@lem3589120 A B s f y) (@lem3589006 A B s f y h1)). Qed.
Lemma lem3589139 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term57 A B s f x y) = (term57 A B s f x y).
Proof. exact (eq_refl (term57 A B s f x y)). Qed.
Lemma lem3589140 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term64 A B s f y) = (term64 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem3589139 A B s f x y)). Qed.
Lemma lem3589141 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3589142 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term65 A B s f y) = (term65 A B s f y).
Proof. exact (MK_COMB (@lem3589141 A) (@lem3589140 A B s f y)). Qed.
Lemma lem3589143 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term55 A B s f y) : term65 A B s f y.
Proof. exact (EQ_MP (@lem3589142 A B s f y) (@lem3589121 A B s f y h1)). Qed.
Lemma lem3589157 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term19 A B y f s x) : term19 A B y f s x.
Proof. exact (h1). Qed.
Lemma lem3589167 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term57 A B s f x y) = (term57 A B s f x y).
Proof. exact (eq_refl (term57 A B s f x y)). Qed.
Lemma lem3589168 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term64 A B s f y) = (term64 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem3589167 A B s f x y)). Qed.
Lemma lem3589169 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3589171 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term65 A B s f y) = (term65 A B s f y).
Proof. exact (MK_COMB (@lem3589169 A) (@lem3589168 A B s f y)). Qed.
Lemma lem3589172 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term55 A B s f y) : term65 A B s f y.
Proof. exact (EQ_MP (@lem3589171 A B s f y) (@lem3589143 A B s f y h1)). Qed.
Lemma lem3589181 {A B : Type'} (_38777 : A) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term55 A B s f y) : term66 A B s f y _38777.
Proof. exact (@lem3589172 A B s f y h1 _38777). Qed.
Lemma lem3589182 {A B : Type'} (s : A -> Prop) (f : A -> B) (_38777 : A) (y : B) : (term66 A B s f y _38777) = (term57 A B s f _38777 y).
Proof. exact (eq_refl (term66 A B s f y _38777)). Qed.
Lemma lem3589189 {A B : Type'} (_38777 : A) (s : A -> Prop) (f : A -> B) (y : B) (h1 : term55 A B s f y) : term57 A B s f _38777 y.
Proof. exact (EQ_MP (@lem3589182 A B s f _38777 y) (@lem3589181 A B _38777 s f y h1)). Qed.
Lemma lem3589191 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term19 A B y f s x) : y = (f x).
Proof. exact (proj1 (@lem3589157 A B y f s x h1)). Qed.
Lemma lem3589208 {A B : Type'} (s : A -> Prop) (f : A -> B) (_38777 : A) : (term67 A B s f _38777) = (term67 A B s f _38777).
Proof. exact (eq_refl (term67 A B s f _38777)). Qed.
Lemma lem3589209 {A B : Type'} (_38777 : A) (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term19 A B y f s x) : (term68 A B s f _38777 y) = (term69 A B s _38777 f x).
Proof. exact (MK_COMB (@lem3589208 A B s f _38777) (@lem3589191 A B y f s x h1)). Qed.
Lemma lem3589210 {A B : Type'} (s : A -> Prop) (_38777 : A) (f : A -> B) (x : A) : (term69 A B s _38777 f x) = (term70 A B s _38777 f x).
Proof. exact (eq_refl (term69 A B s _38777 f x)). Qed.
Lemma lem3589211 {A B : Type'} (s : A -> Prop) (f : A -> B) (_38777 : A) (y : B) : (term71 A B s f _38777 y) = (term71 A B s f _38777 y).
Proof. exact (eq_refl (term71 A B s f _38777 y)). Qed.
Lemma lem3589212 {A B : Type'} (y : B) (s : A -> Prop) (_38777 : A) (f : A -> B) (x : A) : ((term68 A B s f _38777 y) = (term69 A B s _38777 f x)) = ((term68 A B s f _38777 y) = (term70 A B s _38777 f x)).
Proof. exact (MK_COMB (@lem3589211 A B s f _38777 y) (@lem3589210 A B s _38777 f x)). Qed.
Lemma lem3589213 {A B : Type'} (s : A -> Prop) (f : A -> B) (_38777 : A) (y : B) : (term68 A B s f _38777 y) = (term57 A B s f _38777 y).
Proof. exact (eq_refl (term68 A B s f _38777 y)). Qed.
Lemma lem3589214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3589215 {A B : Type'} (s : A -> Prop) (f : A -> B) (_38777 : A) (y : B) : (term71 A B s f _38777 y) = (term72 A B s f _38777 y).
Proof. exact (MK_COMB (@lem3589214) (@lem3589213 A B s f _38777 y)). Qed.
Lemma lem3589216 {A B : Type'} (s : A -> Prop) (_38777 : A) (f : A -> B) (x : A) : (term70 A B s _38777 f x) = (term70 A B s _38777 f x).
Proof. exact (eq_refl (term70 A B s _38777 f x)). Qed.
Lemma lem3589217 {A B : Type'} (y : B) (s : A -> Prop) (_38777 : A) (f : A -> B) (x : A) : ((term68 A B s f _38777 y) = (term70 A B s _38777 f x)) = ((term57 A B s f _38777 y) = (term70 A B s _38777 f x)).
Proof. exact (MK_COMB (@lem3589215 A B s f _38777 y) (@lem3589216 A B s _38777 f x)). Qed.
Lemma lem3589218 {A B : Type'} (y : B) (s : A -> Prop) (_38777 : A) (f : A -> B) (x : A) : ((term68 A B s f _38777 y) = (term69 A B s _38777 f x)) = ((term57 A B s f _38777 y) = (term70 A B s _38777 f x)).
Proof. exact (TRANS (@lem3589212 A B y s _38777 f x) (@lem3589217 A B y s _38777 f x)). Qed.
Lemma lem3589219 {A B : Type'} (_38777 : A) (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term19 A B y f s x) : (term57 A B s f _38777 y) = (term70 A B s _38777 f x).
Proof. exact (EQ_MP (@lem3589218 A B y s _38777 f x) (@lem3589209 A B _38777 y f s x h1)). Qed.
Lemma lem3589220 {A B : Type'} (_38777 : A) (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : term70 A B s _38777 f x.
Proof. exact (EQ_MP (@lem3589219 A B _38777 y f s x h2) (@lem3589189 A B _38777 s f y h1)). Qed.
Lemma lem3589260 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term19 A B y f s x) : s x.
Proof. exact (proj2 (@lem3589157 A B y f s x h1)). Qed.
Lemma lem3589261 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term19 A B y f s x) : term73 A s x.
Proof. exact (fun h0 : term74 A s x => @lem3589260 A B y f s x h1). Qed.
Lemma lem3589263 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3589264 {A : Type'} (s : A -> Prop) (x : A) : (term73 A s x) = (s x).
Proof. exact (@lem3589263 (s x)). Qed.
Lemma lem3589265 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term19 A B y f s x) : s x.
Proof. exact (EQ_MP (@lem3589264 A s x) (@lem3589261 A B y f s x h1)). Qed.
Lemma lem3589267 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3589268 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3589267 B x). Qed.
Lemma lem3589269 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem3589268 B (f x)). Qed.
Lemma lem3589270 {A B : Type'} (f : A -> B) (x : A) : term76 A B f x.
Proof. exact (fun h0 : term77 A B f x => @lem3589269 A B f x). Qed.
Lemma lem3589272 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3589273 {A B : Type'} (f : A -> B) (x : A) : (term76 A B f x) = ((f x) = (f x)).
Proof. exact (@lem3589272 ((f x) = (f x))). Qed.
Lemma lem3589274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3589273 A B f x) (@lem3589270 A B f x)). Qed.
Lemma lem3589276 (a : Prop) (b : Prop) : (term78 a b) = (term79 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3589277 {A B : Type'} (s : A -> Prop) (_38777 : A) (f : A -> B) (x : A) : (term70 A B s _38777 f x) = (term80 A B s _38777 f x).
Proof. exact (@lem3589276 (s _38777) ((f _38777) = (f x))). Qed.
Lemma lem3589279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3589280 {A B : Type'} (s : A -> Prop) (_38777 : A) (f : A -> B) (x : A) : (term80 A B s _38777 f x) = (term81 A B s _38777 f x).
Proof. exact (@lem3589279 (term82 A B s _38777 f x)). Qed.
Lemma lem3589281 {A B : Type'} (s : A -> Prop) (_38777 : A) (f : A -> B) (x : A) : (term70 A B s _38777 f x) = (term81 A B s _38777 f x).
Proof. exact (TRANS (@lem3589277 A B s _38777 f x) (@lem3589280 A B s _38777 f x)). Qed.
Lemma lem3589283 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term19 A B y f s x) : term83 A B s f x.
Proof. exact (conj (@lem3589265 A B y f s x h1) (@lem3589274 A B f x)). Qed.
Lemma lem3589285 {A B : Type'} (_38777 : A) (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : term81 A B s _38777 f x.
Proof. exact (EQ_MP (@lem3589281 A B s _38777 f x) (@lem3589220 A B _38777 y f s x h1 h2)). Qed.
Lemma lem3589286 {A B : Type'} (_38777 : A) (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : term81 A B s _38777 f x.
Proof. exact (@lem3589285 A B _38777 y f s x h1 h2). Qed.
Lemma lem3589287 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : term84 A B s f x.
Proof. exact (@lem3589286 A B x y f s x h1 h2). Qed.
Lemma lem3589290 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : False.
Proof. exact (@lem3589287 A B y f s x h1 h2 (@lem3589283 A B y f s x h2)). Qed.
Lemma lem3589291 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : term85.
Proof. exact (fun h0 : ~ False => @lem3589290 A B y f s x h1 h2). Qed.
Lemma lem3589293 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3589294 : term85 = False.
Proof. exact (@lem3589293 False). Qed.
Lemma lem3589296 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : False.
Proof. exact (EQ_MP (@lem3589294) (@lem3589291 A B y f s x h1 h2)). Qed.
Lemma lem3589297 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : (term19 A B y f s x) = False.
Proof. exact (prop_ext (fun h3 : term19 A B y f s x => @lem3589296 A B y f s x h1 h2) (fun h3 : False => @lem3589157 A B y f s x h2)). Qed.
Lemma lem3589298 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) (h1 : term55 A B s f y) (h2 : term19 A B y f s x) : False.
Proof. exact (EQ_MP (@lem3589297 A B y f s x h1 h2) (@lem3589157 A B y f s x h2)). Qed.
Lemma lem3589299 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term22 A B y f s) (h2 : term55 A B s f y) : False.
Proof. exact (ex_elim (@lem3589051 A B y f s h1) (fun x : A => fun h0 : term21 A B y f s x => @lem3589298 A B y f s x h2 h0)). Qed.
Lemma lem3589300 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term22 A B y f s) (h2 : term55 A B s f y) : (term22 A B y f s) = False.
Proof. exact (prop_ext (fun h3 : term22 A B y f s => @lem3589299 A B s f y h1 h2) (fun h3 : False => @lem3589051 A B y f s h1)). Qed.
Lemma lem3589301 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term22 A B y f s) (h2 : term55 A B s f y) : False.
Proof. exact (EQ_MP (@lem3589300 A B s f y h1 h2) (@lem3589051 A B y f s h1)). Qed.
Lemma lem3589302 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term22 A B y f s) (h2 : term55 A B s f y) : (term55 A B s f y) = False.
Proof. exact (prop_ext (fun h3 : term55 A B s f y => @lem3589301 A B s f y h1 h2) (fun h3 : False => @lem3589006 A B s f y h2)). Qed.
Lemma lem3589303 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (h1 : term22 A B y f s) (h2 : term55 A B s f y) : False.
Proof. exact (EQ_MP (@lem3589302 A B s f y h1 h2) (@lem3589006 A B s f y h2)). Qed.
Lemma lem3589304 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (h1 : term22 A B y f s) : term54 A B s f y.
Proof. exact (fun h0 : term55 A B s f y => @lem3589303 A B s f y h1 h0). Qed.
Lemma lem3589305 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (h1 : term22 A B y f s) : term32 A B s f y.
Proof. exact (EQ_MP (@lem3589005 A B s f y) (@lem3589304 A B y f s h1)). Qed.
Lemma lem3589306 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : term34 A B s f y.
Proof. exact (fun h0 : term22 A B y f s => @lem3589305 A B y f s h0). Qed.
Lemma lem3589311 {A B : Type'} (s : A -> Prop) (f : A -> B) : term37 A B s f.
Proof. exact (fun y : B => @lem3589306 A B s f y). Qed.
Lemma lem3589316 {A B : Type'} (f : A -> B) : term49 A B f.
Proof. exact (fun s : A -> Prop => @lem3589311 A B s f). Qed.
Lemma lem3589321 {A B : Type'} : term53 A B.
Proof. exact (fun f : A -> B => @lem3589316 A B f). Qed.
Lemma lem3589322 {A B : Type'} : term52 A B.
Proof. exact (EQ_MP (@lem3589000 A B) (@lem3589321 A B)). Qed.
Lemma lem3589323 {A B : Type'} (f : A -> B) : term86 A B f.
Proof. exact (@lem3589322 A B f). Qed.
Lemma lem3589324 {A B : Type'} (f : A -> B) : (term86 A B f) = (term48 A B f).
Proof. exact (eq_refl (term86 A B f)). Qed.
Lemma lem3589325 {A B : Type'} (f : A -> B) : term48 A B f.
Proof. exact (EQ_MP (@lem3589324 A B f) (@lem3589323 A B f)). Qed.
Lemma lem3589326 {A B : Type'} (f : A -> B) (s : A -> Prop) : term87 A B f s.
Proof. exact (@lem3589325 A B f s). Qed.
Lemma lem3589327 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term87 A B f s) = (term39 A B s f).
Proof. exact (eq_refl (term87 A B f s)). Qed.
Lemma lem3589328 {A B : Type'} (s : A -> Prop) (f : A -> B) : term39 A B s f.
Proof. exact (EQ_MP (@lem3589327 A B s f) (@lem3589326 A B f s)). Qed.
Lemma lem3589330 {A B : Type'} (s : A -> Prop) (f : A -> B) : term39 A B s f.
Proof. exact (@lem3588829 A B s f (@lem3589328 A B s f)). Qed.
Lemma lem3589331 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term40 A B s f) : False.
Proof. exact (@lem3589330 A B s f (@lem3588813 A B s f h1)). Qed.
Lemma lem3589332 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term40 A B s f) : (term40 A B s f) = False.
Proof. exact (prop_ext (fun h2 : term40 A B s f => @lem3589331 A B s f h1) (fun h2 : False => @lem3588813 A B s f h1)). Qed.
Lemma lem3589333 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term40 A B s f) : False.
Proof. exact (EQ_MP (@lem3589332 A B s f h1) (@lem3588813 A B s f h1)). Qed.
Lemma lem3589334 {A B : Type'} (s : A -> Prop) (f : A -> B) : term39 A B s f.
Proof. exact (fun h0 : term40 A B s f => @lem3589333 A B s f h0). Qed.
Lemma lem3589335 {A B : Type'} (s : A -> Prop) (f : A -> B) : term37 A B s f.
Proof. exact (EQ_MP (@lem3588812 A B s f) (@lem3589334 A B s f)). Qed.
Lemma lem3589337 {A B : Type'} (s : A -> Prop) (f : A -> B) : term14 A B s f.
Proof. exact (EQ_MP (@lem3588808 A B s f) (@lem3589335 A B s f)). Qed.
Lemma lem3589338 {A B : Type'} (s : A -> Prop) (f : A -> B) : term12 A B s f.
Proof. exact (EQ_MP (@lem3588719 A B s f) (@lem3589337 A B s f)). Qed.
Lemma lem3589339 (t1 : Prop) : term88 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3589340 (t1 : Prop) : (term88 t1) = (term89 t1).
Proof. exact (eq_refl (term88 t1)). Qed.
Lemma lem3589341 (t1 : Prop) : term89 t1.
Proof. exact (EQ_MP (@lem3589340 t1) (@lem3589339 t1)). Qed.
Lemma lem3589342 (t1 : Prop) (t2 : Prop) : term90 t1 t2.
Proof. exact (@lem3589341 t1 t2). Qed.
Lemma lem3589343 (t1 : Prop) (t2 : Prop) : (term90 t1 t2) = (term91 t1 t2).
Proof. exact (eq_refl (term90 t1 t2)). Qed.
Lemma lem3589344 (t1 : Prop) (t2 : Prop) : term91 t1 t2.
Proof. exact (EQ_MP (@lem3589343 t1 t2) (@lem3589342 t1 t2)). Qed.
Lemma lem3589345 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term92 t1 t2 t3.
Proof. exact (@lem3589344 t1 t2 t3). Qed.
Lemma lem3589346 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term92 t1 t2 t3) = ((term93 t1 t2 t3) = (term94 t1 t2 t3)).
Proof. exact (eq_refl (term92 t1 t2 t3)). Qed.
Lemma lem3589347 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term93 t1 t2 t3) = (term94 t1 t2 t3).
Proof. exact (EQ_MP (@lem3589346 t1 t2 t3) (@lem3589345 t1 t2 t3)). Qed.
Lemma lem3589348 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term94 t1 t2 t3) = (term93 t1 t2 t3).
Proof. exact (SYM (@lem3589347 t1 t2 t3)). Qed.
Lemma lem3589366 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term95 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3589367 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term95 A s t).
Proof. exact (@lem3589366 A s t). Qed.
Lemma lem3589368 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term96 A B g f s) = (term97 A B g f s).
Proof. exact (@lem3589367 A (term98 A B g f s) s). Qed.
Lemma lem3589375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3589376 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term99 A B g f s) = (term100 A B g f s).
Proof. exact (MK_COMB (@lem3589375) (@lem3589368 A B g f s)). Qed.
Lemma lem3589382 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term101 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3589383 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term101 B s t).
Proof. exact (@lem3589382 B s t). Qed.
Lemma lem3589384 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : ((@IMAGE A B f s) = (term102 A B g f s)) = (term103 A B g f s).
Proof. exact (@lem3589383 B (@IMAGE A B f s) (term102 A B g f s)). Qed.
Lemma lem3589393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3589394 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term104 A B g f s) = (term105 A B g f s).
Proof. exact (MK_COMB (@lem3589393) (@lem3589384 A B g f s)). Qed.
Lemma lem3589417 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term106 A B g s f) = (term106 A B g s f).
Proof. exact (eq_refl (term106 A B g s f)). Qed.
Lemma lem3589418 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term107 A B g s f) = (term108 A B g s f).
Proof. exact (MK_COMB (@lem3589394 A B g f s) (@lem3589417 A B g s f)). Qed.
Lemma lem3589421 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term109 A B g s f) = (term110 A B g s f).
Proof. exact (MK_COMB (@lem3589376 A B g f s) (@lem3589418 A B g s f)). Qed.
Lemma lem3589424 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term111 A B s f g) = (term111 A B s f g).
Proof. exact (eq_refl (term111 A B s f g)). Qed.
Lemma lem3589425 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term112 A B g s f) = (term113 A B g s f).
Proof. exact (MK_COMB (@lem3589424 A B s f g) (@lem3589421 A B g s f)). Qed.
Lemma lem3589428 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term113 A B g s f) = (term112 A B g s f).
Proof. exact (SYM (@lem3589425 A B g s f)). Qed.
Lemma lem3589438 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589439 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3589438 A B y f s). Qed.
Lemma lem3589449 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3589450 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3589449 A P x). Qed.
Lemma lem3589451 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3589450 A s x). Qed.
Lemma lem3589452 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term17 A B y f x) = (term17 A B y f x).
Proof. exact (eq_refl (term17 A B y f x)). Qed.
Lemma lem3589453 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term18 A B y f x s) = (term19 A B y f s x).
Proof. exact (MK_COMB (@lem3589452 A B y f x) (@lem3589451 A s x)). Qed.
Lemma lem3589456 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term20 A B y f s) = (term21 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3589453 A B y f s x)). Qed.
Lemma lem3589457 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3589458 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y f s) = (term22 A B y f s).
Proof. exact (MK_COMB (@lem3589457 A) (@lem3589456 A B y f s)). Qed.
Lemma lem3589463 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term22 A B y f s).
Proof. exact (TRANS (@lem3589439 A B y f s) (@lem3589458 A B y f s)). Qed.
Lemma lem3589464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3589465 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term23 A B y f s) = (term24 A B y f s).
Proof. exact (MK_COMB (@lem3589464) (@lem3589463 A B y f s)). Qed.
Lemma lem3589469 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3589470 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3589469 A P x). Qed.
Lemma lem3589471 {A B : Type'} (s : A -> Prop) (g : B -> A) (y : B) : (term114 A B g y s) = (term115 A B s g y).
Proof. exact (@lem3589470 A s (g y)). Qed.
Lemma lem3589472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3589473 {A B : Type'} (s : A -> Prop) (g : B -> A) (y : B) : (term116 A B g y s) = (term117 A B s g y).
Proof. exact (MK_COMB (@lem3589472) (@lem3589471 A B s g y)). Qed.
Lemma lem3589476 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : ((term118 A B f g y) = y) = ((term118 A B f g y) = y).
Proof. exact (eq_refl ((term118 A B f g y) = y)). Qed.
Lemma lem3589477 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term119 A B s f g y) = (term120 A B s f g y).
Proof. exact (MK_COMB (@lem3589473 A B s g y) (@lem3589476 A B f g y)). Qed.
Lemma lem3589480 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term121 A B s f g y) = (term122 A B s f g y).
Proof. exact (MK_COMB (@lem3589465 A B y f s) (@lem3589477 A B s f g y)). Qed.
Lemma lem3589483 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term123 A B s f g) = (term124 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3589480 A B s f g y)). Qed.
Lemma lem3589484 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3589485 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term13 A B s f g) = (term125 A B s f g).
Proof. exact (MK_COMB (@lem3589484 B) (@lem3589483 A B s f g)). Qed.
Lemma lem3589490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3589491 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term111 A B s f g) = (term126 A B s f g).
Proof. exact (MK_COMB (@lem3589490) (@lem3589485 A B s f g)). Qed.
Lemma lem3589501 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589502 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term127 A B y f s) = (term128 A B y f s).
Proof. exact (@lem3589501 B A y f s). Qed.
Lemma lem3589503 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B x g f s) = (term130 A B x g f s).
Proof. exact (@lem3589502 A B x g (@IMAGE A B f s)). Qed.
Lemma lem3589513 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589514 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3589513 A B y f s). Qed.
Lemma lem3589515 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term16 A B x f s).
Proof. exact (@lem3589514 A B x f s). Qed.
Lemma lem3589525 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3589526 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3589525 A P x). Qed.
Lemma lem3589527 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3589526 A s x). Qed.
Lemma lem3589528 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3589529 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term18 A B x f x' s) = (term19 A B x f s x').
Proof. exact (MK_COMB (@lem3589528 A B x f x') (@lem3589527 A s x')). Qed.
Lemma lem3589532 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term20 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3589529 A B x f s x')). Qed.
Lemma lem3589533 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3589534 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term16 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3589533 A) (@lem3589532 A B x f s)). Qed.
Lemma lem3589539 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term22 A B x f s).
Proof. exact (TRANS (@lem3589515 A B x f s) (@lem3589534 A B x f s)). Qed.
Lemma lem3589540 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3589541 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term132 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3589540 A B x g x') (@lem3589539 A B x' f s)). Qed.
Lemma lem3589544 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term134 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3589541 A B x g x' f s)). Qed.
Lemma lem3589545 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3589546 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term130 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3589545 B) (@lem3589544 A B x g f s)). Qed.
Lemma lem3589551 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B x g f s) = (term136 A B x g f s).
Proof. exact (TRANS (@lem3589503 A B x g f s) (@lem3589546 A B x g f s)). Qed.
Lemma lem3589552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3589553 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term137 A B x g f s) = (term138 A B x g f s).
Proof. exact (MK_COMB (@lem3589552) (@lem3589551 A B x g f s)). Qed.
Lemma lem3589555 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3589556 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3589555 A P x). Qed.
Lemma lem3589557 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3589556 A s x). Qed.
Lemma lem3589558 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term139 A B g f x s) = (term140 A B g f s x).
Proof. exact (MK_COMB (@lem3589553 A B x g f s) (@lem3589557 A s x)). Qed.
Lemma lem3589561 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term141 A B g f s) = (term142 A B g f s).
Proof. exact (fun_ext (fun x : A => @lem3589558 A B g f s x)). Qed.
Lemma lem3589562 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3589563 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term97 A B g f s) = (term143 A B g f s).
Proof. exact (MK_COMB (@lem3589562 A) (@lem3589561 A B g f s)). Qed.
Lemma lem3589568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3589569 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term100 A B g f s) = (term144 A B g f s).
Proof. exact (MK_COMB (@lem3589568) (@lem3589563 A B g f s)). Qed.
Lemma lem3589579 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589580 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3589579 A B y f s). Qed.
Lemma lem3589581 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term16 A B x f s).
Proof. exact (@lem3589580 A B x f s). Qed.
Lemma lem3589591 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3589592 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3589591 A P x). Qed.
Lemma lem3589593 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3589592 A s x). Qed.
Lemma lem3589594 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3589595 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term18 A B x f x' s) = (term19 A B x f s x').
Proof. exact (MK_COMB (@lem3589594 A B x f x') (@lem3589593 A s x')). Qed.
Lemma lem3589598 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term20 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3589595 A B x f s x')). Qed.
Lemma lem3589599 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3589600 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term16 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3589599 A) (@lem3589598 A B x f s)). Qed.
Lemma lem3589605 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term22 A B x f s).
Proof. exact (TRANS (@lem3589581 A B x f s) (@lem3589600 A B x f s)). Qed.
Lemma lem3589606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3589607 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term145 A B x f s) = (term146 A B x f s).
Proof. exact (MK_COMB (@lem3589606) (@lem3589605 A B x f s)). Qed.
Lemma lem3589609 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589610 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3589609 A B y f s). Qed.
Lemma lem3589611 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term147 A B x g f s) = (term148 A B x g f s).
Proof. exact (@lem3589610 A B x f (term98 A B g f s)). Qed.
Lemma lem3589621 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589622 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term127 A B y f s) = (term128 A B y f s).
Proof. exact (@lem3589621 B A y f s). Qed.
Lemma lem3589623 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B x g f s) = (term130 A B x g f s).
Proof. exact (@lem3589622 A B x g (@IMAGE A B f s)). Qed.
Lemma lem3589633 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589634 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3589633 A B y f s). Qed.
Lemma lem3589635 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term16 A B x f s).
Proof. exact (@lem3589634 A B x f s). Qed.
Lemma lem3589645 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3589646 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3589645 A P x). Qed.
Lemma lem3589647 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3589646 A s x). Qed.
Lemma lem3589648 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3589649 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term18 A B x f x' s) = (term19 A B x f s x').
Proof. exact (MK_COMB (@lem3589648 A B x f x') (@lem3589647 A s x')). Qed.
Lemma lem3589652 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term20 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3589649 A B x f s x')). Qed.
Lemma lem3589653 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3589654 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term16 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3589653 A) (@lem3589652 A B x f s)). Qed.
Lemma lem3589659 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term22 A B x f s).
Proof. exact (TRANS (@lem3589635 A B x f s) (@lem3589654 A B x f s)). Qed.
Lemma lem3589660 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3589661 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term132 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3589660 A B x g x') (@lem3589659 A B x' f s)). Qed.
Lemma lem3589664 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term134 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3589661 A B x g x' f s)). Qed.
Lemma lem3589665 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3589666 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term130 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3589665 B) (@lem3589664 A B x g f s)). Qed.
Lemma lem3589671 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B x g f s) = (term136 A B x g f s).
Proof. exact (TRANS (@lem3589623 A B x g f s) (@lem3589666 A B x g f s)). Qed.
Lemma lem3589672 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3589673 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term149 A B x x' g f s) = (term150 A B x x' g f s).
Proof. exact (MK_COMB (@lem3589672 A B x f x') (@lem3589671 A B x' g f s)). Qed.
Lemma lem3589676 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term151 A B x g f s) = (term152 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3589673 A B x x' g f s)). Qed.
Lemma lem3589677 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3589678 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term148 A B x g f s) = (term153 A B x g f s).
Proof. exact (MK_COMB (@lem3589677 A) (@lem3589676 A B x g f s)). Qed.
Lemma lem3589683 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term147 A B x g f s) = (term153 A B x g f s).
Proof. exact (TRANS (@lem3589611 A B x g f s) (@lem3589678 A B x g f s)). Qed.
Lemma lem3589684 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term15 A B x f s) = (term147 A B x g f s)) = ((term22 A B x f s) = (term153 A B x g f s)).
Proof. exact (MK_COMB (@lem3589607 A B x f s) (@lem3589683 A B x g f s)). Qed.
Lemma lem3589687 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term154 A B g f s) = (term155 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3589684 A B x g f s)). Qed.
Lemma lem3589688 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3589689 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term103 A B g f s) = (term156 A B g f s).
Proof. exact (MK_COMB (@lem3589688 B) (@lem3589687 A B g f s)). Qed.
Lemma lem3589694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3589695 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term105 A B g f s) = (term157 A B g f s).
Proof. exact (MK_COMB (@lem3589694) (@lem3589689 A B g f s)). Qed.
Lemma lem3589709 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589710 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term127 A B y f s) = (term128 A B y f s).
Proof. exact (@lem3589709 B A y f s). Qed.
Lemma lem3589711 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B x g f s) = (term130 A B x g f s).
Proof. exact (@lem3589710 A B x g (@IMAGE A B f s)). Qed.
Lemma lem3589721 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589722 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3589721 A B y f s). Qed.
Lemma lem3589723 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term16 A B x f s).
Proof. exact (@lem3589722 A B x f s). Qed.
Lemma lem3589733 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3589734 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3589733 A P x). Qed.
Lemma lem3589735 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3589734 A s x). Qed.
Lemma lem3589736 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3589737 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term18 A B x f x' s) = (term19 A B x f s x').
Proof. exact (MK_COMB (@lem3589736 A B x f x') (@lem3589735 A s x')). Qed.
Lemma lem3589740 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term20 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3589737 A B x f s x')). Qed.
Lemma lem3589741 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3589742 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term16 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3589741 A) (@lem3589740 A B x f s)). Qed.
Lemma lem3589747 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term22 A B x f s).
Proof. exact (TRANS (@lem3589723 A B x f s) (@lem3589742 A B x f s)). Qed.
Lemma lem3589748 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3589749 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term132 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3589748 A B x g x') (@lem3589747 A B x' f s)). Qed.
Lemma lem3589752 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term134 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3589749 A B x g x' f s)). Qed.
Lemma lem3589753 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3589754 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term130 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3589753 B) (@lem3589752 A B x g f s)). Qed.
Lemma lem3589759 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B x g f s) = (term136 A B x g f s).
Proof. exact (TRANS (@lem3589711 A B x g f s) (@lem3589754 A B x g f s)). Qed.
Lemma lem3589760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3589761 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term158 A B x g f s) = (term159 A B x g f s).
Proof. exact (MK_COMB (@lem3589760) (@lem3589759 A B x g f s)). Qed.
Lemma lem3589765 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589766 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term127 A B y f s) = (term128 A B y f s).
Proof. exact (@lem3589765 B A y f s). Qed.
Lemma lem3589767 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B y g f s) = (term130 A B y g f s).
Proof. exact (@lem3589766 A B y g (@IMAGE A B f s)). Qed.
Lemma lem3589777 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3589778 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (@lem3589777 A B y f s). Qed.
Lemma lem3589779 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term16 A B x f s).
Proof. exact (@lem3589778 A B x f s). Qed.
Lemma lem3589789 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3589790 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3589789 A P x). Qed.
Lemma lem3589791 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3589790 A s x). Qed.
Lemma lem3589792 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3589793 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term18 A B x f x' s) = (term19 A B x f s x').
Proof. exact (MK_COMB (@lem3589792 A B x f x') (@lem3589791 A s x')). Qed.
Lemma lem3589796 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term20 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3589793 A B x f s x')). Qed.
Lemma lem3589797 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3589798 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term16 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3589797 A) (@lem3589796 A B x f s)). Qed.
Lemma lem3589803 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term15 A B x f s) = (term22 A B x f s).
Proof. exact (TRANS (@lem3589779 A B x f s) (@lem3589798 A B x f s)). Qed.
Lemma lem3589804 {A B : Type'} (y : A) (g : B -> A) (x : B) : (term131 A B y g x) = (term131 A B y g x).
Proof. exact (eq_refl (term131 A B y g x)). Qed.
Lemma lem3589805 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B y g x f s) = (term133 A B y g x f s).
Proof. exact (MK_COMB (@lem3589804 A B y g x) (@lem3589803 A B x f s)). Qed.
Lemma lem3589808 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term134 A B y g f s) = (term135 A B y g f s).
Proof. exact (fun_ext (fun x : B => @lem3589805 A B y g x f s)). Qed.
Lemma lem3589809 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3589810 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term130 A B y g f s) = (term136 A B y g f s).
Proof. exact (MK_COMB (@lem3589809 B) (@lem3589808 A B y g f s)). Qed.
Lemma lem3589815 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B y g f s) = (term136 A B y g f s).
Proof. exact (TRANS (@lem3589767 A B y g f s) (@lem3589810 A B y g f s)). Qed.
Lemma lem3589816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3589817 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term158 A B y g f s) = (term159 A B y g f s).
Proof. exact (MK_COMB (@lem3589816) (@lem3589815 A B y g f s)). Qed.
Lemma lem3589820 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3589821 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term160 A B g s x f y) = (term161 A B g s x f y).
Proof. exact (MK_COMB (@lem3589817 A B y g f s) (@lem3589820 A B x f y)). Qed.
Lemma lem3589824 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term162 A B g s x f y) = (term163 A B g s x f y).
Proof. exact (MK_COMB (@lem3589761 A B x g f s) (@lem3589821 A B g s x f y)). Qed.
Lemma lem3589827 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3589828 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term164 A B g s x f y) = (term165 A B g s x f y).
Proof. exact (MK_COMB (@lem3589827) (@lem3589824 A B g s x f y)). Qed.
Lemma lem3589831 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3589832 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term166 A B g s f x y) = (term167 A B g s f x y).
Proof. exact (MK_COMB (@lem3589828 A B g s x f y) (@lem3589831 A x y)). Qed.
Lemma lem3589835 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term168 A B g s f x) = (term169 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3589832 A B g s f x y)). Qed.
Lemma lem3589836 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3589837 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term170 A B g s f x) = (term171 A B g s f x).
Proof. exact (MK_COMB (@lem3589836 A) (@lem3589835 A B g s f x)). Qed.
Lemma lem3589842 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term172 A B g s f) = (term173 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3589837 A B g s f x)). Qed.
Lemma lem3589843 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3589844 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term106 A B g s f) = (term174 A B g s f).
Proof. exact (MK_COMB (@lem3589843 A) (@lem3589842 A B g s f)). Qed.
Lemma lem3589849 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term108 A B g s f) = (term175 A B g s f).
Proof. exact (MK_COMB (@lem3589695 A B g f s) (@lem3589844 A B g s f)). Qed.
Lemma lem3589852 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term110 A B g s f) = (term176 A B g s f).
Proof. exact (MK_COMB (@lem3589569 A B g f s) (@lem3589849 A B g s f)). Qed.
Lemma lem3589855 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term113 A B g s f) = (term177 A B g s f).
Proof. exact (MK_COMB (@lem3589491 A B s f g) (@lem3589852 A B g s f)). Qed.
Lemma lem3589858 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term177 A B g s f) = (term113 A B g s f).
Proof. exact (SYM (@lem3589855 A B g s f)). Qed.
Lemma lem3589860 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3589861 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term177 A B g s f) = (term178 A B g s f).
Proof. exact (@lem3589860 (term177 A B g s f)). Qed.
Lemma lem3589862 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term178 A B g s f) = (term177 A B g s f).
Proof. exact (SYM (@lem3589861 A B g s f)). Qed.
Lemma lem3589863 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term179 A B g s f) : term179 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3589866 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term178 A B g s f) : term178 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3589867 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term180 A B g s f.
Proof. exact (fun h0 : term178 A B g s f => @lem3589866 A B g s f h0). Qed.
Lemma lem3589868 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term180 A B g s f) : term180 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3589869 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term178 A B g s f) : term178 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3589870 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term178 A B g s f) (h2 : term180 A B g s f) : term178 A B g s f.
Proof. exact (@lem3589868 A B g s f h2 (@lem3589869 A B g s f h1)). Qed.
Lemma lem3589871 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term178 A B g s f) : term181 A B g s f.
Proof. exact (fun h0 : term180 A B g s f => @lem3589870 A B g s f h1 h0). Qed.
Lemma lem3589872 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term180 A B g s f) : term180 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3589873 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term178 A B g s f) (h2 : term180 A B g s f) : term178 A B g s f.
Proof. exact (@lem3589871 A B g s f h1 (@lem3589872 A B g s f h2)). Qed.
Lemma lem3589874 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term180 A B g s f) : term180 A B g s f.
Proof. exact (fun h0 : term178 A B g s f => @lem3589873 A B g s f h0 h1). Qed.
Lemma lem3589875 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term182 A B g s f.
Proof. exact (fun h0 : term180 A B g s f => @lem3589874 A B g s f h0). Qed.
Lemma lem3589878 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term180 A B g s f.
Proof. exact (@lem3589875 A B g s f (@lem3589867 A B g s f)). Qed.
Lemma lem3589879 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term180 A B g s f.
Proof. exact (@lem3589878 A B g s f). Qed.
Lemma lem3589893 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3589894 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term178 A B g s f) = (term183 A B g s f).
Proof. exact (@lem3589893 (term179 A B g s f)). Qed.
Lemma lem3589896 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3589897 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term183 A B g s f) = (term177 A B g s f).
Proof. exact (@lem3589896 (term177 A B g s f)). Qed.
Lemma lem3589900 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term178 A B g s f) = (term177 A B g s f).
Proof. exact (TRANS (@lem3589894 A B g s f) (@lem3589897 A B g s f)). Qed.
Lemma lem3590391 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term184 A B s f) = (term185 A B s f).
Proof. exact (fun_ext (fun g : B -> A => @lem3589900 A B g s f)). Qed.
Lemma lem3590392 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem3590393 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term186 A B s f) = (term187 A B s f).
Proof. exact (MK_COMB (@lem3590392 A B) (@lem3590391 A B s f)). Qed.
Lemma lem3590398 {A B : Type'} (f : A -> B) : (term188 A B f) = (term189 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3590393 A B s f)). Qed.
Lemma lem3590399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3590400 {A B : Type'} (f : A -> B) : (term190 A B f) = (term191 A B f).
Proof. exact (MK_COMB (@lem3590399 A) (@lem3590398 A B f)). Qed.
Lemma lem3590405 {A B : Type'} : (term192 A B) = (term193 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3590400 A B f)). Qed.
Lemma lem3590406 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3590415 {A B : Type'} : (term194 A B) = (term195 A B).
Proof. exact (MK_COMB (@lem3590406 A B) (@lem3590405 A B)). Qed.
Lemma lem3590416 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3590417 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3590422 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3590423 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590422 A B x f s x')). Qed.
Lemma lem3590424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590425 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3590424 A) (@lem3590423 A B x f s)). Qed.
Lemma lem3590428 {A B : Type'} (y : A) (g : B -> A) (x : B) : (term131 A B y g x) = (term131 A B y g x).
Proof. exact (eq_refl (term131 A B y g x)). Qed.
Lemma lem3590429 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term133 A B y g x f s) = (term133 A B y g x f s).
Proof. exact (MK_COMB (@lem3590428 A B y g x) (@lem3590425 A B x f s)). Qed.
Lemma lem3590430 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B y g f s) = (term135 A B y g f s).
Proof. exact (fun_ext (fun x : B => @lem3590429 A B y g x f s)). Qed.
Lemma lem3590431 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3590432 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B y g f s) = (term136 A B y g f s).
Proof. exact (MK_COMB (@lem3590431 B) (@lem3590430 A B y g f s)). Qed.
Lemma lem3590433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3590434 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B y g f s) = (term159 A B y g f s).
Proof. exact (MK_COMB (@lem3590433) (@lem3590432 A B y g f s)). Qed.
Lemma lem3590435 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term161 A B g s x f y) = (term161 A B g s x f y).
Proof. exact (MK_COMB (@lem3590434 A B y g f s) (@lem3590417 A B x f y)). Qed.
Lemma lem3590440 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3590441 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590440 A B x f s x')). Qed.
Lemma lem3590442 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590443 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3590442 A) (@lem3590441 A B x f s)). Qed.
Lemma lem3590446 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3590447 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3590446 A B x g x') (@lem3590443 A B x' f s)). Qed.
Lemma lem3590448 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3590447 A B x g x' f s)). Qed.
Lemma lem3590449 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3590450 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3590449 B) (@lem3590448 A B x g f s)). Qed.
Lemma lem3590451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3590452 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B x g f s) = (term159 A B x g f s).
Proof. exact (MK_COMB (@lem3590451) (@lem3590450 A B x g f s)). Qed.
Lemma lem3590453 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term163 A B g s x f y) = (term163 A B g s x f y).
Proof. exact (MK_COMB (@lem3590452 A B x g f s) (@lem3590435 A B g s x f y)). Qed.
Lemma lem3590454 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3590455 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term165 A B g s x f y) = (term165 A B g s x f y).
Proof. exact (MK_COMB (@lem3590454) (@lem3590453 A B g s x f y)). Qed.
Lemma lem3590456 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term167 A B g s f x y) = (term167 A B g s f x y).
Proof. exact (MK_COMB (@lem3590455 A B g s x f y) (@lem3590416 A x y)). Qed.
Lemma lem3590457 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term169 A B g s f x) = (term169 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3590456 A B g s f x y)). Qed.
Lemma lem3590458 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3590459 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term171 A B g s f x) = (term171 A B g s f x).
Proof. exact (MK_COMB (@lem3590458 A) (@lem3590457 A B g s f x)). Qed.
Lemma lem3590460 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term173 A B g s f) = (term173 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3590459 A B g s f x)). Qed.
Lemma lem3590461 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3590462 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term174 A B g s f) = (term174 A B g s f).
Proof. exact (MK_COMB (@lem3590461 A) (@lem3590460 A B g s f)). Qed.
Lemma lem3590467 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3590468 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590467 A B x f s x')). Qed.
Lemma lem3590469 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590470 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3590469 A) (@lem3590468 A B x f s)). Qed.
Lemma lem3590473 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3590474 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3590473 A B x g x') (@lem3590470 A B x' f s)). Qed.
Lemma lem3590475 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3590474 A B x g x' f s)). Qed.
Lemma lem3590476 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3590477 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3590476 B) (@lem3590475 A B x g f s)). Qed.
Lemma lem3590480 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3590481 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term150 A B x x' g f s) = (term150 A B x x' g f s).
Proof. exact (MK_COMB (@lem3590480 A B x f x') (@lem3590477 A B x' g f s)). Qed.
Lemma lem3590482 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term152 A B x g f s) = (term152 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3590481 A B x x' g f s)). Qed.
Lemma lem3590483 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590484 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term153 A B x g f s) = (term153 A B x g f s).
Proof. exact (MK_COMB (@lem3590483 A) (@lem3590482 A B x g f s)). Qed.
Lemma lem3590489 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3590490 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590489 A B x f s x')). Qed.
Lemma lem3590491 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590492 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3590491 A) (@lem3590490 A B x f s)). Qed.
Lemma lem3590493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3590494 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term146 A B x f s) = (term146 A B x f s).
Proof. exact (MK_COMB (@lem3590493) (@lem3590492 A B x f s)). Qed.
Lemma lem3590495 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term22 A B x f s) = (term153 A B x g f s)) = ((term22 A B x f s) = (term153 A B x g f s)).
Proof. exact (MK_COMB (@lem3590494 A B x f s) (@lem3590484 A B x g f s)). Qed.
Lemma lem3590496 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term155 A B g f s) = (term155 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3590495 A B x g f s)). Qed.
Lemma lem3590497 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3590498 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term156 A B g f s) = (term156 A B g f s).
Proof. exact (MK_COMB (@lem3590497 B) (@lem3590496 A B g f s)). Qed.
Lemma lem3590499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3590500 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term157 A B g f s) = (term157 A B g f s).
Proof. exact (MK_COMB (@lem3590499) (@lem3590498 A B g f s)). Qed.
Lemma lem3590501 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term175 A B g s f) = (term175 A B g s f).
Proof. exact (MK_COMB (@lem3590500 A B g f s) (@lem3590462 A B g s f)). Qed.
Lemma lem3590502 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3590507 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3590508 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590507 A B x f s x')). Qed.
Lemma lem3590509 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590510 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3590509 A) (@lem3590508 A B x f s)). Qed.
Lemma lem3590513 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3590514 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3590513 A B x g x') (@lem3590510 A B x' f s)). Qed.
Lemma lem3590515 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3590514 A B x g x' f s)). Qed.
Lemma lem3590516 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3590517 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3590516 B) (@lem3590515 A B x g f s)). Qed.
Lemma lem3590518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3590519 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term138 A B x g f s) = (term138 A B x g f s).
Proof. exact (MK_COMB (@lem3590518) (@lem3590517 A B x g f s)). Qed.
Lemma lem3590520 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term140 A B g f s x) = (term140 A B g f s x).
Proof. exact (MK_COMB (@lem3590519 A B x g f s) (@lem3590502 A s x)). Qed.
Lemma lem3590521 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term142 A B g f s) = (term142 A B g f s).
Proof. exact (fun_ext (fun x : A => @lem3590520 A B g f s x)). Qed.
Lemma lem3590522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3590523 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term143 A B g f s) = (term143 A B g f s).
Proof. exact (MK_COMB (@lem3590522 A) (@lem3590521 A B g f s)). Qed.
Lemma lem3590524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3590525 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term144 A B g f s) = (term144 A B g f s).
Proof. exact (MK_COMB (@lem3590524) (@lem3590523 A B g f s)). Qed.
Lemma lem3590526 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term176 A B g s f) = (term176 A B g s f).
Proof. exact (MK_COMB (@lem3590525 A B g f s) (@lem3590501 A B g s f)). Qed.
Lemma lem3590531 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3590536 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term19 A B y f s x) = (term19 A B y f s x).
Proof. exact (eq_refl (term19 A B y f s x)). Qed.
Lemma lem3590537 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term21 A B y f s) = (term21 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3590536 A B y f s x)). Qed.
Lemma lem3590538 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590539 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term22 A B y f s) = (term22 A B y f s).
Proof. exact (MK_COMB (@lem3590538 A) (@lem3590537 A B y f s)). Qed.
Lemma lem3590540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3590541 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term24 A B y f s) = (term24 A B y f s).
Proof. exact (MK_COMB (@lem3590540) (@lem3590539 A B y f s)). Qed.
Lemma lem3590542 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term122 A B s f g y) = (term122 A B s f g y).
Proof. exact (MK_COMB (@lem3590541 A B y f s) (@lem3590531 A B s f g y)). Qed.
Lemma lem3590543 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term124 A B s f g) = (term124 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3590542 A B s f g y)). Qed.
Lemma lem3590544 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3590545 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term125 A B s f g) = (term125 A B s f g).
Proof. exact (MK_COMB (@lem3590544 B) (@lem3590543 A B s f g)). Qed.
Lemma lem3590546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3590547 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term126 A B s f g) = (term126 A B s f g).
Proof. exact (MK_COMB (@lem3590546) (@lem3590545 A B s f g)). Qed.
Lemma lem3590548 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term177 A B g s f) = (term177 A B g s f).
Proof. exact (MK_COMB (@lem3590547 A B s f g) (@lem3590526 A B g s f)). Qed.
Lemma lem3590549 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term185 A B s f) = (term185 A B s f).
Proof. exact (fun_ext (fun g : B -> A => @lem3590548 A B g s f)). Qed.
Lemma lem3590550 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem3590551 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term187 A B s f) = (term187 A B s f).
Proof. exact (MK_COMB (@lem3590550 A B) (@lem3590549 A B s f)). Qed.
Lemma lem3590552 {A B : Type'} (f : A -> B) : (term189 A B f) = (term189 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3590551 A B s f)). Qed.
Lemma lem3590553 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3590554 {A B : Type'} (f : A -> B) : (term191 A B f) = (term191 A B f).
Proof. exact (MK_COMB (@lem3590553 A) (@lem3590552 A B f)). Qed.
Lemma lem3590555 {A B : Type'} : (term193 A B) = (term193 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3590554 A B f)). Qed.
Lemma lem3590556 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3590557 {A B : Type'} : (term195 A B) = (term195 A B).
Proof. exact (MK_COMB (@lem3590556 A B) (@lem3590555 A B)). Qed.
Lemma lem3590714 {A B : Type'} : (term194 A B) = (term195 A B).
Proof. exact (TRANS (@lem3590415 A B) (@lem3590557 A B)). Qed.
Lemma lem3590715 {A B : Type'} : (term195 A B) = (term194 A B).
Proof. exact (SYM (@lem3590714 A B)). Qed.
Lemma lem3590716 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term125 A B s f g.
Proof. exact (h1). Qed.
Lemma lem3590718 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3590719 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term176 A B g s f) = (term196 A B g s f).
Proof. exact (@lem3590718 (term176 A B g s f)). Qed.
Lemma lem3590720 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term196 A B g s f) = (term176 A B g s f).
Proof. exact (SYM (@lem3590719 A B g s f)). Qed.
Lemma lem3590721 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term197 A B g s f) : term197 A B g s f.
Proof. exact (h1). Qed.
Lemma lem3590728 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term198 A B y f s x) = (term199 A B y f s x).
Proof. exact (@lem17045 (y = (f x)) (s x)). Qed.
Lemma lem3590729 {A : Type'} (P : A -> Prop) : (term58 A P) = (term59 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3590730 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term200 A B y f s) = (term201 A B y f s).
Proof. exact (@lem3590729 A (term21 A B y f s)). Qed.
Lemma lem3590731 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term202 A B y f s x) = (term19 A B y f s x).
Proof. exact (eq_refl (term202 A B y f s x)). Qed.
Lemma lem3590732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3590733 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term203 A B y f s x) = (term198 A B y f s x).
Proof. exact (MK_COMB (@lem3590732) (@lem3590731 A B y f s x)). Qed.
Lemma lem3590734 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term203 A B y f s x) = (term199 A B y f s x).
Proof. exact (TRANS (@lem3590733 A B y f s x) (@lem3590728 A B y f s x)). Qed.
Lemma lem3590735 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term204 A B y f s) = (term205 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3590734 A B y f s x)). Qed.
Lemma lem3590736 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3590737 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term201 A B y f s) = (term206 A B y f s).
Proof. exact (MK_COMB (@lem3590736 A) (@lem3590735 A B y f s)). Qed.
Lemma lem3590738 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term200 A B y f s) = (term206 A B y f s).
Proof. exact (TRANS (@lem3590730 A B y f s) (@lem3590737 A B y f s)). Qed.
Lemma lem3590743 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3590744 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3590745 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term207 A B y f s) = (term208 A B y f s).
Proof. exact (MK_COMB (@lem3590744) (@lem3590738 A B y f s)). Qed.
Lemma lem3590746 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term209 A B s f g y) = (term210 A B s f g y).
Proof. exact (MK_COMB (@lem3590745 A B y f s) (@lem3590743 A B s f g y)). Qed.
Lemma lem3590747 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term122 A B s f g y) = (term209 A B s f g y).
Proof. exact (@lem17265 (term22 A B y f s) (term120 A B s f g y)). Qed.
Lemma lem3590748 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term122 A B s f g y) = (term210 A B s f g y).
Proof. exact (TRANS (@lem3590747 A B s f g y) (@lem3590746 A B s f g y)). Qed.
Lemma lem3590749 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term124 A B s f g) = (term211 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3590748 A B s f g y)). Qed.
Lemma lem3590750 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3590851 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term125 A B s f g) = (term212 A B s f g).
Proof. exact (MK_COMB (@lem3590750 B) (@lem3590749 A B s f g)). Qed.
Lemma lem3590852 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term212 A B s f g.
Proof. exact (EQ_MP (@lem3590851 A B s f g) (@lem3590716 A B s f g h1)). Qed.
Lemma lem3590858 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3590859 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590858 A B x f s x')). Qed.
Lemma lem3590860 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590861 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3590860 A) (@lem3590859 A B x f s)). Qed.
Lemma lem3590863 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3590864 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3590863 A B x g x') (@lem3590861 A B x' f s)). Qed.
Lemma lem3590865 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3590864 A B x g x' f s)). Qed.
Lemma lem3590866 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3590867 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3590866 B) (@lem3590865 A B x g f s)). Qed.
Lemma lem3590868 {A : Type'} (s : A -> Prop) (x : A) : (term74 A s x) = (term74 A s x).
Proof. exact (eq_refl (term74 A s x)). Qed.
Lemma lem3590869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3590870 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B x g f s) = (term159 A B x g f s).
Proof. exact (MK_COMB (@lem3590869) (@lem3590867 A B x g f s)). Qed.
Lemma lem3590871 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term213 A B g f s x) = (term213 A B g f s x).
Proof. exact (MK_COMB (@lem3590870 A B x g f s) (@lem3590868 A s x)). Qed.
Lemma lem3590872 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term214 A B g f s x) = (term213 A B g f s x).
Proof. exact (@lem17362 (term136 A B x g f s) (s x)). Qed.
Lemma lem3590873 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term214 A B g f s x) = (term213 A B g f s x).
Proof. exact (TRANS (@lem3590872 A B g f s x) (@lem3590871 A B g f s x)). Qed.
Lemma lem3590874 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3590875 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term217 A B g f s) = (term218 A B g f s).
Proof. exact (@lem3590874 A (term142 A B g f s)). Qed.
Lemma lem3590876 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term219 A B g f s x) = (term140 A B g f s x).
Proof. exact (eq_refl (term219 A B g f s x)). Qed.
Lemma lem3590877 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3590878 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term220 A B g f s x) = (term214 A B g f s x).
Proof. exact (MK_COMB (@lem3590877) (@lem3590876 A B g f s x)). Qed.
Lemma lem3590879 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term220 A B g f s x) = (term213 A B g f s x).
Proof. exact (TRANS (@lem3590878 A B g f s x) (@lem3590873 A B g f s x)). Qed.
Lemma lem3590880 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term221 A B g f s) = (term222 A B g f s).
Proof. exact (fun_ext (fun x : A => @lem3590879 A B g f s x)). Qed.
Lemma lem3590881 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590882 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term218 A B g f s) = (term223 A B g f s).
Proof. exact (MK_COMB (@lem3590881 A) (@lem3590880 A B g f s)). Qed.
Lemma lem3590883 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term217 A B g f s) = (term223 A B g f s).
Proof. exact (TRANS (@lem3590875 A B g f s) (@lem3590882 A B g f s)). Qed.
Lemma lem3590892 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term198 A B x f s x') = (term199 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3590895 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3590896 {A : Type'} (P : A -> Prop) : (term58 A P) = (term59 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3590897 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term200 A B x f s) = (term201 A B x f s).
Proof. exact (@lem3590896 A (term21 A B x f s)). Qed.
Lemma lem3590898 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3590899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3590900 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term203 A B x f s x') = (term198 A B x f s x').
Proof. exact (MK_COMB (@lem3590899) (@lem3590898 A B x f s x')). Qed.
Lemma lem3590901 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term203 A B x f s x') = (term199 A B x f s x').
Proof. exact (TRANS (@lem3590900 A B x f s x') (@lem3590892 A B x f s x')). Qed.
Lemma lem3590902 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term204 A B x f s) = (term205 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590901 A B x f s x')). Qed.
Lemma lem3590903 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3590904 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term201 A B x f s) = (term206 A B x f s).
Proof. exact (MK_COMB (@lem3590903 A) (@lem3590902 A B x f s)). Qed.
Lemma lem3590905 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term200 A B x f s) = (term206 A B x f s).
Proof. exact (TRANS (@lem3590897 A B x f s) (@lem3590904 A B x f s)). Qed.
Lemma lem3590906 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590895 A B x f s x')). Qed.
Lemma lem3590907 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590908 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3590907 A) (@lem3590906 A B x f s)). Qed.
Lemma lem3590921 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term198 A B x f s x') = (term199 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3590924 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3590925 {A : Type'} (P : A -> Prop) : (term58 A P) = (term59 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3590926 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term200 A B x f s) = (term201 A B x f s).
Proof. exact (@lem3590925 A (term21 A B x f s)). Qed.
Lemma lem3590927 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3590928 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3590929 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term203 A B x f s x') = (term198 A B x f s x').
Proof. exact (MK_COMB (@lem3590928) (@lem3590927 A B x f s x')). Qed.
Lemma lem3590930 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term203 A B x f s x') = (term199 A B x f s x').
Proof. exact (TRANS (@lem3590929 A B x f s x') (@lem3590921 A B x f s x')). Qed.
Lemma lem3590931 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term204 A B x f s) = (term205 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590930 A B x f s x')). Qed.
Lemma lem3590932 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3590933 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term201 A B x f s) = (term206 A B x f s).
Proof. exact (MK_COMB (@lem3590932 A) (@lem3590931 A B x f s)). Qed.
Lemma lem3590934 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term200 A B x f s) = (term206 A B x f s).
Proof. exact (TRANS (@lem3590926 A B x f s) (@lem3590933 A B x f s)). Qed.
Lemma lem3590935 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3590924 A B x f s x')). Qed.
Lemma lem3590936 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590937 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3590936 A) (@lem3590935 A B x f s)). Qed.
Lemma lem3590939 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term224 A B x g x') = (term224 A B x g x').
Proof. exact (eq_refl (term224 A B x g x')). Qed.
Lemma lem3590940 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term225 A B x g x' f s) = (term226 A B x g x' f s).
Proof. exact (MK_COMB (@lem3590939 A B x g x') (@lem3590934 A B x' f s)). Qed.
Lemma lem3590941 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term227 A B x g x' f s) = (term225 A B x g x' f s).
Proof. exact (@lem17045 (x = (g x')) (term22 A B x' f s)). Qed.
Lemma lem3590942 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term227 A B x g x' f s) = (term226 A B x g x' f s).
Proof. exact (TRANS (@lem3590941 A B x g x' f s) (@lem3590940 A B x g x' f s)). Qed.
Lemma lem3590944 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3590945 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3590944 A B x g x') (@lem3590937 A B x' f s)). Qed.
Lemma lem3590946 {B : Type'} (P : B -> Prop) : (term58 B P) = (term59 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3590947 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term228 A B x g f s) = (term229 A B x g f s).
Proof. exact (@lem3590946 B (term135 A B x g f s)). Qed.
Lemma lem3590948 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term230 A B x g f s x') = (term133 A B x g x' f s).
Proof. exact (eq_refl (term230 A B x g f s x')). Qed.
Lemma lem3590949 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3590950 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term231 A B x g f s x') = (term227 A B x g x' f s).
Proof. exact (MK_COMB (@lem3590949) (@lem3590948 A B x g x' f s)). Qed.
Lemma lem3590951 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term231 A B x g f s x') = (term226 A B x g x' f s).
Proof. exact (TRANS (@lem3590950 A B x g x' f s) (@lem3590942 A B x g x' f s)). Qed.
Lemma lem3590952 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term232 A B x g f s) = (term233 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3590951 A B x g x' f s)). Qed.
Lemma lem3590953 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3590954 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term229 A B x g f s) = (term234 A B x g f s).
Proof. exact (MK_COMB (@lem3590953 B) (@lem3590952 A B x g f s)). Qed.
Lemma lem3590955 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term228 A B x g f s) = (term234 A B x g f s).
Proof. exact (TRANS (@lem3590947 A B x g f s) (@lem3590954 A B x g f s)). Qed.
Lemma lem3590956 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3590945 A B x g x' f s)). Qed.
Lemma lem3590957 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3590958 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3590957 B) (@lem3590956 A B x g f s)). Qed.
Lemma lem3590960 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term235 A B x f x') = (term235 A B x f x').
Proof. exact (eq_refl (term235 A B x f x')). Qed.
Lemma lem3590961 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term236 A B x x' g f s) = (term237 A B x x' g f s).
Proof. exact (MK_COMB (@lem3590960 A B x f x') (@lem3590955 A B x' g f s)). Qed.
Lemma lem3590962 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term238 A B x x' g f s) = (term236 A B x x' g f s).
Proof. exact (@lem17045 (x = (f x')) (term136 A B x' g f s)). Qed.
Lemma lem3590963 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term238 A B x x' g f s) = (term237 A B x x' g f s).
Proof. exact (TRANS (@lem3590962 A B x x' g f s) (@lem3590961 A B x x' g f s)). Qed.
Lemma lem3590965 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3590966 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term150 A B x x' g f s) = (term150 A B x x' g f s).
Proof. exact (MK_COMB (@lem3590965 A B x f x') (@lem3590958 A B x' g f s)). Qed.
Lemma lem3590967 {A : Type'} (P : A -> Prop) : (term58 A P) = (term59 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3590968 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term239 A B x g f s) = (term240 A B x g f s).
Proof. exact (@lem3590967 A (term152 A B x g f s)). Qed.
Lemma lem3590969 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term241 A B x g f s x') = (term150 A B x x' g f s).
Proof. exact (eq_refl (term241 A B x g f s x')). Qed.
Lemma lem3590970 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3590971 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term242 A B x g f s x') = (term238 A B x x' g f s).
Proof. exact (MK_COMB (@lem3590970) (@lem3590969 A B x x' g f s)). Qed.
Lemma lem3590972 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term242 A B x g f s x') = (term237 A B x x' g f s).
Proof. exact (TRANS (@lem3590971 A B x x' g f s) (@lem3590963 A B x x' g f s)). Qed.
Lemma lem3590973 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term243 A B x g f s) = (term244 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3590972 A B x x' g f s)). Qed.
Lemma lem3590974 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3590975 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term240 A B x g f s) = (term245 A B x g f s).
Proof. exact (MK_COMB (@lem3590974 A) (@lem3590973 A B x g f s)). Qed.
Lemma lem3590976 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term239 A B x g f s) = (term245 A B x g f s).
Proof. exact (TRANS (@lem3590968 A B x g f s) (@lem3590975 A B x g f s)). Qed.
Lemma lem3590977 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term152 A B x g f s) = (term152 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3590966 A B x x' g f s)). Qed.
Lemma lem3590978 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3590979 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term153 A B x g f s) = (term153 A B x g f s).
Proof. exact (MK_COMB (@lem3590978 A) (@lem3590977 A B x g f s)). Qed.
Lemma lem3590980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3590981 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term246 A B x f s) = (term247 A B x f s).
Proof. exact (MK_COMB (@lem3590980) (@lem3590905 A B x f s)). Qed.
Lemma lem3590982 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term248 A B x g f s) = (term249 A B x g f s).
Proof. exact (MK_COMB (@lem3590981 A B x f s) (@lem3590979 A B x g f s)). Qed.
Lemma lem3590983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3590984 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term250 A B x f s) = (term250 A B x f s).
Proof. exact (MK_COMB (@lem3590983) (@lem3590908 A B x f s)). Qed.
Lemma lem3590985 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term251 A B x g f s) = (term252 A B x g f s).
Proof. exact (MK_COMB (@lem3590984 A B x f s) (@lem3590976 A B x g f s)). Qed.
Lemma lem3590986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3590987 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term253 A B x g f s) = (term254 A B x g f s).
Proof. exact (MK_COMB (@lem3590986) (@lem3590985 A B x g f s)). Qed.
Lemma lem3590988 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term255 A B x g f s) = (term256 A B x g f s).
Proof. exact (MK_COMB (@lem3590987 A B x g f s) (@lem3590982 A B x g f s)). Qed.
Lemma lem3590989 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term257 A B x g f s) = (term255 A B x g f s).
Proof. exact (@lem17646 (term22 A B x f s) (term153 A B x g f s)). Qed.
Lemma lem3590990 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term257 A B x g f s) = (term256 A B x g f s).
Proof. exact (TRANS (@lem3590989 A B x g f s) (@lem3590988 A B x g f s)). Qed.
Lemma lem3590991 {B : Type'} (P : B -> Prop) : (term215 B P) = (term216 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3590992 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term258 A B g f s) = (term259 A B g f s).
Proof. exact (@lem3590991 B (term155 A B g f s)). Qed.
Lemma lem3590993 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term260 A B g f s x) = ((term22 A B x f s) = (term153 A B x g f s)).
Proof. exact (eq_refl (term260 A B g f s x)). Qed.
Lemma lem3590994 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3590995 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term261 A B g f s x) = (term257 A B x g f s).
Proof. exact (MK_COMB (@lem3590994) (@lem3590993 A B x g f s)). Qed.
Lemma lem3590996 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term261 A B g f s x) = (term256 A B x g f s).
Proof. exact (TRANS (@lem3590995 A B x g f s) (@lem3590990 A B x g f s)). Qed.
Lemma lem3590997 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term262 A B g f s) = (term263 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3590996 A B x g f s)). Qed.
Lemma lem3590998 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3590999 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term259 A B g f s) = (term264 A B g f s).
Proof. exact (MK_COMB (@lem3590998 B) (@lem3590997 A B g f s)). Qed.
Lemma lem3591000 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term258 A B g f s) = (term264 A B g f s).
Proof. exact (TRANS (@lem3590992 A B g f s) (@lem3590999 A B g f s)). Qed.
Lemma lem3591006 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3591007 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3591006 A B x f s x')). Qed.
Lemma lem3591008 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591009 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3591008 A) (@lem3591007 A B x f s)). Qed.
Lemma lem3591011 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3591012 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3591011 A B x g x') (@lem3591009 A B x' f s)). Qed.
Lemma lem3591013 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term135 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3591012 A B x g x' f s)). Qed.
Lemma lem3591014 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591015 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3591014 B) (@lem3591013 A B x g f s)). Qed.
Lemma lem3591021 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term19 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term19 A B x f s x')). Qed.
Lemma lem3591022 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term21 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3591021 A B x f s x')). Qed.
Lemma lem3591023 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591024 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term22 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3591023 A) (@lem3591022 A B x f s)). Qed.
Lemma lem3591026 {A B : Type'} (y : A) (g : B -> A) (x : B) : (term131 A B y g x) = (term131 A B y g x).
Proof. exact (eq_refl (term131 A B y g x)). Qed.
Lemma lem3591027 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term133 A B y g x f s) = (term133 A B y g x f s).
Proof. exact (MK_COMB (@lem3591026 A B y g x) (@lem3591024 A B x f s)). Qed.
Lemma lem3591028 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B y g f s) = (term135 A B y g f s).
Proof. exact (fun_ext (fun x : B => @lem3591027 A B y g x f s)). Qed.
Lemma lem3591029 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591030 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B y g f s) = (term136 A B y g f s).
Proof. exact (MK_COMB (@lem3591029 B) (@lem3591028 A B y g f s)). Qed.
Lemma lem3591031 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3591032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591033 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B y g f s) = (term159 A B y g f s).
Proof. exact (MK_COMB (@lem3591032) (@lem3591030 A B y g f s)). Qed.
Lemma lem3591034 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term161 A B g s x f y) = (term161 A B g s x f y).
Proof. exact (MK_COMB (@lem3591033 A B y g f s) (@lem3591031 A B x f y)). Qed.
Lemma lem3591035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591036 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B x g f s) = (term159 A B x g f s).
Proof. exact (MK_COMB (@lem3591035) (@lem3591015 A B x g f s)). Qed.
Lemma lem3591037 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term163 A B g s x f y) = (term163 A B g s x f y).
Proof. exact (MK_COMB (@lem3591036 A B x g f s) (@lem3591034 A B g s x f y)). Qed.
Lemma lem3591038 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3591039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591040 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term266 A B g s x f y) = (term266 A B g s x f y).
Proof. exact (MK_COMB (@lem3591039) (@lem3591037 A B g s x f y)). Qed.
Lemma lem3591041 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term267 A B g s f x y) = (term267 A B g s f x y).
Proof. exact (MK_COMB (@lem3591040 A B g s x f y) (@lem3591038 A x y)). Qed.
Lemma lem3591042 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term268 A B g s f x y) = (term267 A B g s f x y).
Proof. exact (@lem17362 (term163 A B g s x f y) (x = y)). Qed.
Lemma lem3591043 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term268 A B g s f x y) = (term267 A B g s f x y).
Proof. exact (TRANS (@lem3591042 A B g s f x y) (@lem3591041 A B g s f x y)). Qed.
Lemma lem3591044 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3591045 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term269 A B g s f x) = (term270 A B g s f x).
Proof. exact (@lem3591044 A (term169 A B g s f x)). Qed.
Lemma lem3591046 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term271 A B g s f x y) = (term167 A B g s f x y).
Proof. exact (eq_refl (term271 A B g s f x y)). Qed.
Lemma lem3591047 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3591048 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term272 A B g s f x y) = (term268 A B g s f x y).
Proof. exact (MK_COMB (@lem3591047) (@lem3591046 A B g s f x y)). Qed.
Lemma lem3591049 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term272 A B g s f x y) = (term267 A B g s f x y).
Proof. exact (TRANS (@lem3591048 A B g s f x y) (@lem3591043 A B g s f x y)). Qed.
Lemma lem3591050 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term273 A B g s f x) = (term274 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3591049 A B g s f x y)). Qed.
Lemma lem3591051 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591052 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term270 A B g s f x) = (term275 A B g s f x).
Proof. exact (MK_COMB (@lem3591051 A) (@lem3591050 A B g s f x)). Qed.
Lemma lem3591053 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term269 A B g s f x) = (term275 A B g s f x).
Proof. exact (TRANS (@lem3591045 A B g s f x) (@lem3591052 A B g s f x)). Qed.
Lemma lem3591054 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3591055 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term276 A B g s f) = (term277 A B g s f).
Proof. exact (@lem3591054 A (term173 A B g s f)). Qed.
Lemma lem3591056 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term278 A B g s f x) = (term171 A B g s f x).
Proof. exact (eq_refl (term278 A B g s f x)). Qed.
Lemma lem3591057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3591058 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term279 A B g s f x) = (term269 A B g s f x).
Proof. exact (MK_COMB (@lem3591057) (@lem3591056 A B g s f x)). Qed.
Lemma lem3591059 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term279 A B g s f x) = (term275 A B g s f x).
Proof. exact (TRANS (@lem3591058 A B g s f x) (@lem3591053 A B g s f x)). Qed.
Lemma lem3591060 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term280 A B g s f) = (term281 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3591059 A B g s f x)). Qed.
Lemma lem3591061 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591062 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term277 A B g s f) = (term282 A B g s f).
Proof. exact (MK_COMB (@lem3591061 A) (@lem3591060 A B g s f)). Qed.
Lemma lem3591063 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term276 A B g s f) = (term282 A B g s f).
Proof. exact (TRANS (@lem3591055 A B g s f) (@lem3591062 A B g s f)). Qed.
Lemma lem3591064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3591065 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term283 A B g f s) = (term284 A B g f s).
Proof. exact (MK_COMB (@lem3591064) (@lem3591000 A B g f s)). Qed.
Lemma lem3591066 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term285 A B g s f) = (term286 A B g s f).
Proof. exact (MK_COMB (@lem3591065 A B g f s) (@lem3591063 A B g s f)). Qed.
Lemma lem3591067 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term287 A B g s f) = (term285 A B g s f).
Proof. exact (@lem17045 (term156 A B g f s) (term174 A B g s f)). Qed.
Lemma lem3591068 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term287 A B g s f) = (term286 A B g s f).
Proof. exact (TRANS (@lem3591067 A B g s f) (@lem3591066 A B g s f)). Qed.
Lemma lem3591069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3591070 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term288 A B g f s) = (term289 A B g f s).
Proof. exact (MK_COMB (@lem3591069) (@lem3590883 A B g f s)). Qed.
Lemma lem3591071 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term290 A B g s f) = (term291 A B g s f).
Proof. exact (MK_COMB (@lem3591070 A B g f s) (@lem3591068 A B g s f)). Qed.
Lemma lem3591072 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term197 A B g s f) = (term290 A B g s f).
Proof. exact (@lem17045 (term143 A B g f s) (term175 A B g s f)). Qed.
Lemma lem3591073 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term197 A B g s f) = (term291 A B g s f).
Proof. exact (TRANS (@lem3591072 A B g s f) (@lem3591071 A B g s f)). Qed.
Lemma lem3591203 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term292 A P Q) = (term293 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3591204 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term292 B P Q) = (term293 B P Q).
Proof. exact (@lem3591203 B P Q). Qed.
Lemma lem3591205 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term294 A B g f s) = (term295 A B g f s).
Proof. exact (@lem3591204 B (term296 A B g f s) (term297 A B g f s)). Qed.
Lemma lem3591206 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term298 A B g f s x) = (term252 A B x g f s).
Proof. exact (eq_refl (term298 A B g f s x)). Qed.
Lemma lem3591207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3591208 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term299 A B g f s x) = (term254 A B x g f s).
Proof. exact (MK_COMB (@lem3591207) (@lem3591206 A B x g f s)). Qed.
Lemma lem3591209 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term300 A B g f s x) = (term249 A B x g f s).
Proof. exact (eq_refl (term300 A B g f s x)). Qed.
Lemma lem3591210 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term301 A B g f s x) = (term256 A B x g f s).
Proof. exact (MK_COMB (@lem3591208 A B x g f s) (@lem3591209 A B x g f s)). Qed.
Lemma lem3591211 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term302 A B g f s) = (term263 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3591210 A B x g f s)). Qed.
Lemma lem3591212 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591213 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term294 A B g f s) = (term264 A B g f s).
Proof. exact (MK_COMB (@lem3591212 B) (@lem3591211 A B g f s)). Qed.
Lemma lem3591214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3591215 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term303 A B g f s) = (term304 A B g f s).
Proof. exact (MK_COMB (@lem3591214) (@lem3591213 A B g f s)). Qed.
Lemma lem3591216 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term298 A B g f s x) = (term252 A B x g f s).
Proof. exact (eq_refl (term298 A B g f s x)). Qed.
Lemma lem3591217 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term305 A B g f s) = (term296 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3591216 A B x g f s)). Qed.
Lemma lem3591218 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591219 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term306 A B g f s) = (term307 A B g f s).
Proof. exact (MK_COMB (@lem3591218 B) (@lem3591217 A B g f s)). Qed.
Lemma lem3591220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3591221 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term308 A B g f s) = (term309 A B g f s).
Proof. exact (MK_COMB (@lem3591220) (@lem3591219 A B g f s)). Qed.
Lemma lem3591222 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term300 A B g f s x) = (term249 A B x g f s).
Proof. exact (eq_refl (term300 A B g f s x)). Qed.
Lemma lem3591223 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term310 A B g f s) = (term297 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3591222 A B x g f s)). Qed.
Lemma lem3591224 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591225 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term311 A B g f s) = (term312 A B g f s).
Proof. exact (MK_COMB (@lem3591224 B) (@lem3591223 A B g f s)). Qed.
Lemma lem3591226 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term295 A B g f s) = (term313 A B g f s).
Proof. exact (MK_COMB (@lem3591221 A B g f s) (@lem3591225 A B g f s)). Qed.
Lemma lem3591227 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term294 A B g f s) = (term295 A B g f s)) = ((term264 A B g f s) = (term313 A B g f s)).
Proof. exact (MK_COMB (@lem3591215 A B g f s) (@lem3591226 A B g f s)). Qed.
Lemma lem3591228 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term264 A B g f s) = (term313 A B g f s).
Proof. exact (EQ_MP (@lem3591227 A B g f s) (@lem3591205 A B g f s)). Qed.
Lemma lem3591677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3591678 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term284 A B g f s) = (term314 A B g f s).
Proof. exact (MK_COMB (@lem3591677) (@lem3591228 A B g f s)). Qed.
Lemma lem3591891 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term282 A B g s f) = (term282 A B g s f).
Proof. exact (eq_refl (term282 A B g s f)). Qed.
Lemma lem3591892 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term286 A B g s f) = (term315 A B g s f).
Proof. exact (MK_COMB (@lem3591678 A B g f s) (@lem3591891 A B g s f)). Qed.
Lemma lem3591893 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term289 A B g f s) = (term289 A B g f s).
Proof. exact (eq_refl (term289 A B g f s)). Qed.
Lemma lem3591894 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term291 A B g s f) = (term316 A B g s f).
Proof. exact (MK_COMB (@lem3591893 A B g f s) (@lem3591892 A B g s f)). Qed.
Lemma lem3591896 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3591897 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3591896 A P Q). Qed.
Lemma lem3591898 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term319 A B x g x' f s) = (term320 A B x g x' f s).
Proof. exact (@lem3591897 A (x = (g x')) (term21 A B x' f s)). Qed.
Lemma lem3591899 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3591900 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term321 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3591899 A B x f s x')). Qed.
Lemma lem3591901 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591902 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term322 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3591901 A) (@lem3591900 A B x f s)). Qed.
Lemma lem3591903 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3591904 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term319 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3591903 A B x g x') (@lem3591902 A B x' f s)). Qed.
Lemma lem3591905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3591906 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term323 A B x g x' f s) = (term324 A B x g x' f s).
Proof. exact (MK_COMB (@lem3591905) (@lem3591904 A B x g x' f s)). Qed.
Lemma lem3591907 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3591908 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3591909 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term325 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3591908 A B x g x') (@lem3591907 A B x' f s x'')). Qed.
Lemma lem3591910 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term327 A B x g x' f s) = (term328 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3591909 A B x g x' f s x'')). Qed.
Lemma lem3591911 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591912 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term320 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (MK_COMB (@lem3591911 A) (@lem3591910 A B x g x' f s)). Qed.
Lemma lem3591913 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term319 A B x g x' f s) = (term320 A B x g x' f s)) = ((term133 A B x g x' f s) = (term329 A B x g x' f s)).
Proof. exact (MK_COMB (@lem3591906 A B x g x' f s) (@lem3591912 A B x g x' f s)). Qed.
Lemma lem3591914 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (EQ_MP (@lem3591913 A B x g x' f s) (@lem3591898 A B x g x' f s)). Qed.
Lemma lem3591915 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term330 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3591914 A B x g x' f s)). Qed.
Lemma lem3591916 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591917 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term331 A B x g f s).
Proof. exact (MK_COMB (@lem3591916 B) (@lem3591915 A B x g f s)). Qed.
Lemma lem3591918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591919 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B x g f s) = (term332 A B x g f s).
Proof. exact (MK_COMB (@lem3591918) (@lem3591917 A B x g f s)). Qed.
Lemma lem3591920 {A : Type'} (s : A -> Prop) (x : A) : (term74 A s x) = (term74 A s x).
Proof. exact (eq_refl (term74 A s x)). Qed.
Lemma lem3591921 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term213 A B g f s x) = (term333 A B g f s x).
Proof. exact (MK_COMB (@lem3591919 A B x g f s) (@lem3591920 A s x)). Qed.
Lemma lem3591923 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3591924 {B : Type'} (P : B -> Prop) (Q : Prop) : (term334 B P Q) = (term335 B P Q).
Proof. exact (@lem3591923 B P Q). Qed.
Lemma lem3591925 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term336 A B g f s x) = (term337 A B g f s x).
Proof. exact (@lem3591924 B (term330 A B x g f s) (term74 A s x)). Qed.
Lemma lem3591926 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term338 A B x g f s x') = (term329 A B x g x' f s).
Proof. exact (eq_refl (term338 A B x g f s x')). Qed.
Lemma lem3591927 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term339 A B x g f s) = (term330 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3591926 A B x g x' f s)). Qed.
Lemma lem3591928 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591929 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term340 A B x g f s) = (term331 A B x g f s).
Proof. exact (MK_COMB (@lem3591928 B) (@lem3591927 A B x g f s)). Qed.
Lemma lem3591930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591931 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term341 A B x g f s) = (term332 A B x g f s).
Proof. exact (MK_COMB (@lem3591930) (@lem3591929 A B x g f s)). Qed.
Lemma lem3591932 {A : Type'} (s : A -> Prop) (x : A) : (term74 A s x) = (term74 A s x).
Proof. exact (eq_refl (term74 A s x)). Qed.
Lemma lem3591933 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term336 A B g f s x) = (term333 A B g f s x).
Proof. exact (MK_COMB (@lem3591931 A B x g f s) (@lem3591932 A s x)). Qed.
Lemma lem3591934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3591935 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term342 A B g f s x) = (term343 A B g f s x).
Proof. exact (MK_COMB (@lem3591934) (@lem3591933 A B g f s x)). Qed.
Lemma lem3591936 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term338 A B x g f s x') = (term329 A B x g x' f s).
Proof. exact (eq_refl (term338 A B x g f s x')). Qed.
Lemma lem3591937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591938 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term344 A B x g f s x') = (term345 A B x g x' f s).
Proof. exact (MK_COMB (@lem3591937) (@lem3591936 A B x g x' f s)). Qed.
Lemma lem3591939 {A : Type'} (s : A -> Prop) (x : A) : (term74 A s x) = (term74 A s x).
Proof. exact (eq_refl (term74 A s x)). Qed.
Lemma lem3591940 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term346 A B g f x s x') = (term347 A B g x f s x').
Proof. exact (MK_COMB (@lem3591938 A B x' g x f s) (@lem3591939 A s x')). Qed.
Lemma lem3591941 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term348 A B g f s x) = (term349 A B g f s x).
Proof. exact (fun_ext (fun x' : B => @lem3591940 A B g x' f s x)). Qed.
Lemma lem3591942 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591943 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term337 A B g f s x) = (term350 A B g f s x).
Proof. exact (MK_COMB (@lem3591942 B) (@lem3591941 A B g f s x)). Qed.
Lemma lem3591944 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : ((term336 A B g f s x) = (term337 A B g f s x)) = ((term333 A B g f s x) = (term350 A B g f s x)).
Proof. exact (MK_COMB (@lem3591935 A B g f s x) (@lem3591943 A B g f s x)). Qed.
Lemma lem3591945 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term333 A B g f s x) = (term350 A B g f s x).
Proof. exact (EQ_MP (@lem3591944 A B g f s x) (@lem3591925 A B g f s x)). Qed.
Lemma lem3591947 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3591948 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem3591947 A P Q). Qed.
Lemma lem3591949 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term351 A B g x f s x') = (term352 A B g x f s x').
Proof. exact (@lem3591948 A (term328 A B x' g x f s) (term74 A s x')). Qed.
Lemma lem3591950 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term353 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (eq_refl (term353 A B x g x' f s x'')). Qed.
Lemma lem3591951 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term354 A B x g x' f s) = (term328 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3591950 A B x g x' f s x'')). Qed.
Lemma lem3591952 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591953 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term355 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (MK_COMB (@lem3591952 A) (@lem3591951 A B x g x' f s)). Qed.
Lemma lem3591954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591955 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term356 A B x g x' f s) = (term345 A B x g x' f s).
Proof. exact (MK_COMB (@lem3591954) (@lem3591953 A B x g x' f s)). Qed.
Lemma lem3591956 {A : Type'} (s : A -> Prop) (x : A) : (term74 A s x) = (term74 A s x).
Proof. exact (eq_refl (term74 A s x)). Qed.
Lemma lem3591957 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term351 A B g x f s x') = (term347 A B g x f s x').
Proof. exact (MK_COMB (@lem3591955 A B x' g x f s) (@lem3591956 A s x')). Qed.
Lemma lem3591958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3591959 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term357 A B g x f s x') = (term358 A B g x f s x').
Proof. exact (MK_COMB (@lem3591958) (@lem3591957 A B g x f s x')). Qed.
Lemma lem3591960 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term353 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (eq_refl (term353 A B x g x' f s x'')). Qed.
Lemma lem3591961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591962 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term359 A B x g x' f s x'') = (term360 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3591961) (@lem3591960 A B x g x' f s x'')). Qed.
Lemma lem3591963 {A : Type'} (s : A -> Prop) (x : A) : (term74 A s x) = (term74 A s x).
Proof. exact (eq_refl (term74 A s x)). Qed.
Lemma lem3591964 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term361 A B g x f x' s x'') = (term362 A B g x f x' s x'').
Proof. exact (MK_COMB (@lem3591962 A B x'' g x f s x') (@lem3591963 A s x'')). Qed.
Lemma lem3591965 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term363 A B g x f s x') = (term364 A B g x f s x').
Proof. exact (fun_ext (fun x'' : A => @lem3591964 A B g x f x'' s x')). Qed.
Lemma lem3591966 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591967 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term352 A B g x f s x') = (term365 A B g x f s x').
Proof. exact (MK_COMB (@lem3591966 A) (@lem3591965 A B g x f s x')). Qed.
Lemma lem3591968 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : ((term351 A B g x f s x') = (term352 A B g x f s x')) = ((term347 A B g x f s x') = (term365 A B g x f s x')).
Proof. exact (MK_COMB (@lem3591959 A B g x f s x') (@lem3591967 A B g x f s x')). Qed.
Lemma lem3591969 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term347 A B g x f s x') = (term365 A B g x f s x').
Proof. exact (EQ_MP (@lem3591968 A B g x f s x') (@lem3591949 A B g x f s x')). Qed.
Lemma lem3591970 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term349 A B g f s x) = (term366 A B g f s x).
Proof. exact (fun_ext (fun x' : B => @lem3591969 A B g x' f s x)). Qed.
Lemma lem3591971 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3591972 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term350 A B g f s x) = (term367 A B g f s x).
Proof. exact (MK_COMB (@lem3591971 B) (@lem3591970 A B g f s x)). Qed.
Lemma lem3591973 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term333 A B g f s x) = (term367 A B g f s x).
Proof. exact (TRANS (@lem3591945 A B g f s x) (@lem3591972 A B g f s x)). Qed.
Lemma lem3591974 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term213 A B g f s x) = (term367 A B g f s x).
Proof. exact (TRANS (@lem3591921 A B g f s x) (@lem3591973 A B g f s x)). Qed.
Lemma lem3591975 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term222 A B g f s) = (term368 A B g f s).
Proof. exact (fun_ext (fun x : A => @lem3591974 A B g f s x)). Qed.
Lemma lem3591976 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591977 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term223 A B g f s) = (term369 A B g f s).
Proof. exact (MK_COMB (@lem3591976 A) (@lem3591975 A B g f s)). Qed.
Lemma lem3591978 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3591979 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term289 A B g f s) = (term370 A B g f s).
Proof. exact (MK_COMB (@lem3591978) (@lem3591977 A B g f s)). Qed.
Lemma lem3591981 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3591982 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem3591981 A P Q). Qed.
Lemma lem3591983 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term371 A B x g f s) = (term372 A B x g f s).
Proof. exact (@lem3591982 A (term21 A B x f s) (term245 A B x g f s)). Qed.
Lemma lem3591984 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3591985 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term321 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3591984 A B x f s x')). Qed.
Lemma lem3591986 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3591987 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term322 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3591986 A) (@lem3591985 A B x f s)). Qed.
Lemma lem3591988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591989 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term373 A B x f s) = (term250 A B x f s).
Proof. exact (MK_COMB (@lem3591988) (@lem3591987 A B x f s)). Qed.
Lemma lem3591990 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term245 A B x g f s) = (term245 A B x g f s).
Proof. exact (eq_refl (term245 A B x g f s)). Qed.
Lemma lem3591991 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term371 A B x g f s) = (term252 A B x g f s).
Proof. exact (MK_COMB (@lem3591989 A B x f s) (@lem3591990 A B x g f s)). Qed.
Lemma lem3591992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3591993 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term374 A B x g f s) = (term375 A B x g f s).
Proof. exact (MK_COMB (@lem3591992) (@lem3591991 A B x g f s)). Qed.
Lemma lem3591994 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3591995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3591996 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term376 A B x f s x') = (term377 A B x f s x').
Proof. exact (MK_COMB (@lem3591995) (@lem3591994 A B x f s x')). Qed.
Lemma lem3591997 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term245 A B x g f s) = (term245 A B x g f s).
Proof. exact (eq_refl (term245 A B x g f s)). Qed.
Lemma lem3591998 {A B : Type'} (x : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term378 A B x x' g f s) = (term379 A B x x' g f s).
Proof. exact (MK_COMB (@lem3591996 A B x' f s x) (@lem3591997 A B x' g f s)). Qed.
Lemma lem3591999 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term380 A B x g f s) = (term381 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3591998 A B x' x g f s)). Qed.
Lemma lem3592000 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592001 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term372 A B x g f s) = (term382 A B x g f s).
Proof. exact (MK_COMB (@lem3592000 A) (@lem3591999 A B x g f s)). Qed.
Lemma lem3592002 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term371 A B x g f s) = (term372 A B x g f s)) = ((term252 A B x g f s) = (term382 A B x g f s)).
Proof. exact (MK_COMB (@lem3591993 A B x g f s) (@lem3592001 A B x g f s)). Qed.
Lemma lem3592003 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term252 A B x g f s) = (term382 A B x g f s).
Proof. exact (EQ_MP (@lem3592002 A B x g f s) (@lem3591983 A B x g f s)). Qed.
Lemma lem3592004 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term296 A B g f s) = (term383 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3592003 A B x g f s)). Qed.
Lemma lem3592005 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592006 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term307 A B g f s) = (term384 A B g f s).
Proof. exact (MK_COMB (@lem3592005 B) (@lem3592004 A B g f s)). Qed.
Lemma lem3592007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592008 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term309 A B g f s) = (term385 A B g f s).
Proof. exact (MK_COMB (@lem3592007) (@lem3592006 A B g f s)). Qed.
Lemma lem3592010 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592011 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3592010 A P Q). Qed.
Lemma lem3592012 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term319 A B x g x' f s) = (term320 A B x g x' f s).
Proof. exact (@lem3592011 A (x = (g x')) (term21 A B x' f s)). Qed.
Lemma lem3592013 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3592014 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term321 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3592013 A B x f s x')). Qed.
Lemma lem3592015 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592016 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term322 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3592015 A) (@lem3592014 A B x f s)). Qed.
Lemma lem3592017 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3592018 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term319 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592017 A B x g x') (@lem3592016 A B x' f s)). Qed.
Lemma lem3592019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592020 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term323 A B x g x' f s) = (term324 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592019) (@lem3592018 A B x g x' f s)). Qed.
Lemma lem3592021 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3592022 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3592023 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term325 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3592022 A B x g x') (@lem3592021 A B x' f s x'')). Qed.
Lemma lem3592024 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term327 A B x g x' f s) = (term328 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3592023 A B x g x' f s x'')). Qed.
Lemma lem3592025 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592026 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term320 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592025 A) (@lem3592024 A B x g x' f s)). Qed.
Lemma lem3592027 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term319 A B x g x' f s) = (term320 A B x g x' f s)) = ((term133 A B x g x' f s) = (term329 A B x g x' f s)).
Proof. exact (MK_COMB (@lem3592020 A B x g x' f s) (@lem3592026 A B x g x' f s)). Qed.
Lemma lem3592028 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (EQ_MP (@lem3592027 A B x g x' f s) (@lem3592012 A B x g x' f s)). Qed.
Lemma lem3592029 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term330 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3592028 A B x g x' f s)). Qed.
Lemma lem3592030 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592031 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term331 A B x g f s).
Proof. exact (MK_COMB (@lem3592030 B) (@lem3592029 A B x g f s)). Qed.
Lemma lem3592032 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3592033 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term150 A B x x' g f s) = (term386 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592032 A B x f x') (@lem3592031 A B x' g f s)). Qed.
Lemma lem3592035 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592036 {B : Type'} (P : Prop) (Q : B -> Prop) : (term317 B P Q) = (term318 B P Q).
Proof. exact (@lem3592035 B P Q). Qed.
Lemma lem3592037 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term387 A B x x' g f s) = (term388 A B x x' g f s).
Proof. exact (@lem3592036 B (x = (f x')) (term330 A B x' g f s)). Qed.
Lemma lem3592038 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term338 A B x g f s x') = (term329 A B x g x' f s).
Proof. exact (eq_refl (term338 A B x g f s x')). Qed.
Lemma lem3592039 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term339 A B x g f s) = (term330 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3592038 A B x g x' f s)). Qed.
Lemma lem3592040 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592041 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term340 A B x g f s) = (term331 A B x g f s).
Proof. exact (MK_COMB (@lem3592040 B) (@lem3592039 A B x g f s)). Qed.
Lemma lem3592042 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3592043 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term387 A B x x' g f s) = (term386 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592042 A B x f x') (@lem3592041 A B x' g f s)). Qed.
Lemma lem3592044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592045 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term389 A B x x' g f s) = (term390 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592044) (@lem3592043 A B x x' g f s)). Qed.
Lemma lem3592046 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term338 A B x g f s x') = (term329 A B x g x' f s).
Proof. exact (eq_refl (term338 A B x g f s x')). Qed.
Lemma lem3592047 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3592048 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term391 A B x x' g f s x'') = (term392 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592047 A B x f x') (@lem3592046 A B x' g x'' f s)). Qed.
Lemma lem3592049 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term393 A B x x' g f s) = (term394 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592048 A B x x' g x'' f s)). Qed.
Lemma lem3592050 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592051 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term388 A B x x' g f s) = (term395 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592050 B) (@lem3592049 A B x x' g f s)). Qed.
Lemma lem3592052 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term387 A B x x' g f s) = (term388 A B x x' g f s)) = ((term386 A B x x' g f s) = (term395 A B x x' g f s)).
Proof. exact (MK_COMB (@lem3592045 A B x x' g f s) (@lem3592051 A B x x' g f s)). Qed.
Lemma lem3592053 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term386 A B x x' g f s) = (term395 A B x x' g f s).
Proof. exact (EQ_MP (@lem3592052 A B x x' g f s) (@lem3592037 A B x x' g f s)). Qed.
Lemma lem3592055 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592056 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3592055 A P Q). Qed.
Lemma lem3592057 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term396 A B x x' g x'' f s) = (term397 A B x x' g x'' f s).
Proof. exact (@lem3592056 A (x = (f x')) (term328 A B x' g x'' f s)). Qed.
Lemma lem3592058 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term353 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (eq_refl (term353 A B x g x' f s x'')). Qed.
Lemma lem3592059 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term354 A B x g x' f s) = (term328 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3592058 A B x g x' f s x'')). Qed.
Lemma lem3592060 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592061 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term355 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592060 A) (@lem3592059 A B x g x' f s)). Qed.
Lemma lem3592062 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3592063 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term396 A B x x' g x'' f s) = (term392 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592062 A B x f x') (@lem3592061 A B x' g x'' f s)). Qed.
Lemma lem3592064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592065 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term398 A B x x' g x'' f s) = (term399 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592064) (@lem3592063 A B x x' g x'' f s)). Qed.
Lemma lem3592066 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term353 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (eq_refl (term353 A B x g x' f s x'')). Qed.
Lemma lem3592067 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term17 A B x f x') = (term17 A B x f x').
Proof. exact (eq_refl (term17 A B x f x')). Qed.
Lemma lem3592068 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term400 A B x x' g x'' f s x''') = (term401 A B x x' g x'' f s x''').
Proof. exact (MK_COMB (@lem3592067 A B x f x') (@lem3592066 A B x' g x'' f s x''')). Qed.
Lemma lem3592069 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term402 A B x x' g x'' f s) = (term403 A B x x' g x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3592068 A B x x' g x'' f s x''')). Qed.
Lemma lem3592070 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592071 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term397 A B x x' g x'' f s) = (term404 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592070 A) (@lem3592069 A B x x' g x'' f s)). Qed.
Lemma lem3592072 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : ((term396 A B x x' g x'' f s) = (term397 A B x x' g x'' f s)) = ((term392 A B x x' g x'' f s) = (term404 A B x x' g x'' f s)).
Proof. exact (MK_COMB (@lem3592065 A B x x' g x'' f s) (@lem3592071 A B x x' g x'' f s)). Qed.
Lemma lem3592073 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term392 A B x x' g x'' f s) = (term404 A B x x' g x'' f s).
Proof. exact (EQ_MP (@lem3592072 A B x x' g x'' f s) (@lem3592057 A B x x' g x'' f s)). Qed.
Lemma lem3592074 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term394 A B x x' g f s) = (term405 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592073 A B x x' g x'' f s)). Qed.
Lemma lem3592075 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592076 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term395 A B x x' g f s) = (term406 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592075 B) (@lem3592074 A B x x' g f s)). Qed.
Lemma lem3592077 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term386 A B x x' g f s) = (term406 A B x x' g f s).
Proof. exact (TRANS (@lem3592053 A B x x' g f s) (@lem3592076 A B x x' g f s)). Qed.
Lemma lem3592078 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term150 A B x x' g f s) = (term406 A B x x' g f s).
Proof. exact (TRANS (@lem3592033 A B x x' g f s) (@lem3592077 A B x x' g f s)). Qed.
Lemma lem3592079 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term152 A B x g f s) = (term407 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592078 A B x x' g f s)). Qed.
Lemma lem3592080 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592081 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term153 A B x g f s) = (term408 A B x g f s).
Proof. exact (MK_COMB (@lem3592080 A) (@lem3592079 A B x g f s)). Qed.
Lemma lem3592082 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B x f s) = (term247 A B x f s).
Proof. exact (eq_refl (term247 A B x f s)). Qed.
Lemma lem3592083 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term249 A B x g f s) = (term409 A B x g f s).
Proof. exact (MK_COMB (@lem3592082 A B x f s) (@lem3592081 A B x g f s)). Qed.
Lemma lem3592085 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592086 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3592085 A P Q). Qed.
Lemma lem3592087 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term410 A B x g f s) = (term411 A B x g f s).
Proof. exact (@lem3592086 A (term206 A B x f s) (term407 A B x g f s)). Qed.
Lemma lem3592088 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term412 A B x g f s x') = (term406 A B x x' g f s).
Proof. exact (eq_refl (term412 A B x g f s x')). Qed.
Lemma lem3592089 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term413 A B x g f s) = (term407 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592088 A B x x' g f s)). Qed.
Lemma lem3592090 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592091 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term414 A B x g f s) = (term408 A B x g f s).
Proof. exact (MK_COMB (@lem3592090 A) (@lem3592089 A B x g f s)). Qed.
Lemma lem3592092 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B x f s) = (term247 A B x f s).
Proof. exact (eq_refl (term247 A B x f s)). Qed.
Lemma lem3592093 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term410 A B x g f s) = (term409 A B x g f s).
Proof. exact (MK_COMB (@lem3592092 A B x f s) (@lem3592091 A B x g f s)). Qed.
Lemma lem3592094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592095 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term415 A B x g f s) = (term416 A B x g f s).
Proof. exact (MK_COMB (@lem3592094) (@lem3592093 A B x g f s)). Qed.
Lemma lem3592096 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term412 A B x g f s x') = (term406 A B x x' g f s).
Proof. exact (eq_refl (term412 A B x g f s x')). Qed.
Lemma lem3592097 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B x f s) = (term247 A B x f s).
Proof. exact (eq_refl (term247 A B x f s)). Qed.
Lemma lem3592098 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term417 A B x g f s x') = (term418 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592097 A B x f s) (@lem3592096 A B x x' g f s)). Qed.
Lemma lem3592099 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term419 A B x g f s) = (term420 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592098 A B x x' g f s)). Qed.
Lemma lem3592100 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592101 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term411 A B x g f s) = (term421 A B x g f s).
Proof. exact (MK_COMB (@lem3592100 A) (@lem3592099 A B x g f s)). Qed.
Lemma lem3592102 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term410 A B x g f s) = (term411 A B x g f s)) = ((term409 A B x g f s) = (term421 A B x g f s)).
Proof. exact (MK_COMB (@lem3592095 A B x g f s) (@lem3592101 A B x g f s)). Qed.
Lemma lem3592103 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term409 A B x g f s) = (term421 A B x g f s).
Proof. exact (EQ_MP (@lem3592102 A B x g f s) (@lem3592087 A B x g f s)). Qed.
Lemma lem3592105 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592106 {B : Type'} (P : Prop) (Q : B -> Prop) : (term317 B P Q) = (term318 B P Q).
Proof. exact (@lem3592105 B P Q). Qed.
Lemma lem3592107 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term422 A B x x' g f s) = (term423 A B x x' g f s).
Proof. exact (@lem3592106 B (term206 A B x f s) (term405 A B x x' g f s)). Qed.
Lemma lem3592108 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term424 A B x x' g f s x'') = (term404 A B x x' g x'' f s).
Proof. exact (eq_refl (term424 A B x x' g f s x'')). Qed.
Lemma lem3592109 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term425 A B x x' g f s) = (term405 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592108 A B x x' g x'' f s)). Qed.
Lemma lem3592110 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592111 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term426 A B x x' g f s) = (term406 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592110 B) (@lem3592109 A B x x' g f s)). Qed.
Lemma lem3592112 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B x f s) = (term247 A B x f s).
Proof. exact (eq_refl (term247 A B x f s)). Qed.
Lemma lem3592113 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term422 A B x x' g f s) = (term418 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592112 A B x f s) (@lem3592111 A B x x' g f s)). Qed.
Lemma lem3592114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592115 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term427 A B x x' g f s) = (term428 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592114) (@lem3592113 A B x x' g f s)). Qed.
Lemma lem3592116 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term424 A B x x' g f s x'') = (term404 A B x x' g x'' f s).
Proof. exact (eq_refl (term424 A B x x' g f s x'')). Qed.
Lemma lem3592117 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B x f s) = (term247 A B x f s).
Proof. exact (eq_refl (term247 A B x f s)). Qed.
Lemma lem3592118 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term429 A B x x' g f s x'') = (term430 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592117 A B x f s) (@lem3592116 A B x x' g x'' f s)). Qed.
Lemma lem3592119 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term431 A B x x' g f s) = (term432 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592118 A B x x' g x'' f s)). Qed.
Lemma lem3592120 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592121 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term423 A B x x' g f s) = (term433 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592120 B) (@lem3592119 A B x x' g f s)). Qed.
Lemma lem3592122 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term422 A B x x' g f s) = (term423 A B x x' g f s)) = ((term418 A B x x' g f s) = (term433 A B x x' g f s)).
Proof. exact (MK_COMB (@lem3592115 A B x x' g f s) (@lem3592121 A B x x' g f s)). Qed.
Lemma lem3592123 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term418 A B x x' g f s) = (term433 A B x x' g f s).
Proof. exact (EQ_MP (@lem3592122 A B x x' g f s) (@lem3592107 A B x x' g f s)). Qed.
Lemma lem3592125 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592126 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3592125 A P Q). Qed.
Lemma lem3592127 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term434 A B x x' g x'' f s) = (term435 A B x x' g x'' f s).
Proof. exact (@lem3592126 A (term206 A B x f s) (term403 A B x x' g x'' f s)). Qed.
Lemma lem3592128 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term436 A B x x' g x'' f s x''') = (term401 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term436 A B x x' g x'' f s x''')). Qed.
Lemma lem3592129 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term437 A B x x' g x'' f s) = (term403 A B x x' g x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3592128 A B x x' g x'' f s x''')). Qed.
Lemma lem3592130 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592131 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term438 A B x x' g x'' f s) = (term404 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592130 A) (@lem3592129 A B x x' g x'' f s)). Qed.
Lemma lem3592132 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B x f s) = (term247 A B x f s).
Proof. exact (eq_refl (term247 A B x f s)). Qed.
Lemma lem3592133 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term434 A B x x' g x'' f s) = (term430 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592132 A B x f s) (@lem3592131 A B x x' g x'' f s)). Qed.
Lemma lem3592134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592135 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term439 A B x x' g x'' f s) = (term440 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592134) (@lem3592133 A B x x' g x'' f s)). Qed.
Lemma lem3592136 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term436 A B x x' g x'' f s x''') = (term401 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term436 A B x x' g x'' f s x''')). Qed.
Lemma lem3592137 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B x f s) = (term247 A B x f s).
Proof. exact (eq_refl (term247 A B x f s)). Qed.
Lemma lem3592138 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term441 A B x x' g x'' f s x''') = (term442 A B x x' g x'' f s x''').
Proof. exact (MK_COMB (@lem3592137 A B x f s) (@lem3592136 A B x x' g x'' f s x''')). Qed.
Lemma lem3592139 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term443 A B x x' g x'' f s) = (term444 A B x x' g x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3592138 A B x x' g x'' f s x''')). Qed.
Lemma lem3592140 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592141 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term435 A B x x' g x'' f s) = (term445 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592140 A) (@lem3592139 A B x x' g x'' f s)). Qed.
Lemma lem3592142 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : ((term434 A B x x' g x'' f s) = (term435 A B x x' g x'' f s)) = ((term430 A B x x' g x'' f s) = (term445 A B x x' g x'' f s)).
Proof. exact (MK_COMB (@lem3592135 A B x x' g x'' f s) (@lem3592141 A B x x' g x'' f s)). Qed.
Lemma lem3592143 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term430 A B x x' g x'' f s) = (term445 A B x x' g x'' f s).
Proof. exact (EQ_MP (@lem3592142 A B x x' g x'' f s) (@lem3592127 A B x x' g x'' f s)). Qed.
Lemma lem3592144 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term432 A B x x' g f s) = (term446 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592143 A B x x' g x'' f s)). Qed.
Lemma lem3592145 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592146 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term433 A B x x' g f s) = (term447 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592145 B) (@lem3592144 A B x x' g f s)). Qed.
Lemma lem3592147 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term418 A B x x' g f s) = (term447 A B x x' g f s).
Proof. exact (TRANS (@lem3592123 A B x x' g f s) (@lem3592146 A B x x' g f s)). Qed.
Lemma lem3592148 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term420 A B x g f s) = (term448 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592147 A B x x' g f s)). Qed.
Lemma lem3592149 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592150 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term421 A B x g f s) = (term449 A B x g f s).
Proof. exact (MK_COMB (@lem3592149 A) (@lem3592148 A B x g f s)). Qed.
Lemma lem3592151 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term409 A B x g f s) = (term449 A B x g f s).
Proof. exact (TRANS (@lem3592103 A B x g f s) (@lem3592150 A B x g f s)). Qed.
Lemma lem3592152 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term249 A B x g f s) = (term449 A B x g f s).
Proof. exact (TRANS (@lem3592083 A B x g f s) (@lem3592151 A B x g f s)). Qed.
Lemma lem3592153 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term297 A B g f s) = (term450 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3592152 A B x g f s)). Qed.
Lemma lem3592154 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592155 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term312 A B g f s) = (term451 A B g f s).
Proof. exact (MK_COMB (@lem3592154 B) (@lem3592153 A B g f s)). Qed.
Lemma lem3592156 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term313 A B g f s) = (term452 A B g f s).
Proof. exact (MK_COMB (@lem3592008 A B g f s) (@lem3592155 A B g f s)). Qed.
Lemma lem3592158 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3592159 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term293 B P Q) = (term292 B P Q).
Proof. exact (@lem3592158 B P Q). Qed.
Lemma lem3592160 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term453 A B g f s) = (term454 A B g f s).
Proof. exact (@lem3592159 B (term383 A B g f s) (term450 A B g f s)). Qed.
Lemma lem3592161 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term455 A B g f s x) = (term382 A B x g f s).
Proof. exact (eq_refl (term455 A B g f s x)). Qed.
Lemma lem3592162 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term456 A B g f s) = (term383 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3592161 A B x g f s)). Qed.
Lemma lem3592163 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592164 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term457 A B g f s) = (term384 A B g f s).
Proof. exact (MK_COMB (@lem3592163 B) (@lem3592162 A B g f s)). Qed.
Lemma lem3592165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592166 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term458 A B g f s) = (term385 A B g f s).
Proof. exact (MK_COMB (@lem3592165) (@lem3592164 A B g f s)). Qed.
Lemma lem3592167 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term459 A B g f s x) = (term449 A B x g f s).
Proof. exact (eq_refl (term459 A B g f s x)). Qed.
Lemma lem3592168 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term460 A B g f s) = (term450 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3592167 A B x g f s)). Qed.
Lemma lem3592169 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592170 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term461 A B g f s) = (term451 A B g f s).
Proof. exact (MK_COMB (@lem3592169 B) (@lem3592168 A B g f s)). Qed.
Lemma lem3592171 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term453 A B g f s) = (term452 A B g f s).
Proof. exact (MK_COMB (@lem3592166 A B g f s) (@lem3592170 A B g f s)). Qed.
Lemma lem3592172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592173 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term462 A B g f s) = (term463 A B g f s).
Proof. exact (MK_COMB (@lem3592172) (@lem3592171 A B g f s)). Qed.
Lemma lem3592174 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term455 A B g f s x) = (term382 A B x g f s).
Proof. exact (eq_refl (term455 A B g f s x)). Qed.
Lemma lem3592175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592176 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term464 A B g f s x) = (term465 A B x g f s).
Proof. exact (MK_COMB (@lem3592175) (@lem3592174 A B x g f s)). Qed.
Lemma lem3592177 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term459 A B g f s x) = (term449 A B x g f s).
Proof. exact (eq_refl (term459 A B g f s x)). Qed.
Lemma lem3592178 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term466 A B g f s x) = (term467 A B x g f s).
Proof. exact (MK_COMB (@lem3592176 A B x g f s) (@lem3592177 A B x g f s)). Qed.
Lemma lem3592179 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term468 A B g f s) = (term469 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3592178 A B x g f s)). Qed.
Lemma lem3592180 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592181 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term454 A B g f s) = (term470 A B g f s).
Proof. exact (MK_COMB (@lem3592180 B) (@lem3592179 A B g f s)). Qed.
Lemma lem3592182 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term453 A B g f s) = (term454 A B g f s)) = ((term452 A B g f s) = (term470 A B g f s)).
Proof. exact (MK_COMB (@lem3592173 A B g f s) (@lem3592181 A B g f s)). Qed.
Lemma lem3592183 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term452 A B g f s) = (term470 A B g f s).
Proof. exact (EQ_MP (@lem3592182 A B g f s) (@lem3592160 A B g f s)). Qed.
Lemma lem3592185 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3592186 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (@lem3592185 A P Q). Qed.
Lemma lem3592187 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term471 A B x g f s) = (term472 A B x g f s).
Proof. exact (@lem3592186 A (term381 A B x g f s) (term448 A B x g f s)). Qed.
Lemma lem3592188 {A B : Type'} (x : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term473 A B x' g f s x) = (term379 A B x x' g f s).
Proof. exact (eq_refl (term473 A B x' g f s x)). Qed.
Lemma lem3592189 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term474 A B x g f s) = (term381 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592188 A B x' x g f s)). Qed.
Lemma lem3592190 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592191 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term475 A B x g f s) = (term382 A B x g f s).
Proof. exact (MK_COMB (@lem3592190 A) (@lem3592189 A B x g f s)). Qed.
Lemma lem3592192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592193 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term476 A B x g f s) = (term465 A B x g f s).
Proof. exact (MK_COMB (@lem3592192) (@lem3592191 A B x g f s)). Qed.
Lemma lem3592194 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term477 A B x g f s x') = (term447 A B x x' g f s).
Proof. exact (eq_refl (term477 A B x g f s x')). Qed.
Lemma lem3592195 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term478 A B x g f s) = (term448 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592194 A B x x' g f s)). Qed.
Lemma lem3592196 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592197 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term479 A B x g f s) = (term449 A B x g f s).
Proof. exact (MK_COMB (@lem3592196 A) (@lem3592195 A B x g f s)). Qed.
Lemma lem3592198 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term471 A B x g f s) = (term467 A B x g f s).
Proof. exact (MK_COMB (@lem3592193 A B x g f s) (@lem3592197 A B x g f s)). Qed.
Lemma lem3592199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592200 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term480 A B x g f s) = (term481 A B x g f s).
Proof. exact (MK_COMB (@lem3592199) (@lem3592198 A B x g f s)). Qed.
Lemma lem3592201 {A B : Type'} (x : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term473 A B x' g f s x) = (term379 A B x x' g f s).
Proof. exact (eq_refl (term473 A B x' g f s x)). Qed.
Lemma lem3592202 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592203 {A B : Type'} (x : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term482 A B x' g f s x) = (term483 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592202) (@lem3592201 A B x x' g f s)). Qed.
Lemma lem3592204 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term477 A B x g f s x') = (term447 A B x x' g f s).
Proof. exact (eq_refl (term477 A B x g f s x')). Qed.
Lemma lem3592205 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term484 A B x g f s x') = (term485 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592203 A B x' x g f s) (@lem3592204 A B x x' g f s)). Qed.
Lemma lem3592206 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term486 A B x g f s) = (term487 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592205 A B x x' g f s)). Qed.
Lemma lem3592207 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592208 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term472 A B x g f s) = (term488 A B x g f s).
Proof. exact (MK_COMB (@lem3592207 A) (@lem3592206 A B x g f s)). Qed.
Lemma lem3592209 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term471 A B x g f s) = (term472 A B x g f s)) = ((term467 A B x g f s) = (term488 A B x g f s)).
Proof. exact (MK_COMB (@lem3592200 A B x g f s) (@lem3592208 A B x g f s)). Qed.
Lemma lem3592210 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term467 A B x g f s) = (term488 A B x g f s).
Proof. exact (EQ_MP (@lem3592209 A B x g f s) (@lem3592187 A B x g f s)). Qed.
Lemma lem3592212 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592213 {B : Type'} (P : Prop) (Q : B -> Prop) : (term489 B P Q) = (term490 B P Q).
Proof. exact (@lem3592212 B P Q). Qed.
Lemma lem3592214 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term491 A B x x' g f s) = (term492 A B x x' g f s).
Proof. exact (@lem3592213 B (term379 A B x' x g f s) (term446 A B x x' g f s)). Qed.
Lemma lem3592215 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term493 A B x x' g f s x'') = (term445 A B x x' g x'' f s).
Proof. exact (eq_refl (term493 A B x x' g f s x'')). Qed.
Lemma lem3592216 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term494 A B x x' g f s) = (term446 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592215 A B x x' g x'' f s)). Qed.
Lemma lem3592217 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592218 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term495 A B x x' g f s) = (term447 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592217 B) (@lem3592216 A B x x' g f s)). Qed.
Lemma lem3592219 {A B : Type'} (x : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term483 A B x x' g f s) = (term483 A B x x' g f s).
Proof. exact (eq_refl (term483 A B x x' g f s)). Qed.
Lemma lem3592220 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term491 A B x x' g f s) = (term485 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592219 A B x' x g f s) (@lem3592218 A B x x' g f s)). Qed.
Lemma lem3592221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592222 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term496 A B x x' g f s) = (term497 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592221) (@lem3592220 A B x x' g f s)). Qed.
Lemma lem3592223 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term493 A B x x' g f s x'') = (term445 A B x x' g x'' f s).
Proof. exact (eq_refl (term493 A B x x' g f s x'')). Qed.
Lemma lem3592224 {A B : Type'} (x : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term483 A B x x' g f s) = (term483 A B x x' g f s).
Proof. exact (eq_refl (term483 A B x x' g f s)). Qed.
Lemma lem3592225 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term498 A B x x' g f s x'') = (term499 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592224 A B x' x g f s) (@lem3592223 A B x x' g x'' f s)). Qed.
Lemma lem3592226 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term500 A B x x' g f s) = (term501 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592225 A B x x' g x'' f s)). Qed.
Lemma lem3592227 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592228 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term492 A B x x' g f s) = (term502 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592227 B) (@lem3592226 A B x x' g f s)). Qed.
Lemma lem3592229 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term491 A B x x' g f s) = (term492 A B x x' g f s)) = ((term485 A B x x' g f s) = (term502 A B x x' g f s)).
Proof. exact (MK_COMB (@lem3592222 A B x x' g f s) (@lem3592228 A B x x' g f s)). Qed.
Lemma lem3592230 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term485 A B x x' g f s) = (term502 A B x x' g f s).
Proof. exact (EQ_MP (@lem3592229 A B x x' g f s) (@lem3592214 A B x x' g f s)). Qed.
Lemma lem3592232 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592233 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (@lem3592232 A P Q). Qed.
Lemma lem3592234 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term503 A B x x' g x'' f s) = (term504 A B x x' g x'' f s).
Proof. exact (@lem3592233 A (term379 A B x' x g f s) (term444 A B x x' g x'' f s)). Qed.
Lemma lem3592235 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term505 A B x x' g x'' f s x''') = (term442 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term505 A B x x' g x'' f s x''')). Qed.
Lemma lem3592236 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term506 A B x x' g x'' f s) = (term444 A B x x' g x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3592235 A B x x' g x'' f s x''')). Qed.
Lemma lem3592237 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592238 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term507 A B x x' g x'' f s) = (term445 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592237 A) (@lem3592236 A B x x' g x'' f s)). Qed.
Lemma lem3592239 {A B : Type'} (x : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term483 A B x x' g f s) = (term483 A B x x' g f s).
Proof. exact (eq_refl (term483 A B x x' g f s)). Qed.
Lemma lem3592240 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term503 A B x x' g x'' f s) = (term499 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592239 A B x' x g f s) (@lem3592238 A B x x' g x'' f s)). Qed.
Lemma lem3592241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592242 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term508 A B x x' g x'' f s) = (term509 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592241) (@lem3592240 A B x x' g x'' f s)). Qed.
Lemma lem3592243 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term505 A B x x' g x'' f s x''') = (term442 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term505 A B x x' g x'' f s x''')). Qed.
Lemma lem3592244 {A B : Type'} (x : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term483 A B x x' g f s) = (term483 A B x x' g f s).
Proof. exact (eq_refl (term483 A B x x' g f s)). Qed.
Lemma lem3592245 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term510 A B x x' g x'' f s x''') = (term511 A B x x' g x'' f s x''').
Proof. exact (MK_COMB (@lem3592244 A B x' x g f s) (@lem3592243 A B x x' g x'' f s x''')). Qed.
Lemma lem3592246 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term512 A B x x' g x'' f s) = (term513 A B x x' g x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3592245 A B x x' g x'' f s x''')). Qed.
Lemma lem3592247 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592248 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term504 A B x x' g x'' f s) = (term514 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592247 A) (@lem3592246 A B x x' g x'' f s)). Qed.
Lemma lem3592249 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : ((term503 A B x x' g x'' f s) = (term504 A B x x' g x'' f s)) = ((term499 A B x x' g x'' f s) = (term514 A B x x' g x'' f s)).
Proof. exact (MK_COMB (@lem3592242 A B x x' g x'' f s) (@lem3592248 A B x x' g x'' f s)). Qed.
Lemma lem3592250 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term499 A B x x' g x'' f s) = (term514 A B x x' g x'' f s).
Proof. exact (EQ_MP (@lem3592249 A B x x' g x'' f s) (@lem3592234 A B x x' g x'' f s)). Qed.
Lemma lem3592251 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term501 A B x x' g f s) = (term515 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592250 A B x x' g x'' f s)). Qed.
Lemma lem3592252 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592253 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term502 A B x x' g f s) = (term516 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592252 B) (@lem3592251 A B x x' g f s)). Qed.
Lemma lem3592254 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term485 A B x x' g f s) = (term516 A B x x' g f s).
Proof. exact (TRANS (@lem3592230 A B x x' g f s) (@lem3592253 A B x x' g f s)). Qed.
Lemma lem3592255 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term487 A B x g f s) = (term517 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592254 A B x x' g f s)). Qed.
Lemma lem3592256 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592257 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term488 A B x g f s) = (term518 A B x g f s).
Proof. exact (MK_COMB (@lem3592256 A) (@lem3592255 A B x g f s)). Qed.
Lemma lem3592258 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term467 A B x g f s) = (term518 A B x g f s).
Proof. exact (TRANS (@lem3592210 A B x g f s) (@lem3592257 A B x g f s)). Qed.
Lemma lem3592259 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term469 A B g f s) = (term519 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3592258 A B x g f s)). Qed.
Lemma lem3592260 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592261 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term470 A B g f s) = (term520 A B g f s).
Proof. exact (MK_COMB (@lem3592260 B) (@lem3592259 A B g f s)). Qed.
Lemma lem3592262 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term452 A B g f s) = (term520 A B g f s).
Proof. exact (TRANS (@lem3592183 A B g f s) (@lem3592261 A B g f s)). Qed.
Lemma lem3592263 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term313 A B g f s) = (term520 A B g f s).
Proof. exact (TRANS (@lem3592156 A B g f s) (@lem3592262 A B g f s)). Qed.
Lemma lem3592264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592265 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term314 A B g f s) = (term521 A B g f s).
Proof. exact (MK_COMB (@lem3592264) (@lem3592263 A B g f s)). Qed.
Lemma lem3592267 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592268 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3592267 A P Q). Qed.
Lemma lem3592269 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term319 A B x g x' f s) = (term320 A B x g x' f s).
Proof. exact (@lem3592268 A (x = (g x')) (term21 A B x' f s)). Qed.
Lemma lem3592270 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3592271 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term321 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3592270 A B x f s x')). Qed.
Lemma lem3592272 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592273 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term322 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3592272 A) (@lem3592271 A B x f s)). Qed.
Lemma lem3592274 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3592275 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term319 A B x g x' f s) = (term133 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592274 A B x g x') (@lem3592273 A B x' f s)). Qed.
Lemma lem3592276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592277 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term323 A B x g x' f s) = (term324 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592276) (@lem3592275 A B x g x' f s)). Qed.
Lemma lem3592278 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3592279 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term131 A B x g x') = (term131 A B x g x').
Proof. exact (eq_refl (term131 A B x g x')). Qed.
Lemma lem3592280 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term325 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3592279 A B x g x') (@lem3592278 A B x' f s x'')). Qed.
Lemma lem3592281 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term327 A B x g x' f s) = (term328 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3592280 A B x g x' f s x'')). Qed.
Lemma lem3592282 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592283 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term320 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592282 A) (@lem3592281 A B x g x' f s)). Qed.
Lemma lem3592284 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term319 A B x g x' f s) = (term320 A B x g x' f s)) = ((term133 A B x g x' f s) = (term329 A B x g x' f s)).
Proof. exact (MK_COMB (@lem3592277 A B x g x' f s) (@lem3592283 A B x g x' f s)). Qed.
Lemma lem3592285 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term133 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (EQ_MP (@lem3592284 A B x g x' f s) (@lem3592269 A B x g x' f s)). Qed.
Lemma lem3592286 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term330 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3592285 A B x g x' f s)). Qed.
Lemma lem3592287 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592288 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term331 A B x g f s).
Proof. exact (MK_COMB (@lem3592287 B) (@lem3592286 A B x g f s)). Qed.
Lemma lem3592289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592290 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B x g f s) = (term332 A B x g f s).
Proof. exact (MK_COMB (@lem3592289) (@lem3592288 A B x g f s)). Qed.
Lemma lem3592292 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592293 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3592292 A P Q). Qed.
Lemma lem3592294 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term319 A B y g x f s) = (term320 A B y g x f s).
Proof. exact (@lem3592293 A (y = (g x)) (term21 A B x f s)). Qed.
Lemma lem3592295 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3592296 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term321 A B x f s) = (term21 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3592295 A B x f s x')). Qed.
Lemma lem3592297 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592298 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term322 A B x f s) = (term22 A B x f s).
Proof. exact (MK_COMB (@lem3592297 A) (@lem3592296 A B x f s)). Qed.
Lemma lem3592299 {A B : Type'} (y : A) (g : B -> A) (x : B) : (term131 A B y g x) = (term131 A B y g x).
Proof. exact (eq_refl (term131 A B y g x)). Qed.
Lemma lem3592300 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term319 A B y g x f s) = (term133 A B y g x f s).
Proof. exact (MK_COMB (@lem3592299 A B y g x) (@lem3592298 A B x f s)). Qed.
Lemma lem3592301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592302 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term323 A B y g x f s) = (term324 A B y g x f s).
Proof. exact (MK_COMB (@lem3592301) (@lem3592300 A B y g x f s)). Qed.
Lemma lem3592303 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term202 A B x f s x') = (term19 A B x f s x').
Proof. exact (eq_refl (term202 A B x f s x')). Qed.
Lemma lem3592304 {A B : Type'} (y : A) (g : B -> A) (x : B) : (term131 A B y g x) = (term131 A B y g x).
Proof. exact (eq_refl (term131 A B y g x)). Qed.
Lemma lem3592305 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term325 A B y g x f s x') = (term326 A B y g x f s x').
Proof. exact (MK_COMB (@lem3592304 A B y g x) (@lem3592303 A B x f s x')). Qed.
Lemma lem3592306 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term327 A B y g x f s) = (term328 A B y g x f s).
Proof. exact (fun_ext (fun x' : A => @lem3592305 A B y g x f s x')). Qed.
Lemma lem3592307 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592308 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term320 A B y g x f s) = (term329 A B y g x f s).
Proof. exact (MK_COMB (@lem3592307 A) (@lem3592306 A B y g x f s)). Qed.
Lemma lem3592309 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : ((term319 A B y g x f s) = (term320 A B y g x f s)) = ((term133 A B y g x f s) = (term329 A B y g x f s)).
Proof. exact (MK_COMB (@lem3592302 A B y g x f s) (@lem3592308 A B y g x f s)). Qed.
Lemma lem3592310 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term133 A B y g x f s) = (term329 A B y g x f s).
Proof. exact (EQ_MP (@lem3592309 A B y g x f s) (@lem3592294 A B y g x f s)). Qed.
Lemma lem3592311 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B y g f s) = (term330 A B y g f s).
Proof. exact (fun_ext (fun x : B => @lem3592310 A B y g x f s)). Qed.
Lemma lem3592312 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592313 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B y g f s) = (term331 A B y g f s).
Proof. exact (MK_COMB (@lem3592312 B) (@lem3592311 A B y g f s)). Qed.
Lemma lem3592314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592315 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B y g f s) = (term332 A B y g f s).
Proof. exact (MK_COMB (@lem3592314) (@lem3592313 A B y g f s)). Qed.
Lemma lem3592316 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3592317 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term161 A B g s x f y) = (term522 A B g s x f y).
Proof. exact (MK_COMB (@lem3592315 A B y g f s) (@lem3592316 A B x f y)). Qed.
Lemma lem3592319 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3592320 {B : Type'} (P : B -> Prop) (Q : Prop) : (term334 B P Q) = (term335 B P Q).
Proof. exact (@lem3592319 B P Q). Qed.
Lemma lem3592321 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term523 A B g s x f y) = (term524 A B g s x f y).
Proof. exact (@lem3592320 B (term330 A B y g f s) ((f x) = (f y))). Qed.
Lemma lem3592322 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term338 A B y g f s x) = (term329 A B y g x f s).
Proof. exact (eq_refl (term338 A B y g f s x)). Qed.
Lemma lem3592323 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term339 A B y g f s) = (term330 A B y g f s).
Proof. exact (fun_ext (fun x : B => @lem3592322 A B y g x f s)). Qed.
Lemma lem3592324 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592325 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term340 A B y g f s) = (term331 A B y g f s).
Proof. exact (MK_COMB (@lem3592324 B) (@lem3592323 A B y g f s)). Qed.
Lemma lem3592326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592327 {A B : Type'} (y : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term341 A B y g f s) = (term332 A B y g f s).
Proof. exact (MK_COMB (@lem3592326) (@lem3592325 A B y g f s)). Qed.
Lemma lem3592328 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3592329 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term523 A B g s x f y) = (term522 A B g s x f y).
Proof. exact (MK_COMB (@lem3592327 A B y g f s) (@lem3592328 A B x f y)). Qed.
Lemma lem3592330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592331 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term525 A B g s x f y) = (term526 A B g s x f y).
Proof. exact (MK_COMB (@lem3592330) (@lem3592329 A B g s x f y)). Qed.
Lemma lem3592332 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term338 A B y g f s x) = (term329 A B y g x f s).
Proof. exact (eq_refl (term338 A B y g f s x)). Qed.
Lemma lem3592333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592334 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term344 A B y g f s x) = (term345 A B y g x f s).
Proof. exact (MK_COMB (@lem3592333) (@lem3592332 A B y g x f s)). Qed.
Lemma lem3592335 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3592336 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term527 A B g s x x' f y) = (term528 A B g x s x' f y).
Proof. exact (MK_COMB (@lem3592334 A B y g x f s) (@lem3592335 A B x' f y)). Qed.
Lemma lem3592337 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term529 A B g s x f y) = (term530 A B g s x f y).
Proof. exact (fun_ext (fun x' : B => @lem3592336 A B g x' s x f y)). Qed.
Lemma lem3592338 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592339 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term524 A B g s x f y) = (term531 A B g s x f y).
Proof. exact (MK_COMB (@lem3592338 B) (@lem3592337 A B g s x f y)). Qed.
Lemma lem3592340 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : ((term523 A B g s x f y) = (term524 A B g s x f y)) = ((term522 A B g s x f y) = (term531 A B g s x f y)).
Proof. exact (MK_COMB (@lem3592331 A B g s x f y) (@lem3592339 A B g s x f y)). Qed.
Lemma lem3592341 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term522 A B g s x f y) = (term531 A B g s x f y).
Proof. exact (EQ_MP (@lem3592340 A B g s x f y) (@lem3592321 A B g s x f y)). Qed.
Lemma lem3592343 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3592344 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem3592343 A P Q). Qed.
Lemma lem3592345 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term532 A B g x s x' f y) = (term533 A B g x s x' f y).
Proof. exact (@lem3592344 A (term328 A B y g x f s) ((f x') = (f y))). Qed.
Lemma lem3592346 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term353 A B y g x f s x') = (term326 A B y g x f s x').
Proof. exact (eq_refl (term353 A B y g x f s x')). Qed.
Lemma lem3592347 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term354 A B y g x f s) = (term328 A B y g x f s).
Proof. exact (fun_ext (fun x' : A => @lem3592346 A B y g x f s x')). Qed.
Lemma lem3592348 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592349 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term355 A B y g x f s) = (term329 A B y g x f s).
Proof. exact (MK_COMB (@lem3592348 A) (@lem3592347 A B y g x f s)). Qed.
Lemma lem3592350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592351 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) : (term356 A B y g x f s) = (term345 A B y g x f s).
Proof. exact (MK_COMB (@lem3592350) (@lem3592349 A B y g x f s)). Qed.
Lemma lem3592352 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3592353 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term532 A B g x s x' f y) = (term528 A B g x s x' f y).
Proof. exact (MK_COMB (@lem3592351 A B y g x f s) (@lem3592352 A B x' f y)). Qed.
Lemma lem3592354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592355 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term534 A B g x s x' f y) = (term535 A B g x s x' f y).
Proof. exact (MK_COMB (@lem3592354) (@lem3592353 A B g x s x' f y)). Qed.
Lemma lem3592356 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term353 A B y g x f s x') = (term326 A B y g x f s x').
Proof. exact (eq_refl (term353 A B y g x f s x')). Qed.
Lemma lem3592357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592358 {A B : Type'} (y : A) (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term359 A B y g x f s x') = (term360 A B y g x f s x').
Proof. exact (MK_COMB (@lem3592357) (@lem3592356 A B y g x f s x')). Qed.
Lemma lem3592359 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3592360 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (x'' : A) (f : A -> B) (y : A) : (term536 A B g x s x' x'' f y) = (term537 A B g x s x' x'' f y).
Proof. exact (MK_COMB (@lem3592358 A B y g x f s x') (@lem3592359 A B x'' f y)). Qed.
Lemma lem3592361 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term538 A B g x s x' f y) = (term539 A B g x s x' f y).
Proof. exact (fun_ext (fun x'' : A => @lem3592360 A B g x s x'' x' f y)). Qed.
Lemma lem3592362 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592363 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term533 A B g x s x' f y) = (term540 A B g x s x' f y).
Proof. exact (MK_COMB (@lem3592362 A) (@lem3592361 A B g x s x' f y)). Qed.
Lemma lem3592364 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : ((term532 A B g x s x' f y) = (term533 A B g x s x' f y)) = ((term528 A B g x s x' f y) = (term540 A B g x s x' f y)).
Proof. exact (MK_COMB (@lem3592355 A B g x s x' f y) (@lem3592363 A B g x s x' f y)). Qed.
Lemma lem3592365 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term528 A B g x s x' f y) = (term540 A B g x s x' f y).
Proof. exact (EQ_MP (@lem3592364 A B g x s x' f y) (@lem3592345 A B g x s x' f y)). Qed.
Lemma lem3592366 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term530 A B g s x f y) = (term541 A B g s x f y).
Proof. exact (fun_ext (fun x' : B => @lem3592365 A B g x' s x f y)). Qed.
Lemma lem3592367 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592368 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term531 A B g s x f y) = (term542 A B g s x f y).
Proof. exact (MK_COMB (@lem3592367 B) (@lem3592366 A B g s x f y)). Qed.
Lemma lem3592369 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term522 A B g s x f y) = (term542 A B g s x f y).
Proof. exact (TRANS (@lem3592341 A B g s x f y) (@lem3592368 A B g s x f y)). Qed.
Lemma lem3592370 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term161 A B g s x f y) = (term542 A B g s x f y).
Proof. exact (TRANS (@lem3592317 A B g s x f y) (@lem3592369 A B g s x f y)). Qed.
Lemma lem3592371 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term163 A B g s x f y) = (term543 A B g s x f y).
Proof. exact (MK_COMB (@lem3592290 A B x g f s) (@lem3592370 A B g s x f y)). Qed.
Lemma lem3592373 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3592374 {B : Type'} (P : B -> Prop) (Q : Prop) : (term334 B P Q) = (term335 B P Q).
Proof. exact (@lem3592373 B P Q). Qed.
Lemma lem3592375 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term544 A B g s x f y) = (term545 A B g s x f y).
Proof. exact (@lem3592374 B (term330 A B x g f s) (term542 A B g s x f y)). Qed.
Lemma lem3592376 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term338 A B x g f s x') = (term329 A B x g x' f s).
Proof. exact (eq_refl (term338 A B x g f s x')). Qed.
Lemma lem3592377 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term339 A B x g f s) = (term330 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3592376 A B x g x' f s)). Qed.
Lemma lem3592378 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592379 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term340 A B x g f s) = (term331 A B x g f s).
Proof. exact (MK_COMB (@lem3592378 B) (@lem3592377 A B x g f s)). Qed.
Lemma lem3592380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592381 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term341 A B x g f s) = (term332 A B x g f s).
Proof. exact (MK_COMB (@lem3592380) (@lem3592379 A B x g f s)). Qed.
Lemma lem3592382 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term542 A B g s x f y) = (term542 A B g s x f y).
Proof. exact (eq_refl (term542 A B g s x f y)). Qed.
Lemma lem3592383 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term544 A B g s x f y) = (term543 A B g s x f y).
Proof. exact (MK_COMB (@lem3592381 A B x g f s) (@lem3592382 A B g s x f y)). Qed.
Lemma lem3592384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592385 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term546 A B g s x f y) = (term547 A B g s x f y).
Proof. exact (MK_COMB (@lem3592384) (@lem3592383 A B g s x f y)). Qed.
Lemma lem3592386 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term338 A B x g f s x') = (term329 A B x g x' f s).
Proof. exact (eq_refl (term338 A B x g f s x')). Qed.
Lemma lem3592387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592388 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term344 A B x g f s x') = (term345 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592387) (@lem3592386 A B x g x' f s)). Qed.
Lemma lem3592389 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term542 A B g s x f y) = (term542 A B g s x f y).
Proof. exact (eq_refl (term542 A B g s x f y)). Qed.
Lemma lem3592390 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term548 A B x g s x' f y) = (term549 A B x g s x' f y).
Proof. exact (MK_COMB (@lem3592388 A B x' g x f s) (@lem3592389 A B g s x' f y)). Qed.
Lemma lem3592391 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term550 A B g s x f y) = (term551 A B g s x f y).
Proof. exact (fun_ext (fun x' : B => @lem3592390 A B x' g s x f y)). Qed.
Lemma lem3592392 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592393 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term545 A B g s x f y) = (term552 A B g s x f y).
Proof. exact (MK_COMB (@lem3592392 B) (@lem3592391 A B g s x f y)). Qed.
Lemma lem3592394 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : ((term544 A B g s x f y) = (term545 A B g s x f y)) = ((term543 A B g s x f y) = (term552 A B g s x f y)).
Proof. exact (MK_COMB (@lem3592385 A B g s x f y) (@lem3592393 A B g s x f y)). Qed.
Lemma lem3592395 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term543 A B g s x f y) = (term552 A B g s x f y).
Proof. exact (EQ_MP (@lem3592394 A B g s x f y) (@lem3592375 A B g s x f y)). Qed.
Lemma lem3592397 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3592398 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem3592397 A P Q). Qed.
Lemma lem3592399 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term553 A B x g s x' f y) = (term554 A B x g s x' f y).
Proof. exact (@lem3592398 A (term328 A B x' g x f s) (term542 A B g s x' f y)). Qed.
Lemma lem3592400 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term353 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (eq_refl (term353 A B x g x' f s x'')). Qed.
Lemma lem3592401 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term354 A B x g x' f s) = (term328 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3592400 A B x g x' f s x'')). Qed.
Lemma lem3592402 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592403 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term355 A B x g x' f s) = (term329 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592402 A) (@lem3592401 A B x g x' f s)). Qed.
Lemma lem3592404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592405 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term356 A B x g x' f s) = (term345 A B x g x' f s).
Proof. exact (MK_COMB (@lem3592404) (@lem3592403 A B x g x' f s)). Qed.
Lemma lem3592406 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term542 A B g s x f y) = (term542 A B g s x f y).
Proof. exact (eq_refl (term542 A B g s x f y)). Qed.
Lemma lem3592407 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term553 A B x g s x' f y) = (term549 A B x g s x' f y).
Proof. exact (MK_COMB (@lem3592405 A B x' g x f s) (@lem3592406 A B g s x' f y)). Qed.
Lemma lem3592408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592409 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term555 A B x g s x' f y) = (term556 A B x g s x' f y).
Proof. exact (MK_COMB (@lem3592408) (@lem3592407 A B x g s x' f y)). Qed.
Lemma lem3592410 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term353 A B x g x' f s x'') = (term326 A B x g x' f s x'').
Proof. exact (eq_refl (term353 A B x g x' f s x'')). Qed.
Lemma lem3592411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592412 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term359 A B x g x' f s x'') = (term360 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3592411) (@lem3592410 A B x g x' f s x'')). Qed.
Lemma lem3592413 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term542 A B g s x f y) = (term542 A B g s x f y).
Proof. exact (eq_refl (term542 A B g s x f y)). Qed.
Lemma lem3592414 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term557 A B x x' g s x'' f y) = (term558 A B x x' g s x'' f y).
Proof. exact (MK_COMB (@lem3592412 A B x'' g x f s x') (@lem3592413 A B g s x'' f y)). Qed.
Lemma lem3592415 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term559 A B x g s x' f y) = (term560 A B x g s x' f y).
Proof. exact (fun_ext (fun x'' : A => @lem3592414 A B x x'' g s x' f y)). Qed.
Lemma lem3592416 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592417 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term554 A B x g s x' f y) = (term561 A B x g s x' f y).
Proof. exact (MK_COMB (@lem3592416 A) (@lem3592415 A B x g s x' f y)). Qed.
Lemma lem3592418 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : ((term553 A B x g s x' f y) = (term554 A B x g s x' f y)) = ((term549 A B x g s x' f y) = (term561 A B x g s x' f y)).
Proof. exact (MK_COMB (@lem3592409 A B x g s x' f y) (@lem3592417 A B x g s x' f y)). Qed.
Lemma lem3592419 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term549 A B x g s x' f y) = (term561 A B x g s x' f y).
Proof. exact (EQ_MP (@lem3592418 A B x g s x' f y) (@lem3592399 A B x g s x' f y)). Qed.
Lemma lem3592421 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592422 {B : Type'} (P : Prop) (Q : B -> Prop) : (term317 B P Q) = (term318 B P Q).
Proof. exact (@lem3592421 B P Q). Qed.
Lemma lem3592423 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term562 A B x x' g s x'' f y) = (term563 A B x x' g s x'' f y).
Proof. exact (@lem3592422 B (term326 A B x'' g x f s x') (term541 A B g s x'' f y)). Qed.
Lemma lem3592424 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term564 A B g s x' f y x) = (term540 A B g x s x' f y).
Proof. exact (eq_refl (term564 A B g s x' f y x)). Qed.
Lemma lem3592425 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term565 A B g s x f y) = (term541 A B g s x f y).
Proof. exact (fun_ext (fun x' : B => @lem3592424 A B g x' s x f y)). Qed.
Lemma lem3592426 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592427 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term566 A B g s x f y) = (term542 A B g s x f y).
Proof. exact (MK_COMB (@lem3592426 B) (@lem3592425 A B g s x f y)). Qed.
Lemma lem3592428 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term360 A B x g x' f s x'') = (term360 A B x g x' f s x'').
Proof. exact (eq_refl (term360 A B x g x' f s x'')). Qed.
Lemma lem3592429 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term562 A B x x' g s x'' f y) = (term558 A B x x' g s x'' f y).
Proof. exact (MK_COMB (@lem3592428 A B x'' g x f s x') (@lem3592427 A B g s x'' f y)). Qed.
Lemma lem3592430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592431 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term567 A B x x' g s x'' f y) = (term568 A B x x' g s x'' f y).
Proof. exact (MK_COMB (@lem3592430) (@lem3592429 A B x x' g s x'' f y)). Qed.
Lemma lem3592432 {A B : Type'} (g : B -> A) (x' : B) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term564 A B g s x f y x') = (term540 A B g x' s x f y).
Proof. exact (eq_refl (term564 A B g s x f y x')). Qed.
Lemma lem3592433 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term360 A B x g x' f s x'') = (term360 A B x g x' f s x'').
Proof. exact (eq_refl (term360 A B x g x' f s x'')). Qed.
Lemma lem3592434 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term569 A B x x' g s x''' f y x'') = (term570 A B x x' g x'' s x''' f y).
Proof. exact (MK_COMB (@lem3592433 A B x''' g x f s x') (@lem3592432 A B g x'' s x''' f y)). Qed.
Lemma lem3592435 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term571 A B x x' g s x'' f y) = (term572 A B x x' g s x'' f y).
Proof. exact (fun_ext (fun x''' : B => @lem3592434 A B x x' g x''' s x'' f y)). Qed.
Lemma lem3592436 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592437 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term563 A B x x' g s x'' f y) = (term573 A B x x' g s x'' f y).
Proof. exact (MK_COMB (@lem3592436 B) (@lem3592435 A B x x' g s x'' f y)). Qed.
Lemma lem3592438 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : ((term562 A B x x' g s x'' f y) = (term563 A B x x' g s x'' f y)) = ((term558 A B x x' g s x'' f y) = (term573 A B x x' g s x'' f y)).
Proof. exact (MK_COMB (@lem3592431 A B x x' g s x'' f y) (@lem3592437 A B x x' g s x'' f y)). Qed.
Lemma lem3592439 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term558 A B x x' g s x'' f y) = (term573 A B x x' g s x'' f y).
Proof. exact (EQ_MP (@lem3592438 A B x x' g s x'' f y) (@lem3592423 A B x x' g s x'' f y)). Qed.
Lemma lem3592441 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3592442 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3592441 A P Q). Qed.
Lemma lem3592443 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term574 A B x x' g x'' s x''' f y) = (term575 A B x x' g x'' s x''' f y).
Proof. exact (@lem3592442 A (term326 A B x''' g x f s x') (term539 A B g x'' s x''' f y)). Qed.
Lemma lem3592444 {A B : Type'} (g : B -> A) (x' : B) (s : A -> Prop) (x'' : A) (x : A) (f : A -> B) (y : A) : (term576 A B g x' s x f y x'') = (term537 A B g x' s x'' x f y).
Proof. exact (eq_refl (term576 A B g x' s x f y x'')). Qed.
Lemma lem3592445 {A B : Type'} (g : B -> A) (x' : B) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term577 A B g x' s x f y) = (term539 A B g x' s x f y).
Proof. exact (fun_ext (fun x'' : A => @lem3592444 A B g x' s x'' x f y)). Qed.
Lemma lem3592446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592447 {A B : Type'} (g : B -> A) (x' : B) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term578 A B g x' s x f y) = (term540 A B g x' s x f y).
Proof. exact (MK_COMB (@lem3592446 A) (@lem3592445 A B g x' s x f y)). Qed.
Lemma lem3592448 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term360 A B x g x' f s x'') = (term360 A B x g x' f s x'').
Proof. exact (eq_refl (term360 A B x g x' f s x'')). Qed.
Lemma lem3592449 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term574 A B x x' g x'' s x''' f y) = (term570 A B x x' g x'' s x''' f y).
Proof. exact (MK_COMB (@lem3592448 A B x''' g x f s x') (@lem3592447 A B g x'' s x''' f y)). Qed.
Lemma lem3592450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592451 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term579 A B x x' g x'' s x''' f y) = (term580 A B x x' g x'' s x''' f y).
Proof. exact (MK_COMB (@lem3592450) (@lem3592449 A B x x' g x'' s x''' f y)). Qed.
Lemma lem3592452 {A B : Type'} (g : B -> A) (x' : B) (s : A -> Prop) (x'' : A) (x : A) (f : A -> B) (y : A) : (term576 A B g x' s x f y x'') = (term537 A B g x' s x'' x f y).
Proof. exact (eq_refl (term576 A B g x' s x f y x'')). Qed.
Lemma lem3592453 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term360 A B x g x' f s x'') = (term360 A B x g x' f s x'').
Proof. exact (eq_refl (term360 A B x g x' f s x'')). Qed.
Lemma lem3592454 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (x'''' : A) (f : A -> B) (y : A) : (term581 A B x x' g x'' s x'''' f y x''') = (term582 A B x x' g x'' s x''' x'''' f y).
Proof. exact (MK_COMB (@lem3592453 A B x'''' g x f s x') (@lem3592452 A B g x'' s x''' x'''' f y)). Qed.
Lemma lem3592455 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term583 A B x x' g x'' s x''' f y) = (term584 A B x x' g x'' s x''' f y).
Proof. exact (fun_ext (fun x'''' : A => @lem3592454 A B x x' g x'' s x'''' x''' f y)). Qed.
Lemma lem3592456 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592457 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term575 A B x x' g x'' s x''' f y) = (term585 A B x x' g x'' s x''' f y).
Proof. exact (MK_COMB (@lem3592456 A) (@lem3592455 A B x x' g x'' s x''' f y)). Qed.
Lemma lem3592458 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : ((term574 A B x x' g x'' s x''' f y) = (term575 A B x x' g x'' s x''' f y)) = ((term570 A B x x' g x'' s x''' f y) = (term585 A B x x' g x'' s x''' f y)).
Proof. exact (MK_COMB (@lem3592451 A B x x' g x'' s x''' f y) (@lem3592457 A B x x' g x'' s x''' f y)). Qed.
Lemma lem3592459 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term570 A B x x' g x'' s x''' f y) = (term585 A B x x' g x'' s x''' f y).
Proof. exact (EQ_MP (@lem3592458 A B x x' g x'' s x''' f y) (@lem3592443 A B x x' g x'' s x''' f y)). Qed.
Lemma lem3592460 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term572 A B x x' g s x'' f y) = (term586 A B x x' g s x'' f y).
Proof. exact (fun_ext (fun x''' : B => @lem3592459 A B x x' g x''' s x'' f y)). Qed.
Lemma lem3592461 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592462 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term573 A B x x' g s x'' f y) = (term587 A B x x' g s x'' f y).
Proof. exact (MK_COMB (@lem3592461 B) (@lem3592460 A B x x' g s x'' f y)). Qed.
Lemma lem3592463 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term558 A B x x' g s x'' f y) = (term587 A B x x' g s x'' f y).
Proof. exact (TRANS (@lem3592439 A B x x' g s x'' f y) (@lem3592462 A B x x' g s x'' f y)). Qed.
Lemma lem3592464 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term560 A B x g s x' f y) = (term588 A B x g s x' f y).
Proof. exact (fun_ext (fun x'' : A => @lem3592463 A B x x'' g s x' f y)). Qed.
Lemma lem3592465 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592466 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term561 A B x g s x' f y) = (term589 A B x g s x' f y).
Proof. exact (MK_COMB (@lem3592465 A) (@lem3592464 A B x g s x' f y)). Qed.
Lemma lem3592467 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term549 A B x g s x' f y) = (term589 A B x g s x' f y).
Proof. exact (TRANS (@lem3592419 A B x g s x' f y) (@lem3592466 A B x g s x' f y)). Qed.
Lemma lem3592468 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term551 A B g s x f y) = (term590 A B g s x f y).
Proof. exact (fun_ext (fun x' : B => @lem3592467 A B x' g s x f y)). Qed.
Lemma lem3592469 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592470 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term552 A B g s x f y) = (term591 A B g s x f y).
Proof. exact (MK_COMB (@lem3592469 B) (@lem3592468 A B g s x f y)). Qed.
Lemma lem3592471 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term543 A B g s x f y) = (term591 A B g s x f y).
Proof. exact (TRANS (@lem3592395 A B g s x f y) (@lem3592470 A B g s x f y)). Qed.
Lemma lem3592472 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term163 A B g s x f y) = (term591 A B g s x f y).
Proof. exact (TRANS (@lem3592371 A B g s x f y) (@lem3592471 A B g s x f y)). Qed.
Lemma lem3592473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592474 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term266 A B g s x f y) = (term592 A B g s x f y).
Proof. exact (MK_COMB (@lem3592473) (@lem3592472 A B g s x f y)). Qed.
Lemma lem3592475 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592476 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term267 A B g s f x y) = (term593 A B g s f x y).
Proof. exact (MK_COMB (@lem3592474 A B g s x f y) (@lem3592475 A x y)). Qed.
Lemma lem3592478 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3592479 {B : Type'} (P : B -> Prop) (Q : Prop) : (term334 B P Q) = (term335 B P Q).
Proof. exact (@lem3592478 B P Q). Qed.
Lemma lem3592480 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term594 A B g s f x y) = (term595 A B g s f x y).
Proof. exact (@lem3592479 B (term590 A B g s x f y) (term265 A x y)). Qed.
Lemma lem3592481 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term596 A B g s x' f y x) = (term589 A B x g s x' f y).
Proof. exact (eq_refl (term596 A B g s x' f y x)). Qed.
Lemma lem3592482 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term597 A B g s x f y) = (term590 A B g s x f y).
Proof. exact (fun_ext (fun x' : B => @lem3592481 A B x' g s x f y)). Qed.
Lemma lem3592483 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592484 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term598 A B g s x f y) = (term591 A B g s x f y).
Proof. exact (MK_COMB (@lem3592483 B) (@lem3592482 A B g s x f y)). Qed.
Lemma lem3592485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592486 {A B : Type'} (g : B -> A) (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term599 A B g s x f y) = (term592 A B g s x f y).
Proof. exact (MK_COMB (@lem3592485) (@lem3592484 A B g s x f y)). Qed.
Lemma lem3592487 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592488 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term594 A B g s f x y) = (term593 A B g s f x y).
Proof. exact (MK_COMB (@lem3592486 A B g s x f y) (@lem3592487 A x y)). Qed.
Lemma lem3592489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592490 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term600 A B g s f x y) = (term601 A B g s f x y).
Proof. exact (MK_COMB (@lem3592489) (@lem3592488 A B g s f x y)). Qed.
Lemma lem3592491 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term596 A B g s x' f y x) = (term589 A B x g s x' f y).
Proof. exact (eq_refl (term596 A B g s x' f y x)). Qed.
Lemma lem3592492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592493 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term602 A B g s x' f y x) = (term603 A B x g s x' f y).
Proof. exact (MK_COMB (@lem3592492) (@lem3592491 A B x g s x' f y)). Qed.
Lemma lem3592494 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592495 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term604 A B g s f x x' y) = (term605 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3592493 A B x g s x' f y) (@lem3592494 A x' y)). Qed.
Lemma lem3592496 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term606 A B g s f x y) = (term607 A B g s f x y).
Proof. exact (fun_ext (fun x' : B => @lem3592495 A B x' g s f x y)). Qed.
Lemma lem3592497 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592498 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term595 A B g s f x y) = (term608 A B g s f x y).
Proof. exact (MK_COMB (@lem3592497 B) (@lem3592496 A B g s f x y)). Qed.
Lemma lem3592499 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : ((term594 A B g s f x y) = (term595 A B g s f x y)) = ((term593 A B g s f x y) = (term608 A B g s f x y)).
Proof. exact (MK_COMB (@lem3592490 A B g s f x y) (@lem3592498 A B g s f x y)). Qed.
Lemma lem3592500 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term593 A B g s f x y) = (term608 A B g s f x y).
Proof. exact (EQ_MP (@lem3592499 A B g s f x y) (@lem3592480 A B g s f x y)). Qed.
Lemma lem3592502 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3592503 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem3592502 A P Q). Qed.
Lemma lem3592504 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term609 A B x g s f x' y) = (term610 A B x g s f x' y).
Proof. exact (@lem3592503 A (term588 A B x g s x' f y) (term265 A x' y)). Qed.
Lemma lem3592505 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term611 A B x g s x'' f y x') = (term587 A B x x' g s x'' f y).
Proof. exact (eq_refl (term611 A B x g s x'' f y x')). Qed.
Lemma lem3592506 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term612 A B x g s x' f y) = (term588 A B x g s x' f y).
Proof. exact (fun_ext (fun x'' : A => @lem3592505 A B x x'' g s x' f y)). Qed.
Lemma lem3592507 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592508 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term613 A B x g s x' f y) = (term589 A B x g s x' f y).
Proof. exact (MK_COMB (@lem3592507 A) (@lem3592506 A B x g s x' f y)). Qed.
Lemma lem3592509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592510 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term614 A B x g s x' f y) = (term603 A B x g s x' f y).
Proof. exact (MK_COMB (@lem3592509) (@lem3592508 A B x g s x' f y)). Qed.
Lemma lem3592511 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592512 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term609 A B x g s f x' y) = (term605 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3592510 A B x g s x' f y) (@lem3592511 A x' y)). Qed.
Lemma lem3592513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592514 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term615 A B x g s f x' y) = (term616 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3592513) (@lem3592512 A B x g s f x' y)). Qed.
Lemma lem3592515 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term611 A B x g s x'' f y x') = (term587 A B x x' g s x'' f y).
Proof. exact (eq_refl (term611 A B x g s x'' f y x')). Qed.
Lemma lem3592516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592517 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term617 A B x g s x'' f y x') = (term618 A B x x' g s x'' f y).
Proof. exact (MK_COMB (@lem3592516) (@lem3592515 A B x x' g s x'' f y)). Qed.
Lemma lem3592518 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592519 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term619 A B x g s f x' x'' y) = (term620 A B x x' g s f x'' y).
Proof. exact (MK_COMB (@lem3592517 A B x x' g s x'' f y) (@lem3592518 A x'' y)). Qed.
Lemma lem3592520 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term621 A B x g s f x' y) = (term622 A B x g s f x' y).
Proof. exact (fun_ext (fun x'' : A => @lem3592519 A B x x'' g s f x' y)). Qed.
Lemma lem3592521 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592522 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term610 A B x g s f x' y) = (term623 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3592521 A) (@lem3592520 A B x g s f x' y)). Qed.
Lemma lem3592523 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : ((term609 A B x g s f x' y) = (term610 A B x g s f x' y)) = ((term605 A B x g s f x' y) = (term623 A B x g s f x' y)).
Proof. exact (MK_COMB (@lem3592514 A B x g s f x' y) (@lem3592522 A B x g s f x' y)). Qed.
Lemma lem3592524 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term605 A B x g s f x' y) = (term623 A B x g s f x' y).
Proof. exact (EQ_MP (@lem3592523 A B x g s f x' y) (@lem3592504 A B x g s f x' y)). Qed.
Lemma lem3592526 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3592527 {B : Type'} (P : B -> Prop) (Q : Prop) : (term334 B P Q) = (term335 B P Q).
Proof. exact (@lem3592526 B P Q). Qed.
Lemma lem3592528 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term624 A B x x' g s f x'' y) = (term625 A B x x' g s f x'' y).
Proof. exact (@lem3592527 B (term586 A B x x' g s x'' f y) (term265 A x'' y)). Qed.
Lemma lem3592529 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term626 A B x x' g s x''' f y x'') = (term585 A B x x' g x'' s x''' f y).
Proof. exact (eq_refl (term626 A B x x' g s x''' f y x'')). Qed.
Lemma lem3592530 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term627 A B x x' g s x'' f y) = (term586 A B x x' g s x'' f y).
Proof. exact (fun_ext (fun x''' : B => @lem3592529 A B x x' g x''' s x'' f y)). Qed.
Lemma lem3592531 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592532 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term628 A B x x' g s x'' f y) = (term587 A B x x' g s x'' f y).
Proof. exact (MK_COMB (@lem3592531 B) (@lem3592530 A B x x' g s x'' f y)). Qed.
Lemma lem3592533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592534 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (x'' : A) (f : A -> B) (y : A) : (term629 A B x x' g s x'' f y) = (term618 A B x x' g s x'' f y).
Proof. exact (MK_COMB (@lem3592533) (@lem3592532 A B x x' g s x'' f y)). Qed.
Lemma lem3592535 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592536 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term624 A B x x' g s f x'' y) = (term620 A B x x' g s f x'' y).
Proof. exact (MK_COMB (@lem3592534 A B x x' g s x'' f y) (@lem3592535 A x'' y)). Qed.
Lemma lem3592537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592538 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term630 A B x x' g s f x'' y) = (term631 A B x x' g s f x'' y).
Proof. exact (MK_COMB (@lem3592537) (@lem3592536 A B x x' g s f x'' y)). Qed.
Lemma lem3592539 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term626 A B x x' g s x''' f y x'') = (term585 A B x x' g x'' s x''' f y).
Proof. exact (eq_refl (term626 A B x x' g s x''' f y x'')). Qed.
Lemma lem3592540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592541 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term632 A B x x' g s x''' f y x'') = (term633 A B x x' g x'' s x''' f y).
Proof. exact (MK_COMB (@lem3592540) (@lem3592539 A B x x' g x'' s x''' f y)). Qed.
Lemma lem3592542 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592543 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (f : A -> B) (x''' : A) (y : A) : (term634 A B x x' g s f x'' x''' y) = (term635 A B x x' g x'' s f x''' y).
Proof. exact (MK_COMB (@lem3592541 A B x x' g x'' s x''' f y) (@lem3592542 A x''' y)). Qed.
Lemma lem3592544 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term636 A B x x' g s f x'' y) = (term637 A B x x' g s f x'' y).
Proof. exact (fun_ext (fun x''' : B => @lem3592543 A B x x' g x''' s f x'' y)). Qed.
Lemma lem3592545 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592546 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term625 A B x x' g s f x'' y) = (term638 A B x x' g s f x'' y).
Proof. exact (MK_COMB (@lem3592545 B) (@lem3592544 A B x x' g s f x'' y)). Qed.
Lemma lem3592547 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : ((term624 A B x x' g s f x'' y) = (term625 A B x x' g s f x'' y)) = ((term620 A B x x' g s f x'' y) = (term638 A B x x' g s f x'' y)).
Proof. exact (MK_COMB (@lem3592538 A B x x' g s f x'' y) (@lem3592546 A B x x' g s f x'' y)). Qed.
Lemma lem3592548 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term620 A B x x' g s f x'' y) = (term638 A B x x' g s f x'' y).
Proof. exact (EQ_MP (@lem3592547 A B x x' g s f x'' y) (@lem3592528 A B x x' g s f x'' y)). Qed.
Lemma lem3592550 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3592551 {A : Type'} (P : A -> Prop) (Q : Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem3592550 A P Q). Qed.
Lemma lem3592552 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (f : A -> B) (x''' : A) (y : A) : (term639 A B x x' g x'' s f x''' y) = (term640 A B x x' g x'' s f x''' y).
Proof. exact (@lem3592551 A (term584 A B x x' g x'' s x''' f y) (term265 A x''' y)). Qed.
Lemma lem3592553 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (x'''' : A) (f : A -> B) (y : A) : (term641 A B x x' g x'' s x'''' f y x''') = (term582 A B x x' g x'' s x''' x'''' f y).
Proof. exact (eq_refl (term641 A B x x' g x'' s x'''' f y x''')). Qed.
Lemma lem3592554 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term642 A B x x' g x'' s x''' f y) = (term584 A B x x' g x'' s x''' f y).
Proof. exact (fun_ext (fun x'''' : A => @lem3592553 A B x x' g x'' s x'''' x''' f y)). Qed.
Lemma lem3592555 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592556 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term643 A B x x' g x'' s x''' f y) = (term585 A B x x' g x'' s x''' f y).
Proof. exact (MK_COMB (@lem3592555 A) (@lem3592554 A B x x' g x'' s x''' f y)). Qed.
Lemma lem3592557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592558 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (y : A) : (term644 A B x x' g x'' s x''' f y) = (term633 A B x x' g x'' s x''' f y).
Proof. exact (MK_COMB (@lem3592557) (@lem3592556 A B x x' g x'' s x''' f y)). Qed.
Lemma lem3592559 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592560 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (f : A -> B) (x''' : A) (y : A) : (term639 A B x x' g x'' s f x''' y) = (term635 A B x x' g x'' s f x''' y).
Proof. exact (MK_COMB (@lem3592558 A B x x' g x'' s x''' f y) (@lem3592559 A x''' y)). Qed.
Lemma lem3592561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592562 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (f : A -> B) (x''' : A) (y : A) : (term645 A B x x' g x'' s f x''' y) = (term646 A B x x' g x'' s f x''' y).
Proof. exact (MK_COMB (@lem3592561) (@lem3592560 A B x x' g x'' s f x''' y)). Qed.
Lemma lem3592563 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (x'''' : A) (f : A -> B) (y : A) : (term641 A B x x' g x'' s x'''' f y x''') = (term582 A B x x' g x'' s x''' x'''' f y).
Proof. exact (eq_refl (term641 A B x x' g x'' s x'''' f y x''')). Qed.
Lemma lem3592564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3592565 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (x'''' : A) (f : A -> B) (y : A) : (term647 A B x x' g x'' s x'''' f y x''') = (term648 A B x x' g x'' s x''' x'''' f y).
Proof. exact (MK_COMB (@lem3592564) (@lem3592563 A B x x' g x'' s x''' x'''' f y)). Qed.
Lemma lem3592566 {A : Type'} (x : A) (y : A) : (term265 A x y) = (term265 A x y).
Proof. exact (eq_refl (term265 A x y)). Qed.
Lemma lem3592567 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (x''' : A) (f : A -> B) (x'''' : A) (y : A) : (term649 A B x x' g x'' s f x''' x'''' y) = (term650 A B x x' g x'' s x''' f x'''' y).
Proof. exact (MK_COMB (@lem3592565 A B x x' g x'' s x''' x'''' f y) (@lem3592566 A x'''' y)). Qed.
Lemma lem3592568 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (f : A -> B) (x''' : A) (y : A) : (term651 A B x x' g x'' s f x''' y) = (term652 A B x x' g x'' s f x''' y).
Proof. exact (fun_ext (fun x'''' : A => @lem3592567 A B x x' g x'' s x'''' f x''' y)). Qed.
Lemma lem3592569 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592570 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (f : A -> B) (x''' : A) (y : A) : (term640 A B x x' g x'' s f x''' y) = (term653 A B x x' g x'' s f x''' y).
Proof. exact (MK_COMB (@lem3592569 A) (@lem3592568 A B x x' g x'' s f x''' y)). Qed.
Lemma lem3592571 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (f : A -> B) (x''' : A) (y : A) : ((term639 A B x x' g x'' s f x''' y) = (term640 A B x x' g x'' s f x''' y)) = ((term635 A B x x' g x'' s f x''' y) = (term653 A B x x' g x'' s f x''' y)).
Proof. exact (MK_COMB (@lem3592562 A B x x' g x'' s f x''' y) (@lem3592570 A B x x' g x'' s f x''' y)). Qed.
Lemma lem3592572 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (s : A -> Prop) (f : A -> B) (x''' : A) (y : A) : (term635 A B x x' g x'' s f x''' y) = (term653 A B x x' g x'' s f x''' y).
Proof. exact (EQ_MP (@lem3592571 A B x x' g x'' s f x''' y) (@lem3592552 A B x x' g x'' s f x''' y)). Qed.
Lemma lem3592573 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term637 A B x x' g s f x'' y) = (term654 A B x x' g s f x'' y).
Proof. exact (fun_ext (fun x''' : B => @lem3592572 A B x x' g x''' s f x'' y)). Qed.
Lemma lem3592574 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592575 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term638 A B x x' g s f x'' y) = (term655 A B x x' g s f x'' y).
Proof. exact (MK_COMB (@lem3592574 B) (@lem3592573 A B x x' g s f x'' y)). Qed.
Lemma lem3592576 {A B : Type'} (x : B) (x' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (y : A) : (term620 A B x x' g s f x'' y) = (term655 A B x x' g s f x'' y).
Proof. exact (TRANS (@lem3592548 A B x x' g s f x'' y) (@lem3592575 A B x x' g s f x'' y)). Qed.
Lemma lem3592577 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term622 A B x g s f x' y) = (term656 A B x g s f x' y).
Proof. exact (fun_ext (fun x'' : A => @lem3592576 A B x x'' g s f x' y)). Qed.
Lemma lem3592578 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592579 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term623 A B x g s f x' y) = (term657 A B x g s f x' y).
Proof. exact (MK_COMB (@lem3592578 A) (@lem3592577 A B x g s f x' y)). Qed.
Lemma lem3592580 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term605 A B x g s f x' y) = (term657 A B x g s f x' y).
Proof. exact (TRANS (@lem3592524 A B x g s f x' y) (@lem3592579 A B x g s f x' y)). Qed.
Lemma lem3592581 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term607 A B g s f x y) = (term658 A B g s f x y).
Proof. exact (fun_ext (fun x' : B => @lem3592580 A B x' g s f x y)). Qed.
Lemma lem3592582 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592583 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term608 A B g s f x y) = (term659 A B g s f x y).
Proof. exact (MK_COMB (@lem3592582 B) (@lem3592581 A B g s f x y)). Qed.
Lemma lem3592584 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term593 A B g s f x y) = (term659 A B g s f x y).
Proof. exact (TRANS (@lem3592500 A B g s f x y) (@lem3592583 A B g s f x y)). Qed.
Lemma lem3592585 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term267 A B g s f x y) = (term659 A B g s f x y).
Proof. exact (TRANS (@lem3592476 A B g s f x y) (@lem3592584 A B g s f x y)). Qed.
Lemma lem3592586 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term274 A B g s f x) = (term660 A B g s f x).
Proof. exact (fun_ext (fun y : A => @lem3592585 A B g s f x y)). Qed.
Lemma lem3592587 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592588 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term275 A B g s f x) = (term661 A B g s f x).
Proof. exact (MK_COMB (@lem3592587 A) (@lem3592586 A B g s f x)). Qed.
Lemma lem3592589 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term281 A B g s f) = (term662 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3592588 A B g s f x)). Qed.
Lemma lem3592590 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592591 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term282 A B g s f) = (term663 A B g s f).
Proof. exact (MK_COMB (@lem3592590 A) (@lem3592589 A B g s f)). Qed.
Lemma lem3592592 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term315 A B g s f) = (term664 A B g s f).
Proof. exact (MK_COMB (@lem3592265 A B g f s) (@lem3592591 A B g s f)). Qed.
Lemma lem3592596 {A : Type'} (P : A -> Prop) (Q : Prop) : (term665 A P Q) = (term666 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3592597 {B : Type'} (P : B -> Prop) (Q : Prop) : (term665 B P Q) = (term666 B P Q).
Proof. exact (@lem3592596 B P Q). Qed.
Lemma lem3592598 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term667 A B g s f) = (term668 A B g s f).
Proof. exact (@lem3592597 B (term519 A B g f s) (term663 A B g s f)). Qed.
Lemma lem3592599 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term669 A B g f s x) = (term518 A B x g f s).
Proof. exact (eq_refl (term669 A B g f s x)). Qed.
Lemma lem3592600 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term670 A B g f s) = (term519 A B g f s).
Proof. exact (fun_ext (fun x : B => @lem3592599 A B x g f s)). Qed.
Lemma lem3592601 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592602 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term671 A B g f s) = (term520 A B g f s).
Proof. exact (MK_COMB (@lem3592601 B) (@lem3592600 A B g f s)). Qed.
Lemma lem3592603 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592604 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term672 A B g f s) = (term521 A B g f s).
Proof. exact (MK_COMB (@lem3592603) (@lem3592602 A B g f s)). Qed.
Lemma lem3592605 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term663 A B g s f) = (term663 A B g s f).
Proof. exact (eq_refl (term663 A B g s f)). Qed.
Lemma lem3592606 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term667 A B g s f) = (term664 A B g s f).
Proof. exact (MK_COMB (@lem3592604 A B g f s) (@lem3592605 A B g s f)). Qed.
Lemma lem3592607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592608 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term673 A B g s f) = (term674 A B g s f).
Proof. exact (MK_COMB (@lem3592607) (@lem3592606 A B g s f)). Qed.
Lemma lem3592609 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term669 A B g f s x) = (term518 A B x g f s).
Proof. exact (eq_refl (term669 A B g f s x)). Qed.
Lemma lem3592610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592611 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term675 A B g f s x) = (term676 A B x g f s).
Proof. exact (MK_COMB (@lem3592610) (@lem3592609 A B x g f s)). Qed.
Lemma lem3592612 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term663 A B g s f) = (term663 A B g s f).
Proof. exact (eq_refl (term663 A B g s f)). Qed.
Lemma lem3592613 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term677 A B x g s f) = (term678 A B x g s f).
Proof. exact (MK_COMB (@lem3592611 A B x g f s) (@lem3592612 A B g s f)). Qed.
Lemma lem3592614 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term679 A B g s f) = (term680 A B g s f).
Proof. exact (fun_ext (fun x : B => @lem3592613 A B x g s f)). Qed.
Lemma lem3592615 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592616 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term668 A B g s f) = (term681 A B g s f).
Proof. exact (MK_COMB (@lem3592615 B) (@lem3592614 A B g s f)). Qed.
Lemma lem3592617 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term667 A B g s f) = (term668 A B g s f)) = ((term664 A B g s f) = (term681 A B g s f)).
Proof. exact (MK_COMB (@lem3592608 A B g s f) (@lem3592616 A B g s f)). Qed.
Lemma lem3592618 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term664 A B g s f) = (term681 A B g s f).
Proof. exact (EQ_MP (@lem3592617 A B g s f) (@lem3592598 A B g s f)). Qed.
Lemma lem3592620 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3592621 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (@lem3592620 A P Q). Qed.
Lemma lem3592622 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term682 A B x g s f) = (term683 A B x g s f).
Proof. exact (@lem3592621 A (term517 A B x g f s) (term662 A B g s f)). Qed.
Lemma lem3592623 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term684 A B x g f s x') = (term516 A B x x' g f s).
Proof. exact (eq_refl (term684 A B x g f s x')). Qed.
Lemma lem3592624 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term685 A B x g f s) = (term517 A B x g f s).
Proof. exact (fun_ext (fun x' : A => @lem3592623 A B x x' g f s)). Qed.
Lemma lem3592625 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592626 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term686 A B x g f s) = (term518 A B x g f s).
Proof. exact (MK_COMB (@lem3592625 A) (@lem3592624 A B x g f s)). Qed.
Lemma lem3592627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592628 {A B : Type'} (x : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term687 A B x g f s) = (term676 A B x g f s).
Proof. exact (MK_COMB (@lem3592627) (@lem3592626 A B x g f s)). Qed.
Lemma lem3592629 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term688 A B g s f x) = (term661 A B g s f x).
Proof. exact (eq_refl (term688 A B g s f x)). Qed.
Lemma lem3592630 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term689 A B g s f) = (term662 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3592629 A B g s f x)). Qed.
Lemma lem3592631 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592632 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term690 A B g s f) = (term663 A B g s f).
Proof. exact (MK_COMB (@lem3592631 A) (@lem3592630 A B g s f)). Qed.
Lemma lem3592633 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term682 A B x g s f) = (term678 A B x g s f).
Proof. exact (MK_COMB (@lem3592628 A B x g f s) (@lem3592632 A B g s f)). Qed.
Lemma lem3592634 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592635 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term691 A B x g s f) = (term692 A B x g s f).
Proof. exact (MK_COMB (@lem3592634) (@lem3592633 A B x g s f)). Qed.
Lemma lem3592636 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term684 A B x g f s x') = (term516 A B x x' g f s).
Proof. exact (eq_refl (term684 A B x g f s x')). Qed.
Lemma lem3592637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592638 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term693 A B x g f s x') = (term694 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592637) (@lem3592636 A B x x' g f s)). Qed.
Lemma lem3592639 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term688 A B g s f x) = (term661 A B g s f x).
Proof. exact (eq_refl (term688 A B g s f x)). Qed.
Lemma lem3592640 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term695 A B x g s f x') = (term696 A B x g s f x').
Proof. exact (MK_COMB (@lem3592638 A B x x' g f s) (@lem3592639 A B g s f x')). Qed.
Lemma lem3592641 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term697 A B x g s f) = (term698 A B x g s f).
Proof. exact (fun_ext (fun x' : A => @lem3592640 A B x g s f x')). Qed.
Lemma lem3592642 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592643 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term683 A B x g s f) = (term699 A B x g s f).
Proof. exact (MK_COMB (@lem3592642 A) (@lem3592641 A B x g s f)). Qed.
Lemma lem3592644 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term682 A B x g s f) = (term683 A B x g s f)) = ((term678 A B x g s f) = (term699 A B x g s f)).
Proof. exact (MK_COMB (@lem3592635 A B x g s f) (@lem3592643 A B x g s f)). Qed.
Lemma lem3592645 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term678 A B x g s f) = (term699 A B x g s f).
Proof. exact (EQ_MP (@lem3592644 A B x g s f) (@lem3592622 A B x g s f)). Qed.
Lemma lem3592649 {A : Type'} (P : A -> Prop) (Q : Prop) : (term665 A P Q) = (term666 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3592650 {B : Type'} (P : B -> Prop) (Q : Prop) : (term665 B P Q) = (term666 B P Q).
Proof. exact (@lem3592649 B P Q). Qed.
Lemma lem3592651 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term700 A B x g s f x') = (term701 A B x g s f x').
Proof. exact (@lem3592650 B (term515 A B x x' g f s) (term661 A B g s f x')). Qed.
Lemma lem3592652 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term702 A B x x' g f s x'') = (term514 A B x x' g x'' f s).
Proof. exact (eq_refl (term702 A B x x' g f s x'')). Qed.
Lemma lem3592653 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term703 A B x x' g f s) = (term515 A B x x' g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3592652 A B x x' g x'' f s)). Qed.
Lemma lem3592654 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592655 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term704 A B x x' g f s) = (term516 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592654 B) (@lem3592653 A B x x' g f s)). Qed.
Lemma lem3592656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592657 {A B : Type'} (x : B) (x' : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term705 A B x x' g f s) = (term694 A B x x' g f s).
Proof. exact (MK_COMB (@lem3592656) (@lem3592655 A B x x' g f s)). Qed.
Lemma lem3592658 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term661 A B g s f x) = (term661 A B g s f x).
Proof. exact (eq_refl (term661 A B g s f x)). Qed.
Lemma lem3592659 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term700 A B x g s f x') = (term696 A B x g s f x').
Proof. exact (MK_COMB (@lem3592657 A B x x' g f s) (@lem3592658 A B g s f x')). Qed.
Lemma lem3592660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592661 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term706 A B x g s f x') = (term707 A B x g s f x').
Proof. exact (MK_COMB (@lem3592660) (@lem3592659 A B x g s f x')). Qed.
Lemma lem3592662 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term702 A B x x' g f s x'') = (term514 A B x x' g x'' f s).
Proof. exact (eq_refl (term702 A B x x' g f s x'')). Qed.
Lemma lem3592663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592664 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term708 A B x x' g f s x'') = (term709 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592663) (@lem3592662 A B x x' g x'' f s)). Qed.
Lemma lem3592665 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term661 A B g s f x) = (term661 A B g s f x).
Proof. exact (eq_refl (term661 A B g s f x)). Qed.
Lemma lem3592666 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term710 A B x x' g s f x'') = (term711 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592664 A B x x'' g x' f s) (@lem3592665 A B g s f x'')). Qed.
Lemma lem3592667 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term712 A B x g s f x') = (term713 A B x g s f x').
Proof. exact (fun_ext (fun x'' : B => @lem3592666 A B x x'' g s f x')). Qed.
Lemma lem3592668 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592669 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term701 A B x g s f x') = (term714 A B x g s f x').
Proof. exact (MK_COMB (@lem3592668 B) (@lem3592667 A B x g s f x')). Qed.
Lemma lem3592670 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : ((term700 A B x g s f x') = (term701 A B x g s f x')) = ((term696 A B x g s f x') = (term714 A B x g s f x')).
Proof. exact (MK_COMB (@lem3592661 A B x g s f x') (@lem3592669 A B x g s f x')). Qed.
Lemma lem3592671 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term696 A B x g s f x') = (term714 A B x g s f x').
Proof. exact (EQ_MP (@lem3592670 A B x g s f x') (@lem3592651 A B x g s f x')). Qed.
Lemma lem3592673 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3592674 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (@lem3592673 A P Q). Qed.
Lemma lem3592675 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term715 A B x x' g s f x'') = (term716 A B x x' g s f x'').
Proof. exact (@lem3592674 A (term513 A B x x'' g x' f s) (term660 A B g s f x'')). Qed.
Lemma lem3592676 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term717 A B x x' g x'' f s x''') = (term511 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term717 A B x x' g x'' f s x''')). Qed.
Lemma lem3592677 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term718 A B x x' g x'' f s) = (term513 A B x x' g x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3592676 A B x x' g x'' f s x''')). Qed.
Lemma lem3592678 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592679 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term719 A B x x' g x'' f s) = (term514 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592678 A) (@lem3592677 A B x x' g x'' f s)). Qed.
Lemma lem3592680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592681 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term720 A B x x' g x'' f s) = (term709 A B x x' g x'' f s).
Proof. exact (MK_COMB (@lem3592680) (@lem3592679 A B x x' g x'' f s)). Qed.
Lemma lem3592682 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term721 A B g s f x x') = (term659 A B g s f x x').
Proof. exact (eq_refl (term721 A B g s f x x')). Qed.
Lemma lem3592683 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term722 A B g s f x) = (term660 A B g s f x).
Proof. exact (fun_ext (fun x' : A => @lem3592682 A B g s f x x')). Qed.
Lemma lem3592684 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592685 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) : (term723 A B g s f x) = (term661 A B g s f x).
Proof. exact (MK_COMB (@lem3592684 A) (@lem3592683 A B g s f x)). Qed.
Lemma lem3592686 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term715 A B x x' g s f x'') = (term711 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592681 A B x x'' g x' f s) (@lem3592685 A B g s f x'')). Qed.
Lemma lem3592687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592688 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term724 A B x x' g s f x'') = (term725 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592687) (@lem3592686 A B x x' g s f x'')). Qed.
Lemma lem3592689 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term717 A B x x' g x'' f s x''') = (term511 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term717 A B x x' g x'' f s x''')). Qed.
Lemma lem3592690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592691 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term726 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (MK_COMB (@lem3592690) (@lem3592689 A B x x' g x'' f s x''')). Qed.
Lemma lem3592692 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term721 A B g s f x x') = (term659 A B g s f x x').
Proof. exact (eq_refl (term721 A B g s f x x')). Qed.
Lemma lem3592693 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term728 A B x x' g s f x'' x''') = (term729 A B x x' g s f x'' x''').
Proof. exact (MK_COMB (@lem3592691 A B x x'' g x' f s x''') (@lem3592692 A B g s f x'' x''')). Qed.
Lemma lem3592694 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term730 A B x x' g s f x'') = (term731 A B x x' g s f x'').
Proof. exact (fun_ext (fun x''' : A => @lem3592693 A B x x' g s f x'' x''')). Qed.
Lemma lem3592695 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592696 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term716 A B x x' g s f x'') = (term732 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592695 A) (@lem3592694 A B x x' g s f x'')). Qed.
Lemma lem3592697 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term715 A B x x' g s f x'') = (term716 A B x x' g s f x'')) = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')).
Proof. exact (MK_COMB (@lem3592688 A B x x' g s f x'') (@lem3592696 A B x x' g s f x'')). Qed.
Lemma lem3592698 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term711 A B x x' g s f x'') = (term732 A B x x' g s f x'').
Proof. exact (EQ_MP (@lem3592697 A B x x' g s f x'') (@lem3592675 A B x x' g s f x'')). Qed.
Lemma lem3592701 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term733 A B x x' g s f x'') = (term733 A B x x' g s f x'').
Proof. exact (eq_refl (term733 A B x x' g s f x'')). Qed.
Lemma lem3592702 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term733 A B x x' g s f x'') = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')).
Proof. exact (eq_refl (term733 A B x x' g s f x'')). Qed.
Lemma lem3592703 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term734 A B x x' g s f x'') = (term734 A B x x' g s f x'').
Proof. exact (eq_refl (term734 A B x x' g s f x'')). Qed.
Lemma lem3592704 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term733 A B x x' g s f x'') = (term733 A B x x' g s f x'')) = ((term733 A B x x' g s f x'') = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x''))).
Proof. exact (MK_COMB (@lem3592703 A B x x' g s f x'') (@lem3592702 A B x x' g s f x'')). Qed.
Lemma lem3592705 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term733 A B x x' g s f x'') = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')).
Proof. exact (eq_refl (term733 A B x x' g s f x'')). Qed.
Lemma lem3592706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592707 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term734 A B x x' g s f x'') = (term735 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592706) (@lem3592705 A B x x' g s f x'')). Qed.
Lemma lem3592708 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')) = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')).
Proof. exact (eq_refl ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x''))). Qed.
Lemma lem3592709 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term733 A B x x' g s f x'') = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x''))) = (((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')) = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x''))).
Proof. exact (MK_COMB (@lem3592707 A B x x' g s f x'') (@lem3592708 A B x x' g s f x'')). Qed.
Lemma lem3592710 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term733 A B x x' g s f x'') = (term733 A B x x' g s f x'')) = (((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')) = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x''))).
Proof. exact (TRANS (@lem3592704 A B x x' g s f x'') (@lem3592709 A B x x' g s f x'')). Qed.
Lemma lem3592711 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')) = ((term711 A B x x' g s f x'') = (term732 A B x x' g s f x'')).
Proof. exact (EQ_MP (@lem3592710 A B x x' g s f x'') (@lem3592701 A B x x' g s f x'')). Qed.
Lemma lem3592712 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term711 A B x x' g s f x'') = (term732 A B x x' g s f x'').
Proof. exact (EQ_MP (@lem3592711 A B x x' g s f x'') (@lem3592698 A B x x' g s f x'')). Qed.
Lemma lem3592714 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592715 {B : Type'} (P : Prop) (Q : B -> Prop) : (term489 B P Q) = (term490 B P Q).
Proof. exact (@lem3592714 B P Q). Qed.
Lemma lem3592716 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term736 A B x x' g s f x'' x''') = (term737 A B x x' g s f x'' x''').
Proof. exact (@lem3592715 B (term511 A B x x'' g x' f s x''') (term658 A B g s f x'' x''')). Qed.
Lemma lem3592717 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) (x'' : A) : (term738 A B g s f x' x'' x) = (term657 A B x g s f x' x'').
Proof. exact (eq_refl (term738 A B g s f x' x'' x)). Qed.
Lemma lem3592718 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term739 A B g s f x x') = (term658 A B g s f x x').
Proof. exact (fun_ext (fun x'' : B => @lem3592717 A B x'' g s f x x')). Qed.
Lemma lem3592719 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592720 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term740 A B g s f x x') = (term659 A B g s f x x').
Proof. exact (MK_COMB (@lem3592719 B) (@lem3592718 A B g s f x x')). Qed.
Lemma lem3592721 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term727 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term727 A B x x' g x'' f s x''')). Qed.
Lemma lem3592722 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term736 A B x x' g s f x'' x''') = (term729 A B x x' g s f x'' x''').
Proof. exact (MK_COMB (@lem3592721 A B x x'' g x' f s x''') (@lem3592720 A B g s f x'' x''')). Qed.
Lemma lem3592723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592724 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term741 A B x x' g s f x'' x''') = (term742 A B x x' g s f x'' x''').
Proof. exact (MK_COMB (@lem3592723) (@lem3592722 A B x x' g s f x'' x''')). Qed.
Lemma lem3592725 {A B : Type'} (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term738 A B g s f x x' x'') = (term657 A B x'' g s f x x').
Proof. exact (eq_refl (term738 A B g s f x x' x'')). Qed.
Lemma lem3592726 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term727 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term727 A B x x' g x'' f s x''')). Qed.
Lemma lem3592727 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term743 A B x x' g s f x''' x'''' x'') = (term744 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592726 A B x x''' g x' f s x'''') (@lem3592725 A B x'' g s f x''' x'''')). Qed.
Lemma lem3592728 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term745 A B x x' g s f x'' x''') = (term746 A B x x' g s f x'' x''').
Proof. exact (fun_ext (fun x'''' : B => @lem3592727 A B x x' x'''' g s f x'' x''')). Qed.
Lemma lem3592729 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592730 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term737 A B x x' g s f x'' x''') = (term747 A B x x' g s f x'' x''').
Proof. exact (MK_COMB (@lem3592729 B) (@lem3592728 A B x x' g s f x'' x''')). Qed.
Lemma lem3592731 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : ((term736 A B x x' g s f x'' x''') = (term737 A B x x' g s f x'' x''')) = ((term729 A B x x' g s f x'' x''') = (term747 A B x x' g s f x'' x''')).
Proof. exact (MK_COMB (@lem3592724 A B x x' g s f x'' x''') (@lem3592730 A B x x' g s f x'' x''')). Qed.
Lemma lem3592732 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term729 A B x x' g s f x'' x''') = (term747 A B x x' g s f x'' x''').
Proof. exact (EQ_MP (@lem3592731 A B x x' g s f x'' x''') (@lem3592716 A B x x' g s f x'' x''')). Qed.
Lemma lem3592734 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592735 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (@lem3592734 A P Q). Qed.
Lemma lem3592736 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term748 A B x x' x'' g s f x''' x'''') = (term749 A B x x' x'' g s f x''' x'''').
Proof. exact (@lem3592735 A (term511 A B x x''' g x' f s x'''') (term656 A B x'' g s f x''' x'''')). Qed.
Lemma lem3592737 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term750 A B x'' g s f x x' x''') = (term655 A B x'' x''' g s f x x').
Proof. exact (eq_refl (term750 A B x'' g s f x x' x''')). Qed.
Lemma lem3592738 {A B : Type'} (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term751 A B x'' g s f x x') = (term656 A B x'' g s f x x').
Proof. exact (fun_ext (fun x''' : A => @lem3592737 A B x'' x''' g s f x x')). Qed.
Lemma lem3592739 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592740 {A B : Type'} (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term752 A B x'' g s f x x') = (term657 A B x'' g s f x x').
Proof. exact (MK_COMB (@lem3592739 A) (@lem3592738 A B x'' g s f x x')). Qed.
Lemma lem3592741 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term727 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term727 A B x x' g x'' f s x''')). Qed.
Lemma lem3592742 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term748 A B x x' x'' g s f x''' x'''') = (term744 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592741 A B x x''' g x' f s x'''') (@lem3592740 A B x'' g s f x''' x'''')). Qed.
Lemma lem3592743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592744 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term753 A B x x' x'' g s f x''' x'''') = (term754 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592743) (@lem3592742 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592745 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term750 A B x'' g s f x x' x''') = (term655 A B x'' x''' g s f x x').
Proof. exact (eq_refl (term750 A B x'' g s f x x' x''')). Qed.
Lemma lem3592746 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term727 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term727 A B x x' g x'' f s x''')). Qed.
Lemma lem3592747 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term755 A B x x' x'' g s f x'''' x''''' x''') = (term756 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592746 A B x x'''' g x' f s x''''') (@lem3592745 A B x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592748 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term757 A B x x' x'' g s f x''' x'''') = (term758 A B x x' x'' g s f x''' x'''').
Proof. exact (fun_ext (fun x''''' : A => @lem3592747 A B x x' x'' x''''' g s f x''' x'''')). Qed.
Lemma lem3592749 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592750 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term749 A B x x' x'' g s f x''' x'''') = (term759 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592749 A) (@lem3592748 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592751 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : ((term748 A B x x' x'' g s f x''' x'''') = (term749 A B x x' x'' g s f x''' x'''')) = ((term744 A B x x' x'' g s f x''' x'''') = (term759 A B x x' x'' g s f x''' x'''')).
Proof. exact (MK_COMB (@lem3592744 A B x x' x'' g s f x''' x'''') (@lem3592750 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592752 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term744 A B x x' x'' g s f x''' x'''') = (term759 A B x x' x'' g s f x''' x'''').
Proof. exact (EQ_MP (@lem3592751 A B x x' x'' g s f x''' x'''') (@lem3592736 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592754 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592755 {B : Type'} (P : Prop) (Q : B -> Prop) : (term489 B P Q) = (term490 B P Q).
Proof. exact (@lem3592754 B P Q). Qed.
Lemma lem3592756 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term760 A B x x' x'' x''' g s f x'''' x''''') = (term761 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (@lem3592755 B (term511 A B x x'''' g x' f s x''''') (term654 A B x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592757 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (x' : B) (s : A -> Prop) (f : A -> B) (x : A) (x'''' : A) : (term762 A B x'' x''' g s f x x'''' x') = (term653 A B x'' x''' g x' s f x x'''').
Proof. exact (eq_refl (term762 A B x'' x''' g s f x x'''' x')). Qed.
Lemma lem3592758 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term763 A B x'' x''' g s f x x') = (term654 A B x'' x''' g s f x x').
Proof. exact (fun_ext (fun x'''' : B => @lem3592757 A B x'' x''' g x'''' s f x x')). Qed.
Lemma lem3592759 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592760 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term764 A B x'' x''' g s f x x') = (term655 A B x'' x''' g s f x x').
Proof. exact (MK_COMB (@lem3592759 B) (@lem3592758 A B x'' x''' g s f x x')). Qed.
Lemma lem3592761 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term727 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term727 A B x x' g x'' f s x''')). Qed.
Lemma lem3592762 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term760 A B x x' x'' x''' g s f x'''' x''''') = (term756 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592761 A B x x'''' g x' f s x''''') (@lem3592760 A B x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592764 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term765 A B x x' x'' x''' g s f x'''' x''''') = (term766 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592763) (@lem3592762 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592765 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term762 A B x'' x''' g s f x x' x'''') = (term653 A B x'' x''' g x'''' s f x x').
Proof. exact (eq_refl (term762 A B x'' x''' g s f x x' x'''')). Qed.
Lemma lem3592766 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term727 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term727 A B x x' g x'' f s x''')). Qed.
Lemma lem3592767 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term767 A B x x' x'' x''' g s f x''''' x'''''' x'''') = (term768 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3592766 A B x x''''' g x' f s x'''''') (@lem3592765 A B x'' x''' g x'''' s f x''''' x'''''')). Qed.
Lemma lem3592768 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term769 A B x x' x'' x''' g s f x'''' x''''') = (term770 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (fun_ext (fun x'''''' : B => @lem3592767 A B x x' x'' x''' g x'''''' s f x'''' x''''')). Qed.
Lemma lem3592769 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592770 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term761 A B x x' x'' x''' g s f x'''' x''''') = (term771 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592769 B) (@lem3592768 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592771 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : ((term760 A B x x' x'' x''' g s f x'''' x''''') = (term761 A B x x' x'' x''' g s f x'''' x''''')) = ((term756 A B x x' x'' x''' g s f x'''' x''''') = (term771 A B x x' x'' x''' g s f x'''' x''''')).
Proof. exact (MK_COMB (@lem3592764 A B x x' x'' x''' g s f x'''' x''''') (@lem3592770 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592772 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term756 A B x x' x'' x''' g s f x'''' x''''') = (term771 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (EQ_MP (@lem3592771 A B x x' x'' x''' g s f x'''' x''''') (@lem3592756 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592774 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592775 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (@lem3592774 A P Q). Qed.
Lemma lem3592776 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term772 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term773 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (@lem3592775 A (term511 A B x x''''' g x' f s x'''''') (term652 A B x'' x''' g x'''' s f x''''' x'''''')). Qed.
Lemma lem3592777 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (x''''' : A) (f : A -> B) (x : A) (x' : A) : (term774 A B x'' x''' g x'''' s f x x' x''''') = (term650 A B x'' x''' g x'''' s x''''' f x x').
Proof. exact (eq_refl (term774 A B x'' x''' g x'''' s f x x' x''''')). Qed.
Lemma lem3592778 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term775 A B x'' x''' g x'''' s f x x') = (term652 A B x'' x''' g x'''' s f x x').
Proof. exact (fun_ext (fun x''''' : A => @lem3592777 A B x'' x''' g x'''' s x''''' f x x')). Qed.
Lemma lem3592779 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592780 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x : A) (x' : A) : (term776 A B x'' x''' g x'''' s f x x') = (term653 A B x'' x''' g x'''' s f x x').
Proof. exact (MK_COMB (@lem3592779 A) (@lem3592778 A B x'' x''' g x'''' s f x x')). Qed.
Lemma lem3592781 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term727 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term727 A B x x' g x'' f s x''')). Qed.
Lemma lem3592782 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term772 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term768 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3592781 A B x x''''' g x' f s x'''''') (@lem3592780 A B x'' x''' g x'''' s f x''''' x'''''')). Qed.
Lemma lem3592783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592784 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term777 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term778 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3592783) (@lem3592782 A B x x' x'' x''' g x'''' s f x''''' x'''''')). Qed.
Lemma lem3592785 {A B : Type'} (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (x''''' : A) (f : A -> B) (x : A) (x' : A) : (term774 A B x'' x''' g x'''' s f x x' x''''') = (term650 A B x'' x''' g x'''' s x''''' f x x').
Proof. exact (eq_refl (term774 A B x'' x''' g x'''' s f x x' x''''')). Qed.
Lemma lem3592786 {A B : Type'} (x : B) (x' : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term727 A B x x' g x'' f s x''') = (term727 A B x x' g x'' f s x''').
Proof. exact (eq_refl (term727 A B x x' g x'' f s x''')). Qed.
Lemma lem3592787 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (x''''' : A) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term779 A B x x' x'' x''' g x'''' s f x'''''' x''''''' x''''') = (term780 A B x x' x'' x''' g x'''' s x''''' f x'''''' x''''''').
Proof. exact (MK_COMB (@lem3592786 A B x x'''''' g x' f s x''''''') (@lem3592785 A B x'' x''' g x'''' s x''''' f x'''''' x''''''')). Qed.
Lemma lem3592788 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term781 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term782 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (fun_ext (fun x''''''' : A => @lem3592787 A B x x' x'' x''' g x'''' s x''''''' f x''''' x'''''')). Qed.
Lemma lem3592789 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592790 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term773 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term783 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3592789 A) (@lem3592788 A B x x' x'' x''' g x'''' s f x''''' x'''''')). Qed.
Lemma lem3592791 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : ((term772 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term773 A B x x' x'' x''' g x'''' s f x''''' x'''''')) = ((term768 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term783 A B x x' x'' x''' g x'''' s f x''''' x'''''')).
Proof. exact (MK_COMB (@lem3592784 A B x x' x'' x''' g x'''' s f x''''' x'''''') (@lem3592790 A B x x' x'' x''' g x'''' s f x''''' x'''''')). Qed.
Lemma lem3592792 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term768 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term783 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (EQ_MP (@lem3592791 A B x x' x'' x''' g x'''' s f x''''' x'''''') (@lem3592776 A B x x' x'' x''' g x'''' s f x''''' x'''''')). Qed.
Lemma lem3592793 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term770 A B x x' x'' x''' g s f x'''' x''''') = (term784 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (fun_ext (fun x'''''' : B => @lem3592792 A B x x' x'' x''' g x'''''' s f x'''' x''''')). Qed.
Lemma lem3592794 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592795 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term771 A B x x' x'' x''' g s f x'''' x''''') = (term785 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592794 B) (@lem3592793 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592796 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term756 A B x x' x'' x''' g s f x'''' x''''') = (term785 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (TRANS (@lem3592772 A B x x' x'' x''' g s f x'''' x''''') (@lem3592795 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592797 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term758 A B x x' x'' g s f x''' x'''') = (term786 A B x x' x'' g s f x''' x'''').
Proof. exact (fun_ext (fun x''''' : A => @lem3592796 A B x x' x'' x''''' g s f x''' x'''')). Qed.
Lemma lem3592798 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592799 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term759 A B x x' x'' g s f x''' x'''') = (term787 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592798 A) (@lem3592797 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592800 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term744 A B x x' x'' g s f x''' x'''') = (term787 A B x x' x'' g s f x''' x'''').
Proof. exact (TRANS (@lem3592752 A B x x' x'' g s f x''' x'''') (@lem3592799 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592801 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term746 A B x x' g s f x'' x''') = (term788 A B x x' g s f x'' x''').
Proof. exact (fun_ext (fun x'''' : B => @lem3592800 A B x x' x'''' g s f x'' x''')). Qed.
Lemma lem3592802 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592803 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term747 A B x x' g s f x'' x''') = (term789 A B x x' g s f x'' x''').
Proof. exact (MK_COMB (@lem3592802 B) (@lem3592801 A B x x' g s f x'' x''')). Qed.
Lemma lem3592804 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term729 A B x x' g s f x'' x''') = (term789 A B x x' g s f x'' x''').
Proof. exact (TRANS (@lem3592732 A B x x' g s f x'' x''') (@lem3592803 A B x x' g s f x'' x''')). Qed.
Lemma lem3592805 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term731 A B x x' g s f x'') = (term790 A B x x' g s f x'').
Proof. exact (fun_ext (fun x''' : A => @lem3592804 A B x x' g s f x'' x''')). Qed.
Lemma lem3592806 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592807 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term732 A B x x' g s f x'') = (term791 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592806 A) (@lem3592805 A B x x' g s f x'')). Qed.
Lemma lem3592808 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term711 A B x x' g s f x'') = (term791 A B x x' g s f x'').
Proof. exact (TRANS (@lem3592712 A B x x' g s f x'') (@lem3592807 A B x x' g s f x'')). Qed.
Lemma lem3592809 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term713 A B x g s f x') = (term792 A B x g s f x').
Proof. exact (fun_ext (fun x'' : B => @lem3592808 A B x x'' g s f x')). Qed.
Lemma lem3592810 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592811 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term714 A B x g s f x') = (term793 A B x g s f x').
Proof. exact (MK_COMB (@lem3592810 B) (@lem3592809 A B x g s f x')). Qed.
Lemma lem3592812 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term696 A B x g s f x') = (term793 A B x g s f x').
Proof. exact (TRANS (@lem3592671 A B x g s f x') (@lem3592811 A B x g s f x')). Qed.
Lemma lem3592813 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term698 A B x g s f) = (term794 A B x g s f).
Proof. exact (fun_ext (fun x' : A => @lem3592812 A B x g s f x')). Qed.
Lemma lem3592814 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592815 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term699 A B x g s f) = (term795 A B x g s f).
Proof. exact (MK_COMB (@lem3592814 A) (@lem3592813 A B x g s f)). Qed.
Lemma lem3592816 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term678 A B x g s f) = (term795 A B x g s f).
Proof. exact (TRANS (@lem3592645 A B x g s f) (@lem3592815 A B x g s f)). Qed.
Lemma lem3592817 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term680 A B g s f) = (term796 A B g s f).
Proof. exact (fun_ext (fun x : B => @lem3592816 A B x g s f)). Qed.
Lemma lem3592818 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592819 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term681 A B g s f) = (term797 A B g s f).
Proof. exact (MK_COMB (@lem3592818 B) (@lem3592817 A B g s f)). Qed.
Lemma lem3592820 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term664 A B g s f) = (term797 A B g s f).
Proof. exact (TRANS (@lem3592618 A B g s f) (@lem3592819 A B g s f)). Qed.
Lemma lem3592821 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term315 A B g s f) = (term797 A B g s f).
Proof. exact (TRANS (@lem3592592 A B g s f) (@lem3592820 A B g s f)). Qed.
Lemma lem3592822 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term316 A B g s f) = (term798 A B g s f).
Proof. exact (MK_COMB (@lem3591979 A B g f s) (@lem3592821 A B g s f)). Qed.
Lemma lem3592826 {A : Type'} (P : A -> Prop) (Q : Prop) : (term665 A P Q) = (term666 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3592827 {A : Type'} (P : A -> Prop) (Q : Prop) : (term665 A P Q) = (term666 A P Q).
Proof. exact (@lem3592826 A P Q). Qed.
Lemma lem3592828 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term799 A B g s f) = (term800 A B g s f).
Proof. exact (@lem3592827 A (term368 A B g f s) (term797 A B g s f)). Qed.
Lemma lem3592829 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term801 A B g f s x) = (term367 A B g f s x).
Proof. exact (eq_refl (term801 A B g f s x)). Qed.
Lemma lem3592830 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term802 A B g f s) = (term368 A B g f s).
Proof. exact (fun_ext (fun x : A => @lem3592829 A B g f s x)). Qed.
Lemma lem3592831 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592832 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term803 A B g f s) = (term369 A B g f s).
Proof. exact (MK_COMB (@lem3592831 A) (@lem3592830 A B g f s)). Qed.
Lemma lem3592833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592834 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term804 A B g f s) = (term370 A B g f s).
Proof. exact (MK_COMB (@lem3592833) (@lem3592832 A B g f s)). Qed.
Lemma lem3592835 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term797 A B g s f) = (term797 A B g s f).
Proof. exact (eq_refl (term797 A B g s f)). Qed.
Lemma lem3592836 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term799 A B g s f) = (term798 A B g s f).
Proof. exact (MK_COMB (@lem3592834 A B g f s) (@lem3592835 A B g s f)). Qed.
Lemma lem3592837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592838 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term805 A B g s f) = (term806 A B g s f).
Proof. exact (MK_COMB (@lem3592837) (@lem3592836 A B g s f)). Qed.
Lemma lem3592839 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term801 A B g f s x) = (term367 A B g f s x).
Proof. exact (eq_refl (term801 A B g f s x)). Qed.
Lemma lem3592840 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592841 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term807 A B g f s x) = (term808 A B g f s x).
Proof. exact (MK_COMB (@lem3592840) (@lem3592839 A B g f s x)). Qed.
Lemma lem3592842 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term797 A B g s f) = (term797 A B g s f).
Proof. exact (eq_refl (term797 A B g s f)). Qed.
Lemma lem3592843 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term809 A B x g s f) = (term810 A B x g s f).
Proof. exact (MK_COMB (@lem3592841 A B g f s x) (@lem3592842 A B g s f)). Qed.
Lemma lem3592844 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term811 A B g s f) = (term812 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3592843 A B x g s f)). Qed.
Lemma lem3592845 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592846 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term800 A B g s f) = (term813 A B g s f).
Proof. exact (MK_COMB (@lem3592845 A) (@lem3592844 A B g s f)). Qed.
Lemma lem3592847 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term799 A B g s f) = (term800 A B g s f)) = ((term798 A B g s f) = (term813 A B g s f)).
Proof. exact (MK_COMB (@lem3592838 A B g s f) (@lem3592846 A B g s f)). Qed.
Lemma lem3592848 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term798 A B g s f) = (term813 A B g s f).
Proof. exact (EQ_MP (@lem3592847 A B g s f) (@lem3592828 A B g s f)). Qed.
Lemma lem3592850 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3592851 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term293 B P Q) = (term292 B P Q).
Proof. exact (@lem3592850 B P Q). Qed.
Lemma lem3592852 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term814 A B x g s f) = (term815 A B x g s f).
Proof. exact (@lem3592851 B (term366 A B g f s x) (term796 A B g s f)). Qed.
Lemma lem3592853 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term816 A B g f s x' x) = (term365 A B g x f s x').
Proof. exact (eq_refl (term816 A B g f s x' x)). Qed.
Lemma lem3592854 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term817 A B g f s x) = (term366 A B g f s x).
Proof. exact (fun_ext (fun x' : B => @lem3592853 A B g x' f s x)). Qed.
Lemma lem3592855 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592856 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term818 A B g f s x) = (term367 A B g f s x).
Proof. exact (MK_COMB (@lem3592855 B) (@lem3592854 A B g f s x)). Qed.
Lemma lem3592857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592858 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : (term819 A B g f s x) = (term808 A B g f s x).
Proof. exact (MK_COMB (@lem3592857) (@lem3592856 A B g f s x)). Qed.
Lemma lem3592859 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term820 A B g s f x) = (term795 A B x g s f).
Proof. exact (eq_refl (term820 A B g s f x)). Qed.
Lemma lem3592860 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term821 A B g s f) = (term796 A B g s f).
Proof. exact (fun_ext (fun x : B => @lem3592859 A B x g s f)). Qed.
Lemma lem3592861 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592862 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term822 A B g s f) = (term797 A B g s f).
Proof. exact (MK_COMB (@lem3592861 B) (@lem3592860 A B g s f)). Qed.
Lemma lem3592863 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term814 A B x g s f) = (term810 A B x g s f).
Proof. exact (MK_COMB (@lem3592858 A B g f s x) (@lem3592862 A B g s f)). Qed.
Lemma lem3592864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592865 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term823 A B x g s f) = (term824 A B x g s f).
Proof. exact (MK_COMB (@lem3592864) (@lem3592863 A B x g s f)). Qed.
Lemma lem3592866 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term816 A B g f s x' x) = (term365 A B g x f s x').
Proof. exact (eq_refl (term816 A B g f s x' x)). Qed.
Lemma lem3592867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592868 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term825 A B g f s x' x) = (term826 A B g x f s x').
Proof. exact (MK_COMB (@lem3592867) (@lem3592866 A B g x f s x')). Qed.
Lemma lem3592869 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term820 A B g s f x) = (term795 A B x g s f).
Proof. exact (eq_refl (term820 A B g s f x)). Qed.
Lemma lem3592870 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term827 A B x g s f x') = (term828 A B x x' g s f).
Proof. exact (MK_COMB (@lem3592868 A B g x' f s x) (@lem3592869 A B x' g s f)). Qed.
Lemma lem3592871 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term829 A B x g s f) = (term830 A B x g s f).
Proof. exact (fun_ext (fun x' : B => @lem3592870 A B x x' g s f)). Qed.
Lemma lem3592872 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592873 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term815 A B x g s f) = (term831 A B x g s f).
Proof. exact (MK_COMB (@lem3592872 B) (@lem3592871 A B x g s f)). Qed.
Lemma lem3592874 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term814 A B x g s f) = (term815 A B x g s f)) = ((term810 A B x g s f) = (term831 A B x g s f)).
Proof. exact (MK_COMB (@lem3592865 A B x g s f) (@lem3592873 A B x g s f)). Qed.
Lemma lem3592875 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term810 A B x g s f) = (term831 A B x g s f).
Proof. exact (EQ_MP (@lem3592874 A B x g s f) (@lem3592852 A B x g s f)). Qed.
Lemma lem3592877 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3592878 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term293 A P Q) = (term292 A P Q).
Proof. exact (@lem3592877 A P Q). Qed.
Lemma lem3592879 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term832 A B x x' g s f) = (term833 A B x x' g s f).
Proof. exact (@lem3592878 A (term364 A B g x' f s x) (term794 A B x' g s f)). Qed.
Lemma lem3592880 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term834 A B g x f s x'' x') = (term362 A B g x f x' s x'').
Proof. exact (eq_refl (term834 A B g x f s x'' x')). Qed.
Lemma lem3592881 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term835 A B g x f s x') = (term364 A B g x f s x').
Proof. exact (fun_ext (fun x'' : A => @lem3592880 A B g x f x'' s x')). Qed.
Lemma lem3592882 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592883 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term836 A B g x f s x') = (term365 A B g x f s x').
Proof. exact (MK_COMB (@lem3592882 A) (@lem3592881 A B g x f s x')). Qed.
Lemma lem3592884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592885 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term837 A B g x f s x') = (term826 A B g x f s x').
Proof. exact (MK_COMB (@lem3592884) (@lem3592883 A B g x f s x')). Qed.
Lemma lem3592886 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term838 A B x g s f x') = (term793 A B x g s f x').
Proof. exact (eq_refl (term838 A B x g s f x')). Qed.
Lemma lem3592887 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term839 A B x g s f) = (term794 A B x g s f).
Proof. exact (fun_ext (fun x' : A => @lem3592886 A B x g s f x')). Qed.
Lemma lem3592888 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592889 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term840 A B x g s f) = (term795 A B x g s f).
Proof. exact (MK_COMB (@lem3592888 A) (@lem3592887 A B x g s f)). Qed.
Lemma lem3592890 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term832 A B x x' g s f) = (term828 A B x x' g s f).
Proof. exact (MK_COMB (@lem3592885 A B g x' f s x) (@lem3592889 A B x' g s f)). Qed.
Lemma lem3592891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592892 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term841 A B x x' g s f) = (term842 A B x x' g s f).
Proof. exact (MK_COMB (@lem3592891) (@lem3592890 A B x x' g s f)). Qed.
Lemma lem3592893 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term834 A B g x f s x'' x') = (term362 A B g x f x' s x'').
Proof. exact (eq_refl (term834 A B g x f s x'' x')). Qed.
Lemma lem3592894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3592895 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term843 A B g x f s x'' x') = (term844 A B g x f x' s x'').
Proof. exact (MK_COMB (@lem3592894) (@lem3592893 A B g x f x' s x'')). Qed.
Lemma lem3592896 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term838 A B x g s f x') = (term793 A B x g s f x').
Proof. exact (eq_refl (term838 A B x g s f x')). Qed.
Lemma lem3592897 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term845 A B x x' g s f x'') = (term846 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592895 A B g x' f x'' s x) (@lem3592896 A B x' g s f x'')). Qed.
Lemma lem3592898 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term847 A B x x' g s f) = (term848 A B x x' g s f).
Proof. exact (fun_ext (fun x'' : A => @lem3592897 A B x x' g s f x'')). Qed.
Lemma lem3592899 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592900 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term833 A B x x' g s f) = (term849 A B x x' g s f).
Proof. exact (MK_COMB (@lem3592899 A) (@lem3592898 A B x x' g s f)). Qed.
Lemma lem3592901 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term832 A B x x' g s f) = (term833 A B x x' g s f)) = ((term828 A B x x' g s f) = (term849 A B x x' g s f)).
Proof. exact (MK_COMB (@lem3592892 A B x x' g s f) (@lem3592900 A B x x' g s f)). Qed.
Lemma lem3592902 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term828 A B x x' g s f) = (term849 A B x x' g s f).
Proof. exact (EQ_MP (@lem3592901 A B x x' g s f) (@lem3592879 A B x x' g s f)). Qed.
Lemma lem3592905 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term850 A B x x' g s f) = (term850 A B x x' g s f).
Proof. exact (eq_refl (term850 A B x x' g s f)). Qed.
Lemma lem3592906 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term850 A B x x' g s f) = ((term828 A B x x' g s f) = (term849 A B x x' g s f)).
Proof. exact (eq_refl (term850 A B x x' g s f)). Qed.
Lemma lem3592907 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term851 A B x x' g s f) = (term851 A B x x' g s f).
Proof. exact (eq_refl (term851 A B x x' g s f)). Qed.
Lemma lem3592908 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term850 A B x x' g s f) = (term850 A B x x' g s f)) = ((term850 A B x x' g s f) = ((term828 A B x x' g s f) = (term849 A B x x' g s f))).
Proof. exact (MK_COMB (@lem3592907 A B x x' g s f) (@lem3592906 A B x x' g s f)). Qed.
Lemma lem3592909 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term850 A B x x' g s f) = ((term828 A B x x' g s f) = (term849 A B x x' g s f)).
Proof. exact (eq_refl (term850 A B x x' g s f)). Qed.
Lemma lem3592910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592911 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term851 A B x x' g s f) = (term852 A B x x' g s f).
Proof. exact (MK_COMB (@lem3592910) (@lem3592909 A B x x' g s f)). Qed.
Lemma lem3592912 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term828 A B x x' g s f) = (term849 A B x x' g s f)) = ((term828 A B x x' g s f) = (term849 A B x x' g s f)).
Proof. exact (eq_refl ((term828 A B x x' g s f) = (term849 A B x x' g s f))). Qed.
Lemma lem3592913 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term850 A B x x' g s f) = ((term828 A B x x' g s f) = (term849 A B x x' g s f))) = (((term828 A B x x' g s f) = (term849 A B x x' g s f)) = ((term828 A B x x' g s f) = (term849 A B x x' g s f))).
Proof. exact (MK_COMB (@lem3592911 A B x x' g s f) (@lem3592912 A B x x' g s f)). Qed.
Lemma lem3592914 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term850 A B x x' g s f) = (term850 A B x x' g s f)) = (((term828 A B x x' g s f) = (term849 A B x x' g s f)) = ((term828 A B x x' g s f) = (term849 A B x x' g s f))).
Proof. exact (TRANS (@lem3592908 A B x x' g s f) (@lem3592913 A B x x' g s f)). Qed.
Lemma lem3592915 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : ((term828 A B x x' g s f) = (term849 A B x x' g s f)) = ((term828 A B x x' g s f) = (term849 A B x x' g s f)).
Proof. exact (EQ_MP (@lem3592914 A B x x' g s f) (@lem3592905 A B x x' g s f)). Qed.
Lemma lem3592916 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term828 A B x x' g s f) = (term849 A B x x' g s f).
Proof. exact (EQ_MP (@lem3592915 A B x x' g s f) (@lem3592902 A B x x' g s f)). Qed.
Lemma lem3592918 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592919 {B : Type'} (P : Prop) (Q : B -> Prop) : (term489 B P Q) = (term490 B P Q).
Proof. exact (@lem3592918 B P Q). Qed.
Lemma lem3592920 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term853 A B x x' g s f x'') = (term854 A B x x' g s f x'').
Proof. exact (@lem3592919 B (term362 A B g x' f x'' s x) (term792 A B x' g s f x'')). Qed.
Lemma lem3592921 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term855 A B x g s f x'' x') = (term791 A B x x' g s f x'').
Proof. exact (eq_refl (term855 A B x g s f x'' x')). Qed.
Lemma lem3592922 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term856 A B x g s f x') = (term792 A B x g s f x').
Proof. exact (fun_ext (fun x'' : B => @lem3592921 A B x x'' g s f x')). Qed.
Lemma lem3592923 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592924 {A B : Type'} (x : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x' : A) : (term857 A B x g s f x') = (term793 A B x g s f x').
Proof. exact (MK_COMB (@lem3592923 B) (@lem3592922 A B x g s f x')). Qed.
Lemma lem3592925 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3592926 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term853 A B x x' g s f x'') = (term846 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592925 A B g x' f x'' s x) (@lem3592924 A B x' g s f x'')). Qed.
Lemma lem3592927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592928 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term858 A B x x' g s f x'') = (term859 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592927) (@lem3592926 A B x x' g s f x'')). Qed.
Lemma lem3592929 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term855 A B x g s f x'' x') = (term791 A B x x' g s f x'').
Proof. exact (eq_refl (term855 A B x g s f x'' x')). Qed.
Lemma lem3592930 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3592931 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term860 A B x x' g s f x''' x'') = (term861 A B x x' x'' g s f x''').
Proof. exact (MK_COMB (@lem3592930 A B g x' f x''' s x) (@lem3592929 A B x' x'' g s f x''')). Qed.
Lemma lem3592932 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term862 A B x x' g s f x'') = (term863 A B x x' g s f x'').
Proof. exact (fun_ext (fun x''' : B => @lem3592931 A B x x' x''' g s f x'')). Qed.
Lemma lem3592933 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592934 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term854 A B x x' g s f x'') = (term864 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592933 B) (@lem3592932 A B x x' g s f x'')). Qed.
Lemma lem3592935 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term853 A B x x' g s f x'') = (term854 A B x x' g s f x'')) = ((term846 A B x x' g s f x'') = (term864 A B x x' g s f x'')).
Proof. exact (MK_COMB (@lem3592928 A B x x' g s f x'') (@lem3592934 A B x x' g s f x'')). Qed.
Lemma lem3592936 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term846 A B x x' g s f x'') = (term864 A B x x' g s f x'').
Proof. exact (EQ_MP (@lem3592935 A B x x' g s f x'') (@lem3592920 A B x x' g s f x'')). Qed.
Lemma lem3592938 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592939 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (@lem3592938 A P Q). Qed.
Lemma lem3592940 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term865 A B x x' x'' g s f x''') = (term866 A B x x' x'' g s f x''').
Proof. exact (@lem3592939 A (term362 A B g x' f x''' s x) (term790 A B x' x'' g s f x''')). Qed.
Lemma lem3592941 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term867 A B x x' g s f x'' x''') = (term789 A B x x' g s f x'' x''').
Proof. exact (eq_refl (term867 A B x x' g s f x'' x''')). Qed.
Lemma lem3592942 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term868 A B x x' g s f x'') = (term790 A B x x' g s f x'').
Proof. exact (fun_ext (fun x''' : A => @lem3592941 A B x x' g s f x'' x''')). Qed.
Lemma lem3592943 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592944 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term869 A B x x' g s f x'') = (term791 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3592943 A) (@lem3592942 A B x x' g s f x'')). Qed.
Lemma lem3592945 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3592946 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term865 A B x x' x'' g s f x''') = (term861 A B x x' x'' g s f x''').
Proof. exact (MK_COMB (@lem3592945 A B g x' f x''' s x) (@lem3592944 A B x' x'' g s f x''')). Qed.
Lemma lem3592947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592948 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term870 A B x x' x'' g s f x''') = (term871 A B x x' x'' g s f x''').
Proof. exact (MK_COMB (@lem3592947) (@lem3592946 A B x x' x'' g s f x''')). Qed.
Lemma lem3592949 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term867 A B x x' g s f x'' x''') = (term789 A B x x' g s f x'' x''').
Proof. exact (eq_refl (term867 A B x x' g s f x'' x''')). Qed.
Lemma lem3592950 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3592951 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term872 A B x x' x'' g s f x''' x'''') = (term873 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592950 A B g x' f x''' s x) (@lem3592949 A B x' x'' g s f x''' x'''')). Qed.
Lemma lem3592952 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term874 A B x x' x'' g s f x''') = (term875 A B x x' x'' g s f x''').
Proof. exact (fun_ext (fun x'''' : A => @lem3592951 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592953 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592954 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term866 A B x x' x'' g s f x''') = (term876 A B x x' x'' g s f x''').
Proof. exact (MK_COMB (@lem3592953 A) (@lem3592952 A B x x' x'' g s f x''')). Qed.
Lemma lem3592955 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : ((term865 A B x x' x'' g s f x''') = (term866 A B x x' x'' g s f x''')) = ((term861 A B x x' x'' g s f x''') = (term876 A B x x' x'' g s f x''')).
Proof. exact (MK_COMB (@lem3592948 A B x x' x'' g s f x''') (@lem3592954 A B x x' x'' g s f x''')). Qed.
Lemma lem3592956 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term861 A B x x' x'' g s f x''') = (term876 A B x x' x'' g s f x''').
Proof. exact (EQ_MP (@lem3592955 A B x x' x'' g s f x''') (@lem3592940 A B x x' x'' g s f x''')). Qed.
Lemma lem3592958 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592959 {B : Type'} (P : Prop) (Q : B -> Prop) : (term489 B P Q) = (term490 B P Q).
Proof. exact (@lem3592958 B P Q). Qed.
Lemma lem3592960 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term877 A B x x' x'' g s f x''' x'''') = (term878 A B x x' x'' g s f x''' x'''').
Proof. exact (@lem3592959 B (term362 A B g x' f x''' s x) (term788 A B x' x'' g s f x''' x'''')). Qed.
Lemma lem3592961 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term879 A B x x' g s f x''' x'''' x'') = (term787 A B x x' x'' g s f x''' x'''').
Proof. exact (eq_refl (term879 A B x x' g s f x''' x'''' x'')). Qed.
Lemma lem3592962 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term880 A B x x' g s f x'' x''') = (term788 A B x x' g s f x'' x''').
Proof. exact (fun_ext (fun x'''' : B => @lem3592961 A B x x' x'''' g s f x'' x''')). Qed.
Lemma lem3592963 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592964 {A B : Type'} (x : B) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x''' : A) : (term881 A B x x' g s f x'' x''') = (term789 A B x x' g s f x'' x''').
Proof. exact (MK_COMB (@lem3592963 B) (@lem3592962 A B x x' g s f x'' x''')). Qed.
Lemma lem3592965 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3592966 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term877 A B x x' x'' g s f x''' x'''') = (term873 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592965 A B g x' f x''' s x) (@lem3592964 A B x' x'' g s f x''' x'''')). Qed.
Lemma lem3592967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592968 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term882 A B x x' x'' g s f x''' x'''') = (term883 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592967) (@lem3592966 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592969 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term879 A B x x' g s f x''' x'''' x'') = (term787 A B x x' x'' g s f x''' x'''').
Proof. exact (eq_refl (term879 A B x x' g s f x''' x'''' x'')). Qed.
Lemma lem3592970 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3592971 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term884 A B x x' x'' g s f x'''' x''''' x''') = (term885 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592970 A B g x' f x'''' s x) (@lem3592969 A B x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592972 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term886 A B x x' x'' g s f x''' x'''') = (term887 A B x x' x'' g s f x''' x'''').
Proof. exact (fun_ext (fun x''''' : B => @lem3592971 A B x x' x'' x''''' g s f x''' x'''')). Qed.
Lemma lem3592973 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3592974 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term878 A B x x' x'' g s f x''' x'''') = (term888 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592973 B) (@lem3592972 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592975 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : ((term877 A B x x' x'' g s f x''' x'''') = (term878 A B x x' x'' g s f x''' x'''')) = ((term873 A B x x' x'' g s f x''' x'''') = (term888 A B x x' x'' g s f x''' x'''')).
Proof. exact (MK_COMB (@lem3592968 A B x x' x'' g s f x''' x'''') (@lem3592974 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592976 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term873 A B x x' x'' g s f x''' x'''') = (term888 A B x x' x'' g s f x''' x'''').
Proof. exact (EQ_MP (@lem3592975 A B x x' x'' g s f x''' x'''') (@lem3592960 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592978 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592979 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (@lem3592978 A P Q). Qed.
Lemma lem3592980 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term889 A B x x' x'' x''' g s f x'''' x''''') = (term890 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (@lem3592979 A (term362 A B g x' f x'''' s x) (term786 A B x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592981 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term891 A B x x' x'' g s f x'''' x''''' x''') = (term785 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (eq_refl (term891 A B x x' x'' g s f x'''' x''''' x''')). Qed.
Lemma lem3592982 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term892 A B x x' x'' g s f x''' x'''') = (term786 A B x x' x'' g s f x''' x'''').
Proof. exact (fun_ext (fun x''''' : A => @lem3592981 A B x x' x'' x''''' g s f x''' x'''')). Qed.
Lemma lem3592983 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592984 {A B : Type'} (x : B) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term893 A B x x' x'' g s f x''' x'''') = (term787 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3592983 A) (@lem3592982 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3592985 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3592986 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term889 A B x x' x'' x''' g s f x'''' x''''') = (term885 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592985 A B g x' f x'''' s x) (@lem3592984 A B x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3592988 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term894 A B x x' x'' x''' g s f x'''' x''''') = (term895 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592987) (@lem3592986 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592989 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term891 A B x x' x'' g s f x'''' x''''' x''') = (term785 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (eq_refl (term891 A B x x' x'' g s f x'''' x''''' x''')). Qed.
Lemma lem3592990 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3592991 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term896 A B x x' x'' x''' g s f x''''' x'''''' x'''') = (term897 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3592990 A B g x' f x''''' s x) (@lem3592989 A B x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3592992 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term898 A B x x' x'' x''' g s f x'''' x''''') = (term899 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (fun_ext (fun x'''''' : A => @lem3592991 A B x x' x'' x''' x'''''' g s f x'''' x''''')). Qed.
Lemma lem3592993 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3592994 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term890 A B x x' x'' x''' g s f x'''' x''''') = (term900 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3592993 A) (@lem3592992 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592995 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : ((term889 A B x x' x'' x''' g s f x'''' x''''') = (term890 A B x x' x'' x''' g s f x'''' x''''')) = ((term885 A B x x' x'' x''' g s f x'''' x''''') = (term900 A B x x' x'' x''' g s f x'''' x''''')).
Proof. exact (MK_COMB (@lem3592988 A B x x' x'' x''' g s f x'''' x''''') (@lem3592994 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592996 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term885 A B x x' x'' x''' g s f x'''' x''''') = (term900 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (EQ_MP (@lem3592995 A B x x' x'' x''' g s f x'''' x''''') (@lem3592980 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3592998 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3592999 {B : Type'} (P : Prop) (Q : B -> Prop) : (term489 B P Q) = (term490 B P Q).
Proof. exact (@lem3592998 B P Q). Qed.
Lemma lem3593000 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term901 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term902 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (@lem3592999 B (term362 A B g x' f x''''' s x) (term784 A B x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3593001 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term903 A B x x' x'' x''' g s f x''''' x'''''' x'''') = (term783 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (eq_refl (term903 A B x x' x'' x''' g s f x''''' x'''''' x'''')). Qed.
Lemma lem3593002 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term904 A B x x' x'' x''' g s f x'''' x''''') = (term784 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (fun_ext (fun x'''''' : B => @lem3593001 A B x x' x'' x''' g x'''''' s f x'''' x''''')). Qed.
Lemma lem3593003 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3593004 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term905 A B x x' x'' x''' g s f x'''' x''''') = (term785 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3593003 B) (@lem3593002 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3593005 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3593006 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term901 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term897 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3593005 A B g x' f x''''' s x) (@lem3593004 A B x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3593007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593008 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term906 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term907 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3593007) (@lem3593006 A B x x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3593009 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term903 A B x x' x'' x''' g s f x''''' x'''''' x'''') = (term783 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (eq_refl (term903 A B x x' x'' x''' g s f x''''' x'''''' x'''')). Qed.
Lemma lem3593010 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3593011 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term908 A B x x' x'' x''' x'''' g s f x'''''' x''''''' x''''') = (term909 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''').
Proof. exact (MK_COMB (@lem3593010 A B g x' f x'''''' s x) (@lem3593009 A B x' x'' x''' x'''' g x''''' s f x'''''' x''''''')). Qed.
Lemma lem3593012 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term910 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term911 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (fun_ext (fun x''''''' : B => @lem3593011 A B x x' x'' x''' x'''' g x''''''' s f x''''' x'''''')). Qed.
Lemma lem3593013 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3593014 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term902 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term912 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3593013 B) (@lem3593012 A B x x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3593015 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : ((term901 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term902 A B x x' x'' x''' x'''' g s f x''''' x'''''')) = ((term897 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term912 A B x x' x'' x''' x'''' g s f x''''' x'''''')).
Proof. exact (MK_COMB (@lem3593008 A B x x' x'' x''' x'''' g s f x''''' x'''''') (@lem3593014 A B x x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3593016 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term897 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term912 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (EQ_MP (@lem3593015 A B x x' x'' x''' x'''' g s f x''''' x'''''') (@lem3593000 A B x x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3593018 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3593019 {A : Type'} (P : Prop) (Q : A -> Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (@lem3593018 A P Q). Qed.
Lemma lem3593020 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term913 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') = (term914 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''').
Proof. exact (@lem3593019 A (term362 A B g x' f x'''''' s x) (term782 A B x' x'' x''' x'''' g x''''' s f x'''''' x''''''')). Qed.
Lemma lem3593021 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (x''''' : A) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term915 A B x x' x'' x''' g x'''' s f x'''''' x''''''' x''''') = (term780 A B x x' x'' x''' g x'''' s x''''' f x'''''' x''''''').
Proof. exact (eq_refl (term915 A B x x' x'' x''' g x'''' s f x'''''' x''''''' x''''')). Qed.
Lemma lem3593022 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term916 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term782 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (fun_ext (fun x''''''' : A => @lem3593021 A B x x' x'' x''' g x'''' s x''''''' f x''''' x'''''')). Qed.
Lemma lem3593023 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3593024 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term917 A B x x' x'' x''' g x'''' s f x''''' x'''''') = (term783 A B x x' x'' x''' g x'''' s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3593023 A) (@lem3593022 A B x x' x'' x''' g x'''' s f x''''' x'''''')). Qed.
Lemma lem3593025 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3593026 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term913 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') = (term909 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''').
Proof. exact (MK_COMB (@lem3593025 A B g x' f x'''''' s x) (@lem3593024 A B x' x'' x''' x'''' g x''''' s f x'''''' x''''''')). Qed.
Lemma lem3593027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593028 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term918 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') = (term919 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''').
Proof. exact (MK_COMB (@lem3593027) (@lem3593026 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''')). Qed.
Lemma lem3593029 {A B : Type'} (x : B) (x' : B) (x'' : B) (x''' : A) (g : B -> A) (x'''' : B) (s : A -> Prop) (x''''' : A) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term915 A B x x' x'' x''' g x'''' s f x'''''' x''''''' x''''') = (term780 A B x x' x'' x''' g x'''' s x''''' f x'''''' x''''''').
Proof. exact (eq_refl (term915 A B x x' x'' x''' g x'''' s f x'''''' x''''''' x''''')). Qed.
Lemma lem3593030 {A B : Type'} (g : B -> A) (x : B) (f : A -> B) (x' : A) (s : A -> Prop) (x'' : A) : (term844 A B g x f x' s x'') = (term844 A B g x f x' s x'').
Proof. exact (eq_refl (term844 A B g x f x' s x'')). Qed.
Lemma lem3593031 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (x'''''' : A) (f : A -> B) (x''''''' : A) (x'''''''' : A) : (term920 A B x x' x'' x''' x'''' g x''''' s f x''''''' x'''''''' x'''''') = (term921 A B x x' x'' x''' x'''' g x''''' s x'''''' f x''''''' x'''''''').
Proof. exact (MK_COMB (@lem3593030 A B g x' f x''''''' s x) (@lem3593029 A B x' x'' x''' x'''' g x''''' s x'''''' f x''''''' x'''''''')). Qed.
Lemma lem3593032 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term922 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') = (term923 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''').
Proof. exact (fun_ext (fun x'''''''' : A => @lem3593031 A B x x' x'' x''' x'''' g x''''' s x'''''''' f x'''''' x''''''')). Qed.
Lemma lem3593033 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3593034 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term914 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') = (term924 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''').
Proof. exact (MK_COMB (@lem3593033 A) (@lem3593032 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''')). Qed.
Lemma lem3593035 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (f : A -> B) (x'''''' : A) (x''''''' : A) : ((term913 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') = (term914 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''')) = ((term909 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') = (term924 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''')).
Proof. exact (MK_COMB (@lem3593028 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') (@lem3593034 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''')). Qed.
Lemma lem3593036 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (x''''' : B) (s : A -> Prop) (f : A -> B) (x'''''' : A) (x''''''' : A) : (term909 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') = (term924 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''').
Proof. exact (EQ_MP (@lem3593035 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''') (@lem3593020 A B x x' x'' x''' x'''' g x''''' s f x'''''' x''''''')). Qed.
Lemma lem3593037 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term911 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term925 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (fun_ext (fun x''''''' : B => @lem3593036 A B x x' x'' x''' x'''' g x''''''' s f x''''' x'''''')). Qed.
Lemma lem3593038 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3593039 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term912 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term926 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (MK_COMB (@lem3593038 B) (@lem3593037 A B x x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3593040 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (x'''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''''' : A) (x'''''' : A) : (term897 A B x x' x'' x''' x'''' g s f x''''' x'''''') = (term926 A B x x' x'' x''' x'''' g s f x''''' x'''''').
Proof. exact (TRANS (@lem3593016 A B x x' x'' x''' x'''' g s f x''''' x'''''') (@lem3593039 A B x x' x'' x''' x'''' g s f x''''' x'''''')). Qed.
Lemma lem3593041 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term899 A B x x' x'' x''' g s f x'''' x''''') = (term927 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (fun_ext (fun x'''''' : A => @lem3593040 A B x x' x'' x''' x'''''' g s f x'''' x''''')). Qed.
Lemma lem3593042 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3593043 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term900 A B x x' x'' x''' g s f x'''' x''''') = (term928 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (MK_COMB (@lem3593042 A) (@lem3593041 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3593044 {A B : Type'} (x : A) (x' : B) (x'' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'''' : A) (x''''' : A) : (term885 A B x x' x'' x''' g s f x'''' x''''') = (term928 A B x x' x'' x''' g s f x'''' x''''').
Proof. exact (TRANS (@lem3592996 A B x x' x'' x''' g s f x'''' x''''') (@lem3593043 A B x x' x'' x''' g s f x'''' x''''')). Qed.
Lemma lem3593045 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term887 A B x x' x'' g s f x''' x'''') = (term929 A B x x' x'' g s f x''' x'''').
Proof. exact (fun_ext (fun x''''' : B => @lem3593044 A B x x' x'' x''''' g s f x''' x'''')). Qed.
Lemma lem3593046 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3593047 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term888 A B x x' x'' g s f x''' x'''') = (term930 A B x x' x'' g s f x''' x'''').
Proof. exact (MK_COMB (@lem3593046 B) (@lem3593045 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3593048 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) (x'''' : A) : (term873 A B x x' x'' g s f x''' x'''') = (term930 A B x x' x'' g s f x''' x'''').
Proof. exact (TRANS (@lem3592976 A B x x' x'' g s f x''' x'''') (@lem3593047 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3593049 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term875 A B x x' x'' g s f x''') = (term931 A B x x' x'' g s f x''').
Proof. exact (fun_ext (fun x'''' : A => @lem3593048 A B x x' x'' g s f x''' x'''')). Qed.
Lemma lem3593050 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3593051 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term876 A B x x' x'' g s f x''') = (term932 A B x x' x'' g s f x''').
Proof. exact (MK_COMB (@lem3593050 A) (@lem3593049 A B x x' x'' g s f x''')). Qed.
Lemma lem3593052 {A B : Type'} (x : A) (x' : B) (x'' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x''' : A) : (term861 A B x x' x'' g s f x''') = (term932 A B x x' x'' g s f x''').
Proof. exact (TRANS (@lem3592956 A B x x' x'' g s f x''') (@lem3593051 A B x x' x'' g s f x''')). Qed.
Lemma lem3593053 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term863 A B x x' g s f x'') = (term933 A B x x' g s f x'').
Proof. exact (fun_ext (fun x''' : B => @lem3593052 A B x x' x''' g s f x'')). Qed.
Lemma lem3593054 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3593055 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term864 A B x x' g s f x'') = (term934 A B x x' g s f x'').
Proof. exact (MK_COMB (@lem3593054 B) (@lem3593053 A B x x' g s f x'')). Qed.
Lemma lem3593056 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term846 A B x x' g s f x'') = (term934 A B x x' g s f x'').
Proof. exact (TRANS (@lem3592936 A B x x' g s f x'') (@lem3593055 A B x x' g s f x'')). Qed.
Lemma lem3593057 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term848 A B x x' g s f) = (term935 A B x x' g s f).
Proof. exact (fun_ext (fun x'' : A => @lem3593056 A B x x' g s f x'')). Qed.
Lemma lem3593058 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3593059 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term849 A B x x' g s f) = (term936 A B x x' g s f).
Proof. exact (MK_COMB (@lem3593058 A) (@lem3593057 A B x x' g s f)). Qed.
Lemma lem3593060 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term828 A B x x' g s f) = (term936 A B x x' g s f).
Proof. exact (TRANS (@lem3592916 A B x x' g s f) (@lem3593059 A B x x' g s f)). Qed.
Lemma lem3593061 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term830 A B x g s f) = (term937 A B x g s f).
Proof. exact (fun_ext (fun x' : B => @lem3593060 A B x x' g s f)). Qed.
Lemma lem3593062 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3593063 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term831 A B x g s f) = (term938 A B x g s f).
Proof. exact (MK_COMB (@lem3593062 B) (@lem3593061 A B x g s f)). Qed.
Lemma lem3593064 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) : (term810 A B x g s f) = (term938 A B x g s f).
Proof. exact (TRANS (@lem3592875 A B x g s f) (@lem3593063 A B x g s f)). Qed.
Lemma lem3593065 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term812 A B g s f) = (term939 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem3593064 A B x g s f)). Qed.
Lemma lem3593066 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3593067 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term813 A B g s f) = (term940 A B g s f).
Proof. exact (MK_COMB (@lem3593066 A) (@lem3593065 A B g s f)). Qed.
Lemma lem3593068 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term798 A B g s f) = (term940 A B g s f).
Proof. exact (TRANS (@lem3592848 A B g s f) (@lem3593067 A B g s f)). Qed.
Lemma lem3593069 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term316 A B g s f) = (term940 A B g s f).
Proof. exact (TRANS (@lem3592822 A B g s f) (@lem3593068 A B g s f)). Qed.
Lemma lem3593070 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term291 A B g s f) = (term940 A B g s f).
Proof. exact (TRANS (@lem3591894 A B g s f) (@lem3593069 A B g s f)). Qed.
Lemma lem3593071 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term197 A B g s f) = (term940 A B g s f).
Proof. exact (TRANS (@lem3591073 A B g s f) (@lem3593070 A B g s f)). Qed.
Lemma lem3593072 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term197 A B g s f) : term940 A B g s f.
Proof. exact (EQ_MP (@lem3593071 A B g s f) (@lem3590721 A B g s f h1)). Qed.
Lemma lem3593073 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term938 A B x g s f) : term938 A B x g s f.
Proof. exact (h1). Qed.
Lemma lem3593074 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term936 A B x x' g s f) : term936 A B x x' g s f.
Proof. exact (h1). Qed.
Lemma lem3593075 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (h1 : term934 A B x x' g s f x'') : term934 A B x x' g s f x''.
Proof. exact (h1). Qed.
Lemma lem3593076 {A B : Type'} (x : A) (x' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (h1 : term932 A B x x' x''' g s f x'') : term932 A B x x' x''' g s f x''.
Proof. exact (h1). Qed.
Lemma lem3593077 {A B : Type'} (x : A) (x' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term930 A B x x' x''' g s f x'' x'''') : term930 A B x x' x''' g s f x'' x''''.
Proof. exact (h1). Qed.
Lemma lem3593078 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term928 A B x x' x''' x''''' g s f x'' x'''') : term928 A B x x' x''' x''''' g s f x'' x''''.
Proof. exact (h1). Qed.
Lemma lem3593079 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term926 A B x x' x''' x''''' x'''''' g s f x'' x'''') : term926 A B x x' x''' x''''' x'''''' g s f x'' x''''.
Proof. exact (h1). Qed.
Lemma lem3593080 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term924 A B x x' x''' x''''' x'''''' g x''''''' s f x'' x'''') : term924 A B x x' x''' x''''' x'''''' g x''''''' s f x'' x''''.
Proof. exact (h1). Qed.
Lemma lem3593081 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x''''.
Proof. exact (h1). Qed.
Lemma lem3593098 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593115 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term199 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term199 A B y f s x)). Qed.
Lemma lem3593116 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term205 A B y f s) = (term205 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3593115 A B y f s x)). Qed.
Lemma lem3593117 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593118 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term206 A B y f s) = (term206 A B y f s).
Proof. exact (MK_COMB (@lem3593117 A) (@lem3593116 A B y f s)). Qed.
Lemma lem3593119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593120 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term208 A B y f s) = (term208 A B y f s).
Proof. exact (MK_COMB (@lem3593119) (@lem3593118 A B y f s)). Qed.
Lemma lem3593121 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term210 A B s f g y) = (term210 A B s f g y).
Proof. exact (MK_COMB (@lem3593120 A B y f s) (@lem3593098 A B s f g y)). Qed.
Lemma lem3593122 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term211 A B s f g) = (term211 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593121 A B s f g y)). Qed.
Lemma lem3593123 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593124 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term212 A B s f g).
Proof. exact (MK_COMB (@lem3593123 B) (@lem3593122 A B s f g)). Qed.
Lemma lem3593125 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term212 A B s f g.
Proof. exact (EQ_MP (@lem3593124 A B s f g) (@lem3590852 A B s f g h1)). Qed.
Lemma lem3593196 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) : (term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') = (term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''').
Proof. exact (eq_refl (term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''')). Qed.
Lemma lem3593229 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) : (term401 A B x' x'' g x''' f s x'''') = (term401 A B x' x'' g x''' f s x'''').
Proof. exact (eq_refl (term401 A B x' x'' g x''' f s x'''')). Qed.
Lemma lem3593246 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term199 A B x' f s x) = (term199 A B x' f s x).
Proof. exact (eq_refl (term199 A B x' f s x)). Qed.
Lemma lem3593247 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term205 A B x' f s) = (term205 A B x' f s).
Proof. exact (fun_ext (fun x : A => @lem3593246 A B x' f s x)). Qed.
Lemma lem3593248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593249 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term206 A B x' f s) = (term206 A B x' f s).
Proof. exact (MK_COMB (@lem3593248 A) (@lem3593247 A B x' f s)). Qed.
Lemma lem3593250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3593251 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term247 A B x' f s) = (term247 A B x' f s).
Proof. exact (MK_COMB (@lem3593250) (@lem3593249 A B x' f s)). Qed.
Lemma lem3593252 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) : (term442 A B x' x'' g x''' f s x'''') = (term442 A B x' x'' g x''' f s x'''').
Proof. exact (MK_COMB (@lem3593251 A B x' f s) (@lem3593229 A B x' x'' g x''' f s x'''')). Qed.
Lemma lem3593269 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term199 A B x f s x') = (term199 A B x f s x').
Proof. exact (eq_refl (term199 A B x f s x')). Qed.
Lemma lem3593270 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term205 A B x f s) = (term205 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3593269 A B x f s x')). Qed.
Lemma lem3593271 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593272 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term206 A B x f s) = (term206 A B x f s).
Proof. exact (MK_COMB (@lem3593271 A) (@lem3593270 A B x f s)). Qed.
Lemma lem3593283 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term224 A B x g x') = (term224 A B x g x').
Proof. exact (eq_refl (term224 A B x g x')). Qed.
Lemma lem3593284 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term226 A B x g x' f s) = (term226 A B x g x' f s).
Proof. exact (MK_COMB (@lem3593283 A B x g x') (@lem3593272 A B x' f s)). Qed.
Lemma lem3593285 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term233 A B x g f s) = (term233 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3593284 A B x g x' f s)). Qed.
Lemma lem3593286 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593287 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term234 A B x g f s) = (term234 A B x g f s).
Proof. exact (MK_COMB (@lem3593286 B) (@lem3593285 A B x g f s)). Qed.
Lemma lem3593298 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term235 A B x' f x) = (term235 A B x' f x).
Proof. exact (eq_refl (term235 A B x' f x)). Qed.
Lemma lem3593299 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term237 A B x' x g f s) = (term237 A B x' x g f s).
Proof. exact (MK_COMB (@lem3593298 A B x' f x) (@lem3593287 A B x g f s)). Qed.
Lemma lem3593300 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term244 A B x' g f s) = (term244 A B x' g f s).
Proof. exact (fun_ext (fun x : A => @lem3593299 A B x' x g f s)). Qed.
Lemma lem3593301 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593302 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term245 A B x' g f s) = (term245 A B x' g f s).
Proof. exact (MK_COMB (@lem3593301 A) (@lem3593300 A B x' g f s)). Qed.
Lemma lem3593317 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term377 A B x' f s x'') = (term377 A B x' f s x'').
Proof. exact (eq_refl (term377 A B x' f s x'')). Qed.
Lemma lem3593318 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term379 A B x'' x' g f s) = (term379 A B x'' x' g f s).
Proof. exact (MK_COMB (@lem3593317 A B x' f s x'') (@lem3593302 A B x' g f s)). Qed.
Lemma lem3593319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593320 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term483 A B x'' x' g f s) = (term483 A B x'' x' g f s).
Proof. exact (MK_COMB (@lem3593319) (@lem3593318 A B x'' x' g f s)). Qed.
Lemma lem3593321 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) : (term511 A B x' x'' g x''' f s x'''') = (term511 A B x' x'' g x''' f s x'''').
Proof. exact (MK_COMB (@lem3593320 A B x'' x' g f s) (@lem3593252 A B x' x'' g x''' f s x'''')). Qed.
Lemma lem3593322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593323 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) : (term727 A B x' x'' g x''' f s x'''') = (term727 A B x' x'' g x''' f s x'''').
Proof. exact (MK_COMB (@lem3593322) (@lem3593321 A B x' x'' g x''' f s x'''')). Qed.
Lemma lem3593324 {A B : Type'} (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) : (term780 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') = (term780 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''').
Proof. exact (MK_COMB (@lem3593323 A B x' x'' g x''' f s x'''') (@lem3593196 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''')). Qed.
Lemma lem3593357 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) : (term844 A B g x' f x'' s x) = (term844 A B g x' f x'' s x).
Proof. exact (eq_refl (term844 A B g x' f x'' s x)). Qed.
Lemma lem3593358 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) : (term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') = (term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''').
Proof. exact (MK_COMB (@lem3593357 A B g x' f x'' s x) (@lem3593324 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''')). Qed.
Lemma lem3593359 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x''''.
Proof. exact (EQ_MP (@lem3593358 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') (@lem3593081 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3593360 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : term362 A B g x' f x'' s x.
Proof. exact (h1). Qed.
Lemma lem3593361 {A B : Type'} (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term780 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term780 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x''''.
Proof. exact (h1). Qed.
Lemma lem3593363 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : term326 A B x g x' f s x''.
Proof. exact (proj1 (@lem3593360 A B g x' f x'' s x h1)). Qed.
Lemma lem3593364 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : term19 A B x' f s x''.
Proof. exact (proj2 (@lem3593363 A B g x' f x'' s x h1)). Qed.
Lemma lem3593368 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term511 A B x' x'' g x''' f s x'''') : term511 A B x' x'' g x''' f s x''''.
Proof. exact (h1). Qed.
Lemma lem3593369 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x''''.
Proof. exact (h1). Qed.
Lemma lem3593370 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term379 A B x'' x' g f s.
Proof. exact (h1). Qed.
Lemma lem3593371 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term442 A B x' x'' g x''' f s x''''.
Proof. exact (h1). Qed.
Lemma lem3593372 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term245 A B x' g f s.
Proof. exact (proj2 (@lem3593370 A B x'' x' g f s h1)). Qed.
Lemma lem3593373 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term19 A B x' f s x''.
Proof. exact (proj1 (@lem3593370 A B x'' x' g f s h1)). Qed.
Lemma lem3593376 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term401 A B x' x'' g x''' f s x''''.
Proof. exact (proj2 (@lem3593371 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3593377 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term206 A B x' f s.
Proof. exact (proj1 (@lem3593371 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3593378 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term326 A B x'' g x''' f s x''''.
Proof. exact (proj2 (@lem3593376 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3593380 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term19 A B x''' f s x''''.
Proof. exact (proj2 (@lem3593378 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3593385 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term582 A B x''''' x'''''' g x''''''' s x'''''''' x'' f x''''.
Proof. exact (proj1 (@lem3593369 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3593386 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term537 A B g x''''''' s x'''''''' x'' f x''''.
Proof. exact (proj2 (@lem3593385 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3593387 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term326 A B x'' g x''''' f s x''''''.
Proof. exact (proj1 (@lem3593385 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3593389 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term326 A B x'''' g x''''''' f s x''''''''.
Proof. exact (proj1 (@lem3593386 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3593390 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term19 A B x''''''' f s x''''''''.
Proof. exact (proj2 (@lem3593389 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3593394 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term19 A B x''''' f s x''''''.
Proof. exact (proj2 (@lem3593387 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3593399 {A : Type'} (P : A -> Prop) (Q : Prop) : (term941 A P Q) = (term942 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3593400 {A : Type'} (P : A -> Prop) (Q : Prop) : (term941 A P Q) = (term942 A P Q).
Proof. exact (@lem3593399 A P Q). Qed.
Lemma lem3593401 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B s f g y) = (term944 A B s f g y).
Proof. exact (@lem3593400 A (term205 A B y f s) (term120 A B s f g y)). Qed.
Lemma lem3593402 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term945 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term945 A B y f s x)). Qed.
Lemma lem3593403 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term946 A B y f s) = (term205 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3593402 A B y f s x)). Qed.
Lemma lem3593404 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593405 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term947 A B y f s) = (term206 A B y f s).
Proof. exact (MK_COMB (@lem3593404 A) (@lem3593403 A B y f s)). Qed.
Lemma lem3593406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593407 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term948 A B y f s) = (term208 A B y f s).
Proof. exact (MK_COMB (@lem3593406) (@lem3593405 A B y f s)). Qed.
Lemma lem3593408 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593409 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B s f g y) = (term210 A B s f g y).
Proof. exact (MK_COMB (@lem3593407 A B y f s) (@lem3593408 A B s f g y)). Qed.
Lemma lem3593410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593411 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term949 A B s f g y) = (term950 A B s f g y).
Proof. exact (MK_COMB (@lem3593410) (@lem3593409 A B s f g y)). Qed.
Lemma lem3593412 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term945 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term945 A B y f s x)). Qed.
Lemma lem3593413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593414 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term951 A B y f s x) = (term952 A B y f s x).
Proof. exact (MK_COMB (@lem3593413) (@lem3593412 A B y f s x)). Qed.
Lemma lem3593415 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593416 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term953 A B x s f g y) = (term954 A B x s f g y).
Proof. exact (MK_COMB (@lem3593414 A B y f s x) (@lem3593415 A B s f g y)). Qed.
Lemma lem3593417 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term955 A B s f g y) = (term956 A B s f g y).
Proof. exact (fun_ext (fun x : A => @lem3593416 A B x s f g y)). Qed.
Lemma lem3593418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593419 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term944 A B s f g y) = (term957 A B s f g y).
Proof. exact (MK_COMB (@lem3593418 A) (@lem3593417 A B s f g y)). Qed.
Lemma lem3593420 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : ((term943 A B s f g y) = (term944 A B s f g y)) = ((term210 A B s f g y) = (term957 A B s f g y)).
Proof. exact (MK_COMB (@lem3593411 A B s f g y) (@lem3593419 A B s f g y)). Qed.
Lemma lem3593421 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term210 A B s f g y) = (term957 A B s f g y).
Proof. exact (EQ_MP (@lem3593420 A B s f g y) (@lem3593401 A B s f g y)). Qed.
Lemma lem3593422 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term211 A B s f g) = (term958 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593421 A B s f g y)). Qed.
Lemma lem3593423 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593424 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term959 A B s f g).
Proof. exact (MK_COMB (@lem3593423 B) (@lem3593422 A B s f g)). Qed.
Lemma lem3593447 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (y : B) : (term954 A B x s f g y) = (term960 A B s x f g y).
Proof. exact (@lem19490 (term115 A B s g y) (term199 A B y f s x) ((term118 A B f g y) = y)). Qed.
Lemma lem3593448 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term956 A B s f g y) = (term961 A B s f g y).
Proof. exact (fun_ext (fun x : A => @lem3593447 A B s x f g y)). Qed.
Lemma lem3593449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593450 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term957 A B s f g y) = (term962 A B s f g y).
Proof. exact (MK_COMB (@lem3593449 A) (@lem3593448 A B s f g y)). Qed.
Lemma lem3593451 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term958 A B s f g) = (term963 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593450 A B s f g y)). Qed.
Lemma lem3593452 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593453 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term959 A B s f g) = (term964 A B s f g).
Proof. exact (MK_COMB (@lem3593452 B) (@lem3593451 A B s f g)). Qed.
Lemma lem3593454 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term964 A B s f g).
Proof. exact (TRANS (@lem3593424 A B s f g) (@lem3593453 A B s f g)). Qed.
Lemma lem3593455 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term964 A B s f g.
Proof. exact (EQ_MP (@lem3593454 A B s f g) (@lem3593125 A B s f g h1)). Qed.
Lemma lem3593473 {A : Type'} (P : A -> Prop) (Q : Prop) : (term941 A P Q) = (term942 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3593474 {A : Type'} (P : A -> Prop) (Q : Prop) : (term941 A P Q) = (term942 A P Q).
Proof. exact (@lem3593473 A P Q). Qed.
Lemma lem3593475 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B s f g y) = (term944 A B s f g y).
Proof. exact (@lem3593474 A (term205 A B y f s) (term120 A B s f g y)). Qed.
Lemma lem3593476 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term945 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term945 A B y f s x)). Qed.
Lemma lem3593477 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term946 A B y f s) = (term205 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3593476 A B y f s x)). Qed.
Lemma lem3593478 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593479 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term947 A B y f s) = (term206 A B y f s).
Proof. exact (MK_COMB (@lem3593478 A) (@lem3593477 A B y f s)). Qed.
Lemma lem3593480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593481 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term948 A B y f s) = (term208 A B y f s).
Proof. exact (MK_COMB (@lem3593480) (@lem3593479 A B y f s)). Qed.
Lemma lem3593482 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593483 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B s f g y) = (term210 A B s f g y).
Proof. exact (MK_COMB (@lem3593481 A B y f s) (@lem3593482 A B s f g y)). Qed.
Lemma lem3593484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593485 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term949 A B s f g y) = (term950 A B s f g y).
Proof. exact (MK_COMB (@lem3593484) (@lem3593483 A B s f g y)). Qed.
Lemma lem3593486 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term945 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term945 A B y f s x)). Qed.
Lemma lem3593487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593488 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term951 A B y f s x) = (term952 A B y f s x).
Proof. exact (MK_COMB (@lem3593487) (@lem3593486 A B y f s x)). Qed.
Lemma lem3593489 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593490 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term953 A B x s f g y) = (term954 A B x s f g y).
Proof. exact (MK_COMB (@lem3593488 A B y f s x) (@lem3593489 A B s f g y)). Qed.
Lemma lem3593491 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term955 A B s f g y) = (term956 A B s f g y).
Proof. exact (fun_ext (fun x : A => @lem3593490 A B x s f g y)). Qed.
Lemma lem3593492 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593493 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term944 A B s f g y) = (term957 A B s f g y).
Proof. exact (MK_COMB (@lem3593492 A) (@lem3593491 A B s f g y)). Qed.
Lemma lem3593494 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : ((term943 A B s f g y) = (term944 A B s f g y)) = ((term210 A B s f g y) = (term957 A B s f g y)).
Proof. exact (MK_COMB (@lem3593485 A B s f g y) (@lem3593493 A B s f g y)). Qed.
Lemma lem3593495 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term210 A B s f g y) = (term957 A B s f g y).
Proof. exact (EQ_MP (@lem3593494 A B s f g y) (@lem3593475 A B s f g y)). Qed.
Lemma lem3593496 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term211 A B s f g) = (term958 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593495 A B s f g y)). Qed.
Lemma lem3593497 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593498 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term959 A B s f g).
Proof. exact (MK_COMB (@lem3593497 B) (@lem3593496 A B s f g)). Qed.
Lemma lem3593521 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (y : B) : (term954 A B x s f g y) = (term960 A B s x f g y).
Proof. exact (@lem19490 (term115 A B s g y) (term199 A B y f s x) ((term118 A B f g y) = y)). Qed.
Lemma lem3593522 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term956 A B s f g y) = (term961 A B s f g y).
Proof. exact (fun_ext (fun x : A => @lem3593521 A B s x f g y)). Qed.
Lemma lem3593523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593524 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term957 A B s f g y) = (term962 A B s f g y).
Proof. exact (MK_COMB (@lem3593523 A) (@lem3593522 A B s f g y)). Qed.
Lemma lem3593525 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term958 A B s f g) = (term963 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593524 A B s f g y)). Qed.
Lemma lem3593526 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593527 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term959 A B s f g) = (term964 A B s f g).
Proof. exact (MK_COMB (@lem3593526 B) (@lem3593525 A B s f g)). Qed.
Lemma lem3593528 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term964 A B s f g).
Proof. exact (TRANS (@lem3593498 A B s f g) (@lem3593527 A B s f g)). Qed.
Lemma lem3593529 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term964 A B s f g.
Proof. exact (EQ_MP (@lem3593528 A B s f g) (@lem3593125 A B s f g h1)). Qed.
Lemma lem3593531 {A : Type'} (P : Prop) (Q : A -> Prop) : (term965 A P Q) = (term966 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3593532 {A : Type'} (P : Prop) (Q : A -> Prop) : (term965 A P Q) = (term966 A P Q).
Proof. exact (@lem3593531 A P Q). Qed.
Lemma lem3593533 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term967 A B x g x' f s) = (term968 A B x g x' f s).
Proof. exact (@lem3593532 A (term969 A B x g x') (term205 A B x' f s)). Qed.
Lemma lem3593534 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term945 A B x f s x') = (term199 A B x f s x').
Proof. exact (eq_refl (term945 A B x f s x')). Qed.
Lemma lem3593535 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term946 A B x f s) = (term205 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3593534 A B x f s x')). Qed.
Lemma lem3593536 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593537 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term947 A B x f s) = (term206 A B x f s).
Proof. exact (MK_COMB (@lem3593536 A) (@lem3593535 A B x f s)). Qed.
Lemma lem3593538 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term224 A B x g x') = (term224 A B x g x').
Proof. exact (eq_refl (term224 A B x g x')). Qed.
Lemma lem3593539 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term967 A B x g x' f s) = (term226 A B x g x' f s).
Proof. exact (MK_COMB (@lem3593538 A B x g x') (@lem3593537 A B x' f s)). Qed.
Lemma lem3593540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593541 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term970 A B x g x' f s) = (term971 A B x g x' f s).
Proof. exact (MK_COMB (@lem3593540) (@lem3593539 A B x g x' f s)). Qed.
Lemma lem3593542 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term945 A B x f s x') = (term199 A B x f s x').
Proof. exact (eq_refl (term945 A B x f s x')). Qed.
Lemma lem3593543 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term224 A B x g x') = (term224 A B x g x').
Proof. exact (eq_refl (term224 A B x g x')). Qed.
Lemma lem3593544 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term972 A B x g x' f s x'') = (term973 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3593543 A B x g x') (@lem3593542 A B x' f s x'')). Qed.
Lemma lem3593545 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term974 A B x g x' f s) = (term975 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3593544 A B x g x' f s x'')). Qed.
Lemma lem3593546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593547 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term968 A B x g x' f s) = (term976 A B x g x' f s).
Proof. exact (MK_COMB (@lem3593546 A) (@lem3593545 A B x g x' f s)). Qed.
Lemma lem3593548 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term967 A B x g x' f s) = (term968 A B x g x' f s)) = ((term226 A B x g x' f s) = (term976 A B x g x' f s)).
Proof. exact (MK_COMB (@lem3593541 A B x g x' f s) (@lem3593547 A B x g x' f s)). Qed.
Lemma lem3593549 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term226 A B x g x' f s) = (term976 A B x g x' f s).
Proof. exact (EQ_MP (@lem3593548 A B x g x' f s) (@lem3593533 A B x g x' f s)). Qed.
Lemma lem3593550 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term233 A B x g f s) = (term977 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3593549 A B x g x' f s)). Qed.
Lemma lem3593551 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593552 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term234 A B x g f s) = (term978 A B x g f s).
Proof. exact (MK_COMB (@lem3593551 B) (@lem3593550 A B x g f s)). Qed.
Lemma lem3593553 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term235 A B x' f x) = (term235 A B x' f x).
Proof. exact (eq_refl (term235 A B x' f x)). Qed.
Lemma lem3593554 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term237 A B x' x g f s) = (term979 A B x' x g f s).
Proof. exact (MK_COMB (@lem3593553 A B x' f x) (@lem3593552 A B x g f s)). Qed.
Lemma lem3593556 {A : Type'} (P : Prop) (Q : A -> Prop) : (term965 A P Q) = (term966 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3593557 {B : Type'} (P : Prop) (Q : B -> Prop) : (term965 B P Q) = (term966 B P Q).
Proof. exact (@lem3593556 B P Q). Qed.
Lemma lem3593558 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term980 A B x' x g f s) = (term981 A B x' x g f s).
Proof. exact (@lem3593557 B (term982 A B x' f x) (term977 A B x g f s)). Qed.
Lemma lem3593559 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term983 A B x g f s x') = (term976 A B x g x' f s).
Proof. exact (eq_refl (term983 A B x g f s x')). Qed.
Lemma lem3593560 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term984 A B x g f s) = (term977 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3593559 A B x g x' f s)). Qed.
Lemma lem3593561 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593562 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term985 A B x g f s) = (term978 A B x g f s).
Proof. exact (MK_COMB (@lem3593561 B) (@lem3593560 A B x g f s)). Qed.
Lemma lem3593563 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term235 A B x' f x) = (term235 A B x' f x).
Proof. exact (eq_refl (term235 A B x' f x)). Qed.
Lemma lem3593564 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term980 A B x' x g f s) = (term979 A B x' x g f s).
Proof. exact (MK_COMB (@lem3593563 A B x' f x) (@lem3593562 A B x g f s)). Qed.
Lemma lem3593565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593566 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term986 A B x' x g f s) = (term987 A B x' x g f s).
Proof. exact (MK_COMB (@lem3593565) (@lem3593564 A B x' x g f s)). Qed.
Lemma lem3593567 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term983 A B x g f s x') = (term976 A B x g x' f s).
Proof. exact (eq_refl (term983 A B x g f s x')). Qed.
Lemma lem3593568 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term235 A B x' f x) = (term235 A B x' f x).
Proof. exact (eq_refl (term235 A B x' f x)). Qed.
Lemma lem3593569 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term988 A B x' x g f s x'') = (term989 A B x' x g x'' f s).
Proof. exact (MK_COMB (@lem3593568 A B x' f x) (@lem3593567 A B x g x'' f s)). Qed.
Lemma lem3593570 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term990 A B x' x g f s) = (term991 A B x' x g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3593569 A B x' x g x'' f s)). Qed.
Lemma lem3593571 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593572 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term981 A B x' x g f s) = (term992 A B x' x g f s).
Proof. exact (MK_COMB (@lem3593571 B) (@lem3593570 A B x' x g f s)). Qed.
Lemma lem3593573 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term980 A B x' x g f s) = (term981 A B x' x g f s)) = ((term979 A B x' x g f s) = (term992 A B x' x g f s)).
Proof. exact (MK_COMB (@lem3593566 A B x' x g f s) (@lem3593572 A B x' x g f s)). Qed.
Lemma lem3593574 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term979 A B x' x g f s) = (term992 A B x' x g f s).
Proof. exact (EQ_MP (@lem3593573 A B x' x g f s) (@lem3593558 A B x' x g f s)). Qed.
Lemma lem3593576 {A : Type'} (P : Prop) (Q : A -> Prop) : (term965 A P Q) = (term966 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3593577 {A : Type'} (P : Prop) (Q : A -> Prop) : (term965 A P Q) = (term966 A P Q).
Proof. exact (@lem3593576 A P Q). Qed.
Lemma lem3593578 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term993 A B x' x g x'' f s) = (term994 A B x' x g x'' f s).
Proof. exact (@lem3593577 A (term982 A B x' f x) (term975 A B x g x'' f s)). Qed.
Lemma lem3593579 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term995 A B x g x' f s x'') = (term973 A B x g x' f s x'').
Proof. exact (eq_refl (term995 A B x g x' f s x'')). Qed.
Lemma lem3593580 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term996 A B x g x' f s) = (term975 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3593579 A B x g x' f s x'')). Qed.
Lemma lem3593581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593582 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term997 A B x g x' f s) = (term976 A B x g x' f s).
Proof. exact (MK_COMB (@lem3593581 A) (@lem3593580 A B x g x' f s)). Qed.
Lemma lem3593583 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term235 A B x' f x) = (term235 A B x' f x).
Proof. exact (eq_refl (term235 A B x' f x)). Qed.
Lemma lem3593584 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term993 A B x' x g x'' f s) = (term989 A B x' x g x'' f s).
Proof. exact (MK_COMB (@lem3593583 A B x' f x) (@lem3593582 A B x g x'' f s)). Qed.
Lemma lem3593585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593586 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term998 A B x' x g x'' f s) = (term999 A B x' x g x'' f s).
Proof. exact (MK_COMB (@lem3593585) (@lem3593584 A B x' x g x'' f s)). Qed.
Lemma lem3593587 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term995 A B x g x' f s x'') = (term973 A B x g x' f s x'').
Proof. exact (eq_refl (term995 A B x g x' f s x'')). Qed.
Lemma lem3593588 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term235 A B x' f x) = (term235 A B x' f x).
Proof. exact (eq_refl (term235 A B x' f x)). Qed.
Lemma lem3593589 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term1000 A B x' x g x'' f s x''') = (term1001 A B x' x g x'' f s x''').
Proof. exact (MK_COMB (@lem3593588 A B x' f x) (@lem3593587 A B x g x'' f s x''')). Qed.
Lemma lem3593590 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term1002 A B x' x g x'' f s) = (term1003 A B x' x g x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3593589 A B x' x g x'' f s x''')). Qed.
Lemma lem3593591 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593592 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term994 A B x' x g x'' f s) = (term1004 A B x' x g x'' f s).
Proof. exact (MK_COMB (@lem3593591 A) (@lem3593590 A B x' x g x'' f s)). Qed.
Lemma lem3593593 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : ((term993 A B x' x g x'' f s) = (term994 A B x' x g x'' f s)) = ((term989 A B x' x g x'' f s) = (term1004 A B x' x g x'' f s)).
Proof. exact (MK_COMB (@lem3593586 A B x' x g x'' f s) (@lem3593592 A B x' x g x'' f s)). Qed.
Lemma lem3593594 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term989 A B x' x g x'' f s) = (term1004 A B x' x g x'' f s).
Proof. exact (EQ_MP (@lem3593593 A B x' x g x'' f s) (@lem3593578 A B x' x g x'' f s)). Qed.
Lemma lem3593595 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term991 A B x' x g f s) = (term1005 A B x' x g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3593594 A B x' x g x'' f s)). Qed.
Lemma lem3593596 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593597 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term992 A B x' x g f s) = (term1006 A B x' x g f s).
Proof. exact (MK_COMB (@lem3593596 B) (@lem3593595 A B x' x g f s)). Qed.
Lemma lem3593598 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term979 A B x' x g f s) = (term1006 A B x' x g f s).
Proof. exact (TRANS (@lem3593574 A B x' x g f s) (@lem3593597 A B x' x g f s)). Qed.
Lemma lem3593599 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term237 A B x' x g f s) = (term1006 A B x' x g f s).
Proof. exact (TRANS (@lem3593554 A B x' x g f s) (@lem3593598 A B x' x g f s)). Qed.
Lemma lem3593600 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term244 A B x' g f s) = (term1007 A B x' g f s).
Proof. exact (fun_ext (fun x : A => @lem3593599 A B x' x g f s)). Qed.
Lemma lem3593601 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593602 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term245 A B x' g f s) = (term1008 A B x' g f s).
Proof. exact (MK_COMB (@lem3593601 A) (@lem3593600 A B x' g f s)). Qed.
Lemma lem3593621 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term1001 A B x' x g x'' f s x''') = (term1001 A B x' x g x'' f s x''').
Proof. exact (eq_refl (term1001 A B x' x g x'' f s x''')). Qed.
Lemma lem3593622 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term1003 A B x' x g x'' f s) = (term1003 A B x' x g x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3593621 A B x' x g x'' f s x''')). Qed.
Lemma lem3593623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593624 {A B : Type'} (x' : B) (x : A) (g : B -> A) (x'' : B) (f : A -> B) (s : A -> Prop) : (term1004 A B x' x g x'' f s) = (term1004 A B x' x g x'' f s).
Proof. exact (MK_COMB (@lem3593623 A) (@lem3593622 A B x' x g x'' f s)). Qed.
Lemma lem3593625 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term1005 A B x' x g f s) = (term1005 A B x' x g f s).
Proof. exact (fun_ext (fun x'' : B => @lem3593624 A B x' x g x'' f s)). Qed.
Lemma lem3593626 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593627 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term1006 A B x' x g f s) = (term1006 A B x' x g f s).
Proof. exact (MK_COMB (@lem3593626 B) (@lem3593625 A B x' x g f s)). Qed.
Lemma lem3593628 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term1007 A B x' g f s) = (term1007 A B x' g f s).
Proof. exact (fun_ext (fun x : A => @lem3593627 A B x' x g f s)). Qed.
Lemma lem3593629 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593630 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term1008 A B x' g f s) = (term1008 A B x' g f s).
Proof. exact (MK_COMB (@lem3593629 A) (@lem3593628 A B x' g f s)). Qed.
Lemma lem3593631 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term245 A B x' g f s) = (term1008 A B x' g f s).
Proof. exact (TRANS (@lem3593602 A B x' g f s) (@lem3593630 A B x' g f s)). Qed.
Lemma lem3593632 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1008 A B x' g f s.
Proof. exact (EQ_MP (@lem3593631 A B x' g f s) (@lem3593372 A B x'' x' g f s h1)). Qed.
Lemma lem3593642 {A : Type'} (P : A -> Prop) (Q : Prop) : (term941 A P Q) = (term942 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3593643 {A : Type'} (P : A -> Prop) (Q : Prop) : (term941 A P Q) = (term942 A P Q).
Proof. exact (@lem3593642 A P Q). Qed.
Lemma lem3593644 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B s f g y) = (term944 A B s f g y).
Proof. exact (@lem3593643 A (term205 A B y f s) (term120 A B s f g y)). Qed.
Lemma lem3593645 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term945 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term945 A B y f s x)). Qed.
Lemma lem3593646 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term946 A B y f s) = (term205 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3593645 A B y f s x)). Qed.
Lemma lem3593647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593648 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term947 A B y f s) = (term206 A B y f s).
Proof. exact (MK_COMB (@lem3593647 A) (@lem3593646 A B y f s)). Qed.
Lemma lem3593649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593650 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term948 A B y f s) = (term208 A B y f s).
Proof. exact (MK_COMB (@lem3593649) (@lem3593648 A B y f s)). Qed.
Lemma lem3593651 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593652 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B s f g y) = (term210 A B s f g y).
Proof. exact (MK_COMB (@lem3593650 A B y f s) (@lem3593651 A B s f g y)). Qed.
Lemma lem3593653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593654 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term949 A B s f g y) = (term950 A B s f g y).
Proof. exact (MK_COMB (@lem3593653) (@lem3593652 A B s f g y)). Qed.
Lemma lem3593655 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term945 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term945 A B y f s x)). Qed.
Lemma lem3593656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593657 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term951 A B y f s x) = (term952 A B y f s x).
Proof. exact (MK_COMB (@lem3593656) (@lem3593655 A B y f s x)). Qed.
Lemma lem3593658 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593659 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term953 A B x s f g y) = (term954 A B x s f g y).
Proof. exact (MK_COMB (@lem3593657 A B y f s x) (@lem3593658 A B s f g y)). Qed.
Lemma lem3593660 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term955 A B s f g y) = (term956 A B s f g y).
Proof. exact (fun_ext (fun x : A => @lem3593659 A B x s f g y)). Qed.
Lemma lem3593661 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593662 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term944 A B s f g y) = (term957 A B s f g y).
Proof. exact (MK_COMB (@lem3593661 A) (@lem3593660 A B s f g y)). Qed.
Lemma lem3593663 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : ((term943 A B s f g y) = (term944 A B s f g y)) = ((term210 A B s f g y) = (term957 A B s f g y)).
Proof. exact (MK_COMB (@lem3593654 A B s f g y) (@lem3593662 A B s f g y)). Qed.
Lemma lem3593664 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term210 A B s f g y) = (term957 A B s f g y).
Proof. exact (EQ_MP (@lem3593663 A B s f g y) (@lem3593644 A B s f g y)). Qed.
Lemma lem3593665 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term211 A B s f g) = (term958 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593664 A B s f g y)). Qed.
Lemma lem3593666 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593667 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term959 A B s f g).
Proof. exact (MK_COMB (@lem3593666 B) (@lem3593665 A B s f g)). Qed.
Lemma lem3593690 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (y : B) : (term954 A B x s f g y) = (term960 A B s x f g y).
Proof. exact (@lem19490 (term115 A B s g y) (term199 A B y f s x) ((term118 A B f g y) = y)). Qed.
Lemma lem3593691 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term956 A B s f g y) = (term961 A B s f g y).
Proof. exact (fun_ext (fun x : A => @lem3593690 A B s x f g y)). Qed.
Lemma lem3593692 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593693 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term957 A B s f g y) = (term962 A B s f g y).
Proof. exact (MK_COMB (@lem3593692 A) (@lem3593691 A B s f g y)). Qed.
Lemma lem3593694 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term958 A B s f g) = (term963 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593693 A B s f g y)). Qed.
Lemma lem3593695 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593696 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term959 A B s f g) = (term964 A B s f g).
Proof. exact (MK_COMB (@lem3593695 B) (@lem3593694 A B s f g)). Qed.
Lemma lem3593697 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term964 A B s f g).
Proof. exact (TRANS (@lem3593667 A B s f g) (@lem3593696 A B s f g)). Qed.
Lemma lem3593698 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term964 A B s f g.
Proof. exact (EQ_MP (@lem3593697 A B s f g) (@lem3593125 A B s f g h1)). Qed.
Lemma lem3593706 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term199 A B x' f s x) = (term199 A B x' f s x).
Proof. exact (eq_refl (term199 A B x' f s x)). Qed.
Lemma lem3593707 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term205 A B x' f s) = (term205 A B x' f s).
Proof. exact (fun_ext (fun x : A => @lem3593706 A B x' f s x)). Qed.
Lemma lem3593708 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593710 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term206 A B x' f s) = (term206 A B x' f s).
Proof. exact (MK_COMB (@lem3593708 A) (@lem3593707 A B x' f s)). Qed.
Lemma lem3593711 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term206 A B x' f s.
Proof. exact (EQ_MP (@lem3593710 A B x' f s) (@lem3593377 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3593729 {A : Type'} (P : A -> Prop) (Q : Prop) : (term941 A P Q) = (term942 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3593730 {A : Type'} (P : A -> Prop) (Q : Prop) : (term941 A P Q) = (term942 A P Q).
Proof. exact (@lem3593729 A P Q). Qed.
Lemma lem3593731 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B s f g y) = (term944 A B s f g y).
Proof. exact (@lem3593730 A (term205 A B y f s) (term120 A B s f g y)). Qed.
Lemma lem3593732 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term945 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term945 A B y f s x)). Qed.
Lemma lem3593733 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term946 A B y f s) = (term205 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem3593732 A B y f s x)). Qed.
Lemma lem3593734 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593735 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term947 A B y f s) = (term206 A B y f s).
Proof. exact (MK_COMB (@lem3593734 A) (@lem3593733 A B y f s)). Qed.
Lemma lem3593736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593737 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term948 A B y f s) = (term208 A B y f s).
Proof. exact (MK_COMB (@lem3593736) (@lem3593735 A B y f s)). Qed.
Lemma lem3593738 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593739 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B s f g y) = (term210 A B s f g y).
Proof. exact (MK_COMB (@lem3593737 A B y f s) (@lem3593738 A B s f g y)). Qed.
Lemma lem3593740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3593741 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term949 A B s f g y) = (term950 A B s f g y).
Proof. exact (MK_COMB (@lem3593740) (@lem3593739 A B s f g y)). Qed.
Lemma lem3593742 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term945 A B y f s x) = (term199 A B y f s x).
Proof. exact (eq_refl (term945 A B y f s x)). Qed.
Lemma lem3593743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3593744 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term951 A B y f s x) = (term952 A B y f s x).
Proof. exact (MK_COMB (@lem3593743) (@lem3593742 A B y f s x)). Qed.
Lemma lem3593745 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term120 A B s f g y) = (term120 A B s f g y).
Proof. exact (eq_refl (term120 A B s f g y)). Qed.
Lemma lem3593746 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term953 A B x s f g y) = (term954 A B x s f g y).
Proof. exact (MK_COMB (@lem3593744 A B y f s x) (@lem3593745 A B s f g y)). Qed.
Lemma lem3593747 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term955 A B s f g y) = (term956 A B s f g y).
Proof. exact (fun_ext (fun x : A => @lem3593746 A B x s f g y)). Qed.
Lemma lem3593748 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593749 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term944 A B s f g y) = (term957 A B s f g y).
Proof. exact (MK_COMB (@lem3593748 A) (@lem3593747 A B s f g y)). Qed.
Lemma lem3593750 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : ((term943 A B s f g y) = (term944 A B s f g y)) = ((term210 A B s f g y) = (term957 A B s f g y)).
Proof. exact (MK_COMB (@lem3593741 A B s f g y) (@lem3593749 A B s f g y)). Qed.
Lemma lem3593751 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term210 A B s f g y) = (term957 A B s f g y).
Proof. exact (EQ_MP (@lem3593750 A B s f g y) (@lem3593731 A B s f g y)). Qed.
Lemma lem3593752 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term211 A B s f g) = (term958 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593751 A B s f g y)). Qed.
Lemma lem3593753 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593754 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term959 A B s f g).
Proof. exact (MK_COMB (@lem3593753 B) (@lem3593752 A B s f g)). Qed.
Lemma lem3593777 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (g : B -> A) (y : B) : (term954 A B x s f g y) = (term960 A B s x f g y).
Proof. exact (@lem19490 (term115 A B s g y) (term199 A B y f s x) ((term118 A B f g y) = y)). Qed.
Lemma lem3593778 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term956 A B s f g y) = (term961 A B s f g y).
Proof. exact (fun_ext (fun x : A => @lem3593777 A B s x f g y)). Qed.
Lemma lem3593779 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3593780 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term957 A B s f g y) = (term962 A B s f g y).
Proof. exact (MK_COMB (@lem3593779 A) (@lem3593778 A B s f g y)). Qed.
Lemma lem3593781 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term958 A B s f g) = (term963 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem3593780 A B s f g y)). Qed.
Lemma lem3593782 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3593783 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term959 A B s f g) = (term964 A B s f g).
Proof. exact (MK_COMB (@lem3593782 B) (@lem3593781 A B s f g)). Qed.
Lemma lem3593784 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term212 A B s f g) = (term964 A B s f g).
Proof. exact (TRANS (@lem3593754 A B s f g) (@lem3593783 A B s f g)). Qed.
Lemma lem3593785 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term964 A B s f g.
Proof. exact (EQ_MP (@lem3593784 A B s f g) (@lem3593125 A B s f g h1)). Qed.
Lemma lem3593818 {A B : Type'} (_38792 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1009 A B s f g _38792.
Proof. exact (@lem3593455 A B s f g h1 _38792). Qed.
Lemma lem3593819 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (_38792 : B) : (term1009 A B s f g _38792) = (term962 A B s f g _38792).
Proof. exact (eq_refl (term1009 A B s f g _38792)). Qed.
Lemma lem3593820 {A B : Type'} (_38792 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term962 A B s f g _38792.
Proof. exact (EQ_MP (@lem3593819 A B s f g _38792) (@lem3593818 A B _38792 s f g h1)). Qed.
Lemma lem3593821 {A B : Type'} (_38792 : B) (_38793 : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1010 A B s f g _38792 _38793.
Proof. exact (@lem3593820 A B _38792 s f g h1 _38793). Qed.
Lemma lem3593822 {A B : Type'} (s : A -> Prop) (_38793 : A) (f : A -> B) (g : B -> A) (_38792 : B) : (term1010 A B s f g _38792 _38793) = (term960 A B s _38793 f g _38792).
Proof. exact (eq_refl (term1010 A B s f g _38792 _38793)). Qed.
Lemma lem3593823 {A B : Type'} (_38793 : A) (_38792 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term960 A B s _38793 f g _38792.
Proof. exact (EQ_MP (@lem3593822 A B s _38793 f g _38792) (@lem3593821 A B _38792 _38793 s f g h1)). Qed.
Lemma lem3593824 {A B : Type'} (_38794 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1009 A B s f g _38794.
Proof. exact (@lem3593529 A B s f g h1 _38794). Qed.
Lemma lem3593825 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (_38794 : B) : (term1009 A B s f g _38794) = (term962 A B s f g _38794).
Proof. exact (eq_refl (term1009 A B s f g _38794)). Qed.
Lemma lem3593826 {A B : Type'} (_38794 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term962 A B s f g _38794.
Proof. exact (EQ_MP (@lem3593825 A B s f g _38794) (@lem3593824 A B _38794 s f g h1)). Qed.
Lemma lem3593827 {A B : Type'} (_38794 : B) (_38795 : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1010 A B s f g _38794 _38795.
Proof. exact (@lem3593826 A B _38794 s f g h1 _38795). Qed.
Lemma lem3593828 {A B : Type'} (s : A -> Prop) (_38795 : A) (f : A -> B) (g : B -> A) (_38794 : B) : (term1010 A B s f g _38794 _38795) = (term960 A B s _38795 f g _38794).
Proof. exact (eq_refl (term1010 A B s f g _38794 _38795)). Qed.
Lemma lem3593829 {A B : Type'} (_38795 : A) (_38794 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term960 A B s _38795 f g _38794.
Proof. exact (EQ_MP (@lem3593828 A B s _38795 f g _38794) (@lem3593827 A B _38794 _38795 s f g h1)). Qed.
Lemma lem3593830 {A B : Type'} (_38796 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1011 A B x' g f s _38796.
Proof. exact (@lem3593632 A B x'' x' g f s h1 _38796). Qed.
Lemma lem3593831 {A B : Type'} (x' : B) (_38796 : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term1011 A B x' g f s _38796) = (term1006 A B x' _38796 g f s).
Proof. exact (eq_refl (term1011 A B x' g f s _38796)). Qed.
Lemma lem3593832 {A B : Type'} (_38796 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1006 A B x' _38796 g f s.
Proof. exact (EQ_MP (@lem3593831 A B x' _38796 g f s) (@lem3593830 A B _38796 x'' x' g f s h1)). Qed.
Lemma lem3593833 {A B : Type'} (_38796 : A) (_38797 : B) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1012 A B x' _38796 g f s _38797.
Proof. exact (@lem3593832 A B _38796 x'' x' g f s h1 _38797). Qed.
Lemma lem3593834 {A B : Type'} (x' : B) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) : (term1012 A B x' _38796 g f s _38797) = (term1004 A B x' _38796 g _38797 f s).
Proof. exact (eq_refl (term1012 A B x' _38796 g f s _38797)). Qed.
Lemma lem3593835 {A B : Type'} (_38796 : A) (_38797 : B) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1004 A B x' _38796 g _38797 f s.
Proof. exact (EQ_MP (@lem3593834 A B x' _38796 g _38797 f s) (@lem3593833 A B _38796 _38797 x'' x' g f s h1)). Qed.
Lemma lem3593836 {A B : Type'} (_38796 : A) (_38797 : B) (_38798 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1013 A B x' _38796 g _38797 f s _38798.
Proof. exact (@lem3593835 A B _38796 _38797 x'' x' g f s h1 _38798). Qed.
Lemma lem3593837 {A B : Type'} (x' : B) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1013 A B x' _38796 g _38797 f s _38798) = (term1001 A B x' _38796 g _38797 f s _38798).
Proof. exact (eq_refl (term1013 A B x' _38796 g _38797 f s _38798)). Qed.
Lemma lem3593839 {A B : Type'} (_38799 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1009 A B s f g _38799.
Proof. exact (@lem3593698 A B s f g h1 _38799). Qed.
Lemma lem3593840 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (_38799 : B) : (term1009 A B s f g _38799) = (term962 A B s f g _38799).
Proof. exact (eq_refl (term1009 A B s f g _38799)). Qed.
Lemma lem3593841 {A B : Type'} (_38799 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term962 A B s f g _38799.
Proof. exact (EQ_MP (@lem3593840 A B s f g _38799) (@lem3593839 A B _38799 s f g h1)). Qed.
Lemma lem3593842 {A B : Type'} (_38799 : B) (_38800 : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1010 A B s f g _38799 _38800.
Proof. exact (@lem3593841 A B _38799 s f g h1 _38800). Qed.
Lemma lem3593843 {A B : Type'} (s : A -> Prop) (_38800 : A) (f : A -> B) (g : B -> A) (_38799 : B) : (term1010 A B s f g _38799 _38800) = (term960 A B s _38800 f g _38799).
Proof. exact (eq_refl (term1010 A B s f g _38799 _38800)). Qed.
Lemma lem3593844 {A B : Type'} (_38800 : A) (_38799 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term960 A B s _38800 f g _38799.
Proof. exact (EQ_MP (@lem3593843 A B s _38800 f g _38799) (@lem3593842 A B _38799 _38800 s f g h1)). Qed.
Lemma lem3593845 {A B : Type'} (_38801 : A) (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term945 A B x' f s _38801.
Proof. exact (@lem3593711 A B x' x'' g x''' f s x'''' h1 _38801). Qed.
Lemma lem3593846 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (_38801 : A) : (term945 A B x' f s _38801) = (term199 A B x' f s _38801).
Proof. exact (eq_refl (term945 A B x' f s _38801)). Qed.
Lemma lem3593848 {A B : Type'} (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1009 A B s f g _38802.
Proof. exact (@lem3593785 A B s f g h1 _38802). Qed.
Lemma lem3593849 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (_38802 : B) : (term1009 A B s f g _38802) = (term962 A B s f g _38802).
Proof. exact (eq_refl (term1009 A B s f g _38802)). Qed.
Lemma lem3593850 {A B : Type'} (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term962 A B s f g _38802.
Proof. exact (EQ_MP (@lem3593849 A B s f g _38802) (@lem3593848 A B _38802 s f g h1)). Qed.
Lemma lem3593851 {A B : Type'} (_38802 : B) (_38803 : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1010 A B s f g _38802 _38803.
Proof. exact (@lem3593850 A B _38802 s f g h1 _38803). Qed.
Lemma lem3593852 {A B : Type'} (s : A -> Prop) (_38803 : A) (f : A -> B) (g : B -> A) (_38802 : B) : (term1010 A B s f g _38802 _38803) = (term960 A B s _38803 f g _38802).
Proof. exact (eq_refl (term1010 A B s f g _38802 _38803)). Qed.
Lemma lem3593853 {A B : Type'} (_38803 : A) (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term960 A B s _38803 f g _38802.
Proof. exact (EQ_MP (@lem3593852 A B s _38803 f g _38802) (@lem3593851 A B _38802 _38803 s f g h1)). Qed.
Lemma lem3593855 {A B : Type'} (_38793 : A) (_38792 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1014 A B f _38793 s g _38792.
Proof. exact (proj1 (@lem3593823 A B _38793 _38792 s f g h1)). Qed.
Lemma lem3593856 {A B : Type'} (_38795 : A) (_38794 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1015 A B s _38795 f g _38794.
Proof. exact (proj2 (@lem3593829 A B _38795 _38794 s f g h1)). Qed.
Lemma lem3593859 {A B : Type'} (_38800 : A) (_38799 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1014 A B f _38800 s g _38799.
Proof. exact (proj1 (@lem3593844 A B _38800 _38799 s f g h1)). Qed.
Lemma lem3593860 {A B : Type'} (_38803 : A) (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1015 A B s _38803 f g _38802.
Proof. exact (proj2 (@lem3593853 A B _38803 _38802 s f g h1)). Qed.
Lemma lem3593865 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : x = (g x').
Proof. exact (proj1 (@lem3593363 A B g x' f x'' s x h1)). Qed.
Lemma lem3593867 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : x' = (f x'').
Proof. exact (proj1 (@lem3593364 A B g x' f x'' s x h1)). Qed.
Lemma lem3593880 {A B : Type'} (f : A -> B) (_38793 : A) (s : A -> Prop) (g : B -> A) (_38792 : B) : (term1014 A B f _38793 s g _38792) = (term1016 A B f _38793 s g _38792).
Proof. exact (@lem3589348 (term982 A B _38792 f _38793) (term74 A s _38793) (term115 A B s g _38792)). Qed.
Lemma lem3593907 {A B : Type'} (_38796 : A) (_38797 : B) (_38798 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1001 A B x' _38796 g _38797 f s _38798.
Proof. exact (EQ_MP (@lem3593837 A B x' _38796 g _38797 f s _38798) (@lem3593836 A B _38796 _38797 _38798 x'' x' g f s h1)). Qed.
Lemma lem3593909 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : x' = (f x'').
Proof. exact (proj1 (@lem3593373 A B x'' x' g f s h1)). Qed.
Lemma lem3593934 {A B : Type'} (s : A -> Prop) (_38795 : A) (f : A -> B) (g : B -> A) (_38794 : B) : (term1015 A B s _38795 f g _38794) = (term1017 A B s _38795 f g _38794).
Proof. exact (@lem3589348 (term982 A B _38794 f _38795) (term74 A s _38795) ((term118 A B f g _38794) = _38794)). Qed.
Lemma lem3593945 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : x'' = (g x''').
Proof. exact (proj1 (@lem3593378 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3593947 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : x''' = (f x'''').
Proof. exact (proj1 (@lem3593380 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3593960 {A B : Type'} (f : A -> B) (_38800 : A) (s : A -> Prop) (g : B -> A) (_38799 : B) : (term1014 A B f _38800 s g _38799) = (term1016 A B f _38800 s g _38799).
Proof. exact (@lem3589348 (term982 A B _38799 f _38800) (term74 A s _38800) (term115 A B s g _38799)). Qed.
Lemma lem3593985 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : x'' = (g x''''').
Proof. exact (proj1 (@lem3593387 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3593987 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : x''''' = (f x'''''').
Proof. exact (proj1 (@lem3593394 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594012 {A B : Type'} (s : A -> Prop) (_38803 : A) (f : A -> B) (g : B -> A) (_38802 : B) : (term1015 A B s _38803 f g _38802) = (term1017 A B s _38803 f g _38802).
Proof. exact (@lem3589348 (term982 A B _38802 f _38803) (term74 A s _38803) ((term118 A B f g _38802) = _38802)). Qed.
Lemma lem3594041 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : term74 A s x.
Proof. exact (proj2 (@lem3593360 A B g x' f x'' s x h1)). Qed.
Lemma lem3594042 {A B : Type'} (x : A) (g : B -> A) : (term1018 A B x g) = (term1018 A B x g).
Proof. exact (eq_refl (term1018 A B x g)). Qed.
Lemma lem3594043 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : (term1019 A B x g x') = (term1020 A B x g f x'').
Proof. exact (MK_COMB (@lem3594042 A B x g) (@lem3593867 A B g x' f x'' s x h1)). Qed.
Lemma lem3594044 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (x'' : A) : (term1020 A B x g f x'') = (x = (term1021 A B g f x'')).
Proof. exact (eq_refl (term1020 A B x g f x'')). Qed.
Lemma lem3594045 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term1022 A B x g x') = (term1022 A B x g x').
Proof. exact (eq_refl (term1022 A B x g x')). Qed.
Lemma lem3594046 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (x'' : A) : ((term1019 A B x g x') = (term1020 A B x g f x'')) = ((term1019 A B x g x') = (x = (term1021 A B g f x''))).
Proof. exact (MK_COMB (@lem3594045 A B x g x') (@lem3594044 A B x g f x'')). Qed.
Lemma lem3594047 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term1019 A B x g x') = (x = (g x')).
Proof. exact (eq_refl (term1019 A B x g x')). Qed.
Lemma lem3594048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594049 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term1022 A B x g x') = (term1023 A B x g x').
Proof. exact (MK_COMB (@lem3594048) (@lem3594047 A B x g x')). Qed.
Lemma lem3594050 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (x'' : A) : (x = (term1021 A B g f x'')) = (x = (term1021 A B g f x'')).
Proof. exact (eq_refl (x = (term1021 A B g f x''))). Qed.
Lemma lem3594051 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (x'' : A) : ((term1019 A B x g x') = (x = (term1021 A B g f x''))) = ((x = (g x')) = (x = (term1021 A B g f x''))).
Proof. exact (MK_COMB (@lem3594049 A B x g x') (@lem3594050 A B x g f x'')). Qed.
Lemma lem3594052 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (x'' : A) : ((term1019 A B x g x') = (term1020 A B x g f x'')) = ((x = (g x')) = (x = (term1021 A B g f x''))).
Proof. exact (TRANS (@lem3594046 A B x' x g f x'') (@lem3594051 A B x' x g f x'')). Qed.
Lemma lem3594053 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : (x = (g x')) = (x = (term1021 A B g f x'')).
Proof. exact (EQ_MP (@lem3594052 A B x' x g f x'') (@lem3594043 A B g x' f x'' s x h1)). Qed.
Lemma lem3594054 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : x = (term1021 A B g f x'').
Proof. exact (EQ_MP (@lem3594053 A B g x' f x'' s x h1) (@lem3593865 A B g x' f x'' s x h1)). Qed.
Lemma lem3594111 {A : Type'} (s : A -> Prop) : (term1024 A s) = (term1024 A s).
Proof. exact (eq_refl (term1024 A s)). Qed.
Lemma lem3594112 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : (term1025 A s x) = (term1026 A B s g f x'').
Proof. exact (MK_COMB (@lem3594111 A s) (@lem3594054 A B g x' f x'' s x h1)). Qed.
Lemma lem3594113 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : (term1026 A B s g f x'') = (term1027 A B s g f x'').
Proof. exact (eq_refl (term1026 A B s g f x'')). Qed.
Lemma lem3594114 {A : Type'} (s : A -> Prop) (x : A) : (term1028 A s x) = (term1028 A s x).
Proof. exact (eq_refl (term1028 A s x)). Qed.
Lemma lem3594115 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : ((term1025 A s x) = (term1026 A B s g f x'')) = ((term1025 A s x) = (term1027 A B s g f x'')).
Proof. exact (MK_COMB (@lem3594114 A s x) (@lem3594113 A B s g f x'')). Qed.
Lemma lem3594116 {A : Type'} (s : A -> Prop) (x : A) : (term1025 A s x) = (term74 A s x).
Proof. exact (eq_refl (term1025 A s x)). Qed.
Lemma lem3594117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594118 {A : Type'} (s : A -> Prop) (x : A) : (term1028 A s x) = (term1029 A s x).
Proof. exact (MK_COMB (@lem3594117) (@lem3594116 A s x)). Qed.
Lemma lem3594119 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : (term1027 A B s g f x'') = (term1027 A B s g f x'').
Proof. exact (eq_refl (term1027 A B s g f x'')). Qed.
Lemma lem3594120 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : ((term1025 A s x) = (term1027 A B s g f x'')) = ((term74 A s x) = (term1027 A B s g f x'')).
Proof. exact (MK_COMB (@lem3594118 A s x) (@lem3594119 A B s g f x'')). Qed.
Lemma lem3594121 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : ((term1025 A s x) = (term1026 A B s g f x'')) = ((term74 A s x) = (term1027 A B s g f x'')).
Proof. exact (TRANS (@lem3594115 A B x s g f x'') (@lem3594120 A B x s g f x'')). Qed.
Lemma lem3594122 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : (term74 A s x) = (term1027 A B s g f x'').
Proof. exact (EQ_MP (@lem3594121 A B x s g f x'') (@lem3594112 A B g x' f x'' s x h1)). Qed.
Lemma lem3594123 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : term1027 A B s g f x''.
Proof. exact (EQ_MP (@lem3594122 A B g x' f x'' s x h1) (@lem3594041 A B g x' f x'' s x h1)). Qed.
Lemma lem3594151 {A B : Type'} (_38793 : A) (_38792 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1016 A B f _38793 s g _38792.
Proof. exact (EQ_MP (@lem3593880 A B f _38793 s g _38792) (@lem3593855 A B _38793 _38792 s f g h1)). Qed.
Lemma lem3594180 {A B : Type'} (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1030 A B _38796 g _38797 f s _38798) = (term1030 A B _38796 g _38797 f s _38798).
Proof. exact (eq_refl (term1030 A B _38796 g _38797 f s _38798)). Qed.
Lemma lem3594181 {A B : Type'} (_38796 : A) (_38797 : B) (_38798 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : (term1031 A B _38796 g _38797 f s _38798 x') = (term1032 A B _38796 g _38797 s _38798 f x'').
Proof. exact (MK_COMB (@lem3594180 A B _38796 g _38797 f s _38798) (@lem3593909 A B x'' x' g f s h1)). Qed.
Lemma lem3594182 {A B : Type'} (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1032 A B _38796 g _38797 s _38798 f x'') = (term1033 A B x'' _38796 g _38797 f s _38798).
Proof. exact (eq_refl (term1032 A B _38796 g _38797 s _38798 f x'')). Qed.
Lemma lem3594183 {A B : Type'} (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) (x' : B) : (term1034 A B _38796 g _38797 f s _38798 x') = (term1034 A B _38796 g _38797 f s _38798 x').
Proof. exact (eq_refl (term1034 A B _38796 g _38797 f s _38798 x')). Qed.
Lemma lem3594184 {A B : Type'} (x' : B) (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : ((term1031 A B _38796 g _38797 f s _38798 x') = (term1032 A B _38796 g _38797 s _38798 f x'')) = ((term1031 A B _38796 g _38797 f s _38798 x') = (term1033 A B x'' _38796 g _38797 f s _38798)).
Proof. exact (MK_COMB (@lem3594183 A B _38796 g _38797 f s _38798 x') (@lem3594182 A B x'' _38796 g _38797 f s _38798)). Qed.
Lemma lem3594185 {A B : Type'} (x' : B) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1031 A B _38796 g _38797 f s _38798 x') = (term1001 A B x' _38796 g _38797 f s _38798).
Proof. exact (eq_refl (term1031 A B _38796 g _38797 f s _38798 x')). Qed.
Lemma lem3594186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594187 {A B : Type'} (x' : B) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1034 A B _38796 g _38797 f s _38798 x') = (term1035 A B x' _38796 g _38797 f s _38798).
Proof. exact (MK_COMB (@lem3594186) (@lem3594185 A B x' _38796 g _38797 f s _38798)). Qed.
Lemma lem3594188 {A B : Type'} (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1033 A B x'' _38796 g _38797 f s _38798) = (term1033 A B x'' _38796 g _38797 f s _38798).
Proof. exact (eq_refl (term1033 A B x'' _38796 g _38797 f s _38798)). Qed.
Lemma lem3594189 {A B : Type'} (x' : B) (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : ((term1031 A B _38796 g _38797 f s _38798 x') = (term1033 A B x'' _38796 g _38797 f s _38798)) = ((term1001 A B x' _38796 g _38797 f s _38798) = (term1033 A B x'' _38796 g _38797 f s _38798)).
Proof. exact (MK_COMB (@lem3594187 A B x' _38796 g _38797 f s _38798) (@lem3594188 A B x'' _38796 g _38797 f s _38798)). Qed.
Lemma lem3594190 {A B : Type'} (x' : B) (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : ((term1031 A B _38796 g _38797 f s _38798 x') = (term1032 A B _38796 g _38797 s _38798 f x'')) = ((term1001 A B x' _38796 g _38797 f s _38798) = (term1033 A B x'' _38796 g _38797 f s _38798)).
Proof. exact (TRANS (@lem3594184 A B x' x'' _38796 g _38797 f s _38798) (@lem3594189 A B x' x'' _38796 g _38797 f s _38798)). Qed.
Lemma lem3594191 {A B : Type'} (_38796 : A) (_38797 : B) (_38798 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : (term1001 A B x' _38796 g _38797 f s _38798) = (term1033 A B x'' _38796 g _38797 f s _38798).
Proof. exact (EQ_MP (@lem3594190 A B x' x'' _38796 g _38797 f s _38798) (@lem3594181 A B _38796 _38797 _38798 x'' x' g f s h1)). Qed.
Lemma lem3594192 {A B : Type'} (_38796 : A) (_38797 : B) (_38798 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1033 A B x'' _38796 g _38797 f s _38798.
Proof. exact (EQ_MP (@lem3594191 A B _38796 _38797 _38798 x'' x' g f s h1) (@lem3593907 A B _38796 _38797 _38798 x'' x' g f s h1)). Qed.
Lemma lem3594234 {A B : Type'} (_38795 : A) (_38794 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1017 A B s _38795 f g _38794.
Proof. exact (EQ_MP (@lem3593934 A B s _38795 f g _38794) (@lem3593856 A B _38795 _38794 s f g h1)). Qed.
Lemma lem3594276 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : x' = (f x'').
Proof. exact (proj1 (@lem3593376 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594277 {A B : Type'} (x'' : A) (g : B -> A) : (term1018 A B x'' g) = (term1018 A B x'' g).
Proof. exact (eq_refl (term1018 A B x'' g)). Qed.
Lemma lem3594278 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : (term1019 A B x'' g x''') = (term1020 A B x'' g f x'''').
Proof. exact (MK_COMB (@lem3594277 A B x'' g) (@lem3593947 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594279 {A B : Type'} (x'' : A) (g : B -> A) (f : A -> B) (x'''' : A) : (term1020 A B x'' g f x'''') = (x'' = (term1021 A B g f x'''')).
Proof. exact (eq_refl (term1020 A B x'' g f x'''')). Qed.
Lemma lem3594280 {A B : Type'} (x'' : A) (g : B -> A) (x''' : B) : (term1022 A B x'' g x''') = (term1022 A B x'' g x''').
Proof. exact (eq_refl (term1022 A B x'' g x''')). Qed.
Lemma lem3594281 {A B : Type'} (x''' : B) (x'' : A) (g : B -> A) (f : A -> B) (x'''' : A) : ((term1019 A B x'' g x''') = (term1020 A B x'' g f x'''')) = ((term1019 A B x'' g x''') = (x'' = (term1021 A B g f x''''))).
Proof. exact (MK_COMB (@lem3594280 A B x'' g x''') (@lem3594279 A B x'' g f x'''')). Qed.
Lemma lem3594282 {A B : Type'} (x'' : A) (g : B -> A) (x''' : B) : (term1019 A B x'' g x''') = (x'' = (g x''')).
Proof. exact (eq_refl (term1019 A B x'' g x''')). Qed.
Lemma lem3594283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594284 {A B : Type'} (x'' : A) (g : B -> A) (x''' : B) : (term1022 A B x'' g x''') = (term1023 A B x'' g x''').
Proof. exact (MK_COMB (@lem3594283) (@lem3594282 A B x'' g x''')). Qed.
Lemma lem3594285 {A B : Type'} (x'' : A) (g : B -> A) (f : A -> B) (x'''' : A) : (x'' = (term1021 A B g f x'''')) = (x'' = (term1021 A B g f x'''')).
Proof. exact (eq_refl (x'' = (term1021 A B g f x''''))). Qed.
Lemma lem3594286 {A B : Type'} (x''' : B) (x'' : A) (g : B -> A) (f : A -> B) (x'''' : A) : ((term1019 A B x'' g x''') = (x'' = (term1021 A B g f x''''))) = ((x'' = (g x''')) = (x'' = (term1021 A B g f x''''))).
Proof. exact (MK_COMB (@lem3594284 A B x'' g x''') (@lem3594285 A B x'' g f x'''')). Qed.
Lemma lem3594287 {A B : Type'} (x''' : B) (x'' : A) (g : B -> A) (f : A -> B) (x'''' : A) : ((term1019 A B x'' g x''') = (term1020 A B x'' g f x'''')) = ((x'' = (g x''')) = (x'' = (term1021 A B g f x''''))).
Proof. exact (TRANS (@lem3594281 A B x''' x'' g f x'''') (@lem3594286 A B x''' x'' g f x'''')). Qed.
Lemma lem3594288 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : (x'' = (g x''')) = (x'' = (term1021 A B g f x'''')).
Proof. exact (EQ_MP (@lem3594287 A B x''' x'' g f x'''') (@lem3594278 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594289 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : x'' = (term1021 A B g f x'''').
Proof. exact (EQ_MP (@lem3594288 A B x' x'' g x''' f s x'''' h1) (@lem3593945 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594359 {A B : Type'} (_38801 : A) (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term199 A B x' f s _38801.
Proof. exact (EQ_MP (@lem3593846 A B x' f s _38801) (@lem3593845 A B _38801 x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594360 {A B : Type'} (x' : B) (f : A -> B) : (term1036 A B x' f) = (term1036 A B x' f).
Proof. exact (eq_refl (term1036 A B x' f)). Qed.
Lemma lem3594361 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : (term1037 A B x' f x'') = (term1038 A B x' g f x'''').
Proof. exact (MK_COMB (@lem3594360 A B x' f) (@lem3594289 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594362 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (x'''' : A) : (term1038 A B x' g f x'''') = (x' = (term1039 A B g f x'''')).
Proof. exact (eq_refl (term1038 A B x' g f x'''')). Qed.
Lemma lem3594363 {A B : Type'} (x' : B) (f : A -> B) (x'' : A) : (term1040 A B x' f x'') = (term1040 A B x' f x'').
Proof. exact (eq_refl (term1040 A B x' f x'')). Qed.
Lemma lem3594364 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (x'''' : A) : ((term1037 A B x' f x'') = (term1038 A B x' g f x'''')) = ((term1037 A B x' f x'') = (x' = (term1039 A B g f x''''))).
Proof. exact (MK_COMB (@lem3594363 A B x' f x'') (@lem3594362 A B x' g f x'''')). Qed.
Lemma lem3594365 {A B : Type'} (x' : B) (f : A -> B) (x'' : A) : (term1037 A B x' f x'') = (x' = (f x'')).
Proof. exact (eq_refl (term1037 A B x' f x'')). Qed.
Lemma lem3594366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594367 {A B : Type'} (x' : B) (f : A -> B) (x'' : A) : (term1040 A B x' f x'') = (term1041 A B x' f x'').
Proof. exact (MK_COMB (@lem3594366) (@lem3594365 A B x' f x'')). Qed.
Lemma lem3594368 {A B : Type'} (x' : B) (g : B -> A) (f : A -> B) (x'''' : A) : (x' = (term1039 A B g f x'''')) = (x' = (term1039 A B g f x'''')).
Proof. exact (eq_refl (x' = (term1039 A B g f x''''))). Qed.
Lemma lem3594369 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (x'''' : A) : ((term1037 A B x' f x'') = (x' = (term1039 A B g f x''''))) = ((x' = (f x'')) = (x' = (term1039 A B g f x''''))).
Proof. exact (MK_COMB (@lem3594367 A B x' f x'') (@lem3594368 A B x' g f x'''')). Qed.
Lemma lem3594370 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (x'''' : A) : ((term1037 A B x' f x'') = (term1038 A B x' g f x'''')) = ((x' = (f x'')) = (x' = (term1039 A B g f x''''))).
Proof. exact (TRANS (@lem3594364 A B x'' x' g f x'''') (@lem3594369 A B x'' x' g f x'''')). Qed.
Lemma lem3594371 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : (x' = (f x'')) = (x' = (term1039 A B g f x'''')).
Proof. exact (EQ_MP (@lem3594370 A B x'' x' g f x'''') (@lem3594361 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594372 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : x' = (term1039 A B g f x'''').
Proof. exact (EQ_MP (@lem3594371 A B x' x'' g x''' f s x'''' h1) (@lem3594276 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594429 {A B : Type'} (f : A -> B) (s : A -> Prop) (_38801 : A) : (term1042 A B f s _38801) = (term1042 A B f s _38801).
Proof. exact (eq_refl (term1042 A B f s _38801)). Qed.
Lemma lem3594430 {A B : Type'} (_38801 : A) (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : (term1043 A B f s _38801 x') = (term1044 A B s _38801 g f x'''').
Proof. exact (MK_COMB (@lem3594429 A B f s _38801) (@lem3594372 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594431 {A B : Type'} (g : B -> A) (x'''' : A) (f : A -> B) (s : A -> Prop) (_38801 : A) : (term1044 A B s _38801 g f x'''') = (term1045 A B g x'''' f s _38801).
Proof. exact (eq_refl (term1044 A B s _38801 g f x'''')). Qed.
Lemma lem3594432 {A B : Type'} (f : A -> B) (s : A -> Prop) (_38801 : A) (x' : B) : (term1046 A B f s _38801 x') = (term1046 A B f s _38801 x').
Proof. exact (eq_refl (term1046 A B f s _38801 x')). Qed.
Lemma lem3594433 {A B : Type'} (x' : B) (g : B -> A) (x'''' : A) (f : A -> B) (s : A -> Prop) (_38801 : A) : ((term1043 A B f s _38801 x') = (term1044 A B s _38801 g f x'''')) = ((term1043 A B f s _38801 x') = (term1045 A B g x'''' f s _38801)).
Proof. exact (MK_COMB (@lem3594432 A B f s _38801 x') (@lem3594431 A B g x'''' f s _38801)). Qed.
Lemma lem3594434 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (_38801 : A) : (term1043 A B f s _38801 x') = (term199 A B x' f s _38801).
Proof. exact (eq_refl (term1043 A B f s _38801 x')). Qed.
Lemma lem3594435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594436 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (_38801 : A) : (term1046 A B f s _38801 x') = (term1047 A B x' f s _38801).
Proof. exact (MK_COMB (@lem3594435) (@lem3594434 A B x' f s _38801)). Qed.
Lemma lem3594437 {A B : Type'} (g : B -> A) (x'''' : A) (f : A -> B) (s : A -> Prop) (_38801 : A) : (term1045 A B g x'''' f s _38801) = (term1045 A B g x'''' f s _38801).
Proof. exact (eq_refl (term1045 A B g x'''' f s _38801)). Qed.
Lemma lem3594438 {A B : Type'} (x' : B) (g : B -> A) (x'''' : A) (f : A -> B) (s : A -> Prop) (_38801 : A) : ((term1043 A B f s _38801 x') = (term1045 A B g x'''' f s _38801)) = ((term199 A B x' f s _38801) = (term1045 A B g x'''' f s _38801)).
Proof. exact (MK_COMB (@lem3594436 A B x' f s _38801) (@lem3594437 A B g x'''' f s _38801)). Qed.
Lemma lem3594439 {A B : Type'} (x' : B) (g : B -> A) (x'''' : A) (f : A -> B) (s : A -> Prop) (_38801 : A) : ((term1043 A B f s _38801 x') = (term1044 A B s _38801 g f x'''')) = ((term199 A B x' f s _38801) = (term1045 A B g x'''' f s _38801)).
Proof. exact (TRANS (@lem3594433 A B x' g x'''' f s _38801) (@lem3594438 A B x' g x'''' f s _38801)). Qed.
Lemma lem3594440 {A B : Type'} (_38801 : A) (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : (term199 A B x' f s _38801) = (term1045 A B g x'''' f s _38801).
Proof. exact (EQ_MP (@lem3594439 A B x' g x'''' f s _38801) (@lem3594430 A B _38801 x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594441 {A B : Type'} (_38801 : A) (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term1045 A B g x'''' f s _38801.
Proof. exact (EQ_MP (@lem3594440 A B _38801 x' x'' g x''' f s x'''' h1) (@lem3594359 A B _38801 x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3594469 {A B : Type'} (_38800 : A) (_38799 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1016 A B f _38800 s g _38799.
Proof. exact (EQ_MP (@lem3593960 A B f _38800 s g _38799) (@lem3593859 A B _38800 _38799 s f g h1)). Qed.
Lemma lem3594511 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term265 A x'' x''''.
Proof. exact (proj2 (@lem3593369 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594525 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (f x'') = (f x'''').
Proof. exact (proj2 (@lem3593386 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594568 {A B : Type'} (x'' : A) (g : B -> A) : (term1018 A B x'' g) = (term1018 A B x'' g).
Proof. exact (eq_refl (term1018 A B x'' g)). Qed.
Lemma lem3594569 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1019 A B x'' g x''''') = (term1020 A B x'' g f x'''''').
Proof. exact (MK_COMB (@lem3594568 A B x'' g) (@lem3593987 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594570 {A B : Type'} (x'' : A) (g : B -> A) (f : A -> B) (x'''''' : A) : (term1020 A B x'' g f x'''''') = (x'' = (term1021 A B g f x'''''')).
Proof. exact (eq_refl (term1020 A B x'' g f x'''''')). Qed.
Lemma lem3594571 {A B : Type'} (x'' : A) (g : B -> A) (x''''' : B) : (term1022 A B x'' g x''''') = (term1022 A B x'' g x''''').
Proof. exact (eq_refl (term1022 A B x'' g x''''')). Qed.
Lemma lem3594572 {A B : Type'} (x''''' : B) (x'' : A) (g : B -> A) (f : A -> B) (x'''''' : A) : ((term1019 A B x'' g x''''') = (term1020 A B x'' g f x'''''')) = ((term1019 A B x'' g x''''') = (x'' = (term1021 A B g f x''''''))).
Proof. exact (MK_COMB (@lem3594571 A B x'' g x''''') (@lem3594570 A B x'' g f x'''''')). Qed.
Lemma lem3594573 {A B : Type'} (x'' : A) (g : B -> A) (x''''' : B) : (term1019 A B x'' g x''''') = (x'' = (g x''''')).
Proof. exact (eq_refl (term1019 A B x'' g x''''')). Qed.
Lemma lem3594574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594575 {A B : Type'} (x'' : A) (g : B -> A) (x''''' : B) : (term1022 A B x'' g x''''') = (term1023 A B x'' g x''''').
Proof. exact (MK_COMB (@lem3594574) (@lem3594573 A B x'' g x''''')). Qed.
Lemma lem3594576 {A B : Type'} (x'' : A) (g : B -> A) (f : A -> B) (x'''''' : A) : (x'' = (term1021 A B g f x'''''')) = (x'' = (term1021 A B g f x'''''')).
Proof. exact (eq_refl (x'' = (term1021 A B g f x''''''))). Qed.
Lemma lem3594577 {A B : Type'} (x''''' : B) (x'' : A) (g : B -> A) (f : A -> B) (x'''''' : A) : ((term1019 A B x'' g x''''') = (x'' = (term1021 A B g f x''''''))) = ((x'' = (g x''''')) = (x'' = (term1021 A B g f x''''''))).
Proof. exact (MK_COMB (@lem3594575 A B x'' g x''''') (@lem3594576 A B x'' g f x'''''')). Qed.
Lemma lem3594578 {A B : Type'} (x''''' : B) (x'' : A) (g : B -> A) (f : A -> B) (x'''''' : A) : ((term1019 A B x'' g x''''') = (term1020 A B x'' g f x'''''')) = ((x'' = (g x''''')) = (x'' = (term1021 A B g f x''''''))).
Proof. exact (TRANS (@lem3594572 A B x''''' x'' g f x'''''') (@lem3594577 A B x''''' x'' g f x'''''')). Qed.
Lemma lem3594579 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (x'' = (g x''''')) = (x'' = (term1021 A B g f x'''''')).
Proof. exact (EQ_MP (@lem3594578 A B x''''' x'' g f x'''''') (@lem3594569 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594580 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : x'' = (term1021 A B g f x'''''').
Proof. exact (EQ_MP (@lem3594579 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1) (@lem3593985 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594637 {A : Type'} (x'''' : A) : (term1048 A x'''') = (term1048 A x'''').
Proof. exact (eq_refl (term1048 A x'''')). Qed.
Lemma lem3594638 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1049 A x'''' x'') = (term1050 A B x'''' g f x'''''').
Proof. exact (MK_COMB (@lem3594637 A x'''') (@lem3594580 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594639 {A B : Type'} (g : B -> A) (f : A -> B) (x'''''' : A) (x'''' : A) : (term1050 A B x'''' g f x'''''') = (term1051 A B g f x'''''' x'''').
Proof. exact (eq_refl (term1050 A B x'''' g f x'''''')). Qed.
Lemma lem3594640 {A : Type'} (x'''' : A) (x'' : A) : (term1052 A x'''' x'') = (term1052 A x'''' x'').
Proof. exact (eq_refl (term1052 A x'''' x'')). Qed.
Lemma lem3594641 {A B : Type'} (x'' : A) (g : B -> A) (f : A -> B) (x'''''' : A) (x'''' : A) : ((term1049 A x'''' x'') = (term1050 A B x'''' g f x'''''')) = ((term1049 A x'''' x'') = (term1051 A B g f x'''''' x'''')).
Proof. exact (MK_COMB (@lem3594640 A x'''' x'') (@lem3594639 A B g f x'''''' x'''')). Qed.
Lemma lem3594642 {A : Type'} (x'' : A) (x'''' : A) : (term1049 A x'''' x'') = (term265 A x'' x'''').
Proof. exact (eq_refl (term1049 A x'''' x'')). Qed.
Lemma lem3594643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594644 {A : Type'} (x'' : A) (x'''' : A) : (term1052 A x'''' x'') = (term1053 A x'' x'''').
Proof. exact (MK_COMB (@lem3594643) (@lem3594642 A x'' x'''')). Qed.
Lemma lem3594645 {A B : Type'} (g : B -> A) (f : A -> B) (x'''''' : A) (x'''' : A) : (term1051 A B g f x'''''' x'''') = (term1051 A B g f x'''''' x'''').
Proof. exact (eq_refl (term1051 A B g f x'''''' x'''')). Qed.
Lemma lem3594646 {A B : Type'} (x'' : A) (g : B -> A) (f : A -> B) (x'''''' : A) (x'''' : A) : ((term1049 A x'''' x'') = (term1051 A B g f x'''''' x'''')) = ((term265 A x'' x'''') = (term1051 A B g f x'''''' x'''')).
Proof. exact (MK_COMB (@lem3594644 A x'' x'''') (@lem3594645 A B g f x'''''' x'''')). Qed.
Lemma lem3594647 {A B : Type'} (x'' : A) (g : B -> A) (f : A -> B) (x'''''' : A) (x'''' : A) : ((term1049 A x'''' x'') = (term1050 A B x'''' g f x'''''')) = ((term265 A x'' x'''') = (term1051 A B g f x'''''' x'''')).
Proof. exact (TRANS (@lem3594641 A B x'' g f x'''''' x'''') (@lem3594646 A B x'' g f x'''''' x'''')). Qed.
Lemma lem3594648 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term265 A x'' x'''') = (term1051 A B g f x'''''' x'''').
Proof. exact (EQ_MP (@lem3594647 A B x'' g f x'''''' x'''') (@lem3594638 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594650 {A B : Type'} (f : A -> B) (x'''' : A) : (term1054 A B f x'''') = (term1054 A B f x'''').
Proof. exact (eq_refl (term1054 A B f x'''')). Qed.
Lemma lem3594651 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1055 A B f x'''' x'') = (term1056 A B x'''' g f x'''''').
Proof. exact (MK_COMB (@lem3594650 A B f x'''') (@lem3594580 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594652 {A B : Type'} (g : B -> A) (x'''''' : A) (f : A -> B) (x'''' : A) : (term1056 A B x'''' g f x'''''') = ((term1039 A B g f x'''''') = (f x'''')).
Proof. exact (eq_refl (term1056 A B x'''' g f x'''''')). Qed.
Lemma lem3594653 {A B : Type'} (f : A -> B) (x'''' : A) (x'' : A) : (term1057 A B f x'''' x'') = (term1057 A B f x'''' x'').
Proof. exact (eq_refl (term1057 A B f x'''' x'')). Qed.
Lemma lem3594654 {A B : Type'} (x'' : A) (g : B -> A) (x'''''' : A) (f : A -> B) (x'''' : A) : ((term1055 A B f x'''' x'') = (term1056 A B x'''' g f x'''''')) = ((term1055 A B f x'''' x'') = ((term1039 A B g f x'''''') = (f x''''))).
Proof. exact (MK_COMB (@lem3594653 A B f x'''' x'') (@lem3594652 A B g x'''''' f x'''')). Qed.
Lemma lem3594655 {A B : Type'} (x'' : A) (f : A -> B) (x'''' : A) : (term1055 A B f x'''' x'') = ((f x'') = (f x'''')).
Proof. exact (eq_refl (term1055 A B f x'''' x'')). Qed.
Lemma lem3594656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594657 {A B : Type'} (x'' : A) (f : A -> B) (x'''' : A) : (term1057 A B f x'''' x'') = (term1058 A B x'' f x'''').
Proof. exact (MK_COMB (@lem3594656) (@lem3594655 A B x'' f x'''')). Qed.
Lemma lem3594658 {A B : Type'} (g : B -> A) (x'''''' : A) (f : A -> B) (x'''' : A) : ((term1039 A B g f x'''''') = (f x'''')) = ((term1039 A B g f x'''''') = (f x'''')).
Proof. exact (eq_refl ((term1039 A B g f x'''''') = (f x''''))). Qed.
Lemma lem3594659 {A B : Type'} (x'' : A) (g : B -> A) (x'''''' : A) (f : A -> B) (x'''' : A) : ((term1055 A B f x'''' x'') = ((term1039 A B g f x'''''') = (f x''''))) = (((f x'') = (f x'''')) = ((term1039 A B g f x'''''') = (f x''''))).
Proof. exact (MK_COMB (@lem3594657 A B x'' f x'''') (@lem3594658 A B g x'''''' f x'''')). Qed.
Lemma lem3594660 {A B : Type'} (x'' : A) (g : B -> A) (x'''''' : A) (f : A -> B) (x'''' : A) : ((term1055 A B f x'''' x'') = (term1056 A B x'''' g f x'''''')) = (((f x'') = (f x'''')) = ((term1039 A B g f x'''''') = (f x''''))).
Proof. exact (TRANS (@lem3594654 A B x'' g x'''''' f x'''') (@lem3594659 A B x'' g x'''''' f x'''')). Qed.
Lemma lem3594661 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : ((f x'') = (f x'''')) = ((term1039 A B g f x'''''') = (f x'''')).
Proof. exact (EQ_MP (@lem3594660 A B x'' g x'''''' f x'''') (@lem3594651 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594676 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : x'''' = (g x''''''').
Proof. exact (proj1 (@lem3593389 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594690 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : x''''''' = (f x'''''''').
Proof. exact (proj1 (@lem3593390 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594774 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1051 A B g f x'''''' x''''.
Proof. exact (EQ_MP (@lem3594648 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1) (@lem3594511 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594788 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''') = (f x'''').
Proof. exact (EQ_MP (@lem3594661 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1) (@lem3594525 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594789 {A B : Type'} (x'''' : A) (g : B -> A) : (term1018 A B x'''' g) = (term1018 A B x'''' g).
Proof. exact (eq_refl (term1018 A B x'''' g)). Qed.
Lemma lem3594790 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1019 A B x'''' g x''''''') = (term1020 A B x'''' g f x'''''''').
Proof. exact (MK_COMB (@lem3594789 A B x'''' g) (@lem3594690 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594791 {A B : Type'} (x'''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : (term1020 A B x'''' g f x'''''''') = (x'''' = (term1021 A B g f x'''''''')).
Proof. exact (eq_refl (term1020 A B x'''' g f x'''''''')). Qed.
Lemma lem3594792 {A B : Type'} (x'''' : A) (g : B -> A) (x''''''' : B) : (term1022 A B x'''' g x''''''') = (term1022 A B x'''' g x''''''').
Proof. exact (eq_refl (term1022 A B x'''' g x''''''')). Qed.
Lemma lem3594793 {A B : Type'} (x''''''' : B) (x'''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1019 A B x'''' g x''''''') = (term1020 A B x'''' g f x'''''''')) = ((term1019 A B x'''' g x''''''') = (x'''' = (term1021 A B g f x''''''''))).
Proof. exact (MK_COMB (@lem3594792 A B x'''' g x''''''') (@lem3594791 A B x'''' g f x'''''''')). Qed.
Lemma lem3594794 {A B : Type'} (x'''' : A) (g : B -> A) (x''''''' : B) : (term1019 A B x'''' g x''''''') = (x'''' = (g x''''''')).
Proof. exact (eq_refl (term1019 A B x'''' g x''''''')). Qed.
Lemma lem3594795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594796 {A B : Type'} (x'''' : A) (g : B -> A) (x''''''' : B) : (term1022 A B x'''' g x''''''') = (term1023 A B x'''' g x''''''').
Proof. exact (MK_COMB (@lem3594795) (@lem3594794 A B x'''' g x''''''')). Qed.
Lemma lem3594797 {A B : Type'} (x'''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : (x'''' = (term1021 A B g f x'''''''')) = (x'''' = (term1021 A B g f x'''''''')).
Proof. exact (eq_refl (x'''' = (term1021 A B g f x''''''''))). Qed.
Lemma lem3594798 {A B : Type'} (x''''''' : B) (x'''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1019 A B x'''' g x''''''') = (x'''' = (term1021 A B g f x''''''''))) = ((x'''' = (g x''''''')) = (x'''' = (term1021 A B g f x''''''''))).
Proof. exact (MK_COMB (@lem3594796 A B x'''' g x''''''') (@lem3594797 A B x'''' g f x'''''''')). Qed.
Lemma lem3594799 {A B : Type'} (x''''''' : B) (x'''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1019 A B x'''' g x''''''') = (term1020 A B x'''' g f x'''''''')) = ((x'''' = (g x''''''')) = (x'''' = (term1021 A B g f x''''''''))).
Proof. exact (TRANS (@lem3594793 A B x''''''' x'''' g f x'''''''') (@lem3594798 A B x''''''' x'''' g f x'''''''')). Qed.
Lemma lem3594800 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (x'''' = (g x''''''')) = (x'''' = (term1021 A B g f x'''''''')).
Proof. exact (EQ_MP (@lem3594799 A B x''''''' x'''' g f x'''''''') (@lem3594790 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594801 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : x'''' = (term1021 A B g f x'''''''').
Proof. exact (EQ_MP (@lem3594800 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1) (@lem3594676 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594872 {A B : Type'} (g : B -> A) (f : A -> B) (x'''''' : A) : (term1059 A B g f x'''''') = (term1059 A B g f x'''''').
Proof. exact (eq_refl (term1059 A B g f x'''''')). Qed.
Lemma lem3594873 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1060 A B g f x'''''' x'''') = (term1061 A B x'''''' g f x'''''''').
Proof. exact (MK_COMB (@lem3594872 A B g f x'''''') (@lem3594801 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594874 {A B : Type'} (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : (term1061 A B x'''''' g f x'''''''') = (term1062 A B x'''''' g f x'''''''').
Proof. exact (eq_refl (term1061 A B x'''''' g f x'''''''')). Qed.
Lemma lem3594875 {A B : Type'} (g : B -> A) (f : A -> B) (x'''''' : A) (x'''' : A) : (term1063 A B g f x'''''' x'''') = (term1063 A B g f x'''''' x'''').
Proof. exact (eq_refl (term1063 A B g f x'''''' x'''')). Qed.
Lemma lem3594876 {A B : Type'} (x'''' : A) (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1060 A B g f x'''''' x'''') = (term1061 A B x'''''' g f x'''''''')) = ((term1060 A B g f x'''''' x'''') = (term1062 A B x'''''' g f x'''''''')).
Proof. exact (MK_COMB (@lem3594875 A B g f x'''''' x'''') (@lem3594874 A B x'''''' g f x'''''''')). Qed.
Lemma lem3594877 {A B : Type'} (g : B -> A) (f : A -> B) (x'''''' : A) (x'''' : A) : (term1060 A B g f x'''''' x'''') = (term1051 A B g f x'''''' x'''').
Proof. exact (eq_refl (term1060 A B g f x'''''' x'''')). Qed.
Lemma lem3594878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594879 {A B : Type'} (g : B -> A) (f : A -> B) (x'''''' : A) (x'''' : A) : (term1063 A B g f x'''''' x'''') = (term1064 A B g f x'''''' x'''').
Proof. exact (MK_COMB (@lem3594878) (@lem3594877 A B g f x'''''' x'''')). Qed.
Lemma lem3594880 {A B : Type'} (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : (term1062 A B x'''''' g f x'''''''') = (term1062 A B x'''''' g f x'''''''').
Proof. exact (eq_refl (term1062 A B x'''''' g f x'''''''')). Qed.
Lemma lem3594881 {A B : Type'} (x'''' : A) (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1060 A B g f x'''''' x'''') = (term1062 A B x'''''' g f x'''''''')) = ((term1051 A B g f x'''''' x'''') = (term1062 A B x'''''' g f x'''''''')).
Proof. exact (MK_COMB (@lem3594879 A B g f x'''''' x'''') (@lem3594880 A B x'''''' g f x'''''''')). Qed.
Lemma lem3594882 {A B : Type'} (x'''' : A) (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1060 A B g f x'''''' x'''') = (term1061 A B x'''''' g f x'''''''')) = ((term1051 A B g f x'''''' x'''') = (term1062 A B x'''''' g f x'''''''')).
Proof. exact (TRANS (@lem3594876 A B x'''' x'''''' g f x'''''''') (@lem3594881 A B x'''' x'''''' g f x'''''''')). Qed.
Lemma lem3594883 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1051 A B g f x'''''' x'''') = (term1062 A B x'''''' g f x'''''''').
Proof. exact (EQ_MP (@lem3594882 A B x'''' x'''''' g f x'''''''') (@lem3594873 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594884 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1062 A B x'''''' g f x''''''''.
Proof. exact (EQ_MP (@lem3594883 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1) (@lem3594774 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594885 {A B : Type'} (g : B -> A) (x'''''' : A) (f : A -> B) : (term1065 A B g x'''''' f) = (term1065 A B g x'''''' f).
Proof. exact (eq_refl (term1065 A B g x'''''' f)). Qed.
Lemma lem3594886 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1066 A B g x'''''' f x'''') = (term1067 A B x'''''' g f x'''''''').
Proof. exact (MK_COMB (@lem3594885 A B g x'''''' f) (@lem3594801 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594887 {A B : Type'} (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : (term1067 A B x'''''' g f x'''''''') = ((term1039 A B g f x'''''') = (term1039 A B g f x'''''''')).
Proof. exact (eq_refl (term1067 A B x'''''' g f x'''''''')). Qed.
Lemma lem3594888 {A B : Type'} (g : B -> A) (x'''''' : A) (f : A -> B) (x'''' : A) : (term1068 A B g x'''''' f x'''') = (term1068 A B g x'''''' f x'''').
Proof. exact (eq_refl (term1068 A B g x'''''' f x'''')). Qed.
Lemma lem3594889 {A B : Type'} (x'''' : A) (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1066 A B g x'''''' f x'''') = (term1067 A B x'''''' g f x'''''''')) = ((term1066 A B g x'''''' f x'''') = ((term1039 A B g f x'''''') = (term1039 A B g f x''''''''))).
Proof. exact (MK_COMB (@lem3594888 A B g x'''''' f x'''') (@lem3594887 A B x'''''' g f x'''''''')). Qed.
Lemma lem3594890 {A B : Type'} (g : B -> A) (x'''''' : A) (f : A -> B) (x'''' : A) : (term1066 A B g x'''''' f x'''') = ((term1039 A B g f x'''''') = (f x'''')).
Proof. exact (eq_refl (term1066 A B g x'''''' f x'''')). Qed.
Lemma lem3594891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3594892 {A B : Type'} (g : B -> A) (x'''''' : A) (f : A -> B) (x'''' : A) : (term1068 A B g x'''''' f x'''') = (term1069 A B g x'''''' f x'''').
Proof. exact (MK_COMB (@lem3594891) (@lem3594890 A B g x'''''' f x'''')). Qed.
Lemma lem3594893 {A B : Type'} (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1039 A B g f x'''''') = (term1039 A B g f x'''''''')) = ((term1039 A B g f x'''''') = (term1039 A B g f x'''''''')).
Proof. exact (eq_refl ((term1039 A B g f x'''''') = (term1039 A B g f x''''''''))). Qed.
Lemma lem3594894 {A B : Type'} (x'''' : A) (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1066 A B g x'''''' f x'''') = ((term1039 A B g f x'''''') = (term1039 A B g f x''''''''))) = (((term1039 A B g f x'''''') = (f x'''')) = ((term1039 A B g f x'''''') = (term1039 A B g f x''''''''))).
Proof. exact (MK_COMB (@lem3594892 A B g x'''''' f x'''') (@lem3594893 A B x'''''' g f x'''''''')). Qed.
Lemma lem3594895 {A B : Type'} (x'''' : A) (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : ((term1066 A B g x'''''' f x'''') = (term1067 A B x'''''' g f x'''''''')) = (((term1039 A B g f x'''''') = (f x'''')) = ((term1039 A B g f x'''''') = (term1039 A B g f x''''''''))).
Proof. exact (TRANS (@lem3594889 A B x'''' x'''''' g f x'''''''') (@lem3594894 A B x'''' x'''''' g f x'''''''')). Qed.
Lemma lem3594896 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : ((term1039 A B g f x'''''') = (f x'''')) = ((term1039 A B g f x'''''') = (term1039 A B g f x'''''''')).
Proof. exact (EQ_MP (@lem3594895 A B x'''' x'''''' g f x'''''''') (@lem3594886 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3594953 {A B : Type'} (_38803 : A) (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1017 A B s _38803 f g _38802.
Proof. exact (EQ_MP (@lem3594012 A B s _38803 f g _38802) (@lem3593860 A B _38803 _38802 s f g h1)). Qed.
Lemma lem3594987 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3594988 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3594987 B x). Qed.
Lemma lem3594989 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (@lem3594988 B (f x'')). Qed.
Lemma lem3594990 {A B : Type'} (f : A -> B) (x'' : A) : term76 A B f x''.
Proof. exact (fun h0 : term77 A B f x'' => @lem3594989 A B f x''). Qed.
Lemma lem3594992 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3594993 {A B : Type'} (f : A -> B) (x'' : A) : (term76 A B f x'') = ((f x'') = (f x'')).
Proof. exact (@lem3594992 ((f x'') = (f x''))). Qed.
Lemma lem3594994 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (EQ_MP (@lem3594993 A B f x'') (@lem3594990 A B f x'')). Qed.
Lemma lem3594996 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : s x''.
Proof. exact (proj2 (@lem3593364 A B g x' f x'' s x h1)). Qed.
Lemma lem3594997 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : term73 A s x''.
Proof. exact (fun h0 : term74 A s x'' => @lem3594996 A B g x' f x'' s x h1). Qed.
Lemma lem3594999 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595000 {A : Type'} (s : A -> Prop) (x'' : A) : (term73 A s x'') = (s x'').
Proof. exact (@lem3594999 (s x'')). Qed.
Lemma lem3595001 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : s x''.
Proof. exact (EQ_MP (@lem3595000 A s x'') (@lem3594997 A B g x' f x'' s x h1)). Qed.
Lemma lem3595007 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595008 {A B : Type'} (f : A -> B) (_38793 : A) (s : A -> Prop) (g : B -> A) (_38792 : B) : (term1016 A B f _38793 s g _38792) = (term1070 A B f _38793 s g _38792).
Proof. exact (@lem3595007 (term74 A s _38793) (term982 A B _38792 f _38793) (term115 A B s g _38792)). Qed.
Lemma lem3595022 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595023 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38792 : B) (f : A -> B) (_38793 : A) : (term1071 A B f _38793 s g _38792) = (term1072 A B s g _38792 f _38793).
Proof. exact (@lem3595022 (term115 A B s g _38792) (term982 A B _38792 f _38793)). Qed.
Lemma lem3595031 {A : Type'} (s : A -> Prop) (_38793 : A) : (term1073 A s _38793) = (term1073 A s _38793).
Proof. exact (eq_refl (term1073 A s _38793)). Qed.
Lemma lem3595032 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38792 : B) (f : A -> B) (_38793 : A) : (term1070 A B f _38793 s g _38792) = (term1074 A B s g _38792 f _38793).
Proof. exact (MK_COMB (@lem3595031 A s _38793) (@lem3595023 A B s g _38792 f _38793)). Qed.
Lemma lem3595036 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595037 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38792 : B) (f : A -> B) (_38793 : A) : (term1074 A B s g _38792 f _38793) = (term1075 A B g s _38792 f _38793).
Proof. exact (@lem3595036 (term115 A B s g _38792) (term74 A s _38793) (term982 A B _38792 f _38793)). Qed.
Lemma lem3595055 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38792 : B) (f : A -> B) (_38793 : A) : (term1070 A B f _38793 s g _38792) = (term1075 A B g s _38792 f _38793).
Proof. exact (TRANS (@lem3595032 A B s g _38792 f _38793) (@lem3595037 A B g s _38792 f _38793)). Qed.
Lemma lem3595056 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38792 : B) (f : A -> B) (_38793 : A) : (term1016 A B f _38793 s g _38792) = (term1075 A B g s _38792 f _38793).
Proof. exact (TRANS (@lem3595008 A B f _38793 s g _38792) (@lem3595055 A B g s _38792 f _38793)). Qed.
Lemma lem3595057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3595058 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38792 : B) (f : A -> B) (_38793 : A) : (term1076 A B f _38793 s g _38792) = (term1077 A B g s _38792 f _38793).
Proof. exact (MK_COMB (@lem3595057) (@lem3595056 A B g s _38792 f _38793)). Qed.
Lemma lem3595072 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595073 {A B : Type'} (s : A -> Prop) (_38792 : B) (f : A -> B) (_38793 : A) : (term199 A B _38792 f s _38793) = (term1078 A B s _38792 f _38793).
Proof. exact (@lem3595072 (term74 A s _38793) (term982 A B _38792 f _38793)). Qed.
Lemma lem3595081 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38792 : B) : (term1079 A B s g _38792) = (term1079 A B s g _38792).
Proof. exact (eq_refl (term1079 A B s g _38792)). Qed.
Lemma lem3595082 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38792 : B) (f : A -> B) (_38793 : A) : (term1080 A B g _38792 f s _38793) = (term1075 A B g s _38792 f _38793).
Proof. exact (MK_COMB (@lem3595081 A B s g _38792) (@lem3595073 A B s _38792 f _38793)). Qed.
Lemma lem3595093 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38792 : B) (f : A -> B) (_38793 : A) : ((term1016 A B f _38793 s g _38792) = (term1080 A B g _38792 f s _38793)) = ((term1075 A B g s _38792 f _38793) = (term1075 A B g s _38792 f _38793)).
Proof. exact (MK_COMB (@lem3595058 A B g s _38792 f _38793) (@lem3595082 A B g s _38792 f _38793)). Qed.
Lemma lem3595095 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3595096 (x : Prop) : (x = x) = True.
Proof. exact (@lem3595095 Prop x). Qed.
Lemma lem3595097 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38792 : B) (f : A -> B) (_38793 : A) : ((term1075 A B g s _38792 f _38793) = (term1075 A B g s _38792 f _38793)) = True.
Proof. exact (@lem3595096 (term1075 A B g s _38792 f _38793)). Qed.
Lemma lem3595098 {A B : Type'} (g : B -> A) (_38792 : B) (f : A -> B) (s : A -> Prop) (_38793 : A) : ((term1016 A B f _38793 s g _38792) = (term1080 A B g _38792 f s _38793)) = True.
Proof. exact (TRANS (@lem3595093 A B g s _38792 f _38793) (@lem3595097 A B g s _38792 f _38793)). Qed.
Lemma lem3595099 {A B : Type'} (g : B -> A) (_38792 : B) (f : A -> B) (s : A -> Prop) (_38793 : A) : True = ((term1016 A B f _38793 s g _38792) = (term1080 A B g _38792 f s _38793)).
Proof. exact (SYM (@lem3595098 A B g _38792 f s _38793)). Qed.
Lemma lem3595100 {A B : Type'} (g : B -> A) (_38792 : B) (f : A -> B) (s : A -> Prop) (_38793 : A) : (term1016 A B f _38793 s g _38792) = (term1080 A B g _38792 f s _38793).
Proof. exact (EQ_MP (@lem3595099 A B g _38792 f s _38793) (@lem0)). Qed.
Lemma lem3595101 {A B : Type'} (_38792 : B) (_38793 : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1080 A B g _38792 f s _38793.
Proof. exact (EQ_MP (@lem3595100 A B g _38792 f s _38793) (@lem3594151 A B _38793 _38792 s f g h1)). Qed.
Lemma lem3595103 (b : Prop) (a : Prop) : (a \/ b) = (term1081 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3595104 {A B : Type'} (f : A -> B) (_38793 : A) (s : A -> Prop) (g : B -> A) (_38792 : B) : (term1080 A B g _38792 f s _38793) = (term1082 A B f _38793 s g _38792).
Proof. exact (@lem3595103 (term199 A B _38792 f s _38793) (term115 A B s g _38792)). Qed.
Lemma lem3595106 (a : Prop) (b : Prop) : (term1083 a b) = (term1084 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3595107 {A B : Type'} (_38792 : B) (f : A -> B) (s : A -> Prop) (_38793 : A) : (term1085 A B _38792 f s _38793) = (term1086 A B _38792 f s _38793).
Proof. exact (@lem3595106 (term982 A B _38792 f _38793) (term74 A s _38793)). Qed.
Lemma lem3595109 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595110 {A B : Type'} (_38792 : B) (f : A -> B) (_38793 : A) : (term1087 A B _38792 f _38793) = (_38792 = (f _38793)).
Proof. exact (@lem3595109 (_38792 = (f _38793))). Qed.
Lemma lem3595111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3595112 {A B : Type'} (_38792 : B) (f : A -> B) (_38793 : A) : (term1088 A B _38792 f _38793) = (term17 A B _38792 f _38793).
Proof. exact (MK_COMB (@lem3595111) (@lem3595110 A B _38792 f _38793)). Qed.
Lemma lem3595114 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595115 {A : Type'} (s : A -> Prop) (_38793 : A) : (term1089 A s _38793) = (s _38793).
Proof. exact (@lem3595114 (s _38793)). Qed.
Lemma lem3595116 {A B : Type'} (_38792 : B) (f : A -> B) (s : A -> Prop) (_38793 : A) : (term1086 A B _38792 f s _38793) = (term19 A B _38792 f s _38793).
Proof. exact (MK_COMB (@lem3595112 A B _38792 f _38793) (@lem3595115 A s _38793)). Qed.
Lemma lem3595117 {A B : Type'} (_38792 : B) (f : A -> B) (s : A -> Prop) (_38793 : A) : (term1085 A B _38792 f s _38793) = (term19 A B _38792 f s _38793).
Proof. exact (TRANS (@lem3595107 A B _38792 f s _38793) (@lem3595116 A B _38792 f s _38793)). Qed.
Lemma lem3595118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3595119 {A B : Type'} (_38792 : B) (f : A -> B) (s : A -> Prop) (_38793 : A) : (term1090 A B _38792 f s _38793) = (term1091 A B _38792 f s _38793).
Proof. exact (MK_COMB (@lem3595118) (@lem3595117 A B _38792 f s _38793)). Qed.
Lemma lem3595120 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38792 : B) : (term115 A B s g _38792) = (term115 A B s g _38792).
Proof. exact (eq_refl (term115 A B s g _38792)). Qed.
Lemma lem3595121 {A B : Type'} (f : A -> B) (_38793 : A) (s : A -> Prop) (g : B -> A) (_38792 : B) : (term1082 A B f _38793 s g _38792) = (term1092 A B f _38793 s g _38792).
Proof. exact (MK_COMB (@lem3595119 A B _38792 f s _38793) (@lem3595120 A B s g _38792)). Qed.
Lemma lem3595122 {A B : Type'} (f : A -> B) (_38793 : A) (s : A -> Prop) (g : B -> A) (_38792 : B) : (term1080 A B g _38792 f s _38793) = (term1092 A B f _38793 s g _38792).
Proof. exact (TRANS (@lem3595104 A B f _38793 s g _38792) (@lem3595121 A B f _38793 s g _38792)). Qed.
Lemma lem3595124 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : term1093 A B f s x''.
Proof. exact (conj (@lem3594994 A B f x'') (@lem3595001 A B g x' f x'' s x h1)). Qed.
Lemma lem3595126 {A B : Type'} (_38793 : A) (_38792 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1092 A B f _38793 s g _38792.
Proof. exact (EQ_MP (@lem3595122 A B f _38793 s g _38792) (@lem3595101 A B _38792 _38793 s f g h1)). Qed.
Lemma lem3595127 {A B : Type'} (_38793 : A) (_38792 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1092 A B f _38793 s g _38792.
Proof. exact (@lem3595126 A B _38793 _38792 s f g h1). Qed.
Lemma lem3595128 {A B : Type'} (x'' : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1094 A B s g f x''.
Proof. exact (@lem3595127 A B x'' (f x'') s f g h1). Qed.
Lemma lem3595131 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term125 A B s f g) (h2 : term362 A B g x' f x'' s x) : term1095 A B s g f x''.
Proof. exact (@lem3595128 A B x'' s f g h1 (@lem3595124 A B g x' f x'' s x h2)). Qed.
Lemma lem3595132 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term125 A B s f g) (h2 : term362 A B g x' f x'' s x) : term1096 A B s g f x''.
Proof. exact (fun h0 : term1027 A B s g f x'' => @lem3595131 A B g x' f x'' s x h1 h2). Qed.
Lemma lem3595134 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595135 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : (term1096 A B s g f x'') = (term1095 A B s g f x'').
Proof. exact (@lem3595134 (term1095 A B s g f x'')). Qed.
Lemma lem3595136 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term125 A B s f g) (h2 : term362 A B g x' f x'' s x) : term1095 A B s g f x''.
Proof. exact (EQ_MP (@lem3595135 A B s g f x'') (@lem3595132 A B g x' f x'' s x h1 h2)). Qed.
Lemma lem3595139 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3595141 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : (term1027 A B s g f x'') = (term1097 A B s g f x'').
Proof. exact (@lem3595139 (term1095 A B s g f x'')). Qed.
Lemma lem3595144 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term362 A B g x' f x'' s x) : term1097 A B s g f x''.
Proof. exact (EQ_MP (@lem3595141 A B s g f x'') (@lem3594123 A B g x' f x'' s x h1)). Qed.
Lemma lem3595147 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term125 A B s f g) (h2 : term362 A B g x' f x'' s x) : False.
Proof. exact (@lem3595144 A B g x' f x'' s x h2 (@lem3595136 A B g x' f x'' s x h1 h2)). Qed.
Lemma lem3595148 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term125 A B s f g) (h2 : term362 A B g x' f x'' s x) : term85.
Proof. exact (fun h0 : ~ False => @lem3595147 A B g x' f x'' s x h1 h2). Qed.
Lemma lem3595150 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595151 : term85 = False.
Proof. exact (@lem3595150 False). Qed.
Lemma lem3595182 {B : Type'} (x : B) (y : B) (z : B) : term1098 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3595186 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3595187 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3595186 B x). Qed.
Lemma lem3595188 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (@lem3595187 B (f x'')). Qed.
Lemma lem3595189 {A B : Type'} (f : A -> B) (x'' : A) : term76 A B f x''.
Proof. exact (fun h0 : term77 A B f x'' => @lem3595188 A B f x''). Qed.
Lemma lem3595191 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595192 {A B : Type'} (f : A -> B) (x'' : A) : (term76 A B f x'') = ((f x'') = (f x'')).
Proof. exact (@lem3595191 ((f x'') = (f x''))). Qed.
Lemma lem3595193 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (EQ_MP (@lem3595192 A B f x'') (@lem3595189 A B f x'')). Qed.
Lemma lem3595195 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : s x''.
Proof. exact (proj2 (@lem3593373 A B x'' x' g f s h1)). Qed.
Lemma lem3595196 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term73 A s x''.
Proof. exact (fun h0 : term74 A s x'' => @lem3595195 A B x'' x' g f s h1). Qed.
Lemma lem3595198 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595199 {A : Type'} (s : A -> Prop) (x'' : A) : (term73 A s x'') = (s x'').
Proof. exact (@lem3595198 (s x'')). Qed.
Lemma lem3595200 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : s x''.
Proof. exact (EQ_MP (@lem3595199 A s x'') (@lem3595196 A B x'' x' g f s h1)). Qed.
Lemma lem3595206 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595207 {A B : Type'} (s : A -> Prop) (_38795 : A) (f : A -> B) (g : B -> A) (_38794 : B) : (term1017 A B s _38795 f g _38794) = (term1099 A B s _38795 f g _38794).
Proof. exact (@lem3595206 (term74 A s _38795) (term982 A B _38794 f _38795) ((term118 A B f g _38794) = _38794)). Qed.
Lemma lem3595221 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595222 {A B : Type'} (g : B -> A) (_38794 : B) (f : A -> B) (_38795 : A) : (term1100 A B _38795 f g _38794) = (term1101 A B g _38794 f _38795).
Proof. exact (@lem3595221 ((term118 A B f g _38794) = _38794) (term982 A B _38794 f _38795)). Qed.
Lemma lem3595232 {A : Type'} (s : A -> Prop) (_38795 : A) : (term1073 A s _38795) = (term1073 A s _38795).
Proof. exact (eq_refl (term1073 A s _38795)). Qed.
Lemma lem3595233 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38794 : B) (f : A -> B) (_38795 : A) : (term1099 A B s _38795 f g _38794) = (term1102 A B s g _38794 f _38795).
Proof. exact (MK_COMB (@lem3595232 A s _38795) (@lem3595222 A B g _38794 f _38795)). Qed.
Lemma lem3595237 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595238 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38794 : B) (f : A -> B) (_38795 : A) : (term1102 A B s g _38794 f _38795) = (term1103 A B g s _38794 f _38795).
Proof. exact (@lem3595237 ((term118 A B f g _38794) = _38794) (term74 A s _38795) (term982 A B _38794 f _38795)). Qed.
Lemma lem3595258 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38794 : B) (f : A -> B) (_38795 : A) : (term1099 A B s _38795 f g _38794) = (term1103 A B g s _38794 f _38795).
Proof. exact (TRANS (@lem3595233 A B s g _38794 f _38795) (@lem3595238 A B g s _38794 f _38795)). Qed.
Lemma lem3595259 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38794 : B) (f : A -> B) (_38795 : A) : (term1017 A B s _38795 f g _38794) = (term1103 A B g s _38794 f _38795).
Proof. exact (TRANS (@lem3595207 A B s _38795 f g _38794) (@lem3595258 A B g s _38794 f _38795)). Qed.
Lemma lem3595260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3595261 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38794 : B) (f : A -> B) (_38795 : A) : (term1104 A B s _38795 f g _38794) = (term1105 A B g s _38794 f _38795).
Proof. exact (MK_COMB (@lem3595260) (@lem3595259 A B g s _38794 f _38795)). Qed.
Lemma lem3595277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595278 {A B : Type'} (s : A -> Prop) (_38794 : B) (f : A -> B) (_38795 : A) : (term199 A B _38794 f s _38795) = (term1078 A B s _38794 f _38795).
Proof. exact (@lem3595277 (term74 A s _38795) (term982 A B _38794 f _38795)). Qed.
Lemma lem3595286 {A B : Type'} (f : A -> B) (g : B -> A) (_38794 : B) : (term1106 A B f g _38794) = (term1106 A B f g _38794).
Proof. exact (eq_refl (term1106 A B f g _38794)). Qed.
Lemma lem3595287 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38794 : B) (f : A -> B) (_38795 : A) : (term1107 A B g _38794 f s _38795) = (term1103 A B g s _38794 f _38795).
Proof. exact (MK_COMB (@lem3595286 A B f g _38794) (@lem3595278 A B s _38794 f _38795)). Qed.
Lemma lem3595298 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38794 : B) (f : A -> B) (_38795 : A) : ((term1017 A B s _38795 f g _38794) = (term1107 A B g _38794 f s _38795)) = ((term1103 A B g s _38794 f _38795) = (term1103 A B g s _38794 f _38795)).
Proof. exact (MK_COMB (@lem3595261 A B g s _38794 f _38795) (@lem3595287 A B g s _38794 f _38795)). Qed.
Lemma lem3595300 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3595301 (x : Prop) : (x = x) = True.
Proof. exact (@lem3595300 Prop x). Qed.
Lemma lem3595302 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38794 : B) (f : A -> B) (_38795 : A) : ((term1103 A B g s _38794 f _38795) = (term1103 A B g s _38794 f _38795)) = True.
Proof. exact (@lem3595301 (term1103 A B g s _38794 f _38795)). Qed.
Lemma lem3595303 {A B : Type'} (g : B -> A) (_38794 : B) (f : A -> B) (s : A -> Prop) (_38795 : A) : ((term1017 A B s _38795 f g _38794) = (term1107 A B g _38794 f s _38795)) = True.
Proof. exact (TRANS (@lem3595298 A B g s _38794 f _38795) (@lem3595302 A B g s _38794 f _38795)). Qed.
Lemma lem3595304 {A B : Type'} (g : B -> A) (_38794 : B) (f : A -> B) (s : A -> Prop) (_38795 : A) : True = ((term1017 A B s _38795 f g _38794) = (term1107 A B g _38794 f s _38795)).
Proof. exact (SYM (@lem3595303 A B g _38794 f s _38795)). Qed.
Lemma lem3595305 {A B : Type'} (g : B -> A) (_38794 : B) (f : A -> B) (s : A -> Prop) (_38795 : A) : (term1017 A B s _38795 f g _38794) = (term1107 A B g _38794 f s _38795).
Proof. exact (EQ_MP (@lem3595304 A B g _38794 f s _38795) (@lem0)). Qed.
Lemma lem3595306 {A B : Type'} (_38794 : B) (_38795 : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1107 A B g _38794 f s _38795.
Proof. exact (EQ_MP (@lem3595305 A B g _38794 f s _38795) (@lem3594234 A B _38795 _38794 s f g h1)). Qed.
Lemma lem3595308 (b : Prop) (a : Prop) : (a \/ b) = (term1081 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3595309 {A B : Type'} (s : A -> Prop) (_38795 : A) (f : A -> B) (g : B -> A) (_38794 : B) : (term1107 A B g _38794 f s _38795) = (term1108 A B s _38795 f g _38794).
Proof. exact (@lem3595308 (term199 A B _38794 f s _38795) ((term118 A B f g _38794) = _38794)). Qed.
Lemma lem3595311 (a : Prop) (b : Prop) : (term1083 a b) = (term1084 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3595312 {A B : Type'} (_38794 : B) (f : A -> B) (s : A -> Prop) (_38795 : A) : (term1085 A B _38794 f s _38795) = (term1086 A B _38794 f s _38795).
Proof. exact (@lem3595311 (term982 A B _38794 f _38795) (term74 A s _38795)). Qed.
Lemma lem3595314 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595315 {A B : Type'} (_38794 : B) (f : A -> B) (_38795 : A) : (term1087 A B _38794 f _38795) = (_38794 = (f _38795)).
Proof. exact (@lem3595314 (_38794 = (f _38795))). Qed.
Lemma lem3595316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3595317 {A B : Type'} (_38794 : B) (f : A -> B) (_38795 : A) : (term1088 A B _38794 f _38795) = (term17 A B _38794 f _38795).
Proof. exact (MK_COMB (@lem3595316) (@lem3595315 A B _38794 f _38795)). Qed.
Lemma lem3595319 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595320 {A : Type'} (s : A -> Prop) (_38795 : A) : (term1089 A s _38795) = (s _38795).
Proof. exact (@lem3595319 (s _38795)). Qed.
Lemma lem3595321 {A B : Type'} (_38794 : B) (f : A -> B) (s : A -> Prop) (_38795 : A) : (term1086 A B _38794 f s _38795) = (term19 A B _38794 f s _38795).
Proof. exact (MK_COMB (@lem3595317 A B _38794 f _38795) (@lem3595320 A s _38795)). Qed.
Lemma lem3595322 {A B : Type'} (_38794 : B) (f : A -> B) (s : A -> Prop) (_38795 : A) : (term1085 A B _38794 f s _38795) = (term19 A B _38794 f s _38795).
Proof. exact (TRANS (@lem3595312 A B _38794 f s _38795) (@lem3595321 A B _38794 f s _38795)). Qed.
Lemma lem3595323 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3595324 {A B : Type'} (_38794 : B) (f : A -> B) (s : A -> Prop) (_38795 : A) : (term1090 A B _38794 f s _38795) = (term1091 A B _38794 f s _38795).
Proof. exact (MK_COMB (@lem3595323) (@lem3595322 A B _38794 f s _38795)). Qed.
Lemma lem3595325 {A B : Type'} (f : A -> B) (g : B -> A) (_38794 : B) : ((term118 A B f g _38794) = _38794) = ((term118 A B f g _38794) = _38794).
Proof. exact (eq_refl ((term118 A B f g _38794) = _38794)). Qed.
Lemma lem3595326 {A B : Type'} (s : A -> Prop) (_38795 : A) (f : A -> B) (g : B -> A) (_38794 : B) : (term1108 A B s _38795 f g _38794) = (term1109 A B s _38795 f g _38794).
Proof. exact (MK_COMB (@lem3595324 A B _38794 f s _38795) (@lem3595325 A B f g _38794)). Qed.
Lemma lem3595327 {A B : Type'} (s : A -> Prop) (_38795 : A) (f : A -> B) (g : B -> A) (_38794 : B) : (term1107 A B g _38794 f s _38795) = (term1109 A B s _38795 f g _38794).
Proof. exact (TRANS (@lem3595309 A B s _38795 f g _38794) (@lem3595326 A B s _38795 f g _38794)). Qed.
Lemma lem3595329 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1093 A B f s x''.
Proof. exact (conj (@lem3595193 A B f x'') (@lem3595200 A B x'' x' g f s h1)). Qed.
Lemma lem3595331 {A B : Type'} (_38795 : A) (_38794 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1109 A B s _38795 f g _38794.
Proof. exact (EQ_MP (@lem3595327 A B s _38795 f g _38794) (@lem3595306 A B _38794 _38795 s f g h1)). Qed.
Lemma lem3595332 {A B : Type'} (_38795 : A) (_38794 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1109 A B s _38795 f g _38794.
Proof. exact (@lem3595331 A B _38795 _38794 s f g h1). Qed.
Lemma lem3595333 {A B : Type'} (x'' : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1110 A B s g f x''.
Proof. exact (@lem3595332 A B x'' (f x'') s f g h1). Qed.
Lemma lem3595336 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : (term1039 A B g f x'') = (f x'').
Proof. exact (@lem3595333 A B x'' s f g h1 (@lem3595329 A B x'' x' g f s h2)). Qed.
Lemma lem3595337 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : term1111 A B g f x''.
Proof. exact (fun h0 : term1112 A B g f x'' => @lem3595336 A B x'' x' g f s h1 h2). Qed.
Lemma lem3595339 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595340 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term1111 A B g f x'') = ((term1039 A B g f x'') = (f x'')).
Proof. exact (@lem3595339 ((term1039 A B g f x'') = (f x''))). Qed.
Lemma lem3595341 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : (term1039 A B g f x'') = (f x'').
Proof. exact (EQ_MP (@lem3595340 A B g f x'') (@lem3595337 A B x'' x' g f s h1 h2)). Qed.
Lemma lem3595343 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3595344 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3595343 B x). Qed.
Lemma lem3595345 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term1039 A B g f x'') = (term1039 A B g f x'').
Proof. exact (@lem3595344 B (term1039 A B g f x'')). Qed.
Lemma lem3595346 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : term1113 A B g f x''.
Proof. exact (fun h0 : term1114 A B g f x'' => @lem3595345 A B g f x''). Qed.
Lemma lem3595348 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595349 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term1113 A B g f x'') = ((term1039 A B g f x'') = (term1039 A B g f x'')).
Proof. exact (@lem3595348 ((term1039 A B g f x'') = (term1039 A B g f x''))). Qed.
Lemma lem3595350 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term1039 A B g f x'') = (term1039 A B g f x'').
Proof. exact (EQ_MP (@lem3595349 A B g f x'') (@lem3595346 A B g f x'')). Qed.
Lemma lem3595368 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595369 {B : Type'} (y : B) (x : B) (z : B) : (term1115 B x y z) = (term1116 B y x z).
Proof. exact (@lem3595368 (y = z) (term265 B x z)). Qed.
Lemma lem3595379 {B : Type'} (x : B) (y : B) : (term1117 B x y) = (term1117 B x y).
Proof. exact (eq_refl (term1117 B x y)). Qed.
Lemma lem3595380 {B : Type'} (y : B) (x : B) (z : B) : (term1098 B x y z) = (term1118 B y x z).
Proof. exact (MK_COMB (@lem3595379 B x y) (@lem3595369 B y x z)). Qed.
Lemma lem3595384 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595385 {B : Type'} (y : B) (x : B) (z : B) : (term1118 B y x z) = (term1119 B y x z).
Proof. exact (@lem3595384 (y = z) (term265 B x y) (term265 B x z)). Qed.
Lemma lem3595407 {B : Type'} (y : B) (x : B) (z : B) : (term1098 B x y z) = (term1119 B y x z).
Proof. exact (TRANS (@lem3595380 B y x z) (@lem3595385 B y x z)). Qed.
Lemma lem3595408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3595409 {B : Type'} (y : B) (x : B) (z : B) : (term1120 B x y z) = (term1121 B y x z).
Proof. exact (MK_COMB (@lem3595408) (@lem3595407 B y x z)). Qed.
Lemma lem3595431 {B : Type'} (y : B) (x : B) (z : B) : (term1119 B y x z) = (term1119 B y x z).
Proof. exact (eq_refl (term1119 B y x z)). Qed.
Lemma lem3595432 {B : Type'} (y : B) (x : B) (z : B) : ((term1098 B x y z) = (term1119 B y x z)) = ((term1119 B y x z) = (term1119 B y x z)).
Proof. exact (MK_COMB (@lem3595409 B y x z) (@lem3595431 B y x z)). Qed.
Lemma lem3595434 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3595435 (x : Prop) : (x = x) = True.
Proof. exact (@lem3595434 Prop x). Qed.
Lemma lem3595436 {B : Type'} (y : B) (x : B) (z : B) : ((term1119 B y x z) = (term1119 B y x z)) = True.
Proof. exact (@lem3595435 (term1119 B y x z)). Qed.
Lemma lem3595437 {B : Type'} (y : B) (x : B) (z : B) : ((term1098 B x y z) = (term1119 B y x z)) = True.
Proof. exact (TRANS (@lem3595432 B y x z) (@lem3595436 B y x z)). Qed.
Lemma lem3595438 {B : Type'} (y : B) (x : B) (z : B) : True = ((term1098 B x y z) = (term1119 B y x z)).
Proof. exact (SYM (@lem3595437 B y x z)). Qed.
Lemma lem3595439 {B : Type'} (y : B) (x : B) (z : B) : (term1098 B x y z) = (term1119 B y x z).
Proof. exact (EQ_MP (@lem3595438 B y x z) (@lem0)). Qed.
Lemma lem3595440 {B : Type'} (y : B) (x : B) (z : B) : term1119 B y x z.
Proof. exact (EQ_MP (@lem3595439 B y x z) (@lem3595182 B x y z)). Qed.
Lemma lem3595442 (b : Prop) (a : Prop) : (a \/ b) = (term1081 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3595443 {B : Type'} (x : B) (y : B) (z : B) : (term1119 B y x z) = (term1122 B x y z).
Proof. exact (@lem3595442 (term1123 B y x z) (y = z)). Qed.
Lemma lem3595445 (a : Prop) (b : Prop) : (term1083 a b) = (term1084 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3595446 {B : Type'} (y : B) (x : B) (z : B) : (term1124 B y x z) = (term1125 B y x z).
Proof. exact (@lem3595445 (term265 B x y) (term265 B x z)). Qed.
Lemma lem3595448 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595449 {B : Type'} (x : B) (y : B) : (term1126 B x y) = (x = y).
Proof. exact (@lem3595448 (x = y)). Qed.
Lemma lem3595450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3595451 {B : Type'} (x : B) (y : B) : (term1127 B x y) = (term1128 B x y).
Proof. exact (MK_COMB (@lem3595450) (@lem3595449 B x y)). Qed.
Lemma lem3595453 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595454 {B : Type'} (x : B) (z : B) : (term1126 B x z) = (x = z).
Proof. exact (@lem3595453 (x = z)). Qed.
Lemma lem3595455 {B : Type'} (y : B) (x : B) (z : B) : (term1125 B y x z) = (term1129 B y x z).
Proof. exact (MK_COMB (@lem3595451 B x y) (@lem3595454 B x z)). Qed.
Lemma lem3595456 {B : Type'} (y : B) (x : B) (z : B) : (term1124 B y x z) = (term1129 B y x z).
Proof. exact (TRANS (@lem3595446 B y x z) (@lem3595455 B y x z)). Qed.
Lemma lem3595457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3595458 {B : Type'} (y : B) (x : B) (z : B) : (term1130 B y x z) = (term1131 B y x z).
Proof. exact (MK_COMB (@lem3595457) (@lem3595456 B y x z)). Qed.
Lemma lem3595459 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3595460 {B : Type'} (x : B) (y : B) (z : B) : (term1122 B x y z) = (term1132 B x y z).
Proof. exact (MK_COMB (@lem3595458 B y x z) (@lem3595459 B y z)). Qed.
Lemma lem3595461 {B : Type'} (x : B) (y : B) (z : B) : (term1119 B y x z) = (term1132 B x y z).
Proof. exact (TRANS (@lem3595443 B x y z) (@lem3595460 B x y z)). Qed.
Lemma lem3595463 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : term1133 A B g f x''.
Proof. exact (conj (@lem3595341 A B x'' x' g f s h1 h2) (@lem3595350 A B g f x'')). Qed.
Lemma lem3595465 {B : Type'} (x : B) (y : B) (z : B) : term1132 B x y z.
Proof. exact (EQ_MP (@lem3595461 B x y z) (@lem3595440 B y x z)). Qed.
Lemma lem3595466 {B : Type'} (x : B) (y : B) (z : B) : term1132 B x y z.
Proof. exact (@lem3595465 B x y z). Qed.
Lemma lem3595467 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : term1134 A B g f x''.
Proof. exact (@lem3595466 B (term1039 A B g f x'') (f x'') (term1039 A B g f x'')). Qed.
Lemma lem3595470 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : (f x'') = (term1039 A B g f x'').
Proof. exact (@lem3595467 A B g f x'' (@lem3595463 A B x'' x' g f s h1 h2)). Qed.
Lemma lem3595471 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : term1135 A B g f x''.
Proof. exact (fun h0 : term1136 A B g f x'' => @lem3595470 A B x'' x' g f s h1 h2). Qed.
Lemma lem3595473 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595474 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term1135 A B g f x'') = ((f x'') = (term1039 A B g f x'')).
Proof. exact (@lem3595473 ((f x'') = (term1039 A B g f x''))). Qed.
Lemma lem3595475 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : (f x'') = (term1039 A B g f x'').
Proof. exact (EQ_MP (@lem3595474 A B g f x'') (@lem3595471 A B x'' x' g f s h1 h2)). Qed.
Lemma lem3595477 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3595478 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3595477 A x). Qed.
Lemma lem3595479 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term1021 A B g f x'') = (term1021 A B g f x'').
Proof. exact (@lem3595478 A (term1021 A B g f x'')). Qed.
Lemma lem3595480 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : term1137 A B g f x''.
Proof. exact (fun h0 : term1138 A B g f x'' => @lem3595479 A B g f x''). Qed.
Lemma lem3595482 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595483 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term1137 A B g f x'') = ((term1021 A B g f x'') = (term1021 A B g f x'')).
Proof. exact (@lem3595482 ((term1021 A B g f x'') = (term1021 A B g f x''))). Qed.
Lemma lem3595484 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term1021 A B g f x'') = (term1021 A B g f x'').
Proof. exact (EQ_MP (@lem3595483 A B g f x'') (@lem3595480 A B g f x'')). Qed.
Lemma lem3595486 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3595487 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3595486 B x). Qed.
Lemma lem3595488 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (@lem3595487 B (f x'')). Qed.
Lemma lem3595489 {A B : Type'} (f : A -> B) (x'' : A) : term76 A B f x''.
Proof. exact (fun h0 : term77 A B f x'' => @lem3595488 A B f x''). Qed.
Lemma lem3595491 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595492 {A B : Type'} (f : A -> B) (x'' : A) : (term76 A B f x'') = ((f x'') = (f x'')).
Proof. exact (@lem3595491 ((f x'') = (f x''))). Qed.
Lemma lem3595493 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (EQ_MP (@lem3595492 A B f x'') (@lem3595489 A B f x'')). Qed.
Lemma lem3595495 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : s x''.
Proof. exact (proj2 (@lem3593373 A B x'' x' g f s h1)). Qed.
Lemma lem3595496 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term73 A s x''.
Proof. exact (fun h0 : term74 A s x'' => @lem3595495 A B x'' x' g f s h1). Qed.
Lemma lem3595498 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595499 {A : Type'} (s : A -> Prop) (x'' : A) : (term73 A s x'') = (s x'').
Proof. exact (@lem3595498 (s x'')). Qed.
Lemma lem3595500 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : s x''.
Proof. exact (EQ_MP (@lem3595499 A s x'') (@lem3595496 A B x'' x' g f s h1)). Qed.
Lemma lem3595502 (a : Prop) (b : Prop) : (term78 a b) = (term79 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3595503 {A B : Type'} (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term199 A B _38797 f s _38798) = (term198 A B _38797 f s _38798).
Proof. exact (@lem3595502 (_38797 = (f _38798)) (s _38798)). Qed.
Lemma lem3595504 {A B : Type'} (_38796 : A) (g : B -> A) (_38797 : B) : (term224 A B _38796 g _38797) = (term224 A B _38796 g _38797).
Proof. exact (eq_refl (term224 A B _38796 g _38797)). Qed.
Lemma lem3595505 {A B : Type'} (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term973 A B _38796 g _38797 f s _38798) = (term1139 A B _38796 g _38797 f s _38798).
Proof. exact (MK_COMB (@lem3595504 A B _38796 g _38797) (@lem3595503 A B _38797 f s _38798)). Qed.
Lemma lem3595507 (a : Prop) (b : Prop) : (term78 a b) = (term79 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3595508 {A B : Type'} (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1139 A B _38796 g _38797 f s _38798) = (term1140 A B _38796 g _38797 f s _38798).
Proof. exact (@lem3595507 (_38796 = (g _38797)) (term19 A B _38797 f s _38798)). Qed.
Lemma lem3595509 {A B : Type'} (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term973 A B _38796 g _38797 f s _38798) = (term1140 A B _38796 g _38797 f s _38798).
Proof. exact (TRANS (@lem3595505 A B _38796 g _38797 f s _38798) (@lem3595508 A B _38796 g _38797 f s _38798)). Qed.
Lemma lem3595510 {A B : Type'} (x'' : A) (f : A -> B) (_38796 : A) : (term1141 A B x'' f _38796) = (term1141 A B x'' f _38796).
Proof. exact (eq_refl (term1141 A B x'' f _38796)). Qed.
Lemma lem3595511 {A B : Type'} (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1033 A B x'' _38796 g _38797 f s _38798) = (term1142 A B x'' _38796 g _38797 f s _38798).
Proof. exact (MK_COMB (@lem3595510 A B x'' f _38796) (@lem3595509 A B _38796 g _38797 f s _38798)). Qed.
Lemma lem3595513 (a : Prop) (b : Prop) : (term78 a b) = (term79 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3595514 {A B : Type'} (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1142 A B x'' _38796 g _38797 f s _38798) = (term1143 A B x'' _38796 g _38797 f s _38798).
Proof. exact (@lem3595513 ((f x'') = (f _38796)) (term326 A B _38796 g _38797 f s _38798)). Qed.
Lemma lem3595515 {A B : Type'} (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1033 A B x'' _38796 g _38797 f s _38798) = (term1143 A B x'' _38796 g _38797 f s _38798).
Proof. exact (TRANS (@lem3595511 A B x'' _38796 g _38797 f s _38798) (@lem3595514 A B x'' _38796 g _38797 f s _38798)). Qed.
Lemma lem3595517 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3595518 {A B : Type'} (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1143 A B x'' _38796 g _38797 f s _38798) = (term1144 A B x'' _38796 g _38797 f s _38798).
Proof. exact (@lem3595517 (term1145 A B x'' _38796 g _38797 f s _38798)). Qed.
Lemma lem3595519 {A B : Type'} (x'' : A) (_38796 : A) (g : B -> A) (_38797 : B) (f : A -> B) (s : A -> Prop) (_38798 : A) : (term1033 A B x'' _38796 g _38797 f s _38798) = (term1144 A B x'' _38796 g _38797 f s _38798).
Proof. exact (TRANS (@lem3595515 A B x'' _38796 g _38797 f s _38798) (@lem3595518 A B x'' _38796 g _38797 f s _38798)). Qed.
Lemma lem3595521 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1093 A B f s x''.
Proof. exact (conj (@lem3595493 A B f x'') (@lem3595500 A B x'' x' g f s h1)). Qed.
Lemma lem3595522 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1146 A B g f s x''.
Proof. exact (conj (@lem3595484 A B g f x'') (@lem3595521 A B x'' x' g f s h1)). Qed.
Lemma lem3595523 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : term1147 A B g f s x''.
Proof. exact (conj (@lem3595475 A B x'' x' g f s h1 h2) (@lem3595522 A B x'' x' g f s h2)). Qed.
Lemma lem3595525 {A B : Type'} (_38796 : A) (_38797 : B) (_38798 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1144 A B x'' _38796 g _38797 f s _38798.
Proof. exact (EQ_MP (@lem3595519 A B x'' _38796 g _38797 f s _38798) (@lem3594192 A B _38796 _38797 _38798 x'' x' g f s h1)). Qed.
Lemma lem3595526 {A B : Type'} (_38796 : A) (_38797 : B) (_38798 : A) (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1144 A B x'' _38796 g _38797 f s _38798.
Proof. exact (@lem3595525 A B _38796 _38797 _38798 x'' x' g f s h1). Qed.
Lemma lem3595527 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term379 A B x'' x' g f s) : term1148 A B g f s x''.
Proof. exact (@lem3595526 A B (term1021 A B g f x'') (f x'') x'' x'' x' g f s h1). Qed.
Lemma lem3595530 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : False.
Proof. exact (@lem3595527 A B x'' x' g f s h2 (@lem3595523 A B x'' x' g f s h1 h2)). Qed.
Lemma lem3595531 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : term85.
Proof. exact (fun h0 : ~ False => @lem3595530 A B x'' x' g f s h1 h2). Qed.
Lemma lem3595533 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595534 : term85 = False.
Proof. exact (@lem3595533 False). Qed.
Lemma lem3595569 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3595570 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3595569 B x). Qed.
Lemma lem3595571 {A B : Type'} (g : B -> A) (f : A -> B) (x'''' : A) : (term1039 A B g f x'''') = (term1039 A B g f x'''').
Proof. exact (@lem3595570 B (term1039 A B g f x'''')). Qed.
Lemma lem3595572 {A B : Type'} (g : B -> A) (f : A -> B) (x'''' : A) : term1113 A B g f x''''.
Proof. exact (fun h0 : term1114 A B g f x'''' => @lem3595571 A B g f x''''). Qed.
Lemma lem3595574 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595575 {A B : Type'} (g : B -> A) (f : A -> B) (x'''' : A) : (term1113 A B g f x'''') = ((term1039 A B g f x'''') = (term1039 A B g f x'''')).
Proof. exact (@lem3595574 ((term1039 A B g f x'''') = (term1039 A B g f x''''))). Qed.
Lemma lem3595576 {A B : Type'} (g : B -> A) (f : A -> B) (x'''' : A) : (term1039 A B g f x'''') = (term1039 A B g f x'''').
Proof. exact (EQ_MP (@lem3595575 A B g f x'''') (@lem3595572 A B g f x'''')). Qed.
Lemma lem3595578 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3595579 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3595578 B x). Qed.
Lemma lem3595580 {A B : Type'} (f : A -> B) (x'''' : A) : (f x'''') = (f x'''').
Proof. exact (@lem3595579 B (f x'''')). Qed.
Lemma lem3595581 {A B : Type'} (f : A -> B) (x'''' : A) : term76 A B f x''''.
Proof. exact (fun h0 : term77 A B f x'''' => @lem3595580 A B f x''''). Qed.
Lemma lem3595583 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595584 {A B : Type'} (f : A -> B) (x'''' : A) : (term76 A B f x'''') = ((f x'''') = (f x'''')).
Proof. exact (@lem3595583 ((f x'''') = (f x''''))). Qed.
Lemma lem3595585 {A B : Type'} (f : A -> B) (x'''' : A) : (f x'''') = (f x'''').
Proof. exact (EQ_MP (@lem3595584 A B f x'''') (@lem3595581 A B f x'''')). Qed.
Lemma lem3595587 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : s x''''.
Proof. exact (proj2 (@lem3593380 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3595588 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term73 A s x''''.
Proof. exact (fun h0 : term74 A s x'''' => @lem3595587 A B x' x'' g x''' f s x'''' h1). Qed.
Lemma lem3595590 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595591 {A : Type'} (s : A -> Prop) (x'''' : A) : (term73 A s x'''') = (s x'''').
Proof. exact (@lem3595590 (s x'''')). Qed.
Lemma lem3595592 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : s x''''.
Proof. exact (EQ_MP (@lem3595591 A s x'''') (@lem3595588 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3595598 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595599 {A B : Type'} (f : A -> B) (_38800 : A) (s : A -> Prop) (g : B -> A) (_38799 : B) : (term1016 A B f _38800 s g _38799) = (term1070 A B f _38800 s g _38799).
Proof. exact (@lem3595598 (term74 A s _38800) (term982 A B _38799 f _38800) (term115 A B s g _38799)). Qed.
Lemma lem3595613 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595614 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38799 : B) (f : A -> B) (_38800 : A) : (term1071 A B f _38800 s g _38799) = (term1072 A B s g _38799 f _38800).
Proof. exact (@lem3595613 (term115 A B s g _38799) (term982 A B _38799 f _38800)). Qed.
Lemma lem3595622 {A : Type'} (s : A -> Prop) (_38800 : A) : (term1073 A s _38800) = (term1073 A s _38800).
Proof. exact (eq_refl (term1073 A s _38800)). Qed.
Lemma lem3595623 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38799 : B) (f : A -> B) (_38800 : A) : (term1070 A B f _38800 s g _38799) = (term1074 A B s g _38799 f _38800).
Proof. exact (MK_COMB (@lem3595622 A s _38800) (@lem3595614 A B s g _38799 f _38800)). Qed.
Lemma lem3595627 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595628 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38799 : B) (f : A -> B) (_38800 : A) : (term1074 A B s g _38799 f _38800) = (term1075 A B g s _38799 f _38800).
Proof. exact (@lem3595627 (term115 A B s g _38799) (term74 A s _38800) (term982 A B _38799 f _38800)). Qed.
Lemma lem3595646 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38799 : B) (f : A -> B) (_38800 : A) : (term1070 A B f _38800 s g _38799) = (term1075 A B g s _38799 f _38800).
Proof. exact (TRANS (@lem3595623 A B s g _38799 f _38800) (@lem3595628 A B g s _38799 f _38800)). Qed.
Lemma lem3595647 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38799 : B) (f : A -> B) (_38800 : A) : (term1016 A B f _38800 s g _38799) = (term1075 A B g s _38799 f _38800).
Proof. exact (TRANS (@lem3595599 A B f _38800 s g _38799) (@lem3595646 A B g s _38799 f _38800)). Qed.
Lemma lem3595648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3595649 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38799 : B) (f : A -> B) (_38800 : A) : (term1076 A B f _38800 s g _38799) = (term1077 A B g s _38799 f _38800).
Proof. exact (MK_COMB (@lem3595648) (@lem3595647 A B g s _38799 f _38800)). Qed.
Lemma lem3595663 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595664 {A B : Type'} (s : A -> Prop) (_38799 : B) (f : A -> B) (_38800 : A) : (term199 A B _38799 f s _38800) = (term1078 A B s _38799 f _38800).
Proof. exact (@lem3595663 (term74 A s _38800) (term982 A B _38799 f _38800)). Qed.
Lemma lem3595672 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38799 : B) : (term1079 A B s g _38799) = (term1079 A B s g _38799).
Proof. exact (eq_refl (term1079 A B s g _38799)). Qed.
Lemma lem3595673 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38799 : B) (f : A -> B) (_38800 : A) : (term1080 A B g _38799 f s _38800) = (term1075 A B g s _38799 f _38800).
Proof. exact (MK_COMB (@lem3595672 A B s g _38799) (@lem3595664 A B s _38799 f _38800)). Qed.
Lemma lem3595684 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38799 : B) (f : A -> B) (_38800 : A) : ((term1016 A B f _38800 s g _38799) = (term1080 A B g _38799 f s _38800)) = ((term1075 A B g s _38799 f _38800) = (term1075 A B g s _38799 f _38800)).
Proof. exact (MK_COMB (@lem3595649 A B g s _38799 f _38800) (@lem3595673 A B g s _38799 f _38800)). Qed.
Lemma lem3595686 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3595687 (x : Prop) : (x = x) = True.
Proof. exact (@lem3595686 Prop x). Qed.
Lemma lem3595688 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38799 : B) (f : A -> B) (_38800 : A) : ((term1075 A B g s _38799 f _38800) = (term1075 A B g s _38799 f _38800)) = True.
Proof. exact (@lem3595687 (term1075 A B g s _38799 f _38800)). Qed.
Lemma lem3595689 {A B : Type'} (g : B -> A) (_38799 : B) (f : A -> B) (s : A -> Prop) (_38800 : A) : ((term1016 A B f _38800 s g _38799) = (term1080 A B g _38799 f s _38800)) = True.
Proof. exact (TRANS (@lem3595684 A B g s _38799 f _38800) (@lem3595688 A B g s _38799 f _38800)). Qed.
Lemma lem3595690 {A B : Type'} (g : B -> A) (_38799 : B) (f : A -> B) (s : A -> Prop) (_38800 : A) : True = ((term1016 A B f _38800 s g _38799) = (term1080 A B g _38799 f s _38800)).
Proof. exact (SYM (@lem3595689 A B g _38799 f s _38800)). Qed.
Lemma lem3595691 {A B : Type'} (g : B -> A) (_38799 : B) (f : A -> B) (s : A -> Prop) (_38800 : A) : (term1016 A B f _38800 s g _38799) = (term1080 A B g _38799 f s _38800).
Proof. exact (EQ_MP (@lem3595690 A B g _38799 f s _38800) (@lem0)). Qed.
Lemma lem3595692 {A B : Type'} (_38799 : B) (_38800 : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1080 A B g _38799 f s _38800.
Proof. exact (EQ_MP (@lem3595691 A B g _38799 f s _38800) (@lem3594469 A B _38800 _38799 s f g h1)). Qed.
Lemma lem3595694 (b : Prop) (a : Prop) : (a \/ b) = (term1081 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3595695 {A B : Type'} (f : A -> B) (_38800 : A) (s : A -> Prop) (g : B -> A) (_38799 : B) : (term1080 A B g _38799 f s _38800) = (term1082 A B f _38800 s g _38799).
Proof. exact (@lem3595694 (term199 A B _38799 f s _38800) (term115 A B s g _38799)). Qed.
Lemma lem3595697 (a : Prop) (b : Prop) : (term1083 a b) = (term1084 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3595698 {A B : Type'} (_38799 : B) (f : A -> B) (s : A -> Prop) (_38800 : A) : (term1085 A B _38799 f s _38800) = (term1086 A B _38799 f s _38800).
Proof. exact (@lem3595697 (term982 A B _38799 f _38800) (term74 A s _38800)). Qed.
Lemma lem3595700 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595701 {A B : Type'} (_38799 : B) (f : A -> B) (_38800 : A) : (term1087 A B _38799 f _38800) = (_38799 = (f _38800)).
Proof. exact (@lem3595700 (_38799 = (f _38800))). Qed.
Lemma lem3595702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3595703 {A B : Type'} (_38799 : B) (f : A -> B) (_38800 : A) : (term1088 A B _38799 f _38800) = (term17 A B _38799 f _38800).
Proof. exact (MK_COMB (@lem3595702) (@lem3595701 A B _38799 f _38800)). Qed.
Lemma lem3595705 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595706 {A : Type'} (s : A -> Prop) (_38800 : A) : (term1089 A s _38800) = (s _38800).
Proof. exact (@lem3595705 (s _38800)). Qed.
Lemma lem3595707 {A B : Type'} (_38799 : B) (f : A -> B) (s : A -> Prop) (_38800 : A) : (term1086 A B _38799 f s _38800) = (term19 A B _38799 f s _38800).
Proof. exact (MK_COMB (@lem3595703 A B _38799 f _38800) (@lem3595706 A s _38800)). Qed.
Lemma lem3595708 {A B : Type'} (_38799 : B) (f : A -> B) (s : A -> Prop) (_38800 : A) : (term1085 A B _38799 f s _38800) = (term19 A B _38799 f s _38800).
Proof. exact (TRANS (@lem3595698 A B _38799 f s _38800) (@lem3595707 A B _38799 f s _38800)). Qed.
Lemma lem3595709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3595710 {A B : Type'} (_38799 : B) (f : A -> B) (s : A -> Prop) (_38800 : A) : (term1090 A B _38799 f s _38800) = (term1091 A B _38799 f s _38800).
Proof. exact (MK_COMB (@lem3595709) (@lem3595708 A B _38799 f s _38800)). Qed.
Lemma lem3595711 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38799 : B) : (term115 A B s g _38799) = (term115 A B s g _38799).
Proof. exact (eq_refl (term115 A B s g _38799)). Qed.
Lemma lem3595712 {A B : Type'} (f : A -> B) (_38800 : A) (s : A -> Prop) (g : B -> A) (_38799 : B) : (term1082 A B f _38800 s g _38799) = (term1092 A B f _38800 s g _38799).
Proof. exact (MK_COMB (@lem3595710 A B _38799 f s _38800) (@lem3595711 A B s g _38799)). Qed.
Lemma lem3595713 {A B : Type'} (f : A -> B) (_38800 : A) (s : A -> Prop) (g : B -> A) (_38799 : B) : (term1080 A B g _38799 f s _38800) = (term1092 A B f _38800 s g _38799).
Proof. exact (TRANS (@lem3595695 A B f _38800 s g _38799) (@lem3595712 A B f _38800 s g _38799)). Qed.
Lemma lem3595715 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term1093 A B f s x''''.
Proof. exact (conj (@lem3595585 A B f x'''') (@lem3595592 A B x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3595717 {A B : Type'} (_38800 : A) (_38799 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1092 A B f _38800 s g _38799.
Proof. exact (EQ_MP (@lem3595713 A B f _38800 s g _38799) (@lem3595692 A B _38799 _38800 s f g h1)). Qed.
Lemma lem3595718 {A B : Type'} (_38800 : A) (_38799 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1092 A B f _38800 s g _38799.
Proof. exact (@lem3595717 A B _38800 _38799 s f g h1). Qed.
Lemma lem3595719 {A B : Type'} (x'''' : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1094 A B s g f x''''.
Proof. exact (@lem3595718 A B x'''' (f x'''') s f g h1). Qed.
Lemma lem3595722 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term125 A B s f g) (h2 : term442 A B x' x'' g x''' f s x'''') : term1095 A B s g f x''''.
Proof. exact (@lem3595719 A B x'''' s f g h1 (@lem3595715 A B x' x'' g x''' f s x'''' h2)). Qed.
Lemma lem3595723 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term125 A B s f g) (h2 : term442 A B x' x'' g x''' f s x'''') : term1096 A B s g f x''''.
Proof. exact (fun h0 : term1027 A B s g f x'''' => @lem3595722 A B x' x'' g x''' f s x'''' h1 h2). Qed.
Lemma lem3595725 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595726 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'''' : A) : (term1096 A B s g f x'''') = (term1095 A B s g f x'''').
Proof. exact (@lem3595725 (term1095 A B s g f x'''')). Qed.
Lemma lem3595727 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term125 A B s f g) (h2 : term442 A B x' x'' g x''' f s x'''') : term1095 A B s g f x''''.
Proof. exact (EQ_MP (@lem3595726 A B s g f x'''') (@lem3595723 A B x' x'' g x''' f s x'''' h1 h2)). Qed.
Lemma lem3595729 (a : Prop) (b : Prop) : (term78 a b) = (term79 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3595730 {A B : Type'} (g : B -> A) (x'''' : A) (f : A -> B) (s : A -> Prop) (_38801 : A) : (term1045 A B g x'''' f s _38801) = (term1149 A B g x'''' f s _38801).
Proof. exact (@lem3595729 ((term1039 A B g f x'''') = (f _38801)) (s _38801)). Qed.
Lemma lem3595732 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3595733 {A B : Type'} (g : B -> A) (x'''' : A) (f : A -> B) (s : A -> Prop) (_38801 : A) : (term1149 A B g x'''' f s _38801) = (term1150 A B g x'''' f s _38801).
Proof. exact (@lem3595732 (term1151 A B g x'''' f s _38801)). Qed.
Lemma lem3595734 {A B : Type'} (g : B -> A) (x'''' : A) (f : A -> B) (s : A -> Prop) (_38801 : A) : (term1045 A B g x'''' f s _38801) = (term1150 A B g x'''' f s _38801).
Proof. exact (TRANS (@lem3595730 A B g x'''' f s _38801) (@lem3595733 A B g x'''' f s _38801)). Qed.
Lemma lem3595736 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term125 A B s f g) (h2 : term442 A B x' x'' g x''' f s x'''') : term1152 A B s g f x''''.
Proof. exact (conj (@lem3595576 A B g f x'''') (@lem3595727 A B x' x'' g x''' f s x'''' h1 h2)). Qed.
Lemma lem3595738 {A B : Type'} (_38801 : A) (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term1150 A B g x'''' f s _38801.
Proof. exact (EQ_MP (@lem3595734 A B g x'''' f s _38801) (@lem3594441 A B _38801 x' x'' g x''' f s x'''' h1)). Qed.
Lemma lem3595739 {A B : Type'} (_38801 : A) (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term1150 A B g x'''' f s _38801.
Proof. exact (@lem3595738 A B _38801 x' x'' g x''' f s x'''' h1). Qed.
Lemma lem3595740 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term442 A B x' x'' g x''' f s x'''') : term1153 A B s g f x''''.
Proof. exact (@lem3595739 A B (term1021 A B g f x'''') x' x'' g x''' f s x'''' h1). Qed.
Lemma lem3595743 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term125 A B s f g) (h2 : term442 A B x' x'' g x''' f s x'''') : False.
Proof. exact (@lem3595740 A B x' x'' g x''' f s x'''' h2 (@lem3595736 A B x' x'' g x''' f s x'''' h1 h2)). Qed.
Lemma lem3595744 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term125 A B s f g) (h2 : term442 A B x' x'' g x''' f s x'''') : term85.
Proof. exact (fun h0 : ~ False => @lem3595743 A B x' x'' g x''' f s x'''' h1 h2). Qed.
Lemma lem3595746 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595747 : term85 = False.
Proof. exact (@lem3595746 False). Qed.
Lemma lem3595769 {A B : Type'} (g : B -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3595770 {B : Type'} (_38962 : B) (_38963 : B) (h1 : _38962 = _38963) : _38962 = _38963.
Proof. exact (h1). Qed.
Lemma lem3595771 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) (h1 : _38962 = _38963) : (g _38962) = (g _38963).
Proof. exact (MK_COMB (@lem3595769 A B g) (@lem3595770 B _38962 _38963 h1)). Qed.
Lemma lem3595772 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : term1154 A B _38962 g _38963.
Proof. exact (fun h0 : _38962 = _38963 => @lem3595771 A B g _38962 _38963 h0). Qed.
Lemma lem3595774 (a : Prop) (b : Prop) : (a -> b) = (term1155 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3595775 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : (term1154 A B _38962 g _38963) = (term1156 A B _38962 g _38963).
Proof. exact (@lem3595774 (_38962 = _38963) ((g _38962) = (g _38963))). Qed.
Lemma lem3595776 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : term1156 A B _38962 g _38963.
Proof. exact (EQ_MP (@lem3595775 A B _38962 g _38963) (@lem3595772 A B _38962 g _38963)). Qed.
Lemma lem3595780 {B : Type'} (x : B) (y : B) (z : B) : term1098 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3595782 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''') = (term1039 A B g f x'''''''').
Proof. exact (EQ_MP (@lem3594896 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1) (@lem3594788 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3595783 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1157 A B x'''''' g f x''''''''.
Proof. exact (fun h0 : term1158 A B x'''''' g f x'''''''' => @lem3595782 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1). Qed.
Lemma lem3595785 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595786 {A B : Type'} (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : (term1157 A B x'''''' g f x'''''''') = ((term1039 A B g f x'''''') = (term1039 A B g f x'''''''')).
Proof. exact (@lem3595785 ((term1039 A B g f x'''''') = (term1039 A B g f x''''''''))). Qed.
Lemma lem3595787 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''') = (term1039 A B g f x'''''''').
Proof. exact (EQ_MP (@lem3595786 A B x'''''' g f x'''''''') (@lem3595783 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3595789 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3595790 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3595789 B x). Qed.
Lemma lem3595791 {A B : Type'} (f : A -> B) (x'''''' : A) : (f x'''''') = (f x'''''').
Proof. exact (@lem3595790 B (f x'''''')). Qed.
Lemma lem3595792 {A B : Type'} (f : A -> B) (x'''''' : A) : term76 A B f x''''''.
Proof. exact (fun h0 : term77 A B f x'''''' => @lem3595791 A B f x''''''). Qed.
Lemma lem3595794 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595795 {A B : Type'} (f : A -> B) (x'''''' : A) : (term76 A B f x'''''') = ((f x'''''') = (f x'''''')).
Proof. exact (@lem3595794 ((f x'''''') = (f x''''''))). Qed.
Lemma lem3595796 {A B : Type'} (f : A -> B) (x'''''' : A) : (f x'''''') = (f x'''''').
Proof. exact (EQ_MP (@lem3595795 A B f x'''''') (@lem3595792 A B f x'''''')). Qed.
Lemma lem3595798 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : s x''''''.
Proof. exact (proj2 (@lem3593394 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3595799 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term73 A s x''''''.
Proof. exact (fun h0 : term74 A s x'''''' => @lem3595798 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1). Qed.
Lemma lem3595801 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595802 {A : Type'} (s : A -> Prop) (x'''''' : A) : (term73 A s x'''''') = (s x'''''').
Proof. exact (@lem3595801 (s x'''''')). Qed.
Lemma lem3595803 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : s x''''''.
Proof. exact (EQ_MP (@lem3595802 A s x'''''') (@lem3595799 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3595809 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595810 {A B : Type'} (s : A -> Prop) (_38803 : A) (f : A -> B) (g : B -> A) (_38802 : B) : (term1017 A B s _38803 f g _38802) = (term1099 A B s _38803 f g _38802).
Proof. exact (@lem3595809 (term74 A s _38803) (term982 A B _38802 f _38803) ((term118 A B f g _38802) = _38802)). Qed.
Lemma lem3595824 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595825 {A B : Type'} (g : B -> A) (_38802 : B) (f : A -> B) (_38803 : A) : (term1100 A B _38803 f g _38802) = (term1101 A B g _38802 f _38803).
Proof. exact (@lem3595824 ((term118 A B f g _38802) = _38802) (term982 A B _38802 f _38803)). Qed.
Lemma lem3595835 {A : Type'} (s : A -> Prop) (_38803 : A) : (term1073 A s _38803) = (term1073 A s _38803).
Proof. exact (eq_refl (term1073 A s _38803)). Qed.
Lemma lem3595836 {A B : Type'} (s : A -> Prop) (g : B -> A) (_38802 : B) (f : A -> B) (_38803 : A) : (term1099 A B s _38803 f g _38802) = (term1102 A B s g _38802 f _38803).
Proof. exact (MK_COMB (@lem3595835 A s _38803) (@lem3595825 A B g _38802 f _38803)). Qed.
Lemma lem3595840 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595841 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38802 : B) (f : A -> B) (_38803 : A) : (term1102 A B s g _38802 f _38803) = (term1103 A B g s _38802 f _38803).
Proof. exact (@lem3595840 ((term118 A B f g _38802) = _38802) (term74 A s _38803) (term982 A B _38802 f _38803)). Qed.
Lemma lem3595861 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38802 : B) (f : A -> B) (_38803 : A) : (term1099 A B s _38803 f g _38802) = (term1103 A B g s _38802 f _38803).
Proof. exact (TRANS (@lem3595836 A B s g _38802 f _38803) (@lem3595841 A B g s _38802 f _38803)). Qed.
Lemma lem3595862 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38802 : B) (f : A -> B) (_38803 : A) : (term1017 A B s _38803 f g _38802) = (term1103 A B g s _38802 f _38803).
Proof. exact (TRANS (@lem3595810 A B s _38803 f g _38802) (@lem3595861 A B g s _38802 f _38803)). Qed.
Lemma lem3595863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3595864 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38802 : B) (f : A -> B) (_38803 : A) : (term1104 A B s _38803 f g _38802) = (term1105 A B g s _38802 f _38803).
Proof. exact (MK_COMB (@lem3595863) (@lem3595862 A B g s _38802 f _38803)). Qed.
Lemma lem3595880 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595881 {A B : Type'} (s : A -> Prop) (_38802 : B) (f : A -> B) (_38803 : A) : (term199 A B _38802 f s _38803) = (term1078 A B s _38802 f _38803).
Proof. exact (@lem3595880 (term74 A s _38803) (term982 A B _38802 f _38803)). Qed.
Lemma lem3595889 {A B : Type'} (f : A -> B) (g : B -> A) (_38802 : B) : (term1106 A B f g _38802) = (term1106 A B f g _38802).
Proof. exact (eq_refl (term1106 A B f g _38802)). Qed.
Lemma lem3595890 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38802 : B) (f : A -> B) (_38803 : A) : (term1107 A B g _38802 f s _38803) = (term1103 A B g s _38802 f _38803).
Proof. exact (MK_COMB (@lem3595889 A B f g _38802) (@lem3595881 A B s _38802 f _38803)). Qed.
Lemma lem3595901 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38802 : B) (f : A -> B) (_38803 : A) : ((term1017 A B s _38803 f g _38802) = (term1107 A B g _38802 f s _38803)) = ((term1103 A B g s _38802 f _38803) = (term1103 A B g s _38802 f _38803)).
Proof. exact (MK_COMB (@lem3595864 A B g s _38802 f _38803) (@lem3595890 A B g s _38802 f _38803)). Qed.
Lemma lem3595903 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3595904 (x : Prop) : (x = x) = True.
Proof. exact (@lem3595903 Prop x). Qed.
Lemma lem3595905 {A B : Type'} (g : B -> A) (s : A -> Prop) (_38802 : B) (f : A -> B) (_38803 : A) : ((term1103 A B g s _38802 f _38803) = (term1103 A B g s _38802 f _38803)) = True.
Proof. exact (@lem3595904 (term1103 A B g s _38802 f _38803)). Qed.
Lemma lem3595906 {A B : Type'} (g : B -> A) (_38802 : B) (f : A -> B) (s : A -> Prop) (_38803 : A) : ((term1017 A B s _38803 f g _38802) = (term1107 A B g _38802 f s _38803)) = True.
Proof. exact (TRANS (@lem3595901 A B g s _38802 f _38803) (@lem3595905 A B g s _38802 f _38803)). Qed.
Lemma lem3595907 {A B : Type'} (g : B -> A) (_38802 : B) (f : A -> B) (s : A -> Prop) (_38803 : A) : True = ((term1017 A B s _38803 f g _38802) = (term1107 A B g _38802 f s _38803)).
Proof. exact (SYM (@lem3595906 A B g _38802 f s _38803)). Qed.
Lemma lem3595908 {A B : Type'} (g : B -> A) (_38802 : B) (f : A -> B) (s : A -> Prop) (_38803 : A) : (term1017 A B s _38803 f g _38802) = (term1107 A B g _38802 f s _38803).
Proof. exact (EQ_MP (@lem3595907 A B g _38802 f s _38803) (@lem0)). Qed.
Lemma lem3595909 {A B : Type'} (_38802 : B) (_38803 : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1107 A B g _38802 f s _38803.
Proof. exact (EQ_MP (@lem3595908 A B g _38802 f s _38803) (@lem3594953 A B _38803 _38802 s f g h1)). Qed.
Lemma lem3595911 (b : Prop) (a : Prop) : (a \/ b) = (term1081 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3595912 {A B : Type'} (s : A -> Prop) (_38803 : A) (f : A -> B) (g : B -> A) (_38802 : B) : (term1107 A B g _38802 f s _38803) = (term1108 A B s _38803 f g _38802).
Proof. exact (@lem3595911 (term199 A B _38802 f s _38803) ((term118 A B f g _38802) = _38802)). Qed.
Lemma lem3595914 (a : Prop) (b : Prop) : (term1083 a b) = (term1084 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3595915 {A B : Type'} (_38802 : B) (f : A -> B) (s : A -> Prop) (_38803 : A) : (term1085 A B _38802 f s _38803) = (term1086 A B _38802 f s _38803).
Proof. exact (@lem3595914 (term982 A B _38802 f _38803) (term74 A s _38803)). Qed.
Lemma lem3595917 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595918 {A B : Type'} (_38802 : B) (f : A -> B) (_38803 : A) : (term1087 A B _38802 f _38803) = (_38802 = (f _38803)).
Proof. exact (@lem3595917 (_38802 = (f _38803))). Qed.
Lemma lem3595919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3595920 {A B : Type'} (_38802 : B) (f : A -> B) (_38803 : A) : (term1088 A B _38802 f _38803) = (term17 A B _38802 f _38803).
Proof. exact (MK_COMB (@lem3595919) (@lem3595918 A B _38802 f _38803)). Qed.
Lemma lem3595922 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3595923 {A : Type'} (s : A -> Prop) (_38803 : A) : (term1089 A s _38803) = (s _38803).
Proof. exact (@lem3595922 (s _38803)). Qed.
Lemma lem3595924 {A B : Type'} (_38802 : B) (f : A -> B) (s : A -> Prop) (_38803 : A) : (term1086 A B _38802 f s _38803) = (term19 A B _38802 f s _38803).
Proof. exact (MK_COMB (@lem3595920 A B _38802 f _38803) (@lem3595923 A s _38803)). Qed.
Lemma lem3595925 {A B : Type'} (_38802 : B) (f : A -> B) (s : A -> Prop) (_38803 : A) : (term1085 A B _38802 f s _38803) = (term19 A B _38802 f s _38803).
Proof. exact (TRANS (@lem3595915 A B _38802 f s _38803) (@lem3595924 A B _38802 f s _38803)). Qed.
Lemma lem3595926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3595927 {A B : Type'} (_38802 : B) (f : A -> B) (s : A -> Prop) (_38803 : A) : (term1090 A B _38802 f s _38803) = (term1091 A B _38802 f s _38803).
Proof. exact (MK_COMB (@lem3595926) (@lem3595925 A B _38802 f s _38803)). Qed.
Lemma lem3595928 {A B : Type'} (f : A -> B) (g : B -> A) (_38802 : B) : ((term118 A B f g _38802) = _38802) = ((term118 A B f g _38802) = _38802).
Proof. exact (eq_refl ((term118 A B f g _38802) = _38802)). Qed.
Lemma lem3595929 {A B : Type'} (s : A -> Prop) (_38803 : A) (f : A -> B) (g : B -> A) (_38802 : B) : (term1108 A B s _38803 f g _38802) = (term1109 A B s _38803 f g _38802).
Proof. exact (MK_COMB (@lem3595927 A B _38802 f s _38803) (@lem3595928 A B f g _38802)). Qed.
Lemma lem3595930 {A B : Type'} (s : A -> Prop) (_38803 : A) (f : A -> B) (g : B -> A) (_38802 : B) : (term1107 A B g _38802 f s _38803) = (term1109 A B s _38803 f g _38802).
Proof. exact (TRANS (@lem3595912 A B s _38803 f g _38802) (@lem3595929 A B s _38803 f g _38802)). Qed.
Lemma lem3595932 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1093 A B f s x''''''.
Proof. exact (conj (@lem3595796 A B f x'''''') (@lem3595803 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3595934 {A B : Type'} (_38803 : A) (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1109 A B s _38803 f g _38802.
Proof. exact (EQ_MP (@lem3595930 A B s _38803 f g _38802) (@lem3595909 A B _38802 _38803 s f g h1)). Qed.
Lemma lem3595935 {A B : Type'} (_38803 : A) (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1109 A B s _38803 f g _38802.
Proof. exact (@lem3595934 A B _38803 _38802 s f g h1). Qed.
Lemma lem3595936 {A B : Type'} (x'''''' : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1110 A B s g f x''''''.
Proof. exact (@lem3595935 A B x'''''' (f x'''''') s f g h1). Qed.
Lemma lem3595939 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''') = (f x'''''').
Proof. exact (@lem3595936 A B x'''''' s f g h1 (@lem3595932 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h2)). Qed.
Lemma lem3595940 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1111 A B g f x''''''.
Proof. exact (fun h0 : term1112 A B g f x'''''' => @lem3595939 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2). Qed.
Lemma lem3595942 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3595943 {A B : Type'} (g : B -> A) (f : A -> B) (x'''''' : A) : (term1111 A B g f x'''''') = ((term1039 A B g f x'''''') = (f x'''''')).
Proof. exact (@lem3595942 ((term1039 A B g f x'''''') = (f x''''''))). Qed.
Lemma lem3595944 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''') = (f x'''''').
Proof. exact (EQ_MP (@lem3595943 A B g f x'''''') (@lem3595940 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3595962 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3595963 {B : Type'} (y : B) (x : B) (z : B) : (term1115 B x y z) = (term1116 B y x z).
Proof. exact (@lem3595962 (y = z) (term265 B x z)). Qed.
Lemma lem3595973 {B : Type'} (x : B) (y : B) : (term1117 B x y) = (term1117 B x y).
Proof. exact (eq_refl (term1117 B x y)). Qed.
Lemma lem3595974 {B : Type'} (y : B) (x : B) (z : B) : (term1098 B x y z) = (term1118 B y x z).
Proof. exact (MK_COMB (@lem3595973 B x y) (@lem3595963 B y x z)). Qed.
Lemma lem3595978 (q : Prop) (p : Prop) (r : Prop) : (term93 p q r) = (term93 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3595979 {B : Type'} (y : B) (x : B) (z : B) : (term1118 B y x z) = (term1119 B y x z).
Proof. exact (@lem3595978 (y = z) (term265 B x y) (term265 B x z)). Qed.
Lemma lem3596001 {B : Type'} (y : B) (x : B) (z : B) : (term1098 B x y z) = (term1119 B y x z).
Proof. exact (TRANS (@lem3595974 B y x z) (@lem3595979 B y x z)). Qed.
Lemma lem3596002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3596003 {B : Type'} (y : B) (x : B) (z : B) : (term1120 B x y z) = (term1121 B y x z).
Proof. exact (MK_COMB (@lem3596002) (@lem3596001 B y x z)). Qed.
Lemma lem3596025 {B : Type'} (y : B) (x : B) (z : B) : (term1119 B y x z) = (term1119 B y x z).
Proof. exact (eq_refl (term1119 B y x z)). Qed.
Lemma lem3596026 {B : Type'} (y : B) (x : B) (z : B) : ((term1098 B x y z) = (term1119 B y x z)) = ((term1119 B y x z) = (term1119 B y x z)).
Proof. exact (MK_COMB (@lem3596003 B y x z) (@lem3596025 B y x z)). Qed.
Lemma lem3596028 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3596029 (x : Prop) : (x = x) = True.
Proof. exact (@lem3596028 Prop x). Qed.
Lemma lem3596030 {B : Type'} (y : B) (x : B) (z : B) : ((term1119 B y x z) = (term1119 B y x z)) = True.
Proof. exact (@lem3596029 (term1119 B y x z)). Qed.
Lemma lem3596031 {B : Type'} (y : B) (x : B) (z : B) : ((term1098 B x y z) = (term1119 B y x z)) = True.
Proof. exact (TRANS (@lem3596026 B y x z) (@lem3596030 B y x z)). Qed.
Lemma lem3596032 {B : Type'} (y : B) (x : B) (z : B) : True = ((term1098 B x y z) = (term1119 B y x z)).
Proof. exact (SYM (@lem3596031 B y x z)). Qed.
Lemma lem3596033 {B : Type'} (y : B) (x : B) (z : B) : (term1098 B x y z) = (term1119 B y x z).
Proof. exact (EQ_MP (@lem3596032 B y x z) (@lem0)). Qed.
Lemma lem3596034 {B : Type'} (y : B) (x : B) (z : B) : term1119 B y x z.
Proof. exact (EQ_MP (@lem3596033 B y x z) (@lem3595780 B x y z)). Qed.
Lemma lem3596036 (b : Prop) (a : Prop) : (a \/ b) = (term1081 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3596037 {B : Type'} (x : B) (y : B) (z : B) : (term1119 B y x z) = (term1122 B x y z).
Proof. exact (@lem3596036 (term1123 B y x z) (y = z)). Qed.
Lemma lem3596039 (a : Prop) (b : Prop) : (term1083 a b) = (term1084 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3596040 {B : Type'} (y : B) (x : B) (z : B) : (term1124 B y x z) = (term1125 B y x z).
Proof. exact (@lem3596039 (term265 B x y) (term265 B x z)). Qed.
Lemma lem3596042 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3596043 {B : Type'} (x : B) (y : B) : (term1126 B x y) = (x = y).
Proof. exact (@lem3596042 (x = y)). Qed.
Lemma lem3596044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3596045 {B : Type'} (x : B) (y : B) : (term1127 B x y) = (term1128 B x y).
Proof. exact (MK_COMB (@lem3596044) (@lem3596043 B x y)). Qed.
Lemma lem3596047 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3596048 {B : Type'} (x : B) (z : B) : (term1126 B x z) = (x = z).
Proof. exact (@lem3596047 (x = z)). Qed.
Lemma lem3596049 {B : Type'} (y : B) (x : B) (z : B) : (term1125 B y x z) = (term1129 B y x z).
Proof. exact (MK_COMB (@lem3596045 B x y) (@lem3596048 B x z)). Qed.
Lemma lem3596050 {B : Type'} (y : B) (x : B) (z : B) : (term1124 B y x z) = (term1129 B y x z).
Proof. exact (TRANS (@lem3596040 B y x z) (@lem3596049 B y x z)). Qed.
Lemma lem3596051 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3596052 {B : Type'} (y : B) (x : B) (z : B) : (term1130 B y x z) = (term1131 B y x z).
Proof. exact (MK_COMB (@lem3596051) (@lem3596050 B y x z)). Qed.
Lemma lem3596053 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3596054 {B : Type'} (x : B) (y : B) (z : B) : (term1122 B x y z) = (term1132 B x y z).
Proof. exact (MK_COMB (@lem3596052 B y x z) (@lem3596053 B y z)). Qed.
Lemma lem3596055 {B : Type'} (x : B) (y : B) (z : B) : (term1119 B y x z) = (term1132 B x y z).
Proof. exact (TRANS (@lem3596037 B x y z) (@lem3596054 B x y z)). Qed.
Lemma lem3596057 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1159 A B x'''''''' g f x''''''.
Proof. exact (conj (@lem3595787 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h2) (@lem3595944 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596059 {B : Type'} (x : B) (y : B) (z : B) : term1132 B x y z.
Proof. exact (EQ_MP (@lem3596055 B x y z) (@lem3596034 B y x z)). Qed.
Lemma lem3596060 {B : Type'} (x : B) (y : B) (z : B) : term1132 B x y z.
Proof. exact (@lem3596059 B x y z). Qed.
Lemma lem3596061 {A B : Type'} (g : B -> A) (x'''''''' : A) (f : A -> B) (x'''''' : A) : term1160 A B g x'''''''' f x''''''.
Proof. exact (@lem3596060 B (term1039 A B g f x'''''') (term1039 A B g f x'''''''') (f x'''''')). Qed.
Lemma lem3596064 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''''') = (f x'''''').
Proof. exact (@lem3596061 A B g x'''''''' f x'''''' (@lem3596057 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596065 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1161 A B g x'''''''' f x''''''.
Proof. exact (fun h0 : term1162 A B g x'''''''' f x'''''' => @lem3596064 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2). Qed.
Lemma lem3596067 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3596068 {A B : Type'} (g : B -> A) (x'''''''' : A) (f : A -> B) (x'''''' : A) : (term1161 A B g x'''''''' f x'''''') = ((term1039 A B g f x'''''''') = (f x'''''')).
Proof. exact (@lem3596067 ((term1039 A B g f x'''''''') = (f x''''''))). Qed.
Lemma lem3596069 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''''') = (f x'''''').
Proof. exact (EQ_MP (@lem3596068 A B g x'''''''' f x'''''') (@lem3596065 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596071 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3596072 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3596071 B x). Qed.
Lemma lem3596073 {A B : Type'} (f : A -> B) (x'''''''' : A) : (f x'''''''') = (f x'''''''').
Proof. exact (@lem3596072 B (f x'''''''')). Qed.
Lemma lem3596074 {A B : Type'} (f : A -> B) (x'''''''' : A) : term76 A B f x''''''''.
Proof. exact (fun h0 : term77 A B f x'''''''' => @lem3596073 A B f x''''''''). Qed.
Lemma lem3596076 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3596077 {A B : Type'} (f : A -> B) (x'''''''' : A) : (term76 A B f x'''''''') = ((f x'''''''') = (f x'''''''')).
Proof. exact (@lem3596076 ((f x'''''''') = (f x''''''''))). Qed.
Lemma lem3596078 {A B : Type'} (f : A -> B) (x'''''''' : A) : (f x'''''''') = (f x'''''''').
Proof. exact (EQ_MP (@lem3596077 A B f x'''''''') (@lem3596074 A B f x'''''''')). Qed.
Lemma lem3596080 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : s x''''''''.
Proof. exact (proj2 (@lem3593390 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3596081 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term73 A s x''''''''.
Proof. exact (fun h0 : term74 A s x'''''''' => @lem3596080 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1). Qed.
Lemma lem3596083 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3596084 {A : Type'} (s : A -> Prop) (x'''''''' : A) : (term73 A s x'''''''') = (s x'''''''').
Proof. exact (@lem3596083 (s x'''''''')). Qed.
Lemma lem3596085 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : s x''''''''.
Proof. exact (EQ_MP (@lem3596084 A s x'''''''') (@lem3596081 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3596086 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1093 A B f s x''''''''.
Proof. exact (conj (@lem3596078 A B f x'''''''') (@lem3596085 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3596088 {A B : Type'} (_38803 : A) (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1109 A B s _38803 f g _38802.
Proof. exact (EQ_MP (@lem3595930 A B s _38803 f g _38802) (@lem3595909 A B _38802 _38803 s f g h1)). Qed.
Lemma lem3596089 {A B : Type'} (_38803 : A) (_38802 : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1109 A B s _38803 f g _38802.
Proof. exact (@lem3596088 A B _38803 _38802 s f g h1). Qed.
Lemma lem3596090 {A B : Type'} (x'''''''' : A) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term1110 A B s g f x''''''''.
Proof. exact (@lem3596089 A B x'''''''' (f x'''''''') s f g h1). Qed.
Lemma lem3596093 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''''') = (f x'''''''').
Proof. exact (@lem3596090 A B x'''''''' s f g h1 (@lem3596086 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h2)). Qed.
Lemma lem3596094 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1111 A B g f x''''''''.
Proof. exact (fun h0 : term1112 A B g f x'''''''' => @lem3596093 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2). Qed.
Lemma lem3596096 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3596097 {A B : Type'} (g : B -> A) (f : A -> B) (x'''''''' : A) : (term1111 A B g f x'''''''') = ((term1039 A B g f x'''''''') = (f x'''''''')).
Proof. exact (@lem3596096 ((term1039 A B g f x'''''''') = (f x''''''''))). Qed.
Lemma lem3596098 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1039 A B g f x'''''''') = (f x'''''''').
Proof. exact (EQ_MP (@lem3596097 A B g f x'''''''') (@lem3596094 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596099 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1163 A B x'''''' g f x''''''''.
Proof. exact (conj (@lem3596069 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2) (@lem3596098 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596101 {B : Type'} (x : B) (y : B) (z : B) : term1132 B x y z.
Proof. exact (EQ_MP (@lem3596055 B x y z) (@lem3596034 B y x z)). Qed.
Lemma lem3596102 {B : Type'} (x : B) (y : B) (z : B) : term1132 B x y z.
Proof. exact (@lem3596101 B x y z). Qed.
Lemma lem3596103 {A B : Type'} (g : B -> A) (x'''''' : A) (f : A -> B) (x'''''''' : A) : term1164 A B g x'''''' f x''''''''.
Proof. exact (@lem3596102 B (term1039 A B g f x'''''''') (f x'''''') (f x'''''''')). Qed.
Lemma lem3596106 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (f x'''''') = (f x'''''''').
Proof. exact (@lem3596103 A B g x'''''' f x'''''''' (@lem3596099 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596107 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1165 A B x'''''' f x''''''''.
Proof. exact (fun h0 : term1166 A B x'''''' f x'''''''' => @lem3596106 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2). Qed.
Lemma lem3596109 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3596110 {A B : Type'} (x'''''' : A) (f : A -> B) (x'''''''' : A) : (term1165 A B x'''''' f x'''''''') = ((f x'''''') = (f x'''''''')).
Proof. exact (@lem3596109 ((f x'''''') = (f x''''''''))). Qed.
Lemma lem3596111 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (f x'''''') = (f x'''''''').
Proof. exact (EQ_MP (@lem3596110 A B x'''''' f x'''''''') (@lem3596107 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596117 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3596118 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : (term1156 A B _38962 g _38963) = (term1167 A B g _38962 _38963).
Proof. exact (@lem3596117 ((g _38962) = (g _38963)) (term265 B _38962 _38963)). Qed.
Lemma lem3596128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3596129 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : (term1168 A B _38962 g _38963) = (term1169 A B g _38962 _38963).
Proof. exact (MK_COMB (@lem3596128) (@lem3596118 A B g _38962 _38963)). Qed.
Lemma lem3596139 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : (term1167 A B g _38962 _38963) = (term1167 A B g _38962 _38963).
Proof. exact (eq_refl (term1167 A B g _38962 _38963)). Qed.
Lemma lem3596140 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : ((term1156 A B _38962 g _38963) = (term1167 A B g _38962 _38963)) = ((term1167 A B g _38962 _38963) = (term1167 A B g _38962 _38963)).
Proof. exact (MK_COMB (@lem3596129 A B g _38962 _38963) (@lem3596139 A B g _38962 _38963)). Qed.
Lemma lem3596142 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3596143 (x : Prop) : (x = x) = True.
Proof. exact (@lem3596142 Prop x). Qed.
Lemma lem3596144 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : ((term1167 A B g _38962 _38963) = (term1167 A B g _38962 _38963)) = True.
Proof. exact (@lem3596143 (term1167 A B g _38962 _38963)). Qed.
Lemma lem3596145 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : ((term1156 A B _38962 g _38963) = (term1167 A B g _38962 _38963)) = True.
Proof. exact (TRANS (@lem3596140 A B g _38962 _38963) (@lem3596144 A B g _38962 _38963)). Qed.
Lemma lem3596146 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : True = ((term1156 A B _38962 g _38963) = (term1167 A B g _38962 _38963)).
Proof. exact (SYM (@lem3596145 A B g _38962 _38963)). Qed.
Lemma lem3596147 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : (term1156 A B _38962 g _38963) = (term1167 A B g _38962 _38963).
Proof. exact (EQ_MP (@lem3596146 A B g _38962 _38963) (@lem0)). Qed.
Lemma lem3596148 {A B : Type'} (g : B -> A) (_38962 : B) (_38963 : B) : term1167 A B g _38962 _38963.
Proof. exact (EQ_MP (@lem3596147 A B g _38962 _38963) (@lem3595776 A B _38962 g _38963)). Qed.
Lemma lem3596150 (b : Prop) (a : Prop) : (a \/ b) = (term1081 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3596151 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : (term1167 A B g _38962 _38963) = (term1170 A B _38962 g _38963).
Proof. exact (@lem3596150 (term265 B _38962 _38963) ((g _38962) = (g _38963))). Qed.
Lemma lem3596153 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3596154 {B : Type'} (_38962 : B) (_38963 : B) : (term1126 B _38962 _38963) = (_38962 = _38963).
Proof. exact (@lem3596153 (_38962 = _38963)). Qed.
Lemma lem3596155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3596156 {B : Type'} (_38962 : B) (_38963 : B) : (term1171 B _38962 _38963) = (term1172 B _38962 _38963).
Proof. exact (MK_COMB (@lem3596155) (@lem3596154 B _38962 _38963)). Qed.
Lemma lem3596157 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : ((g _38962) = (g _38963)) = ((g _38962) = (g _38963)).
Proof. exact (eq_refl ((g _38962) = (g _38963))). Qed.
Lemma lem3596158 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : (term1170 A B _38962 g _38963) = (term1154 A B _38962 g _38963).
Proof. exact (MK_COMB (@lem3596156 B _38962 _38963) (@lem3596157 A B _38962 g _38963)). Qed.
Lemma lem3596159 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : (term1167 A B g _38962 _38963) = (term1154 A B _38962 g _38963).
Proof. exact (TRANS (@lem3596151 A B _38962 g _38963) (@lem3596158 A B _38962 g _38963)). Qed.
Lemma lem3596162 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : term1154 A B _38962 g _38963.
Proof. exact (EQ_MP (@lem3596159 A B _38962 g _38963) (@lem3596148 A B g _38962 _38963)). Qed.
Lemma lem3596163 {A B : Type'} (_38962 : B) (g : B -> A) (_38963 : B) : term1154 A B _38962 g _38963.
Proof. exact (@lem3596162 A B _38962 g _38963). Qed.
Lemma lem3596164 {A B : Type'} (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : term1173 A B x'''''' g f x''''''''.
Proof. exact (@lem3596163 A B (f x'''''') g (f x'''''''')). Qed.
Lemma lem3596167 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1021 A B g f x'''''') = (term1021 A B g f x'''''''').
Proof. exact (@lem3596164 A B x'''''' g f x'''''''' (@lem3596111 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596168 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1174 A B x'''''' g f x''''''''.
Proof. exact (fun h0 : term1062 A B x'''''' g f x'''''''' => @lem3596167 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2). Qed.
Lemma lem3596170 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3596171 {A B : Type'} (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : (term1174 A B x'''''' g f x'''''''') = ((term1021 A B g f x'''''') = (term1021 A B g f x'''''''')).
Proof. exact (@lem3596170 ((term1021 A B g f x'''''') = (term1021 A B g f x''''''''))). Qed.
Lemma lem3596172 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term1021 A B g f x'''''') = (term1021 A B g f x'''''''').
Proof. exact (EQ_MP (@lem3596171 A B x'''''' g f x'''''''') (@lem3596168 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596175 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3596177 {A B : Type'} (x'''''' : A) (g : B -> A) (f : A -> B) (x'''''''' : A) : (term1062 A B x'''''' g f x'''''''') = (term1175 A B x'''''' g f x'''''''').
Proof. exact (@lem3596175 ((term1021 A B g f x'''''') = (term1021 A B g f x''''''''))). Qed.
Lemma lem3596180 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term1175 A B x'''''' g f x''''''''.
Proof. exact (EQ_MP (@lem3596177 A B x'''''' g f x'''''''') (@lem3594884 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1)). Qed.
Lemma lem3596183 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : False.
Proof. exact (@lem3596180 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h2 (@lem3596172 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596184 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : term85.
Proof. exact (fun h0 : ~ False => @lem3596183 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2). Qed.
Lemma lem3596186 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3596187 : term85 = False.
Proof. exact (@lem3596186 False). Qed.
Lemma lem3596192 {A B : Type'} (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : False.
Proof. exact (EQ_MP (@lem3596187) (@lem3596184 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2)). Qed.
Lemma lem3596195 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term125 A B s f g) (h2 : term442 A B x' x'' g x''' f s x'''') : False.
Proof. exact (EQ_MP (@lem3595747) (@lem3595744 A B x' x'' g x''' f s x'''' h1 h2)). Qed.
Lemma lem3596196 {A B : Type'} (x'' : A) (x' : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term125 A B s f g) (h2 : term379 A B x'' x' g f s) : False.
Proof. exact (EQ_MP (@lem3595534) (@lem3595531 A B x'' x' g f s h1 h2)). Qed.
Lemma lem3596198 {A B : Type'} (g : B -> A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) (x : A) (h1 : term125 A B s f g) (h2 : term362 A B g x' f x'' s x) : False.
Proof. exact (EQ_MP (@lem3595151) (@lem3595148 A B g x' f x'' s x h1 h2)). Qed.
Lemma lem3596199 {A B : Type'} (x' : B) (x'' : A) (g : B -> A) (x''' : B) (f : A -> B) (s : A -> Prop) (x'''' : A) (h1 : term125 A B s f g) (h2 : term511 A B x' x'' g x''' f s x'''') : False.
Proof. exact (or_elim (@lem3593368 A B x' x'' g x''' f s x'''' h2) (fun h0 : term379 A B x'' x' g f s => @lem3596196 A B x'' x' g f s h1 h0) (fun h0 : term442 A B x' x'' g x''' f s x'''' => @lem3596195 A B x' x'' g x''' f s x'''' h1 h0)). Qed.
Lemma lem3596200 {A B : Type'} (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term780 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : False.
Proof. exact (or_elim (@lem3593361 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h2) (fun h0 : term511 A B x' x'' g x''' f s x'''' => @lem3596199 A B x' x'' g x''' f s x'''' h1 h0) (fun h0 : term650 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' => @lem3596192 A B x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h0)). Qed.
Lemma lem3596201 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : False.
Proof. exact (or_elim (@lem3593359 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h2) (fun h0 : term362 A B g x' f x'' s x => @lem3596198 A B g x' f x'' s x h1 h0) (fun h0 : term780 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' => @lem3596200 A B x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h0)). Qed.
Lemma lem3596202 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : (term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') = False.
Proof. exact (prop_ext (fun h3 : term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' => @lem3596201 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2) (fun h3 : False => @lem3593359 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h2)). Qed.
Lemma lem3596203 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (x'''''''' : A) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term921 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''') : False.
Proof. exact (EQ_MP (@lem3596202 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h2) (@lem3593359 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h2)). Qed.
Lemma lem3596204 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (x''''''' : B) (s : A -> Prop) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term924 A B x x' x''' x''''' x'''''' g x''''''' s f x'' x'''') : False.
Proof. exact (ex_elim (@lem3593080 A B x x' x''' x''''' x'''''' g x''''''' s f x'' x'''' h2) (fun x'''''''' : A => fun h0 : term923 A B x x' x''' x''''' x'''''' g x''''''' s f x'' x'''' x'''''''' => @lem3596203 A B x x' x''' x''''' x'''''' g x''''''' s x'''''''' f x'' x'''' h1 h0)). Qed.
Lemma lem3596205 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (x'''''' : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term926 A B x x' x''' x''''' x'''''' g s f x'' x'''') : False.
Proof. exact (ex_elim (@lem3593079 A B x x' x''' x''''' x'''''' g s f x'' x'''' h2) (fun x''''''' : B => fun h0 : term925 A B x x' x''' x''''' x'''''' g s f x'' x'''' x''''''' => @lem3596204 A B x x' x''' x''''' x'''''' g x''''''' s f x'' x'''' h1 h0)). Qed.
Lemma lem3596206 {A B : Type'} (x : A) (x' : B) (x''' : B) (x''''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term928 A B x x' x''' x''''' g s f x'' x'''') : False.
Proof. exact (ex_elim (@lem3593078 A B x x' x''' x''''' g s f x'' x'''' h2) (fun x'''''' : A => fun h0 : term927 A B x x' x''' x''''' g s f x'' x'''' x'''''' => @lem3596205 A B x x' x''' x''''' x'''''' g s f x'' x'''' h1 h0)). Qed.
Lemma lem3596207 {A B : Type'} (x : A) (x' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (x'''' : A) (h1 : term125 A B s f g) (h2 : term930 A B x x' x''' g s f x'' x'''') : False.
Proof. exact (ex_elim (@lem3593077 A B x x' x''' g s f x'' x'''' h2) (fun x''''' : B => fun h0 : term929 A B x x' x''' g s f x'' x'''' x''''' => @lem3596206 A B x x' x''' x''''' g s f x'' x'''' h1 h0)). Qed.
Lemma lem3596208 {A B : Type'} (x : A) (x' : B) (x''' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (h1 : term125 A B s f g) (h2 : term932 A B x x' x''' g s f x'') : False.
Proof. exact (ex_elim (@lem3593076 A B x x' x''' g s f x'' h2) (fun x'''' : A => fun h0 : term931 A B x x' x''' g s f x'' x'''' => @lem3596207 A B x x' x''' g s f x'' x'''' h1 h0)). Qed.
Lemma lem3596209 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (x'' : A) (h1 : term125 A B s f g) (h2 : term934 A B x x' g s f x'') : False.
Proof. exact (ex_elim (@lem3593075 A B x x' g s f x'' h2) (fun x''' : B => fun h0 : term933 A B x x' g s f x'' x''' => @lem3596208 A B x x' x''' g s f x'' h1 h0)). Qed.
Lemma lem3596210 {A B : Type'} (x : A) (x' : B) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term125 A B s f g) (h2 : term936 A B x x' g s f) : False.
Proof. exact (ex_elim (@lem3593074 A B x x' g s f h2) (fun x'' : A => fun h0 : term935 A B x x' g s f x'' => @lem3596209 A B x x' g s f x'' h1 h0)). Qed.
Lemma lem3596211 {A B : Type'} (x : A) (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term125 A B s f g) (h2 : term938 A B x g s f) : False.
Proof. exact (ex_elim (@lem3593073 A B x g s f h2) (fun x' : B => fun h0 : term937 A B x g s f x' => @lem3596210 A B x x' g s f h1 h0)). Qed.
Lemma lem3596212 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term125 A B s f g) (h2 : term197 A B g s f) : False.
Proof. exact (ex_elim (@lem3593072 A B g s f h2) (fun x : A => fun h0 : term939 A B g s f x => @lem3596211 A B x g s f h1 h0)). Qed.
Lemma lem3596213 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term125 A B s f g) (h2 : term197 A B g s f) : (term197 A B g s f) = False.
Proof. exact (prop_ext (fun h3 : term197 A B g s f => @lem3596212 A B g s f h1 h2) (fun h3 : False => @lem3590721 A B g s f h2)). Qed.
Lemma lem3596214 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term125 A B s f g) (h2 : term197 A B g s f) : False.
Proof. exact (EQ_MP (@lem3596213 A B g s f h1 h2) (@lem3590721 A B g s f h2)). Qed.
Lemma lem3596215 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term196 A B g s f.
Proof. exact (fun h0 : term197 A B g s f => @lem3596214 A B g s f h1 h0). Qed.
Lemma lem3596216 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term125 A B s f g) : term176 A B g s f.
Proof. exact (EQ_MP (@lem3590720 A B g s f) (@lem3596215 A B s f g h1)). Qed.
Lemma lem3596217 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term177 A B g s f.
Proof. exact (fun h0 : term125 A B s f g => @lem3596216 A B s f g h0). Qed.
Lemma lem3596222 {A B : Type'} (s : A -> Prop) (f : A -> B) : term187 A B s f.
Proof. exact (fun g : B -> A => @lem3596217 A B g s f). Qed.
Lemma lem3596227 {A B : Type'} (f : A -> B) : term191 A B f.
Proof. exact (fun s : A -> Prop => @lem3596222 A B s f). Qed.
Lemma lem3596232 {A B : Type'} : term195 A B.
Proof. exact (fun f : A -> B => @lem3596227 A B f). Qed.
Lemma lem3596233 {A B : Type'} : term194 A B.
Proof. exact (EQ_MP (@lem3590715 A B) (@lem3596232 A B)). Qed.
Lemma lem3596234 {A B : Type'} (f : A -> B) : term1176 A B f.
Proof. exact (@lem3596233 A B f). Qed.
Lemma lem3596235 {A B : Type'} (f : A -> B) : (term1176 A B f) = (term190 A B f).
Proof. exact (eq_refl (term1176 A B f)). Qed.
Lemma lem3596236 {A B : Type'} (f : A -> B) : term190 A B f.
Proof. exact (EQ_MP (@lem3596235 A B f) (@lem3596234 A B f)). Qed.
Lemma lem3596237 {A B : Type'} (f : A -> B) (s : A -> Prop) : term1177 A B f s.
Proof. exact (@lem3596236 A B f s). Qed.
Lemma lem3596238 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1177 A B f s) = (term186 A B s f).
Proof. exact (eq_refl (term1177 A B f s)). Qed.
Lemma lem3596239 {A B : Type'} (s : A -> Prop) (f : A -> B) : term186 A B s f.
Proof. exact (EQ_MP (@lem3596238 A B s f) (@lem3596237 A B f s)). Qed.
Lemma lem3596240 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : term1178 A B s f g.
Proof. exact (@lem3596239 A B s f g). Qed.
Lemma lem3596241 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : (term1178 A B s f g) = (term178 A B g s f).
Proof. exact (eq_refl (term1178 A B s f g)). Qed.
Lemma lem3596242 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term178 A B g s f.
Proof. exact (EQ_MP (@lem3596241 A B g s f) (@lem3596240 A B s f g)). Qed.
Lemma lem3596244 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term178 A B g s f.
Proof. exact (@lem3589879 A B g s f (@lem3596242 A B g s f)). Qed.
Lemma lem3596245 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term179 A B g s f) : False.
Proof. exact (@lem3596244 A B g s f (@lem3589863 A B g s f h1)). Qed.
Lemma lem3596246 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term179 A B g s f) : (term179 A B g s f) = False.
Proof. exact (prop_ext (fun h2 : term179 A B g s f => @lem3596245 A B g s f h1) (fun h2 : False => @lem3589863 A B g s f h1)). Qed.
Lemma lem3596247 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term179 A B g s f) : False.
Proof. exact (EQ_MP (@lem3596246 A B g s f h1) (@lem3589863 A B g s f h1)). Qed.
Lemma lem3596248 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term178 A B g s f.
Proof. exact (fun h0 : term179 A B g s f => @lem3596247 A B g s f h0). Qed.
Lemma lem3596249 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term177 A B g s f.
Proof. exact (EQ_MP (@lem3589862 A B g s f) (@lem3596248 A B g s f)). Qed.
Lemma lem3596250 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term113 A B g s f.
Proof. exact (EQ_MP (@lem3589858 A B g s f) (@lem3596249 A B g s f)). Qed.
Lemma lem3596251 {A B : Type'} (g : B -> A) (s : A -> Prop) (f : A -> B) : term112 A B g s f.
Proof. exact (EQ_MP (@lem3589428 A B g s f) (@lem3596250 A B g s f)). Qed.
Lemma lem3596252 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term13 A B s f g) : term109 A B g s f.
Proof. exact (@lem3596251 A B g s f (@lem3588700 A B s f g h1)). Qed.
Lemma lem3596253 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term13 A B s f g) : term1179 A B s f.
Proof. exact (ex_intro (term1180 A B s f) (term98 A B g f s) (@lem3596252 A B s f g h1)). Qed.
Lemma lem3596254 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term13 A B s f g) : (term13 A B s f g) = (term1179 A B s f).
Proof. exact (prop_ext (fun h2 : term13 A B s f g => @lem3596253 A B s f g h1) (fun h2 : term1179 A B s f => @lem3588700 A B s f g h1)). Qed.
Lemma lem3596255 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term13 A B s f g) : term1179 A B s f.
Proof. exact (EQ_MP (@lem3596254 A B s f g h1) (@lem3588700 A B s f g h1)). Qed.
Lemma lem3596256 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term12 A B s f) : term1179 A B s f.
Proof. exact (ex_elim (@lem3588699 A B s f h1) (fun g : B -> A => fun h0 : term1181 A B s f g => @lem3596255 A B s f g h0)). Qed.
Lemma lem3596257 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term12 A B s f) = (term1179 A B s f).
Proof. exact (prop_ext (fun h1 : term12 A B s f => @lem3596256 A B s f h1) (fun h1 : term1179 A B s f => @lem3589338 A B s f)). Qed.
Lemma lem3596258 {A B : Type'} (s : A -> Prop) (f : A -> B) : term1179 A B s f.
Proof. exact (EQ_MP (@lem3596257 A B s f) (@lem3589338 A B s f)). Qed.
Lemma lem3596263 {A B : Type'} (f : A -> B) : term1182 A B f.
Proof. exact (fun s : A -> Prop => @lem3596258 A B s f). Qed.
Lemma lem3596268 {A B : Type'} : term1183 A B.
Proof. exact (fun f : A -> B => @lem3596263 A B f). Qed.
