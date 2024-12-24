Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_DEFINED_term_abbrevs.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4386715 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4386716 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4386717 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4386716 A B s) (@lem4386715 A B s)). Qed.
Lemma lem4386718 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4386717 A B s f). Qed.
Lemma lem4386719 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4386720 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4386719 A B s f) (@lem4386718 A B s f)). Qed.
Lemma lem4386721 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4386720 A B s f x). Qed.
Lemma lem4386722 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4386739 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term6 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4386740 (p : Prop) (q : Prop) (p' : Prop) : term7 p q p'.
Proof. exact (fun q' : Prop => @lem4386739 p q p' q'). Qed.
Lemma lem4386741 (p : Prop) (q : Prop) : term8 p q.
Proof. exact (fun p' : Prop => @lem4386740 p q p'). Qed.
Lemma lem4386742 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term9 A B s f x.
Proof. exact (@lem4386741 (@IN A x s) ((@RESTRICTION A B s f x) = (f x))). Qed.
Lemma lem4386743 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term10 A B s f x p'.
Proof. exact (@lem4386742 A B s f x p'). Qed.
Lemma lem4386744 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : (term10 A B s f x p') = (term11 A B s f x p').
Proof. exact (eq_refl (term10 A B s f x p')). Qed.
Lemma lem4386745 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term11 A B s f x p'.
Proof. exact (EQ_MP (@lem4386744 A B s f x p') (@lem4386743 A B s f x p')). Qed.
Lemma lem4386746 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term12 A B s f x p' q'.
Proof. exact (@lem4386745 A B s f x p' q'). Qed.
Lemma lem4386747 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term12 A B s f x p' q') = (term13 A B s f x p' q').
Proof. exact (eq_refl (term12 A B s f x p' q')). Qed.
Lemma lem4386748 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term13 A B s f x p' q'.
Proof. exact (EQ_MP (@lem4386747 A B s f x p' q') (@lem4386746 A B s f x p' q')). Qed.
Lemma lem4386749 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4386750 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term14 A B f x s q'.
Proof. exact (@lem4386748 A B s f x (@IN A x s) q'). Qed.
Lemma lem4386751 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term15 A B f x s q'.
Proof. exact (@lem4386750 A B f x s q' (@lem4386749 A x s)). Qed.
Lemma lem4386752 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4386753 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4386758 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4386722 A B s f x) (@lem4386721 A B s f x)). Qed.
Lemma lem4386759 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4386758 A B s f x). Qed.
Lemma lem4386761 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term16 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4386762 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term17 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4386761 _2963 g t e g' t' e'). Qed.
Lemma lem4386763 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term18 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4386762 _2963 g t e g' t'). Qed.
Lemma lem4386764 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term19 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4386763 _2963 g t e g'). Qed.
Lemma lem4386765 {B : Type'} (g : Prop) (t : B) (e : B) : term19 B g t e.
Proof. exact (@lem4386764 B g t e). Qed.
Lemma lem4386766 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term20 A B s f x.
Proof. exact (@lem4386765 B (@IN A x s) (f x) (@ARB B)). Qed.
Lemma lem4386767 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term21 A B s f x g'.
Proof. exact (@lem4386766 A B s f x g'). Qed.
Lemma lem4386768 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : (term21 A B s f x g') = (term22 A B s f x g').
Proof. exact (eq_refl (term21 A B s f x g')). Qed.
Lemma lem4386769 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term22 A B s f x g'.
Proof. exact (EQ_MP (@lem4386768 A B s f x g') (@lem4386767 A B s f x g')). Qed.
Lemma lem4386770 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : term23 A B s f x g' t'.
Proof. exact (@lem4386769 A B s f x g' t'). Qed.
Lemma lem4386771 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : (term23 A B s f x g' t') = (term24 A B s f x g' t').
Proof. exact (eq_refl (term23 A B s f x g' t')). Qed.
Lemma lem4386772 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : term24 A B s f x g' t'.
Proof. exact (EQ_MP (@lem4386771 A B s f x g' t') (@lem4386770 A B s f x g' t')). Qed.
Lemma lem4386773 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term25 A B s f x g' t' e'.
Proof. exact (@lem4386772 A B s f x g' t' e'). Qed.
Lemma lem4386774 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : (term25 A B s f x g' t' e') = (term26 A B s f x g' t' e').
Proof. exact (eq_refl (term25 A B s f x g' t' e')). Qed.
Lemma lem4386775 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term26 A B s f x g' t' e'.
Proof. exact (EQ_MP (@lem4386774 A B s f x g' t' e') (@lem4386773 A B s f x g' t' e')). Qed.
Lemma lem4386777 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4386753 A x s) (@lem4386752 A x s h1)). Qed.
Lemma lem4386778 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t' : B) (e' : B) : term27 A B s f x t' e'.
Proof. exact (@lem4386775 A B s f x True t' e'). Qed.
Lemma lem4386779 {A B : Type'} (f : A -> B) (t' : B) (e' : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term28 A B s f x t' e'.
Proof. exact (@lem4386778 A B s f x t' e' (@lem4386777 A x s h1)). Qed.
Lemma lem4386785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4386786 {A B : Type'} (f : A -> B) (x : A) : term29 A B f x.
Proof. exact (fun h0 : True => @lem4386785 A B f x). Qed.
Lemma lem4386787 {A B : Type'} (f : A -> B) (e' : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term30 A B s f x e'.
Proof. exact (@lem4386779 A B f (f x) e' x s h1). Qed.
Lemma lem4386788 {A B : Type'} (f : A -> B) (e' : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term31 A B s f x e'.
Proof. exact (@lem4386787 A B f e' x s h1 (@lem4386786 A B f x)). Qed.
Lemma lem4386792 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4386793 {B : Type'} : term32 B.
Proof. exact (fun h0 : ~ True => @lem4386792 B). Qed.
Lemma lem4386794 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term33 A B s f x.
Proof. exact (@lem4386788 A B f (@ARB B) x s h1). Qed.
Lemma lem4386795 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term5 A B s f x) = (term34 A B f x).
Proof. exact (@lem4386794 A B f x s h1 (@lem4386793 B)). Qed.
Lemma lem4386797 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4386798 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4386797 B t2 t1). Qed.
Lemma lem4386799 {A B : Type'} (f : A -> B) (x : A) : (term34 A B f x) = (f x).
Proof. exact (@lem4386798 B (@ARB B) (f x)). Qed.
Lemma lem4386800 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term5 A B s f x) = (f x).
Proof. exact (TRANS (@lem4386795 A B f x s h1) (@lem4386799 A B f x)). Qed.
Lemma lem4386801 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@RESTRICTION A B s f x) = (f x).
Proof. exact (TRANS (@lem4386759 A B s f x) (@lem4386800 A B f x s h1)). Qed.
Lemma lem4386802 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4386803 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term35 A B s f x) = (term36 A B f x).
Proof. exact (MK_COMB (@lem4386802 B) (@lem4386801 A B f x s h1)). Qed.
Lemma lem4386804 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4386805 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : ((@RESTRICTION A B s f x) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem4386803 A B f x s h1) (@lem4386804 A B f x)). Qed.
Lemma lem4386807 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4386808 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4386807 B x). Qed.
Lemma lem4386809 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem4386808 B (f x)). Qed.
Lemma lem4386810 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : ((@RESTRICTION A B s f x) = (f x)) = True.
Proof. exact (TRANS (@lem4386805 A B f x s h1) (@lem4386809 A B f x)). Qed.
Lemma lem4386811 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term37 A B s f x.
Proof. exact (fun h0 : @IN A x s => @lem4386810 A B f x s h0). Qed.
Lemma lem4386812 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term38 A B f x s.
Proof. exact (@lem4386751 A B f x s True). Qed.
Lemma lem4386813 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term39 A B s f x) = (term40 A x s).
Proof. exact (@lem4386812 A B f x s (@lem4386811 A B s f x)). Qed.
Lemma lem4386815 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4386816 {A : Type'} (x : A) (s : A -> Prop) : (term40 A x s) = True.
Proof. exact (@lem4386815 (@IN A x s)). Qed.
Lemma lem4386817 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term39 A B s f x) = True.
Proof. exact (TRANS (@lem4386813 A B f x s) (@lem4386816 A x s)). Qed.
Lemma lem4386818 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term41 A B s f) = (term42 A).
Proof. exact (fun_ext (fun x : A => @lem4386817 A B s f x)). Qed.
Lemma lem4386819 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4386820 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term43 A B s f) = (term44 A).
Proof. exact (MK_COMB (@lem4386819 A) (@lem4386818 A B s f)). Qed.
Lemma lem4386822 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386823 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (@lem4386822 A t). Qed.
Lemma lem4386824 {A : Type'} : (term44 A) = True.
Proof. exact (@lem4386823 A True). Qed.
Lemma lem4386825 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term43 A B s f) = True.
Proof. exact (TRANS (@lem4386820 A B s f) (@lem4386824 A)). Qed.
Lemma lem4386826 {A B : Type'} (s : A -> Prop) : (term46 A B s) = (term47 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4386825 A B s f)). Qed.
Lemma lem4386827 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4386828 {A B : Type'} (s : A -> Prop) : (term48 A B s) = (term49 A B).
Proof. exact (MK_COMB (@lem4386827 A B) (@lem4386826 A B s)). Qed.
Lemma lem4386830 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386831 {A B : Type'} (t : Prop) : (term50 A B t) = t.
Proof. exact (@lem4386830 (A -> B) t). Qed.
Lemma lem4386832 {A B : Type'} : (term49 A B) = True.
Proof. exact (@lem4386831 A B True). Qed.
Lemma lem4386833 {A B : Type'} (s : A -> Prop) : (term48 A B s) = True.
Proof. exact (TRANS (@lem4386828 A B s) (@lem4386832 A B)). Qed.
Lemma lem4386834 {A B : Type'} : (term51 A B) = (term52 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4386833 A B s)). Qed.
Lemma lem4386835 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4386836 {A B : Type'} : (term53 A B) = (term54 A).
Proof. exact (MK_COMB (@lem4386835 A) (@lem4386834 A B)). Qed.
Lemma lem4386838 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4386839 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (@lem4386838 (A -> Prop) t). Qed.
Lemma lem4386840 {A : Type'} : (term54 A) = True.
Proof. exact (@lem4386839 A True). Qed.
Lemma lem4386841 {A B : Type'} : (term53 A B) = True.
Proof. exact (TRANS (@lem4386836 A B) (@lem4386840 A)). Qed.
Lemma lem4386842 {A B : Type'} : True = (term53 A B).
Proof. exact (SYM (@lem4386841 A B)). Qed.
Lemma lem4386843 {A B : Type'} : term53 A B.
Proof. exact (EQ_MP (@lem4386842 A B) (@lem0)). Qed.
