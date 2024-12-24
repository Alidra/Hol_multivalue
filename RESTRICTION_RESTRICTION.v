Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_RESTRICTION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem4389671 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4389672 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4389673 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4389672 A B s) (@lem4389671 A B s)). Qed.
Lemma lem4389674 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4389673 A B s f). Qed.
Lemma lem4389675 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4389676 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4389675 A B s f) (@lem4389674 A B s f)). Qed.
Lemma lem4389677 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4389676 A B s f x). Qed.
Lemma lem4389678 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4389680 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4389681 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (eq_refl (term6 A B f)). Qed.
Lemma lem4389682 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (EQ_MP (@lem4389681 A B f) (@lem4389680 A B f)). Qed.
Lemma lem4389683 {A B : Type'} (f : A -> B) (g : A -> B) : term8 A B f g.
Proof. exact (@lem4389682 A B f g). Qed.
Lemma lem4389684 {A B : Type'} (f : A -> B) (g : A -> B) : (term8 A B f g) = ((f = g) = (term9 A B f g)).
Proof. exact (eq_refl (term8 A B f g)). Qed.
Lemma lem4389703 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem4389684 A B f g) (@lem4389683 A B f g)). Qed.
Lemma lem4389704 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (@lem4389703 A B f g). Qed.
Lemma lem4389705 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : ((term10 A B s t f) = (@RESTRICTION A B s f)) = (term11 A B t s f).
Proof. exact (@lem4389704 A B (term10 A B s t f) (@RESTRICTION A B s f)). Qed.
Lemma lem4389715 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4389678 A B s f x) (@lem4389677 A B s f x)). Qed.
Lemma lem4389716 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4389715 A B s f x). Qed.
Lemma lem4389717 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term12 A B s t f x) = (term13 A B s t f x).
Proof. exact (@lem4389716 A B s (@RESTRICTION A B t f) x). Qed.
Lemma lem4389719 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4389678 A B s f x) (@lem4389677 A B s f x)). Qed.
Lemma lem4389720 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4389719 A B s f x). Qed.
Lemma lem4389721 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B t f x) = (term5 A B t f x).
Proof. exact (@lem4389720 A B t f x). Qed.
Lemma lem4389722 {A B : Type'} (x : A) (s : A -> Prop) : (term14 A B x s) = (term14 A B x s).
Proof. exact (eq_refl (term14 A B x s)). Qed.
Lemma lem4389723 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term15 A B s t f x) = (term16 A B s t f x).
Proof. exact (MK_COMB (@lem4389722 A B x s) (@lem4389721 A B t f x)). Qed.
Lemma lem4389724 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4389725 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term13 A B s t f x) = (term17 A B s t f x).
Proof. exact (MK_COMB (@lem4389723 A B s t f x) (@lem4389724 B)). Qed.
Lemma lem4389726 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term12 A B s t f x) = (term17 A B s t f x).
Proof. exact (TRANS (@lem4389717 A B s t f x) (@lem4389725 A B s t f x)). Qed.
Lemma lem4389727 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4389728 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term18 A B s t f x) = (term19 A B s t f x).
Proof. exact (MK_COMB (@lem4389727 B) (@lem4389726 A B s t f x)). Qed.
Lemma lem4389730 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4389678 A B s f x) (@lem4389677 A B s f x)). Qed.
Lemma lem4389731 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4389730 A B s f x). Qed.
Lemma lem4389732 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term12 A B s t f x) = (@RESTRICTION A B s f x)) = ((term17 A B s t f x) = (term5 A B s f x)).
Proof. exact (MK_COMB (@lem4389728 A B s t f x) (@lem4389731 A B s f x)). Qed.
Lemma lem4389737 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term20 A B t s f) = (term21 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem4389732 A B t s f x)). Qed.
Lemma lem4389738 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4389739 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term11 A B t s f) = (term22 A B t s f).
Proof. exact (MK_COMB (@lem4389738 A) (@lem4389737 A B t s f)). Qed.
Lemma lem4389744 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : ((term10 A B s t f) = (@RESTRICTION A B s f)) = (term22 A B t s f).
Proof. exact (TRANS (@lem4389705 A B t s f) (@lem4389739 A B t s f)). Qed.
Lemma lem4389745 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term23 A s t).
Proof. exact (eq_refl (term23 A s t)). Qed.
Lemma lem4389746 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term24 A B t s f) = (term25 A B t s f).
Proof. exact (MK_COMB (@lem4389745 A s t) (@lem4389744 A B t s f)). Qed.
Lemma lem4389749 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : (term26 A B t s) = (term27 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem4389746 A B t s f)). Qed.
Lemma lem4389750 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4389751 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : (term28 A B t s) = (term29 A B t s).
Proof. exact (MK_COMB (@lem4389750 A B) (@lem4389749 A B t s)). Qed.
Lemma lem4389756 {A B : Type'} (s : A -> Prop) : (term30 A B s) = (term31 A B s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4389751 A B t s)). Qed.
Lemma lem4389757 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4389758 {A B : Type'} (s : A -> Prop) : (term32 A B s) = (term33 A B s).
Proof. exact (MK_COMB (@lem4389757 A) (@lem4389756 A B s)). Qed.
Lemma lem4389763 {A B : Type'} : (term34 A B) = (term35 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4389758 A B s)). Qed.
Lemma lem4389764 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4389765 {A B : Type'} : (term36 A B) = (term37 A B).
Proof. exact (MK_COMB (@lem4389764 A) (@lem4389763 A B)). Qed.
Lemma lem4389770 {A B : Type'} : (term37 A B) = (term36 A B).
Proof. exact (SYM (@lem4389765 A B)). Qed.
Lemma lem4389786 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term38 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4389787 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term38 A s t).
Proof. exact (@lem4389786 A s t). Qed.
Lemma lem4389794 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4389795 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term39 A s t).
Proof. exact (MK_COMB (@lem4389794) (@lem4389787 A s t)). Qed.
Lemma lem4389804 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term22 A B t s f) = (term22 A B t s f).
Proof. exact (eq_refl (term22 A B t s f)). Qed.
Lemma lem4389805 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term25 A B t s f) = (term40 A B t s f).
Proof. exact (MK_COMB (@lem4389795 A s t) (@lem4389804 A B t s f)). Qed.
Lemma lem4389808 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : (term27 A B t s) = (term41 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem4389805 A B t s f)). Qed.
Lemma lem4389809 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4389810 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A B t s) = (term42 A B t s).
Proof. exact (MK_COMB (@lem4389809 A B) (@lem4389808 A B t s)). Qed.
Lemma lem4389815 {A B : Type'} (s : A -> Prop) : (term31 A B s) = (term43 A B s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4389810 A B t s)). Qed.
Lemma lem4389816 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4389817 {A B : Type'} (s : A -> Prop) : (term33 A B s) = (term44 A B s).
Proof. exact (MK_COMB (@lem4389816 A) (@lem4389815 A B s)). Qed.
Lemma lem4389822 {A B : Type'} : (term35 A B) = (term45 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4389817 A B s)). Qed.
Lemma lem4389823 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4389824 {A B : Type'} : (term37 A B) = (term46 A B).
Proof. exact (MK_COMB (@lem4389823 A) (@lem4389822 A B)). Qed.
Lemma lem4389829 {A B : Type'} : (term46 A B) = (term37 A B).
Proof. exact (SYM (@lem4389824 A B)). Qed.
Lemma lem4389851 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4389852 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4389851 A P x). Qed.
Lemma lem4389853 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4389852 A s x). Qed.
Lemma lem4389854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4389855 {A : Type'} (s : A -> Prop) (x : A) : (term47 A x s) = (term48 A s x).
Proof. exact (MK_COMB (@lem4389854) (@lem4389853 A s x)). Qed.
Lemma lem4389857 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4389858 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4389857 A P x). Qed.
Lemma lem4389859 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4389858 A t x). Qed.
Lemma lem4389860 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term49 A s x t) = (term50 A s t x).
Proof. exact (MK_COMB (@lem4389855 A s x) (@lem4389859 A t x)). Qed.
Lemma lem4389863 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term52 A s t).
Proof. exact (fun_ext (fun x : A => @lem4389860 A s t x)). Qed.
Lemma lem4389864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4389865 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term53 A s t).
Proof. exact (MK_COMB (@lem4389864 A) (@lem4389863 A s t)). Qed.
Lemma lem4389870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4389871 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem4389870) (@lem4389865 A s t)). Qed.
Lemma lem4389879 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4389880 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4389879 A P x). Qed.
Lemma lem4389881 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4389880 A s x). Qed.
Lemma lem4389882 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4389883 {A B : Type'} (s : A -> Prop) (x : A) : (term14 A B x s) = (term55 A B s x).
Proof. exact (MK_COMB (@lem4389882 B) (@lem4389881 A s x)). Qed.
Lemma lem4389885 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4389886 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4389885 A P x). Qed.
Lemma lem4389887 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4389886 A t x). Qed.
Lemma lem4389888 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4389889 {A B : Type'} (t : A -> Prop) (x : A) : (term14 A B x t) = (term55 A B t x).
Proof. exact (MK_COMB (@lem4389888 B) (@lem4389887 A t x)). Qed.
Lemma lem4389890 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4389891 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (term56 A B t f x) = (term57 A B t f x).
Proof. exact (MK_COMB (@lem4389889 A B t x) (@lem4389890 A B f x)). Qed.
Lemma lem4389892 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4389893 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (term5 A B t f x) = (term58 A B t f x).
Proof. exact (MK_COMB (@lem4389891 A B t f x) (@lem4389892 B)). Qed.
Lemma lem4389894 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term16 A B s t f x) = (term59 A B s t f x).
Proof. exact (MK_COMB (@lem4389883 A B s x) (@lem4389893 A B t f x)). Qed.
Lemma lem4389895 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4389896 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term17 A B s t f x) = (term60 A B s t f x).
Proof. exact (MK_COMB (@lem4389894 A B s t f x) (@lem4389895 B)). Qed.
Lemma lem4389897 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4389898 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term19 A B s t f x) = (term61 A B s t f x).
Proof. exact (MK_COMB (@lem4389897 B) (@lem4389896 A B s t f x)). Qed.
Lemma lem4389900 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4389901 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4389900 A P x). Qed.
Lemma lem4389902 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4389901 A s x). Qed.
Lemma lem4389903 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4389904 {A B : Type'} (s : A -> Prop) (x : A) : (term14 A B x s) = (term55 A B s x).
Proof. exact (MK_COMB (@lem4389903 B) (@lem4389902 A s x)). Qed.
Lemma lem4389905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4389906 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term56 A B s f x) = (term57 A B s f x).
Proof. exact (MK_COMB (@lem4389904 A B s x) (@lem4389905 A B f x)). Qed.
Lemma lem4389907 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4389908 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term5 A B s f x) = (term58 A B s f x).
Proof. exact (MK_COMB (@lem4389906 A B s f x) (@lem4389907 B)). Qed.
Lemma lem4389909 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term17 A B s t f x) = (term5 A B s f x)) = ((term60 A B s t f x) = (term58 A B s f x)).
Proof. exact (MK_COMB (@lem4389898 A B s t f x) (@lem4389908 A B s f x)). Qed.
Lemma lem4389912 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term21 A B t s f) = (term62 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem4389909 A B t s f x)). Qed.
Lemma lem4389913 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4389914 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term22 A B t s f) = (term63 A B t s f).
Proof. exact (MK_COMB (@lem4389913 A) (@lem4389912 A B t s f)). Qed.
Lemma lem4389919 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term40 A B t s f) = (term64 A B t s f).
Proof. exact (MK_COMB (@lem4389871 A s t) (@lem4389914 A B t s f)). Qed.
Lemma lem4389922 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : (term41 A B t s) = (term65 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem4389919 A B t s f)). Qed.
Lemma lem4389923 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4389924 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : (term42 A B t s) = (term66 A B t s).
Proof. exact (MK_COMB (@lem4389923 A B) (@lem4389922 A B t s)). Qed.
Lemma lem4389929 {A B : Type'} (s : A -> Prop) : (term43 A B s) = (term67 A B s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4389924 A B t s)). Qed.
Lemma lem4389930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4389931 {A B : Type'} (s : A -> Prop) : (term44 A B s) = (term68 A B s).
Proof. exact (MK_COMB (@lem4389930 A) (@lem4389929 A B s)). Qed.
Lemma lem4389936 {A B : Type'} : (term45 A B) = (term69 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4389931 A B s)). Qed.
Lemma lem4389937 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4389938 {A B : Type'} : (term46 A B) = (term70 A B).
Proof. exact (MK_COMB (@lem4389937 A) (@lem4389936 A B)). Qed.
Lemma lem4389943 {A B : Type'} : (term70 A B) = (term46 A B).
Proof. exact (SYM (@lem4389938 A B)). Qed.
Lemma lem4389945 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4389946 {A B : Type'} : (term70 A B) = (term72 A B).
Proof. exact (@lem4389945 (term70 A B)). Qed.
Lemma lem4389947 {A B : Type'} : (term72 A B) = (term70 A B).
Proof. exact (SYM (@lem4389946 A B)). Qed.
Lemma lem4389948 {A B : Type'} (h1 : term73 A B) : term73 A B.
Proof. exact (h1). Qed.
Lemma lem4389951 {A B : Type'} (h1 : term72 A B) : term72 A B.
Proof. exact (h1). Qed.
Lemma lem4389952 {A B : Type'} : term74 A B.
Proof. exact (fun h0 : term72 A B => @lem4389951 A B h0). Qed.
Lemma lem4389953 {A B : Type'} (h1 : term74 A B) : term74 A B.
Proof. exact (h1). Qed.
Lemma lem4389954 {A B : Type'} (h1 : term72 A B) : term72 A B.
Proof. exact (h1). Qed.
Lemma lem4389955 {A B : Type'} (h1 : term72 A B) (h2 : term74 A B) : term72 A B.
Proof. exact (@lem4389953 A B h2 (@lem4389954 A B h1)). Qed.
Lemma lem4389956 {A B : Type'} (h1 : term72 A B) : term75 A B.
Proof. exact (fun h0 : term74 A B => @lem4389955 A B h1 h0). Qed.
Lemma lem4389957 {A B : Type'} (h1 : term74 A B) : term74 A B.
Proof. exact (h1). Qed.
Lemma lem4389958 {A B : Type'} (h1 : term72 A B) (h2 : term74 A B) : term72 A B.
Proof. exact (@lem4389956 A B h1 (@lem4389957 A B h2)). Qed.
Lemma lem4389959 {A B : Type'} (h1 : term74 A B) : term74 A B.
Proof. exact (fun h0 : term72 A B => @lem4389958 A B h0 h1). Qed.
Lemma lem4389960 {A B : Type'} : term76 A B.
Proof. exact (fun h0 : term74 A B => @lem4389959 A B h0). Qed.
Lemma lem4389963 {A B : Type'} : term74 A B.
Proof. exact (@lem4389960 A B (@lem4389952 A B)). Qed.
Lemma lem4389964 {A B : Type'} : term74 A B.
Proof. exact (@lem4389963 A B). Qed.
Lemma lem4389966 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4389967 {A B : Type'} : (term72 A B) = (term77 A B).
Proof. exact (@lem4389966 (term73 A B)). Qed.
Lemma lem4389969 (t : Prop) : (term78 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4389970 {A B : Type'} : (term77 A B) = (term70 A B).
Proof. exact (@lem4389969 (term70 A B)). Qed.
Lemma lem4389999 {A B : Type'} : (term72 A B) = (term70 A B).
Proof. exact (TRANS (@lem4389967 A B) (@lem4389970 A B)). Qed.
Lemma lem4390003 {A : Type'} (s : A -> Prop) (x : A) (h1 : (s x) = False) : (s x) = False.
Proof. exact (h1). Qed.
Lemma lem4390004 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4390005 {A B : Type'} (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term55 A B s x) = (@COND B False).
Proof. exact (MK_COMB (@lem4390004 B) (@lem4390003 A s x h1)). Qed.
Lemma lem4390006 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (term58 A B t f x) = (term58 A B t f x).
Proof. exact (eq_refl (term58 A B t f x)). Qed.
Lemma lem4390007 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term59 A B s t f x) = (term79 A B t f x).
Proof. exact (MK_COMB (@lem4390005 A B s x h1) (@lem4390006 A B t f x)). Qed.
Lemma lem4390008 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4390009 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term60 A B s t f x) = (term80 A B t f x).
Proof. exact (MK_COMB (@lem4390007 A B t f s x h1) (@lem4390008 B)). Qed.
Lemma lem4390011 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4390012 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4390011 B t1 t2). Qed.
Lemma lem4390013 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (term80 A B t f x) = (@ARB B).
Proof. exact (@lem4390012 B (term58 A B t f x) (@ARB B)). Qed.
Lemma lem4390014 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term60 A B s t f x) = (@ARB B).
Proof. exact (TRANS (@lem4390009 A B t f s x h1) (@lem4390013 A B t f x)). Qed.
Lemma lem4390015 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4390016 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term61 A B s t f x) = (@eq B (@ARB B)).
Proof. exact (MK_COMB (@lem4390015 B) (@lem4390014 A B t f s x h1)). Qed.
Lemma lem4390018 {A : Type'} (s : A -> Prop) (x : A) (h1 : (s x) = False) : (s x) = False.
Proof. exact (h1). Qed.
Lemma lem4390019 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4390020 {A B : Type'} (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term55 A B s x) = (@COND B False).
Proof. exact (MK_COMB (@lem4390019 B) (@lem4390018 A s x h1)). Qed.
Lemma lem4390021 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4390022 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term57 A B s f x) = (term81 A B f x).
Proof. exact (MK_COMB (@lem4390020 A B s x h1) (@lem4390021 A B f x)). Qed.
Lemma lem4390023 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4390024 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term58 A B s f x) = (term82 A B f x).
Proof. exact (MK_COMB (@lem4390022 A B f s x h1) (@lem4390023 B)). Qed.
Lemma lem4390026 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4390027 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4390026 B t1 t2). Qed.
Lemma lem4390028 {A B : Type'} (f : A -> B) (x : A) : (term82 A B f x) = (@ARB B).
Proof. exact (@lem4390027 B (f x) (@ARB B)). Qed.
Lemma lem4390029 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : (term58 A B s f x) = (@ARB B).
Proof. exact (TRANS (@lem4390024 A B f s x h1) (@lem4390028 A B f x)). Qed.
Lemma lem4390030 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : ((term60 A B s t f x) = (term58 A B s f x)) = ((@ARB B) = (@ARB B)).
Proof. exact (MK_COMB (@lem4390016 A B t f s x h1) (@lem4390029 A B f s x h1)). Qed.
Lemma lem4390032 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4390033 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4390032 B x). Qed.
Lemma lem4390034 {B : Type'} : ((@ARB B) = (@ARB B)) = True.
Proof. exact (@lem4390033 B (@ARB B)). Qed.
Lemma lem4390035 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = False) : ((term60 A B s t f x) = (term58 A B s f x)) = True.
Proof. exact (TRANS (@lem4390030 A B t f s x h1) (@lem4390034 B)). Qed.
Lemma lem4390036 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : term83 A B t s f x.
Proof. exact (fun h0 : (s x) = False => @lem4390035 A B t f s x h0). Qed.
Lemma lem4390038 {A : Type'} (s : A -> Prop) (x : A) (h1 : (s x) = True) : (s x) = True.
Proof. exact (h1). Qed.
Lemma lem4390039 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4390040 {A B : Type'} (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term55 A B s x) = (@COND B True).
Proof. exact (MK_COMB (@lem4390039 B) (@lem4390038 A s x h1)). Qed.
Lemma lem4390041 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (term58 A B t f x) = (term58 A B t f x).
Proof. exact (eq_refl (term58 A B t f x)). Qed.
Lemma lem4390042 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term59 A B s t f x) = (term84 A B t f x).
Proof. exact (MK_COMB (@lem4390040 A B s x h1) (@lem4390041 A B t f x)). Qed.
Lemma lem4390043 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4390044 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term60 A B s t f x) = (term85 A B t f x).
Proof. exact (MK_COMB (@lem4390042 A B t f s x h1) (@lem4390043 B)). Qed.
Lemma lem4390046 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4390047 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4390046 B t2 t1). Qed.
Lemma lem4390048 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (term85 A B t f x) = (term58 A B t f x).
Proof. exact (@lem4390047 B (@ARB B) (term58 A B t f x)). Qed.
Lemma lem4390049 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term60 A B s t f x) = (term58 A B t f x).
Proof. exact (TRANS (@lem4390044 A B t f s x h1) (@lem4390048 A B t f x)). Qed.
Lemma lem4390050 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4390051 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term61 A B s t f x) = (term86 A B t f x).
Proof. exact (MK_COMB (@lem4390050 B) (@lem4390049 A B t f s x h1)). Qed.
Lemma lem4390053 {A : Type'} (s : A -> Prop) (x : A) (h1 : (s x) = True) : (s x) = True.
Proof. exact (h1). Qed.
Lemma lem4390054 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4390055 {A B : Type'} (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term55 A B s x) = (@COND B True).
Proof. exact (MK_COMB (@lem4390054 B) (@lem4390053 A s x h1)). Qed.
Lemma lem4390056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4390057 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term57 A B s f x) = (term87 A B f x).
Proof. exact (MK_COMB (@lem4390055 A B s x h1) (@lem4390056 A B f x)). Qed.
Lemma lem4390058 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4390059 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term58 A B s f x) = (term88 A B f x).
Proof. exact (MK_COMB (@lem4390057 A B f s x h1) (@lem4390058 B)). Qed.
Lemma lem4390061 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4390062 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4390061 B t2 t1). Qed.
Lemma lem4390063 {A B : Type'} (f : A -> B) (x : A) : (term88 A B f x) = (f x).
Proof. exact (@lem4390062 B (@ARB B) (f x)). Qed.
Lemma lem4390064 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = True) : (term58 A B s f x) = (f x).
Proof. exact (TRANS (@lem4390059 A B f s x h1) (@lem4390063 A B f x)). Qed.
Lemma lem4390065 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) (h1 : (s x) = True) : ((term60 A B s t f x) = (term58 A B s f x)) = ((term58 A B t f x) = (f x)).
Proof. exact (MK_COMB (@lem4390051 A B t f s x h1) (@lem4390064 A B f s x h1)). Qed.
Lemma lem4390068 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : term89 A B s t f x.
Proof. exact (fun h0 : (s x) = True => @lem4390065 A B t f s x h0). Qed.
Lemma lem4390069 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : term90 A B s t f x.
Proof. exact (conj (@lem4390036 A B t s f x) (@lem4390068 A B s t f x)). Qed.
Lemma lem4390071 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term91 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4390072 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : term92 A B t f s x.
Proof. exact (@lem4390071 ((term60 A B s t f x) = (term58 A B s f x)) ((term58 A B t f x) = (f x)) (s x) True). Qed.
Lemma lem4390073 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x : A) : ((term60 A B s t f x) = (term58 A B s f x)) = (term93 A B t f s x).
Proof. exact (@lem4390072 A B t f s x (@lem4390069 A B s t f x)). Qed.
Lemma lem4390075 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4390076 {A : Type'} (s : A -> Prop) (x : A) : (term94 A s x) = True.
Proof. exact (@lem4390075 (s x)). Qed.
Lemma lem4390081 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term95 A B s t f x) = (term95 A B s t f x).
Proof. exact (eq_refl (term95 A B s t f x)). Qed.
Lemma lem4390082 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term93 A B t f s x) = (term96 A B s t f x).
Proof. exact (MK_COMB (@lem4390081 A B s t f x) (@lem4390076 A s x)). Qed.
Lemma lem4390084 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4390085 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term96 A B s t f x) = (term97 A B s t f x).
Proof. exact (@lem4390084 (term97 A B s t f x)). Qed.
Lemma lem4390086 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term93 A B t f s x) = (term97 A B s t f x).
Proof. exact (TRANS (@lem4390082 A B s t f x) (@lem4390085 A B s t f x)). Qed.
Lemma lem4390087 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : ((term60 A B s t f x) = (term58 A B s f x)) = (term97 A B s t f x).
Proof. exact (TRANS (@lem4390073 A B t f s x) (@lem4390086 A B s t f x)). Qed.
Lemma lem4390091 {A : Type'} (t : A -> Prop) (x : A) (h1 : (t x) = False) : (t x) = False.
Proof. exact (h1). Qed.
Lemma lem4390092 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4390093 {A B : Type'} (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term55 A B t x) = (@COND B False).
Proof. exact (MK_COMB (@lem4390092 B) (@lem4390091 A t x h1)). Qed.
Lemma lem4390094 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4390095 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term57 A B t f x) = (term81 A B f x).
Proof. exact (MK_COMB (@lem4390093 A B t x h1) (@lem4390094 A B f x)). Qed.
Lemma lem4390096 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4390097 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term58 A B t f x) = (term82 A B f x).
Proof. exact (MK_COMB (@lem4390095 A B f t x h1) (@lem4390096 B)). Qed.
Lemma lem4390099 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4390100 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4390099 B t1 t2). Qed.
Lemma lem4390101 {A B : Type'} (f : A -> B) (x : A) : (term82 A B f x) = (@ARB B).
Proof. exact (@lem4390100 B (f x) (@ARB B)). Qed.
Lemma lem4390102 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term58 A B t f x) = (@ARB B).
Proof. exact (TRANS (@lem4390097 A B f t x h1) (@lem4390101 A B f x)). Qed.
Lemma lem4390103 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4390104 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term86 A B t f x) = (@eq B (@ARB B)).
Proof. exact (MK_COMB (@lem4390103 B) (@lem4390102 A B f t x h1)). Qed.
Lemma lem4390105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4390106 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : ((term58 A B t f x) = (f x)) = ((@ARB B) = (f x)).
Proof. exact (MK_COMB (@lem4390104 A B f t x h1) (@lem4390105 A B f x)). Qed.
Lemma lem4390109 {A : Type'} (s : A -> Prop) (x : A) : (term98 A s x) = (term98 A s x).
Proof. exact (eq_refl (term98 A s x)). Qed.
Lemma lem4390110 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term97 A B s t f x) = (term99 A B s f x).
Proof. exact (MK_COMB (@lem4390109 A s x) (@lem4390106 A B f t x h1)). Qed.
Lemma lem4390113 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : term100 A B t s f x.
Proof. exact (fun h0 : (t x) = False => @lem4390110 A B s f t x h0). Qed.
Lemma lem4390115 {A : Type'} (t : A -> Prop) (x : A) (h1 : (t x) = True) : (t x) = True.
Proof. exact (h1). Qed.
Lemma lem4390116 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4390117 {A B : Type'} (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term55 A B t x) = (@COND B True).
Proof. exact (MK_COMB (@lem4390116 B) (@lem4390115 A t x h1)). Qed.
Lemma lem4390118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4390119 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term57 A B t f x) = (term87 A B f x).
Proof. exact (MK_COMB (@lem4390117 A B t x h1) (@lem4390118 A B f x)). Qed.
Lemma lem4390120 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4390121 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term58 A B t f x) = (term88 A B f x).
Proof. exact (MK_COMB (@lem4390119 A B f t x h1) (@lem4390120 B)). Qed.
Lemma lem4390123 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4390124 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4390123 B t2 t1). Qed.
Lemma lem4390125 {A B : Type'} (f : A -> B) (x : A) : (term88 A B f x) = (f x).
Proof. exact (@lem4390124 B (@ARB B) (f x)). Qed.
Lemma lem4390126 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term58 A B t f x) = (f x).
Proof. exact (TRANS (@lem4390121 A B f t x h1) (@lem4390125 A B f x)). Qed.
Lemma lem4390127 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4390128 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term86 A B t f x) = (term101 A B f x).
Proof. exact (MK_COMB (@lem4390127 B) (@lem4390126 A B f t x h1)). Qed.
Lemma lem4390129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4390130 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : ((term58 A B t f x) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem4390128 A B f t x h1) (@lem4390129 A B f x)). Qed.
Lemma lem4390132 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4390133 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4390132 B x). Qed.
Lemma lem4390134 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem4390133 B (f x)). Qed.
Lemma lem4390135 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : ((term58 A B t f x) = (f x)) = True.
Proof. exact (TRANS (@lem4390130 A B f t x h1) (@lem4390134 A B f x)). Qed.
Lemma lem4390136 {A : Type'} (s : A -> Prop) (x : A) : (term98 A s x) = (term98 A s x).
Proof. exact (eq_refl (term98 A s x)). Qed.
Lemma lem4390137 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term97 A B s t f x) = (term102 A s x).
Proof. exact (MK_COMB (@lem4390136 A s x) (@lem4390135 A B f t x h1)). Qed.
Lemma lem4390139 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4390140 {A : Type'} (s : A -> Prop) (x : A) : (term102 A s x) = True.
Proof. exact (@lem4390139 (term103 A s x)). Qed.
Lemma lem4390141 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term97 A B s t f x) = True.
Proof. exact (TRANS (@lem4390137 A B f s t x h1) (@lem4390140 A s x)). Qed.
Lemma lem4390142 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : term104 A B s t f x.
Proof. exact (fun h0 : (t x) = True => @lem4390141 A B s f t x h0). Qed.
Lemma lem4390143 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : term105 A B s t f x.
Proof. exact (conj (@lem4390113 A B t s f x) (@lem4390142 A B s t f x)). Qed.
Lemma lem4390145 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term91 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4390146 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : term106 A B t s f x.
Proof. exact (@lem4390145 (term97 A B s t f x) True (t x) (term99 A B s f x)). Qed.
Lemma lem4390147 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term97 A B s t f x) = (term107 A B t s f x).
Proof. exact (@lem4390146 A B t s f x (@lem4390143 A B s t f x)). Qed.
Lemma lem4390150 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term108 A B t s f x) = (term108 A B t s f x).
Proof. exact (eq_refl (term108 A B t s f x)). Qed.
Lemma lem4390152 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4390153 {A : Type'} (t : A -> Prop) (x : A) : (term102 A t x) = True.
Proof. exact (@lem4390152 (term103 A t x)). Qed.
Lemma lem4390154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4390155 {A : Type'} (t : A -> Prop) (x : A) : (term109 A t x) = (and True).
Proof. exact (MK_COMB (@lem4390154) (@lem4390153 A t x)). Qed.
Lemma lem4390156 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B t s f x) = (term110 A B t s f x).
Proof. exact (MK_COMB (@lem4390155 A t x) (@lem4390150 A B t s f x)). Qed.
Lemma lem4390158 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4390159 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term110 A B t s f x) = (term108 A B t s f x).
Proof. exact (@lem4390158 (term108 A B t s f x)). Qed.
Lemma lem4390160 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B t s f x) = (term108 A B t s f x).
Proof. exact (TRANS (@lem4390156 A B t s f x) (@lem4390159 A B t s f x)). Qed.
Lemma lem4390175 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term97 A B s t f x) = (term108 A B t s f x).
Proof. exact (TRANS (@lem4390147 A B t s f x) (@lem4390160 A B t s f x)). Qed.
Lemma lem4390176 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term111 A B t s f x) = (term111 A B t s f x).
Proof. exact (eq_refl (term111 A B t s f x)). Qed.
Lemma lem4390177 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (((term60 A B s t f x) = (term58 A B s f x)) = (term97 A B s t f x)) = (((term60 A B s t f x) = (term58 A B s f x)) = (term108 A B t s f x)).
Proof. exact (MK_COMB (@lem4390176 A B t s f x) (@lem4390175 A B t s f x)). Qed.
Lemma lem4390178 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term60 A B s t f x) = (term58 A B s f x)) = (term108 A B t s f x).
Proof. exact (EQ_MP (@lem4390177 A B t s f x) (@lem4390087 A B s t f x)). Qed.
Lemma lem4390179 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term62 A B t s f) = (term112 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem4390178 A B t s f x)). Qed.
Lemma lem4390180 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4390181 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term63 A B t s f) = (term113 A B t s f).
Proof. exact (MK_COMB (@lem4390180 A) (@lem4390179 A B t s f)). Qed.
Lemma lem4390186 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term50 A s t x) = (term50 A s t x).
Proof. exact (eq_refl (term50 A s t x)). Qed.
Lemma lem4390187 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term52 A s t) = (term52 A s t).
Proof. exact (fun_ext (fun x : A => @lem4390186 A s t x)). Qed.
Lemma lem4390188 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4390189 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term53 A s t).
Proof. exact (MK_COMB (@lem4390188 A) (@lem4390187 A s t)). Qed.
Lemma lem4390190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4390191 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term54 A s t).
Proof. exact (MK_COMB (@lem4390190) (@lem4390189 A s t)). Qed.
Lemma lem4390192 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : (term64 A B t s f) = (term114 A B t s f).
Proof. exact (MK_COMB (@lem4390191 A s t) (@lem4390181 A B t s f)). Qed.
Lemma lem4390193 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : (term65 A B t s) = (term115 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem4390192 A B t s f)). Qed.
Lemma lem4390194 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4390195 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : (term66 A B t s) = (term116 A B t s).
Proof. exact (MK_COMB (@lem4390194 A B) (@lem4390193 A B t s)). Qed.
Lemma lem4390196 {A B : Type'} (s : A -> Prop) : (term67 A B s) = (term117 A B s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4390195 A B t s)). Qed.
Lemma lem4390197 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390198 {A B : Type'} (s : A -> Prop) : (term68 A B s) = (term118 A B s).
Proof. exact (MK_COMB (@lem4390197 A) (@lem4390196 A B s)). Qed.
Lemma lem4390199 {A B : Type'} : (term69 A B) = (term119 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4390198 A B s)). Qed.
Lemma lem4390200 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390201 {A B : Type'} : (term70 A B) = (term120 A B).
Proof. exact (MK_COMB (@lem4390200 A) (@lem4390199 A B)). Qed.
Lemma lem4390242 {A B : Type'} : (term72 A B) = (term120 A B).
Proof. exact (TRANS (@lem4389999 A B) (@lem4390201 A B)). Qed.
Lemma lem4390243 {A B : Type'} : (term120 A B) = (term72 A B).
Proof. exact (SYM (@lem4390242 A B)). Qed.
Lemma lem4390244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term53 A s t.
Proof. exact (h1). Qed.
Lemma lem4390246 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4390247 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term108 A B t s f x) = (term121 A B t s f x).
Proof. exact (@lem4390246 (term108 A B t s f x)). Qed.
Lemma lem4390248 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term121 A B t s f x) = (term108 A B t s f x).
Proof. exact (SYM (@lem4390247 A B t s f x)). Qed.
Lemma lem4390249 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term122 A B t s f x) : term122 A B t s f x.
Proof. exact (h1). Qed.
Lemma lem4390256 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term50 A s t x) = (term123 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem4390257 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term52 A s t) = (term124 A s t).
Proof. exact (fun_ext (fun x : A => @lem4390256 A s t x)). Qed.
Lemma lem4390258 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4390295 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term53 A s t) = (term125 A s t).
Proof. exact (MK_COMB (@lem4390258 A) (@lem4390257 A s t)). Qed.
Lemma lem4390296 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term125 A s t.
Proof. exact (EQ_MP (@lem4390295 A s t) (@lem4390244 A s t h1)). Qed.
Lemma lem4390300 {A : Type'} (s : A -> Prop) (x : A) : (term126 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4390301 {A B : Type'} (f : A -> B) (x : A) : (term127 A B f x) = (term127 A B f x).
Proof. exact (eq_refl (term127 A B f x)). Qed.
Lemma lem4390302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4390303 {A : Type'} (s : A -> Prop) (x : A) : (term128 A s x) = (term129 A s x).
Proof. exact (MK_COMB (@lem4390302) (@lem4390300 A s x)). Qed.
Lemma lem4390304 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term130 A B s f x) = (term131 A B s f x).
Proof. exact (MK_COMB (@lem4390303 A s x) (@lem4390301 A B f x)). Qed.
Lemma lem4390305 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term132 A B s f x) = (term130 A B s f x).
Proof. exact (@lem17160 (term103 A s x) ((@ARB B) = (f x))). Qed.
Lemma lem4390306 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term132 A B s f x) = (term131 A B s f x).
Proof. exact (TRANS (@lem4390305 A B s f x) (@lem4390304 A B s f x)). Qed.
Lemma lem4390308 {A : Type'} (t : A -> Prop) (x : A) : (term133 A t x) = (term133 A t x).
Proof. exact (eq_refl (term133 A t x)). Qed.
Lemma lem4390309 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term134 A B t s f x) = (term135 A B t s f x).
Proof. exact (MK_COMB (@lem4390308 A t x) (@lem4390306 A B s f x)). Qed.
Lemma lem4390310 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term122 A B t s f x) = (term134 A B t s f x).
Proof. exact (@lem17160 (t x) (term99 A B s f x)). Qed.
Lemma lem4390315 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term122 A B t s f x) = (term135 A B t s f x).
Proof. exact (TRANS (@lem4390310 A B t s f x) (@lem4390309 A B t s f x)). Qed.
Lemma lem4390327 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term123 A s t x) = (term123 A s t x).
Proof. exact (eq_refl (term123 A s t x)). Qed.
Lemma lem4390328 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term124 A s t).
Proof. exact (fun_ext (fun x : A => @lem4390327 A s t x)). Qed.
Lemma lem4390329 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4390330 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term125 A s t).
Proof. exact (MK_COMB (@lem4390329 A) (@lem4390328 A s t)). Qed.
Lemma lem4390331 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term125 A s t.
Proof. exact (EQ_MP (@lem4390330 A s t) (@lem4390296 A s t h1)). Qed.
Lemma lem4390355 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term122 A B t s f x) : term135 A B t s f x.
Proof. exact (EQ_MP (@lem4390315 A B t s f x) (@lem4390249 A B t s f x h1)). Qed.
Lemma lem4390356 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term122 A B t s f x) : term131 A B s f x.
Proof. exact (proj2 (@lem4390355 A B t s f x h1)). Qed.
Lemma lem4390367 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term123 A s t x) = (term123 A s t x).
Proof. exact (eq_refl (term123 A s t x)). Qed.
Lemma lem4390368 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term124 A s t).
Proof. exact (fun_ext (fun x : A => @lem4390367 A s t x)). Qed.
Lemma lem4390369 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4390371 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term125 A s t).
Proof. exact (MK_COMB (@lem4390369 A) (@lem4390368 A s t)). Qed.
Lemma lem4390372 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term125 A s t.
Proof. exact (EQ_MP (@lem4390371 A s t) (@lem4390331 A s t h1)). Qed.
Lemma lem4390385 {A : Type'} (_50151 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term136 A s t _50151.
Proof. exact (@lem4390372 A s t h1 _50151). Qed.
Lemma lem4390386 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50151 : A) : (term136 A s t _50151) = (term123 A s t _50151).
Proof. exact (eq_refl (term136 A s t _50151)). Qed.
Lemma lem4390393 {A : Type'} (_50151 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term123 A s t _50151.
Proof. exact (EQ_MP (@lem4390386 A s t _50151) (@lem4390385 A _50151 s t h1)). Qed.
Lemma lem4390395 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term122 A B t s f x) : term103 A t x.
Proof. exact (proj1 (@lem4390355 A B t s f x h1)). Qed.
Lemma lem4390437 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term122 A B t s f x) : s x.
Proof. exact (proj1 (@lem4390356 A B t s f x h1)). Qed.
Lemma lem4390438 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term122 A B t s f x) : term137 A s x.
Proof. exact (fun h0 : term103 A s x => @lem4390437 A B t s f x h1). Qed.
Lemma lem4390440 (p : Prop) : (term138 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4390441 {A : Type'} (s : A -> Prop) (x : A) : (term137 A s x) = (s x).
Proof. exact (@lem4390440 (s x)). Qed.
Lemma lem4390442 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term122 A B t s f x) : s x.
Proof. exact (EQ_MP (@lem4390441 A s x) (@lem4390438 A B t s f x h1)). Qed.
Lemma lem4390448 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4390449 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50151 : A) : (term123 A s t _50151) = (term139 A t s _50151).
Proof. exact (@lem4390448 (t _50151) (term103 A s _50151)). Qed.
Lemma lem4390455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4390456 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50151 : A) : (term140 A s t _50151) = (term141 A t s _50151).
Proof. exact (MK_COMB (@lem4390455) (@lem4390449 A t s _50151)). Qed.
Lemma lem4390462 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50151 : A) : (term139 A t s _50151) = (term139 A t s _50151).
Proof. exact (eq_refl (term139 A t s _50151)). Qed.
Lemma lem4390463 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50151 : A) : ((term123 A s t _50151) = (term139 A t s _50151)) = ((term139 A t s _50151) = (term139 A t s _50151)).
Proof. exact (MK_COMB (@lem4390456 A t s _50151) (@lem4390462 A t s _50151)). Qed.
Lemma lem4390465 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4390466 (x : Prop) : (x = x) = True.
Proof. exact (@lem4390465 Prop x). Qed.
Lemma lem4390467 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50151 : A) : ((term139 A t s _50151) = (term139 A t s _50151)) = True.
Proof. exact (@lem4390466 (term139 A t s _50151)). Qed.
Lemma lem4390468 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50151 : A) : ((term123 A s t _50151) = (term139 A t s _50151)) = True.
Proof. exact (TRANS (@lem4390463 A t s _50151) (@lem4390467 A t s _50151)). Qed.
Lemma lem4390469 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50151 : A) : True = ((term123 A s t _50151) = (term139 A t s _50151)).
Proof. exact (SYM (@lem4390468 A t s _50151)). Qed.
Lemma lem4390470 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50151 : A) : (term123 A s t _50151) = (term139 A t s _50151).
Proof. exact (EQ_MP (@lem4390469 A t s _50151) (@lem0)). Qed.
Lemma lem4390471 {A : Type'} (_50151 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term139 A t s _50151.
Proof. exact (EQ_MP (@lem4390470 A t s _50151) (@lem4390393 A _50151 s t h1)). Qed.
Lemma lem4390473 (b : Prop) (a : Prop) : (a \/ b) = (term142 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4390474 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50151 : A) : (term139 A t s _50151) = (term143 A s t _50151).
Proof. exact (@lem4390473 (term103 A s _50151) (t _50151)). Qed.
Lemma lem4390476 (a : Prop) : (term78 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4390477 {A : Type'} (s : A -> Prop) (_50151 : A) : (term126 A s _50151) = (s _50151).
Proof. exact (@lem4390476 (s _50151)). Qed.
Lemma lem4390478 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4390479 {A : Type'} (s : A -> Prop) (_50151 : A) : (term144 A s _50151) = (term48 A s _50151).
Proof. exact (MK_COMB (@lem4390478) (@lem4390477 A s _50151)). Qed.
Lemma lem4390480 {A : Type'} (t : A -> Prop) (_50151 : A) : (t _50151) = (t _50151).
Proof. exact (eq_refl (t _50151)). Qed.
Lemma lem4390481 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50151 : A) : (term143 A s t _50151) = (term50 A s t _50151).
Proof. exact (MK_COMB (@lem4390479 A s _50151) (@lem4390480 A t _50151)). Qed.
Lemma lem4390482 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50151 : A) : (term139 A t s _50151) = (term50 A s t _50151).
Proof. exact (TRANS (@lem4390474 A s t _50151) (@lem4390481 A s t _50151)). Qed.
Lemma lem4390485 {A : Type'} (_50151 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term50 A s t _50151.
Proof. exact (EQ_MP (@lem4390482 A s t _50151) (@lem4390471 A _50151 s t h1)). Qed.
Lemma lem4390486 {A : Type'} (_50151 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term50 A s t _50151.
Proof. exact (@lem4390485 A _50151 s t h1). Qed.
Lemma lem4390487 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term50 A s t x.
Proof. exact (@lem4390486 A x s t h1). Qed.
Lemma lem4390490 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term53 A s t) (h2 : term122 A B t s f x) : t x.
Proof. exact (@lem4390487 A x s t h1 (@lem4390442 A B t s f x h2)). Qed.
Lemma lem4390491 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term53 A s t) (h2 : term122 A B t s f x) : term137 A t x.
Proof. exact (fun h0 : term103 A t x => @lem4390490 A B t s f x h1 h2). Qed.
Lemma lem4390493 (p : Prop) : (term138 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4390494 {A : Type'} (t : A -> Prop) (x : A) : (term137 A t x) = (t x).
Proof. exact (@lem4390493 (t x)). Qed.
Lemma lem4390495 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term53 A s t) (h2 : term122 A B t s f x) : t x.
Proof. exact (EQ_MP (@lem4390494 A t x) (@lem4390491 A B t s f x h1 h2)). Qed.
Lemma lem4390498 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4390500 {A : Type'} (t : A -> Prop) (x : A) : (term103 A t x) = (term145 A t x).
Proof. exact (@lem4390498 (t x)). Qed.
Lemma lem4390503 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term122 A B t s f x) : term145 A t x.
Proof. exact (EQ_MP (@lem4390500 A t x) (@lem4390395 A B t s f x h1)). Qed.
Lemma lem4390506 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term53 A s t) (h2 : term122 A B t s f x) : False.
Proof. exact (@lem4390503 A B t s f x h2 (@lem4390495 A B t s f x h1 h2)). Qed.
Lemma lem4390507 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term53 A s t) (h2 : term122 A B t s f x) : term146.
Proof. exact (fun h0 : ~ False => @lem4390506 A B t s f x h1 h2). Qed.
Lemma lem4390509 (p : Prop) : (term138 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4390510 : term146 = False.
Proof. exact (@lem4390509 False). Qed.
Lemma lem4390511 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term53 A s t) (h2 : term122 A B t s f x) : False.
Proof. exact (EQ_MP (@lem4390510) (@lem4390507 A B t s f x h1 h2)). Qed.
Lemma lem4390512 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term53 A s t) (h2 : term122 A B t s f x) : (term122 A B t s f x) = False.
Proof. exact (prop_ext (fun h3 : term122 A B t s f x => @lem4390511 A B t s f x h1 h2) (fun h3 : False => @lem4390249 A B t s f x h2)). Qed.
Lemma lem4390513 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term53 A s t) (h2 : term122 A B t s f x) : False.
Proof. exact (EQ_MP (@lem4390512 A B t s f x h1 h2) (@lem4390249 A B t s f x h2)). Qed.
Lemma lem4390514 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term121 A B t s f x.
Proof. exact (fun h0 : term122 A B t s f x => @lem4390513 A B t s f x h1 h0). Qed.
Lemma lem4390515 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term108 A B t s f x.
Proof. exact (EQ_MP (@lem4390248 A B t s f x) (@lem4390514 A B f x s t h1)). Qed.
Lemma lem4390520 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A s t) : term113 A B t s f.
Proof. exact (fun x : A => @lem4390515 A B f x s t h1). Qed.
Lemma lem4390521 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) : term114 A B t s f.
Proof. exact (fun h0 : term53 A s t => @lem4390520 A B f s t h0). Qed.
Lemma lem4390526 {A B : Type'} (t : A -> Prop) (s : A -> Prop) : term116 A B t s.
Proof. exact (fun f : A -> B => @lem4390521 A B t s f). Qed.
Lemma lem4390531 {A B : Type'} (s : A -> Prop) : term118 A B s.
Proof. exact (fun t : A -> Prop => @lem4390526 A B t s). Qed.
Lemma lem4390536 {A B : Type'} : term120 A B.
Proof. exact (fun s : A -> Prop => @lem4390531 A B s). Qed.
Lemma lem4390537 {A B : Type'} : term72 A B.
Proof. exact (EQ_MP (@lem4390243 A B) (@lem4390536 A B)). Qed.
Lemma lem4390539 {A B : Type'} : term72 A B.
Proof. exact (@lem4389964 A B (@lem4390537 A B)). Qed.
Lemma lem4390540 {A B : Type'} (h1 : term73 A B) : False.
Proof. exact (@lem4390539 A B (@lem4389948 A B h1)). Qed.
Lemma lem4390541 {A B : Type'} (h1 : term73 A B) : (term73 A B) = False.
Proof. exact (prop_ext (fun h2 : term73 A B => @lem4390540 A B h1) (fun h2 : False => @lem4389948 A B h1)). Qed.
Lemma lem4390542 {A B : Type'} (h1 : term73 A B) : False.
Proof. exact (EQ_MP (@lem4390541 A B h1) (@lem4389948 A B h1)). Qed.
Lemma lem4390543 {A B : Type'} : term72 A B.
Proof. exact (fun h0 : term73 A B => @lem4390542 A B h0). Qed.
Lemma lem4390544 {A B : Type'} : term70 A B.
Proof. exact (EQ_MP (@lem4389947 A B) (@lem4390543 A B)). Qed.
Lemma lem4390545 {A B : Type'} : term46 A B.
Proof. exact (EQ_MP (@lem4389943 A B) (@lem4390544 A B)). Qed.
Lemma lem4390546 {A B : Type'} : term37 A B.
Proof. exact (EQ_MP (@lem4389829 A B) (@lem4390545 A B)). Qed.
Lemma lem4390547 {A B : Type'} : term36 A B.
Proof. exact (EQ_MP (@lem4389770 A B) (@lem4390546 A B)). Qed.
