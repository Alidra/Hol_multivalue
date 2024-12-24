Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_RESTRICTION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
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
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem4390606 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4390607 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4390608 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4390607 A B s) (@lem4390606 A B s)). Qed.
Lemma lem4390609 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4390608 A B s f). Qed.
Lemma lem4390610 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4390611 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4390610 A B s f) (@lem4390609 A B s f)). Qed.
Lemma lem4390612 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4390611 A B s f x). Qed.
Lemma lem4390613 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4390615 {A B : Type'} (y : B) : term6 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4390616 {A B : Type'} (y : B) : (term6 A B y) = (term7 A B y).
Proof. exact (eq_refl (term6 A B y)). Qed.
Lemma lem4390617 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (EQ_MP (@lem4390616 A B y) (@lem4390615 A B y)). Qed.
Lemma lem4390618 {A B : Type'} (y : B) (s : A -> Prop) : term8 A B y s.
Proof. exact (@lem4390617 A B y s). Qed.
Lemma lem4390619 {A B : Type'} (y : B) (s : A -> Prop) : (term8 A B y s) = (term9 A B y s).
Proof. exact (eq_refl (term8 A B y s)). Qed.
Lemma lem4390620 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (EQ_MP (@lem4390619 A B y s) (@lem4390618 A B y s)). Qed.
Lemma lem4390621 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term10 A B y s f.
Proof. exact (@lem4390620 A B y s f). Qed.
Lemma lem4390622 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term10 A B y s f) = ((term11 A B y f s) = (term12 A B y f s)).
Proof. exact (eq_refl (term10 A B y s f)). Qed.
Lemma lem4390624 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4390625 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4390626 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem4390625 A s) (@lem4390624 A s)). Qed.
Lemma lem4390627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem4390626 A s t). Qed.
Lemma lem4390628 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = ((s = t) = (term16 A s t)).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem4390647 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term16 A s t).
Proof. exact (EQ_MP (@lem4390628 A s t) (@lem4390627 A s t)). Qed.
Lemma lem4390648 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term16 B s t).
Proof. exact (@lem4390647 B s t). Qed.
Lemma lem4390649 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : ((term17 A B t f s) = (@IMAGE A B f s)) = (term18 A B t f s).
Proof. exact (@lem4390648 B (term17 A B t f s) (@IMAGE A B f s)). Qed.
Lemma lem4390659 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y f s) = (term12 A B y f s).
Proof. exact (EQ_MP (@lem4390622 A B y f s) (@lem4390621 A B y s f)). Qed.
Lemma lem4390660 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y f s) = (term12 A B y f s).
Proof. exact (@lem4390659 A B y f s). Qed.
Lemma lem4390661 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term19 A B x t f s) = (term20 A B x t f s).
Proof. exact (@lem4390660 A B x (@RESTRICTION A B t f) s). Qed.
Lemma lem4390673 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4390613 A B s f x) (@lem4390612 A B s f x)). Qed.
Lemma lem4390674 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4390673 A B s f x). Qed.
Lemma lem4390675 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B t f x) = (term5 A B t f x).
Proof. exact (@lem4390674 A B t f x). Qed.
Lemma lem4390676 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4390677 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (x' : A) : (x = (@RESTRICTION A B t f x')) = (x = (term5 A B t f x')).
Proof. exact (MK_COMB (@lem4390676 B x) (@lem4390675 A B t f x')). Qed.
Lemma lem4390682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4390683 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (x' : A) : (term21 A B x t f x') = (term22 A B x t f x').
Proof. exact (MK_COMB (@lem4390682) (@lem4390677 A B x t f x')). Qed.
Lemma lem4390684 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4390685 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (x' : A) (s : A -> Prop) : (term23 A B x t f x' s) = (term24 A B x t f x' s).
Proof. exact (MK_COMB (@lem4390683 A B x t f x') (@lem4390684 A x' s)). Qed.
Lemma lem4390688 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term25 A B x t f s) = (term26 A B x t f s).
Proof. exact (fun_ext (fun x' : A => @lem4390685 A B x t f x' s)). Qed.
Lemma lem4390689 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4390690 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term20 A B x t f s) = (term27 A B x t f s).
Proof. exact (MK_COMB (@lem4390689 A) (@lem4390688 A B x t f s)). Qed.
Lemma lem4390695 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term19 A B x t f s) = (term27 A B x t f s).
Proof. exact (TRANS (@lem4390661 A B x t f s) (@lem4390690 A B x t f s)). Qed.
Lemma lem4390696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4390697 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term28 A B x t f s) = (term29 A B x t f s).
Proof. exact (MK_COMB (@lem4390696) (@lem4390695 A B x t f s)). Qed.
Lemma lem4390699 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y f s) = (term12 A B y f s).
Proof. exact (EQ_MP (@lem4390622 A B y f s) (@lem4390621 A B y s f)). Qed.
Lemma lem4390700 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y f s) = (term12 A B y f s).
Proof. exact (@lem4390699 A B y f s). Qed.
Lemma lem4390701 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term11 A B x f s) = (term12 A B x f s).
Proof. exact (@lem4390700 A B x f s). Qed.
Lemma lem4390712 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term19 A B x t f s) = (term11 A B x f s)) = ((term27 A B x t f s) = (term12 A B x f s)).
Proof. exact (MK_COMB (@lem4390697 A B x t f s) (@lem4390701 A B x f s)). Qed.
Lemma lem4390717 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term30 A B t f s) = (term31 A B t f s).
Proof. exact (fun_ext (fun x : B => @lem4390712 A B t x f s)). Qed.
Lemma lem4390718 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4390719 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term18 A B t f s) = (term32 A B t f s).
Proof. exact (MK_COMB (@lem4390718 B) (@lem4390717 A B t f s)). Qed.
Lemma lem4390724 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : ((term17 A B t f s) = (@IMAGE A B f s)) = (term32 A B t f s).
Proof. exact (TRANS (@lem4390649 A B t f s) (@lem4390719 A B t f s)). Qed.
Lemma lem4390725 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term33 A s t).
Proof. exact (eq_refl (term33 A s t)). Qed.
Lemma lem4390726 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term34 A B t f s) = (term35 A B t f s).
Proof. exact (MK_COMB (@lem4390725 A s t) (@lem4390724 A B t f s)). Qed.
Lemma lem4390729 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term36 A B f s) = (term37 A B f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4390726 A B t f s)). Qed.
Lemma lem4390730 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390731 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term38 A B f s) = (term39 A B f s).
Proof. exact (MK_COMB (@lem4390730 A) (@lem4390729 A B f s)). Qed.
Lemma lem4390736 {A B : Type'} (f : A -> B) : (term40 A B f) = (term41 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4390731 A B f s)). Qed.
Lemma lem4390737 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390738 {A B : Type'} (f : A -> B) : (term42 A B f) = (term43 A B f).
Proof. exact (MK_COMB (@lem4390737 A) (@lem4390736 A B f)). Qed.
Lemma lem4390743 {A B : Type'} : (term44 A B) = (term45 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4390738 A B f)). Qed.
Lemma lem4390744 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4390745 {A B : Type'} : (term46 A B) = (term47 A B).
Proof. exact (MK_COMB (@lem4390744 A B) (@lem4390743 A B)). Qed.
Lemma lem4390750 {A B : Type'} : (term47 A B) = (term46 A B).
Proof. exact (SYM (@lem4390745 A B)). Qed.
Lemma lem4390766 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term48 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4390767 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term48 A s t).
Proof. exact (@lem4390766 A s t). Qed.
Lemma lem4390774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4390775 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term49 A s t).
Proof. exact (MK_COMB (@lem4390774) (@lem4390767 A s t)). Qed.
Lemma lem4390804 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term32 A B t f s) = (term32 A B t f s).
Proof. exact (eq_refl (term32 A B t f s)). Qed.
Lemma lem4390805 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term35 A B t f s) = (term50 A B t f s).
Proof. exact (MK_COMB (@lem4390775 A s t) (@lem4390804 A B t f s)). Qed.
Lemma lem4390808 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term37 A B f s) = (term51 A B f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4390805 A B t f s)). Qed.
Lemma lem4390809 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390810 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term39 A B f s) = (term52 A B f s).
Proof. exact (MK_COMB (@lem4390809 A) (@lem4390808 A B f s)). Qed.
Lemma lem4390815 {A B : Type'} (f : A -> B) : (term41 A B f) = (term53 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4390810 A B f s)). Qed.
Lemma lem4390816 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390817 {A B : Type'} (f : A -> B) : (term43 A B f) = (term54 A B f).
Proof. exact (MK_COMB (@lem4390816 A) (@lem4390815 A B f)). Qed.
Lemma lem4390822 {A B : Type'} : (term45 A B) = (term55 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4390817 A B f)). Qed.
Lemma lem4390823 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4390824 {A B : Type'} : (term47 A B) = (term56 A B).
Proof. exact (MK_COMB (@lem4390823 A B) (@lem4390822 A B)). Qed.
Lemma lem4390829 {A B : Type'} : (term56 A B) = (term47 A B).
Proof. exact (SYM (@lem4390824 A B)). Qed.
Lemma lem4390851 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4390852 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4390851 A P x). Qed.
Lemma lem4390853 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4390852 A s x). Qed.
Lemma lem4390854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4390855 {A : Type'} (s : A -> Prop) (x : A) : (term57 A x s) = (term58 A s x).
Proof. exact (MK_COMB (@lem4390854) (@lem4390853 A s x)). Qed.
Lemma lem4390857 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4390858 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4390857 A P x). Qed.
Lemma lem4390859 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4390858 A t x). Qed.
Lemma lem4390860 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term59 A s x t) = (term60 A s t x).
Proof. exact (MK_COMB (@lem4390855 A s x) (@lem4390859 A t x)). Qed.
Lemma lem4390863 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term62 A s t).
Proof. exact (fun_ext (fun x : A => @lem4390860 A s t x)). Qed.
Lemma lem4390864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4390865 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term48 A s t) = (term63 A s t).
Proof. exact (MK_COMB (@lem4390864 A) (@lem4390863 A s t)). Qed.
Lemma lem4390870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4390871 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term64 A s t).
Proof. exact (MK_COMB (@lem4390870) (@lem4390865 A s t)). Qed.
Lemma lem4390887 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4390888 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4390887 A P x). Qed.
Lemma lem4390889 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4390888 A t x). Qed.
Lemma lem4390890 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4390891 {A B : Type'} (t : A -> Prop) (x : A) : (term65 A B x t) = (term66 A B t x).
Proof. exact (MK_COMB (@lem4390890 B) (@lem4390889 A t x)). Qed.
Lemma lem4390892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4390893 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (term67 A B t f x) = (term68 A B t f x).
Proof. exact (MK_COMB (@lem4390891 A B t x) (@lem4390892 A B f x)). Qed.
Lemma lem4390894 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4390895 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) : (term5 A B t f x) = (term69 A B t f x).
Proof. exact (MK_COMB (@lem4390893 A B t f x) (@lem4390894 B)). Qed.
Lemma lem4390896 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4390897 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (x' : A) : (x = (term5 A B t f x')) = (x = (term69 A B t f x')).
Proof. exact (MK_COMB (@lem4390896 B x) (@lem4390895 A B t f x')). Qed.
Lemma lem4390900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4390901 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (x' : A) : (term22 A B x t f x') = (term70 A B x t f x').
Proof. exact (MK_COMB (@lem4390900) (@lem4390897 A B x t f x')). Qed.
Lemma lem4390903 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4390904 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4390903 A P x). Qed.
Lemma lem4390905 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4390904 A s x). Qed.
Lemma lem4390906 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) (x' : A) : (term24 A B x t f x' s) = (term71 A B x t f s x').
Proof. exact (MK_COMB (@lem4390901 A B x t f x') (@lem4390905 A s x')). Qed.
Lemma lem4390909 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term26 A B x t f s) = (term72 A B x t f s).
Proof. exact (fun_ext (fun x' : A => @lem4390906 A B x t f s x')). Qed.
Lemma lem4390910 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4390911 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term27 A B x t f s) = (term73 A B x t f s).
Proof. exact (MK_COMB (@lem4390910 A) (@lem4390909 A B x t f s)). Qed.
Lemma lem4390916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4390917 {A B : Type'} (x : B) (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term29 A B x t f s) = (term74 A B x t f s).
Proof. exact (MK_COMB (@lem4390916) (@lem4390911 A B x t f s)). Qed.
Lemma lem4390927 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4390928 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4390927 A P x). Qed.
Lemma lem4390929 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4390928 A s x). Qed.
Lemma lem4390930 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term75 A B x f x') = (term75 A B x f x').
Proof. exact (eq_refl (term75 A B x f x')). Qed.
Lemma lem4390931 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term76 A B x f x' s) = (term77 A B x f s x').
Proof. exact (MK_COMB (@lem4390930 A B x f x') (@lem4390929 A s x')). Qed.
Lemma lem4390934 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term78 A B x f s) = (term79 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4390931 A B x f s x')). Qed.
Lemma lem4390935 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4390936 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term12 A B x f s) = (term80 A B x f s).
Proof. exact (MK_COMB (@lem4390935 A) (@lem4390934 A B x f s)). Qed.
Lemma lem4390941 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term27 A B x t f s) = (term12 A B x f s)) = ((term73 A B x t f s) = (term80 A B x f s)).
Proof. exact (MK_COMB (@lem4390917 A B x t f s) (@lem4390936 A B x f s)). Qed.
Lemma lem4390944 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term31 A B t f s) = (term81 A B t f s).
Proof. exact (fun_ext (fun x : B => @lem4390941 A B t x f s)). Qed.
Lemma lem4390945 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4390946 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term32 A B t f s) = (term82 A B t f s).
Proof. exact (MK_COMB (@lem4390945 B) (@lem4390944 A B t f s)). Qed.
Lemma lem4390951 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term50 A B t f s) = (term83 A B t f s).
Proof. exact (MK_COMB (@lem4390871 A s t) (@lem4390946 A B t f s)). Qed.
Lemma lem4390954 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term51 A B f s) = (term84 A B f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4390951 A B t f s)). Qed.
Lemma lem4390955 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390956 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term52 A B f s) = (term85 A B f s).
Proof. exact (MK_COMB (@lem4390955 A) (@lem4390954 A B f s)). Qed.
Lemma lem4390961 {A B : Type'} (f : A -> B) : (term53 A B f) = (term86 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4390956 A B f s)). Qed.
Lemma lem4390962 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390963 {A B : Type'} (f : A -> B) : (term54 A B f) = (term87 A B f).
Proof. exact (MK_COMB (@lem4390962 A) (@lem4390961 A B f)). Qed.
Lemma lem4390968 {A B : Type'} : (term55 A B) = (term88 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4390963 A B f)). Qed.
Lemma lem4390969 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4390970 {A B : Type'} : (term56 A B) = (term89 A B).
Proof. exact (MK_COMB (@lem4390969 A B) (@lem4390968 A B)). Qed.
Lemma lem4390975 {A B : Type'} : (term89 A B) = (term56 A B).
Proof. exact (SYM (@lem4390970 A B)). Qed.
Lemma lem4390977 (p : Prop) : p = (term90 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4390978 {A B : Type'} : (term89 A B) = (term91 A B).
Proof. exact (@lem4390977 (term89 A B)). Qed.
Lemma lem4390979 {A B : Type'} : (term91 A B) = (term89 A B).
Proof. exact (SYM (@lem4390978 A B)). Qed.
Lemma lem4390980 {A B : Type'} (h1 : term92 A B) : term92 A B.
Proof. exact (h1). Qed.
Lemma lem4390983 {A B : Type'} (h1 : term91 A B) : term91 A B.
Proof. exact (h1). Qed.
Lemma lem4390984 {A B : Type'} : term93 A B.
Proof. exact (fun h0 : term91 A B => @lem4390983 A B h0). Qed.
Lemma lem4390985 {A B : Type'} (h1 : term93 A B) : term93 A B.
Proof. exact (h1). Qed.
Lemma lem4390986 {A B : Type'} (h1 : term91 A B) : term91 A B.
Proof. exact (h1). Qed.
Lemma lem4390987 {A B : Type'} (h1 : term91 A B) (h2 : term93 A B) : term91 A B.
Proof. exact (@lem4390985 A B h2 (@lem4390986 A B h1)). Qed.
Lemma lem4390988 {A B : Type'} (h1 : term91 A B) : term94 A B.
Proof. exact (fun h0 : term93 A B => @lem4390987 A B h1 h0). Qed.
Lemma lem4390989 {A B : Type'} (h1 : term93 A B) : term93 A B.
Proof. exact (h1). Qed.
Lemma lem4390990 {A B : Type'} (h1 : term91 A B) (h2 : term93 A B) : term91 A B.
Proof. exact (@lem4390988 A B h1 (@lem4390989 A B h2)). Qed.
Lemma lem4390991 {A B : Type'} (h1 : term93 A B) : term93 A B.
Proof. exact (fun h0 : term91 A B => @lem4390990 A B h0 h1). Qed.
Lemma lem4390992 {A B : Type'} : term95 A B.
Proof. exact (fun h0 : term93 A B => @lem4390991 A B h0). Qed.
Lemma lem4390995 {A B : Type'} : term93 A B.
Proof. exact (@lem4390992 A B (@lem4390984 A B)). Qed.
Lemma lem4390996 {A B : Type'} : term93 A B.
Proof. exact (@lem4390995 A B). Qed.
Lemma lem4390998 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4390999 {A B : Type'} : (term91 A B) = (term96 A B).
Proof. exact (@lem4390998 (term92 A B)). Qed.
Lemma lem4391001 (t : Prop) : (term97 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4391002 {A B : Type'} : (term96 A B) = (term89 A B).
Proof. exact (@lem4391001 (term89 A B)). Qed.
Lemma lem4391099 {A B : Type'} : (term91 A B) = (term89 A B).
Proof. exact (TRANS (@lem4390999 A B) (@lem4391002 A B)). Qed.
Lemma lem4391104 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term77 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term77 A B x f s x')). Qed.
Lemma lem4391105 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term79 A B x f s) = (term79 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391104 A B x f s x')). Qed.
Lemma lem4391106 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391107 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term80 A B x f s) = (term80 A B x f s).
Proof. exact (MK_COMB (@lem4391106 A) (@lem4391105 A B x f s)). Qed.
Lemma lem4391111 {A : Type'} (t : A -> Prop) (x : A) (h1 : (t x) = False) : (t x) = False.
Proof. exact (h1). Qed.
Lemma lem4391112 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4391113 {A B : Type'} (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term66 A B t x) = (@COND B False).
Proof. exact (MK_COMB (@lem4391112 B) (@lem4391111 A t x h1)). Qed.
Lemma lem4391114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4391115 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term68 A B t f x) = (term98 A B f x).
Proof. exact (MK_COMB (@lem4391113 A B t x h1) (@lem4391114 A B f x)). Qed.
Lemma lem4391116 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4391117 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term69 A B t f x) = (term99 A B f x).
Proof. exact (MK_COMB (@lem4391115 A B f t x h1) (@lem4391116 B)). Qed.
Lemma lem4391119 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4391120 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4391119 B t1 t2). Qed.
Lemma lem4391121 {A B : Type'} (f : A -> B) (x : A) : (term99 A B f x) = (@ARB B).
Proof. exact (@lem4391120 B (f x) (@ARB B)). Qed.
Lemma lem4391122 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = False) : (term69 A B t f x) = (@ARB B).
Proof. exact (TRANS (@lem4391117 A B f t x h1) (@lem4391121 A B f x)). Qed.
Lemma lem4391123 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4391124 {A B : Type'} (f : A -> B) (x : B) (t : A -> Prop) (x' : A) (h1 : (t x') = False) : (x = (term69 A B t f x')) = (x = (@ARB B)).
Proof. exact (MK_COMB (@lem4391123 B x) (@lem4391122 A B f t x' h1)). Qed.
Lemma lem4391127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391128 {A B : Type'} (f : A -> B) (x : B) (t : A -> Prop) (x' : A) (h1 : (t x') = False) : (term70 A B x t f x') = (term100 B x).
Proof. exact (MK_COMB (@lem4391127) (@lem4391124 A B f x t x' h1)). Qed.
Lemma lem4391129 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4391130 {A B : Type'} (f : A -> B) (x : B) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : (t x') = False) : (term71 A B x t f s x') = (term101 A B x s x').
Proof. exact (MK_COMB (@lem4391128 A B f x t x' h1) (@lem4391129 A s x')). Qed.
Lemma lem4391133 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : B) (s : A -> Prop) (x' : A) : term102 A B t f x s x'.
Proof. exact (fun h0 : (t x') = False => @lem4391130 A B f x s t x' h0). Qed.
Lemma lem4391135 {A : Type'} (t : A -> Prop) (x : A) (h1 : (t x) = True) : (t x) = True.
Proof. exact (h1). Qed.
Lemma lem4391136 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4391137 {A B : Type'} (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term66 A B t x) = (@COND B True).
Proof. exact (MK_COMB (@lem4391136 B) (@lem4391135 A t x h1)). Qed.
Lemma lem4391138 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4391139 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term68 A B t f x) = (term103 A B f x).
Proof. exact (MK_COMB (@lem4391137 A B t x h1) (@lem4391138 A B f x)). Qed.
Lemma lem4391140 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4391141 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term69 A B t f x) = (term104 A B f x).
Proof. exact (MK_COMB (@lem4391139 A B f t x h1) (@lem4391140 B)). Qed.
Lemma lem4391143 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4391144 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4391143 B t2 t1). Qed.
Lemma lem4391145 {A B : Type'} (f : A -> B) (x : A) : (term104 A B f x) = (f x).
Proof. exact (@lem4391144 B (@ARB B) (f x)). Qed.
Lemma lem4391146 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : A) (h1 : (t x) = True) : (term69 A B t f x) = (f x).
Proof. exact (TRANS (@lem4391141 A B f t x h1) (@lem4391145 A B f x)). Qed.
Lemma lem4391147 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem4391148 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) (h1 : (t x') = True) : (x = (term69 A B t f x')) = (x = (f x')).
Proof. exact (MK_COMB (@lem4391147 B x) (@lem4391146 A B f t x' h1)). Qed.
Lemma lem4391151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391152 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) (h1 : (t x') = True) : (term70 A B x t f x') = (term75 A B x f x').
Proof. exact (MK_COMB (@lem4391151) (@lem4391148 A B x f t x' h1)). Qed.
Lemma lem4391153 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4391154 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : (t x') = True) : (term71 A B x t f s x') = (term77 A B x f s x').
Proof. exact (MK_COMB (@lem4391152 A B x f t x' h1) (@lem4391153 A s x')). Qed.
Lemma lem4391157 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : term105 A B t x f s x'.
Proof. exact (fun h0 : (t x') = True => @lem4391154 A B x f s t x' h0). Qed.
Lemma lem4391158 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : term106 A B t x f s x'.
Proof. exact (conj (@lem4391133 A B t f x s x') (@lem4391157 A B t x f s x')). Qed.
Lemma lem4391160 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term107 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem4391161 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : term108 A B f t x s x'.
Proof. exact (@lem4391160 (term71 A B x t f s x') (term77 A B x f s x') (t x') (term101 A B x s x')). Qed.
Lemma lem4391202 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term71 A B x t f s x') = (term109 A B f t x s x').
Proof. exact (@lem4391161 A B f t x s x' (@lem4391158 A B t x f s x')). Qed.
Lemma lem4391203 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term72 A B x t f s) = (term110 A B f t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391202 A B f t x s x')). Qed.
Lemma lem4391204 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391205 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term73 A B x t f s) = (term111 A B f t x s).
Proof. exact (MK_COMB (@lem4391204 A) (@lem4391203 A B f t x s)). Qed.
Lemma lem4391206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4391207 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term74 A B x t f s) = (term112 A B f t x s).
Proof. exact (MK_COMB (@lem4391206) (@lem4391205 A B f t x s)). Qed.
Lemma lem4391208 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term73 A B x t f s) = (term80 A B x f s)) = ((term111 A B f t x s) = (term80 A B x f s)).
Proof. exact (MK_COMB (@lem4391207 A B f t x s) (@lem4391107 A B x f s)). Qed.
Lemma lem4391209 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term81 A B t f s) = (term113 A B t f s).
Proof. exact (fun_ext (fun x : B => @lem4391208 A B t x f s)). Qed.
Lemma lem4391210 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4391211 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term82 A B t f s) = (term114 A B t f s).
Proof. exact (MK_COMB (@lem4391210 B) (@lem4391209 A B t f s)). Qed.
Lemma lem4391216 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term60 A s t x) = (term60 A s t x).
Proof. exact (eq_refl (term60 A s t x)). Qed.
Lemma lem4391217 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term62 A s t) = (term62 A s t).
Proof. exact (fun_ext (fun x : A => @lem4391216 A s t x)). Qed.
Lemma lem4391218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391219 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term63 A s t) = (term63 A s t).
Proof. exact (MK_COMB (@lem4391218 A) (@lem4391217 A s t)). Qed.
Lemma lem4391220 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4391221 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (MK_COMB (@lem4391220) (@lem4391219 A s t)). Qed.
Lemma lem4391222 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term83 A B t f s) = (term115 A B t f s).
Proof. exact (MK_COMB (@lem4391221 A s t) (@lem4391211 A B t f s)). Qed.
Lemma lem4391223 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term84 A B f s) = (term116 A B f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4391222 A B t f s)). Qed.
Lemma lem4391224 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4391225 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term85 A B f s) = (term117 A B f s).
Proof. exact (MK_COMB (@lem4391224 A) (@lem4391223 A B f s)). Qed.
Lemma lem4391226 {A B : Type'} (f : A -> B) : (term86 A B f) = (term118 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4391225 A B f s)). Qed.
Lemma lem4391227 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4391228 {A B : Type'} (f : A -> B) : (term87 A B f) = (term119 A B f).
Proof. exact (MK_COMB (@lem4391227 A) (@lem4391226 A B f)). Qed.
Lemma lem4391229 {A B : Type'} : (term88 A B) = (term120 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4391228 A B f)). Qed.
Lemma lem4391230 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4391231 {A B : Type'} : (term89 A B) = (term121 A B).
Proof. exact (MK_COMB (@lem4391230 A B) (@lem4391229 A B)). Qed.
Lemma lem4391292 {A B : Type'} : (term91 A B) = (term121 A B).
Proof. exact (TRANS (@lem4391099 A B) (@lem4391231 A B)). Qed.
Lemma lem4391293 {A B : Type'} : (term121 A B) = (term91 A B).
Proof. exact (SYM (@lem4391292 A B)). Qed.
Lemma lem4391294 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term63 A s t.
Proof. exact (h1). Qed.
Lemma lem4391296 (p : Prop) : p = (term90 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4391297 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term111 A B f t x s) = (term80 A B x f s)) = (term122 A B t x f s).
Proof. exact (@lem4391296 ((term111 A B f t x s) = (term80 A B x f s))). Qed.
Lemma lem4391298 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term122 A B t x f s) = ((term111 A B f t x s) = (term80 A B x f s)).
Proof. exact (SYM (@lem4391297 A B t x f s)). Qed.
Lemma lem4391299 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term123 A B t x f s) : term123 A B t x f s.
Proof. exact (h1). Qed.
Lemma lem4391306 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term60 A s t x) = (term124 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem4391307 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term62 A s t) = (term125 A s t).
Proof. exact (fun_ext (fun x : A => @lem4391306 A s t x)). Qed.
Lemma lem4391308 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391345 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term63 A s t) = (term126 A s t).
Proof. exact (MK_COMB (@lem4391308 A) (@lem4391307 A s t)). Qed.
Lemma lem4391346 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term126 A s t.
Proof. exact (EQ_MP (@lem4391345 A s t) (@lem4391294 A s t h1)). Qed.
Lemma lem4391357 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term127 A B x f s x') = (term128 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem4391362 {A : Type'} (t : A -> Prop) (x : A) : (term129 A t x) = (term129 A t x).
Proof. exact (eq_refl (term129 A t x)). Qed.
Lemma lem4391363 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term130 A B t x f s x') = (term131 A B t x f s x').
Proof. exact (MK_COMB (@lem4391362 A t x') (@lem4391357 A B x f s x')). Qed.
Lemma lem4391364 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term132 A B t x f s x') = (term130 A B t x f s x').
Proof. exact (@lem17045 (t x') (term77 A B x f s x')). Qed.
Lemma lem4391365 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term132 A B t x f s x') = (term131 A B t x f s x').
Proof. exact (TRANS (@lem4391364 A B t x f s x') (@lem4391363 A B t x f s x')). Qed.
Lemma lem4391372 {A : Type'} (t : A -> Prop) (x : A) : (term133 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4391381 {A B : Type'} (x : B) (s : A -> Prop) (x' : A) : (term134 A B x s x') = (term135 A B x s x').
Proof. exact (@lem17045 (x = (@ARB B)) (s x')). Qed.
Lemma lem4391385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391386 {A : Type'} (t : A -> Prop) (x : A) : (term136 A t x) = (term137 A t x).
Proof. exact (MK_COMB (@lem4391385) (@lem4391372 A t x)). Qed.
Lemma lem4391387 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term138 A B t x s x') = (term139 A B t x s x').
Proof. exact (MK_COMB (@lem4391386 A t x') (@lem4391381 A B x s x')). Qed.
Lemma lem4391388 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term140 A B t x s x') = (term138 A B t x s x').
Proof. exact (@lem17045 (term141 A t x') (term101 A B x s x')). Qed.
Lemma lem4391389 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term140 A B t x s x') = (term139 A B t x s x').
Proof. exact (TRANS (@lem4391388 A B t x s x') (@lem4391387 A B t x s x')). Qed.
Lemma lem4391393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391394 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term142 A B t x f s x') = (term143 A B t x f s x').
Proof. exact (MK_COMB (@lem4391393) (@lem4391365 A B t x f s x')). Qed.
Lemma lem4391395 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term144 A B f t x s x') = (term145 A B f t x s x').
Proof. exact (MK_COMB (@lem4391394 A B t x f s x') (@lem4391389 A B t x s x')). Qed.
Lemma lem4391396 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term146 A B f t x s x') = (term144 A B f t x s x').
Proof. exact (@lem17160 (term147 A B t x f s x') (term148 A B t x s x')). Qed.
Lemma lem4391397 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term146 A B f t x s x') = (term145 A B f t x s x').
Proof. exact (TRANS (@lem4391396 A B f t x s x') (@lem4391395 A B f t x s x')). Qed.
Lemma lem4391400 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term109 A B f t x s x') = (term109 A B f t x s x').
Proof. exact (eq_refl (term109 A B f t x s x')). Qed.
Lemma lem4391401 {A : Type'} (P : A -> Prop) : (term149 A P) = (term150 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4391402 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term151 A B f t x s) = (term152 A B f t x s).
Proof. exact (@lem4391401 A (term110 A B f t x s)). Qed.
Lemma lem4391403 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term153 A B f t x s x') = (term109 A B f t x s x').
Proof. exact (eq_refl (term153 A B f t x s x')). Qed.
Lemma lem4391404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4391405 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term154 A B f t x s x') = (term146 A B f t x s x').
Proof. exact (MK_COMB (@lem4391404) (@lem4391403 A B f t x s x')). Qed.
Lemma lem4391406 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term154 A B f t x s x') = (term145 A B f t x s x').
Proof. exact (TRANS (@lem4391405 A B f t x s x') (@lem4391397 A B f t x s x')). Qed.
Lemma lem4391407 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term155 A B f t x s) = (term156 A B f t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391406 A B f t x s x')). Qed.
Lemma lem4391408 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391409 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term152 A B f t x s) = (term157 A B f t x s).
Proof. exact (MK_COMB (@lem4391408 A) (@lem4391407 A B f t x s)). Qed.
Lemma lem4391410 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term151 A B f t x s) = (term157 A B f t x s).
Proof. exact (TRANS (@lem4391402 A B f t x s) (@lem4391409 A B f t x s)). Qed.
Lemma lem4391411 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term110 A B f t x s) = (term110 A B f t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391400 A B f t x s x')). Qed.
Lemma lem4391412 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391413 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term111 A B f t x s) = (term111 A B f t x s).
Proof. exact (MK_COMB (@lem4391412 A) (@lem4391411 A B f t x s)). Qed.
Lemma lem4391422 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term127 A B x f s x') = (term128 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem4391425 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term77 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term77 A B x f s x')). Qed.
Lemma lem4391426 {A : Type'} (P : A -> Prop) : (term149 A P) = (term150 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4391427 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term158 A B x f s) = (term159 A B x f s).
Proof. exact (@lem4391426 A (term79 A B x f s)). Qed.
Lemma lem4391428 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term160 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term160 A B x f s x')). Qed.
Lemma lem4391429 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4391430 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term161 A B x f s x') = (term127 A B x f s x').
Proof. exact (MK_COMB (@lem4391429) (@lem4391428 A B x f s x')). Qed.
Lemma lem4391431 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term161 A B x f s x') = (term128 A B x f s x').
Proof. exact (TRANS (@lem4391430 A B x f s x') (@lem4391422 A B x f s x')). Qed.
Lemma lem4391432 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term162 A B x f s) = (term163 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391431 A B x f s x')). Qed.
Lemma lem4391433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391434 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term159 A B x f s) = (term164 A B x f s).
Proof. exact (MK_COMB (@lem4391433 A) (@lem4391432 A B x f s)). Qed.
Lemma lem4391435 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term158 A B x f s) = (term164 A B x f s).
Proof. exact (TRANS (@lem4391427 A B x f s) (@lem4391434 A B x f s)). Qed.
Lemma lem4391436 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term79 A B x f s) = (term79 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391425 A B x f s x')). Qed.
Lemma lem4391437 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391438 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term80 A B x f s) = (term80 A B x f s).
Proof. exact (MK_COMB (@lem4391437 A) (@lem4391436 A B x f s)). Qed.
Lemma lem4391439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391440 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term165 A B f t x s) = (term166 A B f t x s).
Proof. exact (MK_COMB (@lem4391439) (@lem4391410 A B f t x s)). Qed.
Lemma lem4391441 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term167 A B t x f s) = (term168 A B t x f s).
Proof. exact (MK_COMB (@lem4391440 A B f t x s) (@lem4391438 A B x f s)). Qed.
Lemma lem4391442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391443 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term169 A B f t x s) = (term169 A B f t x s).
Proof. exact (MK_COMB (@lem4391442) (@lem4391413 A B f t x s)). Qed.
Lemma lem4391444 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term170 A B t x f s) = (term171 A B t x f s).
Proof. exact (MK_COMB (@lem4391443 A B f t x s) (@lem4391435 A B x f s)). Qed.
Lemma lem4391445 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391446 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term172 A B t x f s) = (term173 A B t x f s).
Proof. exact (MK_COMB (@lem4391445) (@lem4391444 A B t x f s)). Qed.
Lemma lem4391447 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term174 A B t x f s) = (term175 A B t x f s).
Proof. exact (MK_COMB (@lem4391446 A B t x f s) (@lem4391441 A B t x f s)). Qed.
Lemma lem4391448 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term123 A B t x f s) = (term174 A B t x f s).
Proof. exact (@lem17646 (term111 A B f t x s) (term80 A B x f s)). Qed.
Lemma lem4391449 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term123 A B t x f s) = (term175 A B t x f s).
Proof. exact (TRANS (@lem4391448 A B t x f s) (@lem4391447 A B t x f s)). Qed.
Lemma lem4391451 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4391452 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (@lem4391451 A P Q). Qed.
Lemma lem4391453 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term178 A B f t x s) = (term179 A B f t x s).
Proof. exact (@lem4391452 A (term180 A B t x f s) (term181 A B t x s)). Qed.
Lemma lem4391454 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term182 A B t x f s x') = (term147 A B t x f s x').
Proof. exact (eq_refl (term182 A B t x f s x')). Qed.
Lemma lem4391455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391456 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term183 A B t x f s x') = (term184 A B t x f s x').
Proof. exact (MK_COMB (@lem4391455) (@lem4391454 A B t x f s x')). Qed.
Lemma lem4391457 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term185 A B t x s x') = (term148 A B t x s x').
Proof. exact (eq_refl (term185 A B t x s x')). Qed.
Lemma lem4391458 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term186 A B f t x s x') = (term109 A B f t x s x').
Proof. exact (MK_COMB (@lem4391456 A B t x f s x') (@lem4391457 A B t x s x')). Qed.
Lemma lem4391459 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term187 A B f t x s) = (term110 A B f t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391458 A B f t x s x')). Qed.
Lemma lem4391460 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391461 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term178 A B f t x s) = (term111 A B f t x s).
Proof. exact (MK_COMB (@lem4391460 A) (@lem4391459 A B f t x s)). Qed.
Lemma lem4391462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4391463 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term188 A B f t x s) = (term112 A B f t x s).
Proof. exact (MK_COMB (@lem4391462) (@lem4391461 A B f t x s)). Qed.
Lemma lem4391464 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term182 A B t x f s x') = (term147 A B t x f s x').
Proof. exact (eq_refl (term182 A B t x f s x')). Qed.
Lemma lem4391465 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term189 A B t x f s) = (term180 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391464 A B t x f s x')). Qed.
Lemma lem4391466 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391467 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term190 A B t x f s) = (term191 A B t x f s).
Proof. exact (MK_COMB (@lem4391466 A) (@lem4391465 A B t x f s)). Qed.
Lemma lem4391468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391469 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term192 A B t x f s) = (term193 A B t x f s).
Proof. exact (MK_COMB (@lem4391468) (@lem4391467 A B t x f s)). Qed.
Lemma lem4391470 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term185 A B t x s x') = (term148 A B t x s x').
Proof. exact (eq_refl (term185 A B t x s x')). Qed.
Lemma lem4391471 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) : (term194 A B t x s) = (term181 A B t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391470 A B t x s x')). Qed.
Lemma lem4391472 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391473 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) : (term195 A B t x s) = (term196 A B t x s).
Proof. exact (MK_COMB (@lem4391472 A) (@lem4391471 A B t x s)). Qed.
Lemma lem4391474 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term179 A B f t x s) = (term197 A B f t x s).
Proof. exact (MK_COMB (@lem4391469 A B t x f s) (@lem4391473 A B t x s)). Qed.
Lemma lem4391475 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : ((term178 A B f t x s) = (term179 A B f t x s)) = ((term111 A B f t x s) = (term197 A B f t x s)).
Proof. exact (MK_COMB (@lem4391463 A B f t x s) (@lem4391474 A B f t x s)). Qed.
Lemma lem4391476 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term111 A B f t x s) = (term197 A B f t x s).
Proof. exact (EQ_MP (@lem4391475 A B f t x s) (@lem4391453 A B f t x s)). Qed.
Lemma lem4391553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391554 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term169 A B f t x s) = (term198 A B f t x s).
Proof. exact (MK_COMB (@lem4391553) (@lem4391476 A B f t x s)). Qed.
Lemma lem4391603 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term164 A B x f s) = (term164 A B x f s).
Proof. exact (eq_refl (term164 A B x f s)). Qed.
Lemma lem4391604 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term171 A B t x f s) = (term199 A B t x f s).
Proof. exact (MK_COMB (@lem4391554 A B f t x s) (@lem4391603 A B x f s)). Qed.
Lemma lem4391605 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391606 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term173 A B t x f s) = (term200 A B t x f s).
Proof. exact (MK_COMB (@lem4391605) (@lem4391604 A B t x f s)). Qed.
Lemma lem4391608 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term201 A P Q) = (term202 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4391609 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term201 A P Q) = (term202 A P Q).
Proof. exact (@lem4391608 A P Q). Qed.
Lemma lem4391610 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term203 A B f t x s) = (term204 A B f t x s).
Proof. exact (@lem4391609 A (term205 A B t x f s) (term206 A B t x s)). Qed.
Lemma lem4391611 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term207 A B t x f s x') = (term131 A B t x f s x').
Proof. exact (eq_refl (term207 A B t x f s x')). Qed.
Lemma lem4391612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391613 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term208 A B t x f s x') = (term143 A B t x f s x').
Proof. exact (MK_COMB (@lem4391612) (@lem4391611 A B t x f s x')). Qed.
Lemma lem4391614 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term209 A B t x s x') = (term139 A B t x s x').
Proof. exact (eq_refl (term209 A B t x s x')). Qed.
Lemma lem4391615 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term210 A B f t x s x') = (term145 A B f t x s x').
Proof. exact (MK_COMB (@lem4391613 A B t x f s x') (@lem4391614 A B t x s x')). Qed.
Lemma lem4391616 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term211 A B f t x s) = (term156 A B f t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391615 A B f t x s x')). Qed.
Lemma lem4391617 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391618 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term203 A B f t x s) = (term157 A B f t x s).
Proof. exact (MK_COMB (@lem4391617 A) (@lem4391616 A B f t x s)). Qed.
Lemma lem4391619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4391620 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term212 A B f t x s) = (term213 A B f t x s).
Proof. exact (MK_COMB (@lem4391619) (@lem4391618 A B f t x s)). Qed.
Lemma lem4391621 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term207 A B t x f s x') = (term131 A B t x f s x').
Proof. exact (eq_refl (term207 A B t x f s x')). Qed.
Lemma lem4391622 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term214 A B t x f s) = (term205 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391621 A B t x f s x')). Qed.
Lemma lem4391623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391624 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term215 A B t x f s) = (term216 A B t x f s).
Proof. exact (MK_COMB (@lem4391623 A) (@lem4391622 A B t x f s)). Qed.
Lemma lem4391625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391626 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term217 A B t x f s) = (term218 A B t x f s).
Proof. exact (MK_COMB (@lem4391625) (@lem4391624 A B t x f s)). Qed.
Lemma lem4391627 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term209 A B t x s x') = (term139 A B t x s x').
Proof. exact (eq_refl (term209 A B t x s x')). Qed.
Lemma lem4391628 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) : (term219 A B t x s) = (term206 A B t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391627 A B t x s x')). Qed.
Lemma lem4391629 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391630 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) : (term220 A B t x s) = (term221 A B t x s).
Proof. exact (MK_COMB (@lem4391629 A) (@lem4391628 A B t x s)). Qed.
Lemma lem4391631 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term204 A B f t x s) = (term222 A B f t x s).
Proof. exact (MK_COMB (@lem4391626 A B t x f s) (@lem4391630 A B t x s)). Qed.
Lemma lem4391632 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : ((term203 A B f t x s) = (term204 A B f t x s)) = ((term157 A B f t x s) = (term222 A B f t x s)).
Proof. exact (MK_COMB (@lem4391620 A B f t x s) (@lem4391631 A B f t x s)). Qed.
Lemma lem4391633 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term157 A B f t x s) = (term222 A B f t x s).
Proof. exact (EQ_MP (@lem4391632 A B f t x s) (@lem4391610 A B f t x s)). Qed.
Lemma lem4391710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391711 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term166 A B f t x s) = (term223 A B f t x s).
Proof. exact (MK_COMB (@lem4391710) (@lem4391633 A B f t x s)). Qed.
Lemma lem4391744 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term80 A B x f s) = (term80 A B x f s).
Proof. exact (eq_refl (term80 A B x f s)). Qed.
Lemma lem4391745 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term168 A B t x f s) = (term224 A B t x f s).
Proof. exact (MK_COMB (@lem4391711 A B f t x s) (@lem4391744 A B x f s)). Qed.
Lemma lem4391746 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term175 A B t x f s) = (term225 A B t x f s).
Proof. exact (MK_COMB (@lem4391606 A B t x f s) (@lem4391745 A B t x f s)). Qed.
Lemma lem4391748 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term177 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4391749 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term177 A P Q) = (term176 A P Q).
Proof. exact (@lem4391748 A P Q). Qed.
Lemma lem4391750 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term179 A B f t x s) = (term178 A B f t x s).
Proof. exact (@lem4391749 A (term180 A B t x f s) (term181 A B t x s)). Qed.
Lemma lem4391751 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term182 A B t x f s x') = (term147 A B t x f s x').
Proof. exact (eq_refl (term182 A B t x f s x')). Qed.
Lemma lem4391752 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term189 A B t x f s) = (term180 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391751 A B t x f s x')). Qed.
Lemma lem4391753 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391754 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term190 A B t x f s) = (term191 A B t x f s).
Proof. exact (MK_COMB (@lem4391753 A) (@lem4391752 A B t x f s)). Qed.
Lemma lem4391755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391756 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term192 A B t x f s) = (term193 A B t x f s).
Proof. exact (MK_COMB (@lem4391755) (@lem4391754 A B t x f s)). Qed.
Lemma lem4391757 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term185 A B t x s x') = (term148 A B t x s x').
Proof. exact (eq_refl (term185 A B t x s x')). Qed.
Lemma lem4391758 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) : (term194 A B t x s) = (term181 A B t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391757 A B t x s x')). Qed.
Lemma lem4391759 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391760 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) : (term195 A B t x s) = (term196 A B t x s).
Proof. exact (MK_COMB (@lem4391759 A) (@lem4391758 A B t x s)). Qed.
Lemma lem4391761 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term179 A B f t x s) = (term197 A B f t x s).
Proof. exact (MK_COMB (@lem4391756 A B t x f s) (@lem4391760 A B t x s)). Qed.
Lemma lem4391762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4391763 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term226 A B f t x s) = (term227 A B f t x s).
Proof. exact (MK_COMB (@lem4391762) (@lem4391761 A B f t x s)). Qed.
Lemma lem4391764 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term182 A B t x f s x') = (term147 A B t x f s x').
Proof. exact (eq_refl (term182 A B t x f s x')). Qed.
Lemma lem4391765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391766 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term183 A B t x f s x') = (term184 A B t x f s x').
Proof. exact (MK_COMB (@lem4391765) (@lem4391764 A B t x f s x')). Qed.
Lemma lem4391767 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term185 A B t x s x') = (term148 A B t x s x').
Proof. exact (eq_refl (term185 A B t x s x')). Qed.
Lemma lem4391768 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term186 A B f t x s x') = (term109 A B f t x s x').
Proof. exact (MK_COMB (@lem4391766 A B t x f s x') (@lem4391767 A B t x s x')). Qed.
Lemma lem4391769 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term187 A B f t x s) = (term110 A B f t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391768 A B f t x s x')). Qed.
Lemma lem4391770 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391771 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term178 A B f t x s) = (term111 A B f t x s).
Proof. exact (MK_COMB (@lem4391770 A) (@lem4391769 A B f t x s)). Qed.
Lemma lem4391772 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : ((term179 A B f t x s) = (term178 A B f t x s)) = ((term197 A B f t x s) = (term111 A B f t x s)).
Proof. exact (MK_COMB (@lem4391763 A B f t x s) (@lem4391771 A B f t x s)). Qed.
Lemma lem4391773 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term197 A B f t x s) = (term111 A B f t x s).
Proof. exact (EQ_MP (@lem4391772 A B f t x s) (@lem4391750 A B f t x s)). Qed.
Lemma lem4391774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391775 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term198 A B f t x s) = (term169 A B f t x s).
Proof. exact (MK_COMB (@lem4391774) (@lem4391773 A B f t x s)). Qed.
Lemma lem4391776 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term164 A B x f s) = (term164 A B x f s).
Proof. exact (eq_refl (term164 A B x f s)). Qed.
Lemma lem4391777 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term199 A B t x f s) = (term171 A B t x f s).
Proof. exact (MK_COMB (@lem4391775 A B f t x s) (@lem4391776 A B x f s)). Qed.
Lemma lem4391779 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4391780 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (@lem4391779 A P Q). Qed.
Lemma lem4391781 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term230 A B t x f s) = (term231 A B t x f s).
Proof. exact (@lem4391780 A (term110 A B f t x s) (term164 A B x f s)). Qed.
Lemma lem4391782 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term153 A B f t x s x') = (term109 A B f t x s x').
Proof. exact (eq_refl (term153 A B f t x s x')). Qed.
Lemma lem4391783 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term232 A B f t x s) = (term110 A B f t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391782 A B f t x s x')). Qed.
Lemma lem4391784 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391785 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term233 A B f t x s) = (term111 A B f t x s).
Proof. exact (MK_COMB (@lem4391784 A) (@lem4391783 A B f t x s)). Qed.
Lemma lem4391786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391787 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term234 A B f t x s) = (term169 A B f t x s).
Proof. exact (MK_COMB (@lem4391786) (@lem4391785 A B f t x s)). Qed.
Lemma lem4391788 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term164 A B x f s) = (term164 A B x f s).
Proof. exact (eq_refl (term164 A B x f s)). Qed.
Lemma lem4391789 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term230 A B t x f s) = (term171 A B t x f s).
Proof. exact (MK_COMB (@lem4391787 A B f t x s) (@lem4391788 A B x f s)). Qed.
Lemma lem4391790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4391791 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term235 A B t x f s) = (term236 A B t x f s).
Proof. exact (MK_COMB (@lem4391790) (@lem4391789 A B t x f s)). Qed.
Lemma lem4391792 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term153 A B f t x s x') = (term109 A B f t x s x').
Proof. exact (eq_refl (term153 A B f t x s x')). Qed.
Lemma lem4391793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391794 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term237 A B f t x s x') = (term238 A B f t x s x').
Proof. exact (MK_COMB (@lem4391793) (@lem4391792 A B f t x s x')). Qed.
Lemma lem4391795 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term164 A B x f s) = (term164 A B x f s).
Proof. exact (eq_refl (term164 A B x f s)). Qed.
Lemma lem4391796 {A B : Type'} (t : A -> Prop) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term239 A B t x x' f s) = (term240 A B t x x' f s).
Proof. exact (MK_COMB (@lem4391794 A B f t x' s x) (@lem4391795 A B x' f s)). Qed.
Lemma lem4391797 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term241 A B t x f s) = (term242 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391796 A B t x' x f s)). Qed.
Lemma lem4391798 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391799 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term231 A B t x f s) = (term243 A B t x f s).
Proof. exact (MK_COMB (@lem4391798 A) (@lem4391797 A B t x f s)). Qed.
Lemma lem4391800 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term230 A B t x f s) = (term231 A B t x f s)) = ((term171 A B t x f s) = (term243 A B t x f s)).
Proof. exact (MK_COMB (@lem4391791 A B t x f s) (@lem4391799 A B t x f s)). Qed.
Lemma lem4391801 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term171 A B t x f s) = (term243 A B t x f s).
Proof. exact (EQ_MP (@lem4391800 A B t x f s) (@lem4391781 A B t x f s)). Qed.
Lemma lem4391802 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term199 A B t x f s) = (term243 A B t x f s).
Proof. exact (TRANS (@lem4391777 A B t x f s) (@lem4391801 A B t x f s)). Qed.
Lemma lem4391803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391804 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term200 A B t x f s) = (term244 A B t x f s).
Proof. exact (MK_COMB (@lem4391803) (@lem4391802 A B t x f s)). Qed.
Lemma lem4391806 {A : Type'} (P : Prop) (Q : A -> Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4391807 {A : Type'} (P : Prop) (Q : A -> Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (@lem4391806 A P Q). Qed.
Lemma lem4391808 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B t x f s) = (term248 A B t x f s).
Proof. exact (@lem4391807 A (term222 A B f t x s) (term79 A B x f s)). Qed.
Lemma lem4391809 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term160 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term160 A B x f s x')). Qed.
Lemma lem4391810 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term249 A B x f s) = (term79 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391809 A B x f s x')). Qed.
Lemma lem4391811 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391812 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term250 A B x f s) = (term80 A B x f s).
Proof. exact (MK_COMB (@lem4391811 A) (@lem4391810 A B x f s)). Qed.
Lemma lem4391813 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term223 A B f t x s) = (term223 A B f t x s).
Proof. exact (eq_refl (term223 A B f t x s)). Qed.
Lemma lem4391814 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B t x f s) = (term224 A B t x f s).
Proof. exact (MK_COMB (@lem4391813 A B f t x s) (@lem4391812 A B x f s)). Qed.
Lemma lem4391815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4391816 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term251 A B t x f s) = (term252 A B t x f s).
Proof. exact (MK_COMB (@lem4391815) (@lem4391814 A B t x f s)). Qed.
Lemma lem4391817 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term160 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term160 A B x f s x')). Qed.
Lemma lem4391818 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term223 A B f t x s) = (term223 A B f t x s).
Proof. exact (eq_refl (term223 A B f t x s)). Qed.
Lemma lem4391819 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term253 A B t x f s x') = (term254 A B t x f s x').
Proof. exact (MK_COMB (@lem4391818 A B f t x s) (@lem4391817 A B x f s x')). Qed.
Lemma lem4391820 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term255 A B t x f s) = (term256 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391819 A B t x f s x')). Qed.
Lemma lem4391821 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391822 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term248 A B t x f s) = (term257 A B t x f s).
Proof. exact (MK_COMB (@lem4391821 A) (@lem4391820 A B t x f s)). Qed.
Lemma lem4391823 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term247 A B t x f s) = (term248 A B t x f s)) = ((term224 A B t x f s) = (term257 A B t x f s)).
Proof. exact (MK_COMB (@lem4391816 A B t x f s) (@lem4391822 A B t x f s)). Qed.
Lemma lem4391824 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term224 A B t x f s) = (term257 A B t x f s).
Proof. exact (EQ_MP (@lem4391823 A B t x f s) (@lem4391808 A B t x f s)). Qed.
Lemma lem4391825 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term225 A B t x f s) = (term258 A B t x f s).
Proof. exact (MK_COMB (@lem4391804 A B t x f s) (@lem4391824 A B t x f s)). Qed.
Lemma lem4391827 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term177 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4391828 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term177 A P Q) = (term176 A P Q).
Proof. exact (@lem4391827 A P Q). Qed.
Lemma lem4391829 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term259 A B t x f s) = (term260 A B t x f s).
Proof. exact (@lem4391828 A (term242 A B t x f s) (term256 A B t x f s)). Qed.
Lemma lem4391830 {A B : Type'} (t : A -> Prop) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term261 A B t x' f s x) = (term240 A B t x x' f s).
Proof. exact (eq_refl (term261 A B t x' f s x)). Qed.
Lemma lem4391831 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term262 A B t x f s) = (term242 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391830 A B t x' x f s)). Qed.
Lemma lem4391832 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391833 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term263 A B t x f s) = (term243 A B t x f s).
Proof. exact (MK_COMB (@lem4391832 A) (@lem4391831 A B t x f s)). Qed.
Lemma lem4391834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391835 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term264 A B t x f s) = (term244 A B t x f s).
Proof. exact (MK_COMB (@lem4391834) (@lem4391833 A B t x f s)). Qed.
Lemma lem4391836 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term265 A B t x f s x') = (term254 A B t x f s x').
Proof. exact (eq_refl (term265 A B t x f s x')). Qed.
Lemma lem4391837 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term266 A B t x f s) = (term256 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391836 A B t x f s x')). Qed.
Lemma lem4391838 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391839 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term267 A B t x f s) = (term257 A B t x f s).
Proof. exact (MK_COMB (@lem4391838 A) (@lem4391837 A B t x f s)). Qed.
Lemma lem4391840 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term259 A B t x f s) = (term258 A B t x f s).
Proof. exact (MK_COMB (@lem4391835 A B t x f s) (@lem4391839 A B t x f s)). Qed.
Lemma lem4391841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4391842 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term268 A B t x f s) = (term269 A B t x f s).
Proof. exact (MK_COMB (@lem4391841) (@lem4391840 A B t x f s)). Qed.
Lemma lem4391843 {A B : Type'} (t : A -> Prop) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term261 A B t x' f s x) = (term240 A B t x x' f s).
Proof. exact (eq_refl (term261 A B t x' f s x)). Qed.
Lemma lem4391844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4391845 {A B : Type'} (t : A -> Prop) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term270 A B t x' f s x) = (term271 A B t x x' f s).
Proof. exact (MK_COMB (@lem4391844) (@lem4391843 A B t x x' f s)). Qed.
Lemma lem4391846 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term265 A B t x f s x') = (term254 A B t x f s x').
Proof. exact (eq_refl (term265 A B t x f s x')). Qed.
Lemma lem4391847 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term272 A B t x f s x') = (term273 A B t x f s x').
Proof. exact (MK_COMB (@lem4391845 A B t x' x f s) (@lem4391846 A B t x f s x')). Qed.
Lemma lem4391848 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term274 A B t x f s) = (term275 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391847 A B t x f s x')). Qed.
Lemma lem4391849 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4391850 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term260 A B t x f s) = (term276 A B t x f s).
Proof. exact (MK_COMB (@lem4391849 A) (@lem4391848 A B t x f s)). Qed.
Lemma lem4391851 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : ((term259 A B t x f s) = (term260 A B t x f s)) = ((term258 A B t x f s) = (term276 A B t x f s)).
Proof. exact (MK_COMB (@lem4391842 A B t x f s) (@lem4391850 A B t x f s)). Qed.
Lemma lem4391852 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term258 A B t x f s) = (term276 A B t x f s).
Proof. exact (EQ_MP (@lem4391851 A B t x f s) (@lem4391829 A B t x f s)). Qed.
Lemma lem4391853 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term225 A B t x f s) = (term276 A B t x f s).
Proof. exact (TRANS (@lem4391825 A B t x f s) (@lem4391852 A B t x f s)). Qed.
Lemma lem4391854 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term175 A B t x f s) = (term276 A B t x f s).
Proof. exact (TRANS (@lem4391746 A B t x f s) (@lem4391853 A B t x f s)). Qed.
Lemma lem4391855 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term123 A B t x f s) = (term276 A B t x f s).
Proof. exact (TRANS (@lem4391449 A B t x f s) (@lem4391854 A B t x f s)). Qed.
Lemma lem4391856 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term123 A B t x f s) : term276 A B t x f s.
Proof. exact (EQ_MP (@lem4391855 A B t x f s) (@lem4391299 A B t x f s h1)). Qed.
Lemma lem4391857 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term273 A B t x f s x') : term273 A B t x f s x'.
Proof. exact (h1). Qed.
Lemma lem4391868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term124 A s t x) = (term124 A s t x).
Proof. exact (eq_refl (term124 A s t x)). Qed.
Lemma lem4391869 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term125 A s t).
Proof. exact (fun_ext (fun x : A => @lem4391868 A s t x)). Qed.
Lemma lem4391870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391871 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term126 A s t).
Proof. exact (MK_COMB (@lem4391870 A) (@lem4391869 A s t)). Qed.
Lemma lem4391872 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term126 A s t.
Proof. exact (EQ_MP (@lem4391871 A s t) (@lem4391346 A s t h1)). Qed.
Lemma lem4391885 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term77 A B x f s x') = (term77 A B x f s x').
Proof. exact (eq_refl (term77 A B x f s x')). Qed.
Lemma lem4391906 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term139 A B t x s x') = (term139 A B t x s x').
Proof. exact (eq_refl (term139 A B t x s x')). Qed.
Lemma lem4391907 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) : (term206 A B t x s) = (term206 A B t x s).
Proof. exact (fun_ext (fun x' : A => @lem4391906 A B t x s x')). Qed.
Lemma lem4391908 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391909 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) : (term221 A B t x s) = (term221 A B t x s).
Proof. exact (MK_COMB (@lem4391908 A) (@lem4391907 A B t x s)). Qed.
Lemma lem4391934 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term131 A B t x f s x') = (term131 A B t x f s x').
Proof. exact (eq_refl (term131 A B t x f s x')). Qed.
Lemma lem4391935 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term205 A B t x f s) = (term205 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391934 A B t x f s x')). Qed.
Lemma lem4391936 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391937 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term216 A B t x f s) = (term216 A B t x f s).
Proof. exact (MK_COMB (@lem4391936 A) (@lem4391935 A B t x f s)). Qed.
Lemma lem4391938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391939 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term218 A B t x f s) = (term218 A B t x f s).
Proof. exact (MK_COMB (@lem4391938) (@lem4391937 A B t x f s)). Qed.
Lemma lem4391940 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term222 A B f t x s) = (term222 A B f t x s).
Proof. exact (MK_COMB (@lem4391939 A B t x f s) (@lem4391909 A B t x s)). Qed.
Lemma lem4391941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4391942 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) : (term223 A B f t x s) = (term223 A B f t x s).
Proof. exact (MK_COMB (@lem4391941) (@lem4391940 A B f t x s)). Qed.
Lemma lem4391943 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term254 A B t x f s x') = (term254 A B t x f s x').
Proof. exact (MK_COMB (@lem4391942 A B f t x s) (@lem4391885 A B x f s x')). Qed.
Lemma lem4391960 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term128 A B x f s x') = (term128 A B x f s x').
Proof. exact (eq_refl (term128 A B x f s x')). Qed.
Lemma lem4391961 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term163 A B x f s) = (term163 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4391960 A B x f s x')). Qed.
Lemma lem4391962 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4391963 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term164 A B x f s) = (term164 A B x f s).
Proof. exact (MK_COMB (@lem4391962 A) (@lem4391961 A B x f s)). Qed.
Lemma lem4392006 {A B : Type'} (f : A -> B) (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) : (term238 A B f t x s x') = (term238 A B f t x s x').
Proof. exact (eq_refl (term238 A B f t x s x')). Qed.
Lemma lem4392007 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) : (term240 A B t x' x f s) = (term240 A B t x' x f s).
Proof. exact (MK_COMB (@lem4392006 A B f t x s x') (@lem4391963 A B x f s)). Qed.
Lemma lem4392008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4392009 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) : (term271 A B t x' x f s) = (term271 A B t x' x f s).
Proof. exact (MK_COMB (@lem4392008) (@lem4392007 A B t x' x f s)). Qed.
Lemma lem4392010 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term273 A B t x f s x') = (term273 A B t x f s x').
Proof. exact (MK_COMB (@lem4392009 A B t x' x f s) (@lem4391943 A B t x f s x')). Qed.
Lemma lem4392011 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term273 A B t x f s x') : term273 A B t x f s x'.
Proof. exact (EQ_MP (@lem4392010 A B t x f s x') (@lem4391857 A B t x f s x' h1)). Qed.
Lemma lem4392012 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term240 A B t x' x f s) : term240 A B t x' x f s.
Proof. exact (h1). Qed.
Lemma lem4392013 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term254 A B t x f s x'.
Proof. exact (h1). Qed.
Lemma lem4392014 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term240 A B t x' x f s) : term164 A B x f s.
Proof. exact (proj2 (@lem4392012 A B t x' x f s h1)). Qed.
Lemma lem4392015 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term240 A B t x' x f s) : term109 A B f t x s x'.
Proof. exact (proj1 (@lem4392012 A B t x' x f s h1)). Qed.
Lemma lem4392016 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : term147 A B t x f s x'.
Proof. exact (h1). Qed.
Lemma lem4392017 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term148 A B t x s x') : term148 A B t x s x'.
Proof. exact (h1). Qed.
Lemma lem4392018 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : term77 A B x f s x'.
Proof. exact (proj2 (@lem4392016 A B t x f s x' h1)). Qed.
Lemma lem4392022 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term148 A B t x s x') : term101 A B x s x'.
Proof. exact (proj2 (@lem4392017 A B t x s x' h1)). Qed.
Lemma lem4392026 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term77 A B x f s x'.
Proof. exact (proj2 (@lem4392013 A B t x f s x' h1)). Qed.
Lemma lem4392027 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term222 A B f t x s.
Proof. exact (proj1 (@lem4392013 A B t x f s x' h1)). Qed.
Lemma lem4392031 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term216 A B t x f s.
Proof. exact (proj1 (@lem4392027 A B t x f s x' h1)). Qed.
Lemma lem4392052 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term128 A B x f s x') = (term128 A B x f s x').
Proof. exact (eq_refl (term128 A B x f s x')). Qed.
Lemma lem4392053 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term163 A B x f s) = (term163 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem4392052 A B x f s x')). Qed.
Lemma lem4392054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4392056 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term164 A B x f s) = (term164 A B x f s).
Proof. exact (MK_COMB (@lem4392054 A) (@lem4392053 A B x f s)). Qed.
Lemma lem4392057 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term240 A B t x' x f s) : term164 A B x f s.
Proof. exact (EQ_MP (@lem4392056 A B x f s) (@lem4392014 A B t x' x f s h1)). Qed.
Lemma lem4392077 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term124 A s t x) = (term124 A s t x).
Proof. exact (eq_refl (term124 A s t x)). Qed.
Lemma lem4392078 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term125 A s t).
Proof. exact (fun_ext (fun x : A => @lem4392077 A s t x)). Qed.
Lemma lem4392079 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4392081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term126 A s t).
Proof. exact (MK_COMB (@lem4392079 A) (@lem4392078 A s t)). Qed.
Lemma lem4392082 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term126 A s t.
Proof. exact (EQ_MP (@lem4392081 A s t) (@lem4391872 A s t h1)). Qed.
Lemma lem4392115 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term124 A s t x) = (term124 A s t x).
Proof. exact (eq_refl (term124 A s t x)). Qed.
Lemma lem4392116 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term125 A s t).
Proof. exact (fun_ext (fun x : A => @lem4392115 A s t x)). Qed.
Lemma lem4392117 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4392119 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term126 A s t).
Proof. exact (MK_COMB (@lem4392117 A) (@lem4392116 A s t)). Qed.
Lemma lem4392120 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term126 A s t.
Proof. exact (EQ_MP (@lem4392119 A s t) (@lem4391872 A s t h1)). Qed.
Lemma lem4392142 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term131 A B t x f s x') = (term131 A B t x f s x').
Proof. exact (eq_refl (term131 A B t x f s x')). Qed.
Lemma lem4392143 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term205 A B t x f s) = (term205 A B t x f s).
Proof. exact (fun_ext (fun x' : A => @lem4392142 A B t x f s x')). Qed.
Lemma lem4392144 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4392146 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term216 A B t x f s) = (term216 A B t x f s).
Proof. exact (MK_COMB (@lem4392144 A) (@lem4392143 A B t x f s)). Qed.
Lemma lem4392147 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term216 A B t x f s.
Proof. exact (EQ_MP (@lem4392146 A B t x f s) (@lem4392031 A B t x f s x' h1)). Qed.
Lemma lem4392170 {A B : Type'} (_50159 : A) (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term240 A B t x' x f s) : term277 A B x f s _50159.
Proof. exact (@lem4392057 A B t x' x f s h1 _50159). Qed.
Lemma lem4392171 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_50159 : A) : (term277 A B x f s _50159) = (term128 A B x f s _50159).
Proof. exact (eq_refl (term277 A B x f s _50159)). Qed.
Lemma lem4392173 {A : Type'} (_50160 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term278 A s t _50160.
Proof. exact (@lem4392082 A s t h1 _50160). Qed.
Lemma lem4392174 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50160 : A) : (term278 A s t _50160) = (term124 A s t _50160).
Proof. exact (eq_refl (term278 A s t _50160)). Qed.
Lemma lem4392179 {A : Type'} (_50162 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term278 A s t _50162.
Proof. exact (@lem4392120 A s t h1 _50162). Qed.
Lemma lem4392180 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50162 : A) : (term278 A s t _50162) = (term124 A s t _50162).
Proof. exact (eq_refl (term278 A s t _50162)). Qed.
Lemma lem4392182 {A B : Type'} (_50163 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term207 A B t x f s _50163.
Proof. exact (@lem4392147 A B t x f s x' h1 _50163). Qed.
Lemma lem4392183 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term207 A B t x f s _50163) = (term131 A B t x f s _50163).
Proof. exact (eq_refl (term207 A B t x f s _50163)). Qed.
Lemma lem4392199 {A B : Type'} (_50159 : A) (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term240 A B t x' x f s) : term128 A B x f s _50159.
Proof. exact (EQ_MP (@lem4392171 A B x f s _50159) (@lem4392170 A B _50159 t x' x f s h1)). Qed.
Lemma lem4392203 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : x = (f x').
Proof. exact (proj1 (@lem4392018 A B t x f s x' h1)). Qed.
Lemma lem4392231 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : x = (f x').
Proof. exact (proj1 (@lem4392026 A B t x f s x' h1)). Qed.
Lemma lem4392243 {A B : Type'} (_50163 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term131 A B t x f s _50163.
Proof. exact (EQ_MP (@lem4392183 A B t x f s _50163) (@lem4392182 A B _50163 t x f s x' h1)). Qed.
Lemma lem4392282 {A B : Type'} (f : A -> B) (s : A -> Prop) (_50159 : A) : (term279 A B f s _50159) = (term279 A B f s _50159).
Proof. exact (eq_refl (term279 A B f s _50159)). Qed.
Lemma lem4392283 {A B : Type'} (_50159 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : (term280 A B f s _50159 x) = (term281 A B s _50159 f x').
Proof. exact (MK_COMB (@lem4392282 A B f s _50159) (@lem4392203 A B t x f s x' h1)). Qed.
Lemma lem4392284 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_50159 : A) : (term281 A B s _50159 f x') = (term282 A B x' f s _50159).
Proof. exact (eq_refl (term281 A B s _50159 f x')). Qed.
Lemma lem4392285 {A B : Type'} (f : A -> B) (s : A -> Prop) (_50159 : A) (x : B) : (term283 A B f s _50159 x) = (term283 A B f s _50159 x).
Proof. exact (eq_refl (term283 A B f s _50159 x)). Qed.
Lemma lem4392286 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_50159 : A) : ((term280 A B f s _50159 x) = (term281 A B s _50159 f x')) = ((term280 A B f s _50159 x) = (term282 A B x' f s _50159)).
Proof. exact (MK_COMB (@lem4392285 A B f s _50159 x) (@lem4392284 A B x' f s _50159)). Qed.
Lemma lem4392287 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_50159 : A) : (term280 A B f s _50159 x) = (term128 A B x f s _50159).
Proof. exact (eq_refl (term280 A B f s _50159 x)). Qed.
Lemma lem4392288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4392289 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_50159 : A) : (term283 A B f s _50159 x) = (term284 A B x f s _50159).
Proof. exact (MK_COMB (@lem4392288) (@lem4392287 A B x f s _50159)). Qed.
Lemma lem4392290 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_50159 : A) : (term282 A B x' f s _50159) = (term282 A B x' f s _50159).
Proof. exact (eq_refl (term282 A B x' f s _50159)). Qed.
Lemma lem4392291 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_50159 : A) : ((term280 A B f s _50159 x) = (term282 A B x' f s _50159)) = ((term128 A B x f s _50159) = (term282 A B x' f s _50159)).
Proof. exact (MK_COMB (@lem4392289 A B x f s _50159) (@lem4392290 A B x' f s _50159)). Qed.
Lemma lem4392292 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_50159 : A) : ((term280 A B f s _50159 x) = (term281 A B s _50159 f x')) = ((term128 A B x f s _50159) = (term282 A B x' f s _50159)).
Proof. exact (TRANS (@lem4392286 A B x x' f s _50159) (@lem4392291 A B x x' f s _50159)). Qed.
Lemma lem4392293 {A B : Type'} (_50159 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : (term128 A B x f s _50159) = (term282 A B x' f s _50159).
Proof. exact (EQ_MP (@lem4392292 A B x x' f s _50159) (@lem4392283 A B _50159 t x f s x' h1)). Qed.
Lemma lem4392294 {A B : Type'} (_50159 : A) (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term147 A B t x f s x') (h2 : term240 A B t x' x f s) : term282 A B x' f s _50159.
Proof. exact (EQ_MP (@lem4392293 A B _50159 t x f s x' h1) (@lem4392199 A B _50159 t x' x f s h2)). Qed.
Lemma lem4392350 {A : Type'} (_50160 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term124 A s t _50160.
Proof. exact (EQ_MP (@lem4392174 A s t _50160) (@lem4392173 A _50160 s t h1)). Qed.
Lemma lem4392377 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term148 A B t x s x') : term141 A t x'.
Proof. exact (proj1 (@lem4392017 A B t x s x' h1)). Qed.
Lemma lem4392419 {A : Type'} (_50162 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term124 A s t _50162.
Proof. exact (EQ_MP (@lem4392180 A s t _50162) (@lem4392179 A _50162 s t h1)). Qed.
Lemma lem4392434 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term285 A B t f s _50163) = (term285 A B t f s _50163).
Proof. exact (eq_refl (term285 A B t f s _50163)). Qed.
Lemma lem4392435 {A B : Type'} (_50163 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : (term286 A B t f s _50163 x) = (term287 A B t s _50163 f x').
Proof. exact (MK_COMB (@lem4392434 A B t f s _50163) (@lem4392231 A B t x f s x' h1)). Qed.
Lemma lem4392436 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term287 A B t s _50163 f x') = (term288 A B t x' f s _50163).
Proof. exact (eq_refl (term287 A B t s _50163 f x')). Qed.
Lemma lem4392437 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (_50163 : A) (x : B) : (term289 A B t f s _50163 x) = (term289 A B t f s _50163 x).
Proof. exact (eq_refl (term289 A B t f s _50163 x)). Qed.
Lemma lem4392438 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : ((term286 A B t f s _50163 x) = (term287 A B t s _50163 f x')) = ((term286 A B t f s _50163 x) = (term288 A B t x' f s _50163)).
Proof. exact (MK_COMB (@lem4392437 A B t f s _50163 x) (@lem4392436 A B t x' f s _50163)). Qed.
Lemma lem4392439 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term286 A B t f s _50163 x) = (term131 A B t x f s _50163).
Proof. exact (eq_refl (term286 A B t f s _50163 x)). Qed.
Lemma lem4392440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4392441 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term289 A B t f s _50163 x) = (term290 A B t x f s _50163).
Proof. exact (MK_COMB (@lem4392440) (@lem4392439 A B t x f s _50163)). Qed.
Lemma lem4392442 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term288 A B t x' f s _50163) = (term288 A B t x' f s _50163).
Proof. exact (eq_refl (term288 A B t x' f s _50163)). Qed.
Lemma lem4392443 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : ((term286 A B t f s _50163 x) = (term288 A B t x' f s _50163)) = ((term131 A B t x f s _50163) = (term288 A B t x' f s _50163)).
Proof. exact (MK_COMB (@lem4392441 A B t x f s _50163) (@lem4392442 A B t x' f s _50163)). Qed.
Lemma lem4392444 {A B : Type'} (x : B) (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : ((term286 A B t f s _50163 x) = (term287 A B t s _50163 f x')) = ((term131 A B t x f s _50163) = (term288 A B t x' f s _50163)).
Proof. exact (TRANS (@lem4392438 A B x t x' f s _50163) (@lem4392443 A B x t x' f s _50163)). Qed.
Lemma lem4392445 {A B : Type'} (_50163 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : (term131 A B t x f s _50163) = (term288 A B t x' f s _50163).
Proof. exact (EQ_MP (@lem4392444 A B x t x' f s _50163) (@lem4392435 A B _50163 t x f s x' h1)). Qed.
Lemma lem4392446 {A B : Type'} (_50163 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term288 A B t x' f s _50163.
Proof. exact (EQ_MP (@lem4392445 A B _50163 t x f s x' h1) (@lem4392243 A B _50163 t x f s x' h1)). Qed.
Lemma lem4392497 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4392498 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4392497 B x). Qed.
Lemma lem4392499 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem4392498 B (f x')). Qed.
Lemma lem4392500 {A B : Type'} (f : A -> B) (x' : A) : term291 A B f x'.
Proof. exact (fun h0 : term292 A B f x' => @lem4392499 A B f x'). Qed.
Lemma lem4392502 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392503 {A B : Type'} (f : A -> B) (x' : A) : (term291 A B f x') = ((f x') = (f x')).
Proof. exact (@lem4392502 ((f x') = (f x'))). Qed.
Lemma lem4392504 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem4392503 A B f x') (@lem4392500 A B f x')). Qed.
Lemma lem4392506 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : s x'.
Proof. exact (proj2 (@lem4392018 A B t x f s x' h1)). Qed.
Lemma lem4392507 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : term294 A s x'.
Proof. exact (fun h0 : term141 A s x' => @lem4392506 A B t x f s x' h1). Qed.
Lemma lem4392509 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392510 {A : Type'} (s : A -> Prop) (x' : A) : (term294 A s x') = (s x').
Proof. exact (@lem4392509 (s x')). Qed.
Lemma lem4392511 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : s x'.
Proof. exact (EQ_MP (@lem4392510 A s x') (@lem4392507 A B t x f s x' h1)). Qed.
Lemma lem4392513 (a : Prop) (b : Prop) : (term295 a b) = (term296 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4392514 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_50159 : A) : (term282 A B x' f s _50159) = (term297 A B x' f s _50159).
Proof. exact (@lem4392513 ((f x') = (f _50159)) (s _50159)). Qed.
Lemma lem4392516 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4392517 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_50159 : A) : (term297 A B x' f s _50159) = (term298 A B x' f s _50159).
Proof. exact (@lem4392516 (term299 A B x' f s _50159)). Qed.
Lemma lem4392518 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_50159 : A) : (term282 A B x' f s _50159) = (term298 A B x' f s _50159).
Proof. exact (TRANS (@lem4392514 A B x' f s _50159) (@lem4392517 A B x' f s _50159)). Qed.
Lemma lem4392520 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term147 A B t x f s x') : term300 A B f s x'.
Proof. exact (conj (@lem4392504 A B f x') (@lem4392511 A B t x f s x' h1)). Qed.
Lemma lem4392522 {A B : Type'} (_50159 : A) (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term147 A B t x f s x') (h2 : term240 A B t x' x f s) : term298 A B x' f s _50159.
Proof. exact (EQ_MP (@lem4392518 A B x' f s _50159) (@lem4392294 A B _50159 t x' x f s h1 h2)). Qed.
Lemma lem4392523 {A B : Type'} (_50159 : A) (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term147 A B t x f s x') (h2 : term240 A B t x' x f s) : term298 A B x' f s _50159.
Proof. exact (@lem4392522 A B _50159 t x' x f s h1 h2). Qed.
Lemma lem4392524 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term147 A B t x f s x') (h2 : term240 A B t x' x f s) : term301 A B f s x'.
Proof. exact (@lem4392523 A B x' t x' x f s h1 h2). Qed.
Lemma lem4392527 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term147 A B t x f s x') (h2 : term240 A B t x' x f s) : False.
Proof. exact (@lem4392524 A B t x' x f s h1 h2 (@lem4392520 A B t x f s x' h1)). Qed.
Lemma lem4392528 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term147 A B t x f s x') (h2 : term240 A B t x' x f s) : term302.
Proof. exact (fun h0 : ~ False => @lem4392527 A B t x' x f s h1 h2). Qed.
Lemma lem4392530 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392531 : term302 = False.
Proof. exact (@lem4392530 False). Qed.
Lemma lem4392570 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term148 A B t x s x') : s x'.
Proof. exact (proj2 (@lem4392022 A B t x s x' h1)). Qed.
Lemma lem4392571 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term148 A B t x s x') : term294 A s x'.
Proof. exact (fun h0 : term141 A s x' => @lem4392570 A B t x s x' h1). Qed.
Lemma lem4392573 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392574 {A : Type'} (s : A -> Prop) (x' : A) : (term294 A s x') = (s x').
Proof. exact (@lem4392573 (s x')). Qed.
Lemma lem4392575 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term148 A B t x s x') : s x'.
Proof. exact (EQ_MP (@lem4392574 A s x') (@lem4392571 A B t x s x' h1)). Qed.
Lemma lem4392581 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4392582 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50160 : A) : (term124 A s t _50160) = (term303 A t s _50160).
Proof. exact (@lem4392581 (t _50160) (term141 A s _50160)). Qed.
Lemma lem4392588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4392589 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50160 : A) : (term304 A s t _50160) = (term305 A t s _50160).
Proof. exact (MK_COMB (@lem4392588) (@lem4392582 A t s _50160)). Qed.
Lemma lem4392595 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50160 : A) : (term303 A t s _50160) = (term303 A t s _50160).
Proof. exact (eq_refl (term303 A t s _50160)). Qed.
Lemma lem4392596 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50160 : A) : ((term124 A s t _50160) = (term303 A t s _50160)) = ((term303 A t s _50160) = (term303 A t s _50160)).
Proof. exact (MK_COMB (@lem4392589 A t s _50160) (@lem4392595 A t s _50160)). Qed.
Lemma lem4392598 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4392599 (x : Prop) : (x = x) = True.
Proof. exact (@lem4392598 Prop x). Qed.
Lemma lem4392600 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50160 : A) : ((term303 A t s _50160) = (term303 A t s _50160)) = True.
Proof. exact (@lem4392599 (term303 A t s _50160)). Qed.
Lemma lem4392601 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50160 : A) : ((term124 A s t _50160) = (term303 A t s _50160)) = True.
Proof. exact (TRANS (@lem4392596 A t s _50160) (@lem4392600 A t s _50160)). Qed.
Lemma lem4392602 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50160 : A) : True = ((term124 A s t _50160) = (term303 A t s _50160)).
Proof. exact (SYM (@lem4392601 A t s _50160)). Qed.
Lemma lem4392603 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50160 : A) : (term124 A s t _50160) = (term303 A t s _50160).
Proof. exact (EQ_MP (@lem4392602 A t s _50160) (@lem0)). Qed.
Lemma lem4392604 {A : Type'} (_50160 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term303 A t s _50160.
Proof. exact (EQ_MP (@lem4392603 A t s _50160) (@lem4392350 A _50160 s t h1)). Qed.
Lemma lem4392606 (b : Prop) (a : Prop) : (a \/ b) = (term306 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4392607 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50160 : A) : (term303 A t s _50160) = (term307 A s t _50160).
Proof. exact (@lem4392606 (term141 A s _50160) (t _50160)). Qed.
Lemma lem4392609 (a : Prop) : (term97 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4392610 {A : Type'} (s : A -> Prop) (_50160 : A) : (term133 A s _50160) = (s _50160).
Proof. exact (@lem4392609 (s _50160)). Qed.
Lemma lem4392611 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4392612 {A : Type'} (s : A -> Prop) (_50160 : A) : (term308 A s _50160) = (term58 A s _50160).
Proof. exact (MK_COMB (@lem4392611) (@lem4392610 A s _50160)). Qed.
Lemma lem4392613 {A : Type'} (t : A -> Prop) (_50160 : A) : (t _50160) = (t _50160).
Proof. exact (eq_refl (t _50160)). Qed.
Lemma lem4392614 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50160 : A) : (term307 A s t _50160) = (term60 A s t _50160).
Proof. exact (MK_COMB (@lem4392612 A s _50160) (@lem4392613 A t _50160)). Qed.
Lemma lem4392615 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50160 : A) : (term303 A t s _50160) = (term60 A s t _50160).
Proof. exact (TRANS (@lem4392607 A s t _50160) (@lem4392614 A s t _50160)). Qed.
Lemma lem4392618 {A : Type'} (_50160 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term60 A s t _50160.
Proof. exact (EQ_MP (@lem4392615 A s t _50160) (@lem4392604 A _50160 s t h1)). Qed.
Lemma lem4392619 {A : Type'} (_50160 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term60 A s t _50160.
Proof. exact (@lem4392618 A _50160 s t h1). Qed.
Lemma lem4392620 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term60 A s t x'.
Proof. exact (@lem4392619 A x' s t h1). Qed.
Lemma lem4392623 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term148 A B t x s x') : t x'.
Proof. exact (@lem4392620 A x' s t h1 (@lem4392575 A B t x s x' h2)). Qed.
Lemma lem4392624 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term148 A B t x s x') : term294 A t x'.
Proof. exact (fun h0 : term141 A t x' => @lem4392623 A B t x s x' h1 h2). Qed.
Lemma lem4392626 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392627 {A : Type'} (t : A -> Prop) (x' : A) : (term294 A t x') = (t x').
Proof. exact (@lem4392626 (t x')). Qed.
Lemma lem4392628 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term148 A B t x s x') : t x'.
Proof. exact (EQ_MP (@lem4392627 A t x') (@lem4392624 A B t x s x' h1 h2)). Qed.
Lemma lem4392631 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4392633 {A : Type'} (t : A -> Prop) (x' : A) : (term141 A t x') = (term309 A t x').
Proof. exact (@lem4392631 (t x')). Qed.
Lemma lem4392636 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term148 A B t x s x') : term309 A t x'.
Proof. exact (EQ_MP (@lem4392633 A t x') (@lem4392377 A B t x s x' h1)). Qed.
Lemma lem4392639 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term148 A B t x s x') : False.
Proof. exact (@lem4392636 A B t x s x' h2 (@lem4392628 A B t x s x' h1 h2)). Qed.
Lemma lem4392640 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term148 A B t x s x') : term302.
Proof. exact (fun h0 : ~ False => @lem4392639 A B t x s x' h1 h2). Qed.
Lemma lem4392642 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392643 : term302 = False.
Proof. exact (@lem4392642 False). Qed.
Lemma lem4392682 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : s x'.
Proof. exact (proj2 (@lem4392026 A B t x f s x' h1)). Qed.
Lemma lem4392683 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term294 A s x'.
Proof. exact (fun h0 : term141 A s x' => @lem4392682 A B t x f s x' h1). Qed.
Lemma lem4392685 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392686 {A : Type'} (s : A -> Prop) (x' : A) : (term294 A s x') = (s x').
Proof. exact (@lem4392685 (s x')). Qed.
Lemma lem4392687 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : s x'.
Proof. exact (EQ_MP (@lem4392686 A s x') (@lem4392683 A B t x f s x' h1)). Qed.
Lemma lem4392693 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4392694 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50162 : A) : (term124 A s t _50162) = (term303 A t s _50162).
Proof. exact (@lem4392693 (t _50162) (term141 A s _50162)). Qed.
Lemma lem4392700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4392701 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50162 : A) : (term304 A s t _50162) = (term305 A t s _50162).
Proof. exact (MK_COMB (@lem4392700) (@lem4392694 A t s _50162)). Qed.
Lemma lem4392707 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50162 : A) : (term303 A t s _50162) = (term303 A t s _50162).
Proof. exact (eq_refl (term303 A t s _50162)). Qed.
Lemma lem4392708 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50162 : A) : ((term124 A s t _50162) = (term303 A t s _50162)) = ((term303 A t s _50162) = (term303 A t s _50162)).
Proof. exact (MK_COMB (@lem4392701 A t s _50162) (@lem4392707 A t s _50162)). Qed.
Lemma lem4392710 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4392711 (x : Prop) : (x = x) = True.
Proof. exact (@lem4392710 Prop x). Qed.
Lemma lem4392712 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50162 : A) : ((term303 A t s _50162) = (term303 A t s _50162)) = True.
Proof. exact (@lem4392711 (term303 A t s _50162)). Qed.
Lemma lem4392713 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50162 : A) : ((term124 A s t _50162) = (term303 A t s _50162)) = True.
Proof. exact (TRANS (@lem4392708 A t s _50162) (@lem4392712 A t s _50162)). Qed.
Lemma lem4392714 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50162 : A) : True = ((term124 A s t _50162) = (term303 A t s _50162)).
Proof. exact (SYM (@lem4392713 A t s _50162)). Qed.
Lemma lem4392715 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_50162 : A) : (term124 A s t _50162) = (term303 A t s _50162).
Proof. exact (EQ_MP (@lem4392714 A t s _50162) (@lem0)). Qed.
Lemma lem4392716 {A : Type'} (_50162 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term303 A t s _50162.
Proof. exact (EQ_MP (@lem4392715 A t s _50162) (@lem4392419 A _50162 s t h1)). Qed.
Lemma lem4392718 (b : Prop) (a : Prop) : (a \/ b) = (term306 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4392719 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50162 : A) : (term303 A t s _50162) = (term307 A s t _50162).
Proof. exact (@lem4392718 (term141 A s _50162) (t _50162)). Qed.
Lemma lem4392721 (a : Prop) : (term97 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4392722 {A : Type'} (s : A -> Prop) (_50162 : A) : (term133 A s _50162) = (s _50162).
Proof. exact (@lem4392721 (s _50162)). Qed.
Lemma lem4392723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4392724 {A : Type'} (s : A -> Prop) (_50162 : A) : (term308 A s _50162) = (term58 A s _50162).
Proof. exact (MK_COMB (@lem4392723) (@lem4392722 A s _50162)). Qed.
Lemma lem4392725 {A : Type'} (t : A -> Prop) (_50162 : A) : (t _50162) = (t _50162).
Proof. exact (eq_refl (t _50162)). Qed.
Lemma lem4392726 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50162 : A) : (term307 A s t _50162) = (term60 A s t _50162).
Proof. exact (MK_COMB (@lem4392724 A s _50162) (@lem4392725 A t _50162)). Qed.
Lemma lem4392727 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_50162 : A) : (term303 A t s _50162) = (term60 A s t _50162).
Proof. exact (TRANS (@lem4392719 A s t _50162) (@lem4392726 A s t _50162)). Qed.
Lemma lem4392730 {A : Type'} (_50162 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term60 A s t _50162.
Proof. exact (EQ_MP (@lem4392727 A s t _50162) (@lem4392716 A _50162 s t h1)). Qed.
Lemma lem4392731 {A : Type'} (_50162 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term60 A s t _50162.
Proof. exact (@lem4392730 A _50162 s t h1). Qed.
Lemma lem4392732 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term60 A s t x'.
Proof. exact (@lem4392731 A x' s t h1). Qed.
Lemma lem4392735 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term254 A B t x f s x') : t x'.
Proof. exact (@lem4392732 A x' s t h1 (@lem4392687 A B t x f s x' h2)). Qed.
Lemma lem4392736 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term254 A B t x f s x') : term294 A t x'.
Proof. exact (fun h0 : term141 A t x' => @lem4392735 A B t x f s x' h1 h2). Qed.
Lemma lem4392738 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392739 {A : Type'} (t : A -> Prop) (x' : A) : (term294 A t x') = (t x').
Proof. exact (@lem4392738 (t x')). Qed.
Lemma lem4392740 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term254 A B t x f s x') : t x'.
Proof. exact (EQ_MP (@lem4392739 A t x') (@lem4392736 A B t x f s x' h1 h2)). Qed.
Lemma lem4392742 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4392743 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4392742 B x). Qed.
Lemma lem4392744 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem4392743 B (f x')). Qed.
Lemma lem4392745 {A B : Type'} (f : A -> B) (x' : A) : term291 A B f x'.
Proof. exact (fun h0 : term292 A B f x' => @lem4392744 A B f x'). Qed.
Lemma lem4392747 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392748 {A B : Type'} (f : A -> B) (x' : A) : (term291 A B f x') = ((f x') = (f x')).
Proof. exact (@lem4392747 ((f x') = (f x'))). Qed.
Lemma lem4392749 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem4392748 A B f x') (@lem4392745 A B f x')). Qed.
Lemma lem4392751 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : s x'.
Proof. exact (proj2 (@lem4392026 A B t x f s x' h1)). Qed.
Lemma lem4392752 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term294 A s x'.
Proof. exact (fun h0 : term141 A s x' => @lem4392751 A B t x f s x' h1). Qed.
Lemma lem4392754 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392755 {A : Type'} (s : A -> Prop) (x' : A) : (term294 A s x') = (s x').
Proof. exact (@lem4392754 (s x')). Qed.
Lemma lem4392756 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : s x'.
Proof. exact (EQ_MP (@lem4392755 A s x') (@lem4392752 A B t x f s x' h1)). Qed.
Lemma lem4392758 (a : Prop) (b : Prop) : (term295 a b) = (term296 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4392759 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term282 A B x' f s _50163) = (term297 A B x' f s _50163).
Proof. exact (@lem4392758 ((f x') = (f _50163)) (s _50163)). Qed.
Lemma lem4392760 {A : Type'} (t : A -> Prop) (_50163 : A) : (term129 A t _50163) = (term129 A t _50163).
Proof. exact (eq_refl (term129 A t _50163)). Qed.
Lemma lem4392761 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term288 A B t x' f s _50163) = (term310 A B t x' f s _50163).
Proof. exact (MK_COMB (@lem4392760 A t _50163) (@lem4392759 A B x' f s _50163)). Qed.
Lemma lem4392763 (a : Prop) (b : Prop) : (term295 a b) = (term296 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4392764 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term310 A B t x' f s _50163) = (term311 A B t x' f s _50163).
Proof. exact (@lem4392763 (t _50163) (term299 A B x' f s _50163)). Qed.
Lemma lem4392765 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term288 A B t x' f s _50163) = (term311 A B t x' f s _50163).
Proof. exact (TRANS (@lem4392761 A B t x' f s _50163) (@lem4392764 A B t x' f s _50163)). Qed.
Lemma lem4392767 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4392768 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term311 A B t x' f s _50163) = (term312 A B t x' f s _50163).
Proof. exact (@lem4392767 (term313 A B t x' f s _50163)). Qed.
Lemma lem4392769 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_50163 : A) : (term288 A B t x' f s _50163) = (term312 A B t x' f s _50163).
Proof. exact (TRANS (@lem4392765 A B t x' f s _50163) (@lem4392768 A B t x' f s _50163)). Qed.
Lemma lem4392771 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term300 A B f s x'.
Proof. exact (conj (@lem4392749 A B f x') (@lem4392756 A B t x f s x' h1)). Qed.
Lemma lem4392772 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term254 A B t x f s x') : term314 A B t f s x'.
Proof. exact (conj (@lem4392740 A B t x f s x' h1 h2) (@lem4392771 A B t x f s x' h2)). Qed.
Lemma lem4392774 {A B : Type'} (_50163 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term312 A B t x' f s _50163.
Proof. exact (EQ_MP (@lem4392769 A B t x' f s _50163) (@lem4392446 A B _50163 t x f s x' h1)). Qed.
Lemma lem4392775 {A B : Type'} (_50163 : A) (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term312 A B t x' f s _50163.
Proof. exact (@lem4392774 A B _50163 t x f s x' h1). Qed.
Lemma lem4392776 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term254 A B t x f s x') : term315 A B t f s x'.
Proof. exact (@lem4392775 A B x' t x f s x' h1). Qed.
Lemma lem4392779 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term254 A B t x f s x') : False.
Proof. exact (@lem4392776 A B t x f s x' h2 (@lem4392772 A B t x f s x' h1 h2)). Qed.
Lemma lem4392780 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term254 A B t x f s x') : term302.
Proof. exact (fun h0 : ~ False => @lem4392779 A B t x f s x' h1 h2). Qed.
Lemma lem4392782 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4392783 : term302 = False.
Proof. exact (@lem4392782 False). Qed.
Lemma lem4392785 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term254 A B t x f s x') : False.
Proof. exact (EQ_MP (@lem4392783) (@lem4392780 A B t x f s x' h1 h2)). Qed.
Lemma lem4392786 {A B : Type'} (t : A -> Prop) (x : B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term148 A B t x s x') : False.
Proof. exact (EQ_MP (@lem4392643) (@lem4392640 A B t x s x' h1 h2)). Qed.
Lemma lem4392787 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term147 A B t x f s x') (h2 : term240 A B t x' x f s) : False.
Proof. exact (EQ_MP (@lem4392531) (@lem4392528 A B t x' x f s h1 h2)). Qed.
Lemma lem4392788 {A B : Type'} (t : A -> Prop) (x' : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term63 A s t) (h2 : term240 A B t x' x f s) : False.
Proof. exact (or_elim (@lem4392015 A B t x' x f s h2) (fun h0 : term147 A B t x f s x' => @lem4392787 A B t x' x f s h0 h2) (fun h0 : term148 A B t x s x' => @lem4392786 A B t x s x' h1 h0)). Qed.
Lemma lem4392789 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term273 A B t x f s x') : False.
Proof. exact (or_elim (@lem4392011 A B t x f s x' h2) (fun h0 : term240 A B t x' x f s => @lem4392788 A B t x' x f s h1 h0) (fun h0 : term254 A B t x f s x' => @lem4392785 A B t x f s x' h1 h0)). Qed.
Lemma lem4392790 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term273 A B t x f s x') : (term273 A B t x f s x') = False.
Proof. exact (prop_ext (fun h3 : term273 A B t x f s x' => @lem4392789 A B t x f s x' h1 h2) (fun h3 : False => @lem4392011 A B t x f s x' h2)). Qed.
Lemma lem4392791 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (h1 : term63 A s t) (h2 : term273 A B t x f s x') : False.
Proof. exact (EQ_MP (@lem4392790 A B t x f s x' h1 h2) (@lem4392011 A B t x f s x' h2)). Qed.
Lemma lem4392792 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term63 A s t) (h2 : term123 A B t x f s) : False.
Proof. exact (ex_elim (@lem4391856 A B t x f s h2) (fun x' : A => fun h0 : term275 A B t x f s x' => @lem4392791 A B t x f s x' h1 h0)). Qed.
Lemma lem4392793 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term63 A s t) (h2 : term123 A B t x f s) : (term123 A B t x f s) = False.
Proof. exact (prop_ext (fun h3 : term123 A B t x f s => @lem4392792 A B t x f s h1 h2) (fun h3 : False => @lem4391299 A B t x f s h2)). Qed.
Lemma lem4392794 {A B : Type'} (t : A -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term63 A s t) (h2 : term123 A B t x f s) : False.
Proof. exact (EQ_MP (@lem4392793 A B t x f s h1 h2) (@lem4391299 A B t x f s h2)). Qed.
Lemma lem4392795 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term122 A B t x f s.
Proof. exact (fun h0 : term123 A B t x f s => @lem4392794 A B t x f s h1 h0). Qed.
Lemma lem4392796 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : (term111 A B f t x s) = (term80 A B x f s).
Proof. exact (EQ_MP (@lem4391298 A B t x f s) (@lem4392795 A B x f s t h1)). Qed.
Lemma lem4392801 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (h1 : term63 A s t) : term114 A B t f s.
Proof. exact (fun x : B => @lem4392796 A B x f s t h1). Qed.
Lemma lem4392802 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : term115 A B t f s.
Proof. exact (fun h0 : term63 A s t => @lem4392801 A B f s t h0). Qed.
Lemma lem4392807 {A B : Type'} (f : A -> B) (s : A -> Prop) : term117 A B f s.
Proof. exact (fun t : A -> Prop => @lem4392802 A B t f s). Qed.
Lemma lem4392812 {A B : Type'} (f : A -> B) : term119 A B f.
Proof. exact (fun s : A -> Prop => @lem4392807 A B f s). Qed.
Lemma lem4392817 {A B : Type'} : term121 A B.
Proof. exact (fun f : A -> B => @lem4392812 A B f). Qed.
Lemma lem4392818 {A B : Type'} : term91 A B.
Proof. exact (EQ_MP (@lem4391293 A B) (@lem4392817 A B)). Qed.
Lemma lem4392820 {A B : Type'} : term91 A B.
Proof. exact (@lem4390996 A B (@lem4392818 A B)). Qed.
Lemma lem4392821 {A B : Type'} (h1 : term92 A B) : False.
Proof. exact (@lem4392820 A B (@lem4390980 A B h1)). Qed.
Lemma lem4392822 {A B : Type'} (h1 : term92 A B) : (term92 A B) = False.
Proof. exact (prop_ext (fun h2 : term92 A B => @lem4392821 A B h1) (fun h2 : False => @lem4390980 A B h1)). Qed.
Lemma lem4392823 {A B : Type'} (h1 : term92 A B) : False.
Proof. exact (EQ_MP (@lem4392822 A B h1) (@lem4390980 A B h1)). Qed.
Lemma lem4392824 {A B : Type'} : term91 A B.
Proof. exact (fun h0 : term92 A B => @lem4392823 A B h0). Qed.
Lemma lem4392825 {A B : Type'} : term89 A B.
Proof. exact (EQ_MP (@lem4390979 A B) (@lem4392824 A B)). Qed.
Lemma lem4392826 {A B : Type'} : term56 A B.
Proof. exact (EQ_MP (@lem4390975 A B) (@lem4392825 A B)). Qed.
Lemma lem4392827 {A B : Type'} : term47 A B.
Proof. exact (EQ_MP (@lem4390829 A B) (@lem4392826 A B)). Qed.
Lemma lem4392828 {A B : Type'} : term46 A B.
Proof. exact (EQ_MP (@lem4390750 A B) (@lem4392827 A B)). Qed.
