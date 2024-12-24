Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_DIFF_term_abbrevs.
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
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3288675 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (_476 : type686 A) (_477 : A -> Prop) : (term0 A _476 _475 _474 _477) = (term1 A _474 _475 _476 _477).
Proof. exact (@lem13473 (A -> Prop) _474 _475 _476 _477). Qed.
Lemma lem3288676 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (x : A) (s : A -> Prop) (t : A -> Prop) (_477 : A -> Prop) : (term2 A x s t _475 _474 _477) = (term3 A _474 _475 x s t _477).
Proof. exact (@lem3288675 A _474 _475 (term4 A x s t) _477). Qed.
Lemma lem3288677 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term5 A x s t) = (term6 A x s t).
Proof. exact (@lem3288676 A (@DIFF A s t) (@IN A x t) x s t (term7 A x s t)). Qed.
Lemma lem3288678 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term8 A x s t) = ((term9 A x s t) = (term7 A x s t)).
Proof. exact (eq_refl (term8 A x s t)). Qed.
Lemma lem3288679 {A : Type'} (x : A) (t : A -> Prop) : (term10 A x t) = (term10 A x t).
Proof. exact (eq_refl (term10 A x t)). Qed.
Lemma lem3288680 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term11 A x s t) = (term12 A x s t).
Proof. exact (MK_COMB (@lem3288679 A x t) (@lem3288678 A x s t)). Qed.
Lemma lem3288681 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term13 A x s t) = ((term9 A x s t) = (@DIFF A s t)).
Proof. exact (eq_refl (term13 A x s t)). Qed.
Lemma lem3288682 {A : Type'} (x : A) (t : A -> Prop) : (term14 A x t) = (term14 A x t).
Proof. exact (eq_refl (term14 A x t)). Qed.
Lemma lem3288683 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term15 A x s t) = (term16 A x s t).
Proof. exact (MK_COMB (@lem3288682 A x t) (@lem3288681 A x s t)). Qed.
Lemma lem3288684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3288685 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term17 A x s t) = (term18 A x s t).
Proof. exact (MK_COMB (@lem3288684) (@lem3288683 A x s t)). Qed.
Lemma lem3288686 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term6 A x s t) = (term19 A x s t).
Proof. exact (MK_COMB (@lem3288685 A x s t) (@lem3288680 A x s t)). Qed.
Lemma lem3288687 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term5 A x s t) = ((term9 A x s t) = (term20 A x s t)).
Proof. exact (eq_refl (term5 A x s t)). Qed.
Lemma lem3288688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3288689 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term21 A x s t) = (term22 A x s t).
Proof. exact (MK_COMB (@lem3288688) (@lem3288687 A x s t)). Qed.
Lemma lem3288690 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term5 A x s t) = (term6 A x s t)) = (((term9 A x s t) = (term20 A x s t)) = (term19 A x s t)).
Proof. exact (MK_COMB (@lem3288689 A x s t) (@lem3288686 A x s t)). Qed.
Lemma lem3288691 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (term20 A x s t)) = (term19 A x s t).
Proof. exact (EQ_MP (@lem3288690 A x s t) (@lem3288677 A x s t)). Qed.
Lemma lem3288692 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term19 A x s t) = ((term9 A x s t) = (term20 A x s t)).
Proof. exact (SYM (@lem3288691 A x s t)). Qed.
Lemma lem3288693 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3288710 {A : Type'} (x : A) (t : A -> Prop) (h1 : term23 A x t) : term23 A x t.
Proof. exact (h1). Qed.
Lemma lem3288732 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3288733 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (@lem3288732 A s t). Qed.
Lemma lem3288734 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (@DIFF A s t)) = (term25 A x s t).
Proof. exact (@lem3288733 A (term9 A x s t) (@DIFF A s t)). Qed.
Lemma lem3288743 {A : Type'} (x : A) (t : A -> Prop) : (term14 A x t) = (term14 A x t).
Proof. exact (eq_refl (term14 A x t)). Qed.
Lemma lem3288744 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term16 A x s t) = (term26 A x s t).
Proof. exact (MK_COMB (@lem3288743 A x t) (@lem3288734 A x s t)). Qed.
Lemma lem3288747 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term16 A x s t).
Proof. exact (SYM (@lem3288744 A x s t)). Qed.
Lemma lem3288751 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3288752 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3288751 A P x). Qed.
Lemma lem3288753 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3288752 A t x). Qed.
Lemma lem3288754 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3288755 {A : Type'} (t : A -> Prop) (x : A) : (term14 A x t) = (term27 A t x).
Proof. exact (MK_COMB (@lem3288754) (@lem3288753 A t x)). Qed.
Lemma lem3288763 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3288764 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3288763 A s x t). Qed.
Lemma lem3288765 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term30 A x' x s t) = (term31 A x s x' t).
Proof. exact (@lem3288764 A (@INSERT A x s) x' t). Qed.
Lemma lem3288769 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3288770 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3288769 A y x s). Qed.
Lemma lem3288771 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term32 A x' x s) = (term33 A x x' s).
Proof. exact (@lem3288770 A x x' s). Qed.
Lemma lem3288777 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3288778 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3288777 A P x). Qed.
Lemma lem3288779 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3288778 A s x'). Qed.
Lemma lem3288780 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3288781 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term33 A x x' s) = (term35 A x s x').
Proof. exact (MK_COMB (@lem3288780 A x' x) (@lem3288779 A s x')). Qed.
Lemma lem3288784 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x' x s) = (term35 A x s x').
Proof. exact (TRANS (@lem3288771 A x x' s) (@lem3288781 A x s x')). Qed.
Lemma lem3288785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3288786 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term36 A x' x s) = (term37 A x s x').
Proof. exact (MK_COMB (@lem3288785) (@lem3288784 A x s x')). Qed.
Lemma lem3288788 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3288789 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3288788 A P x). Qed.
Lemma lem3288790 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3288789 A t x'). Qed.
Lemma lem3288791 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3288792 {A : Type'} (t : A -> Prop) (x' : A) : (term23 A x' t) = (term38 A t x').
Proof. exact (MK_COMB (@lem3288791) (@lem3288790 A t x')). Qed.
Lemma lem3288793 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term31 A x s x' t) = (term39 A x s t x').
Proof. exact (MK_COMB (@lem3288786 A x s x') (@lem3288792 A t x')). Qed.
Lemma lem3288796 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term30 A x' x s t) = (term39 A x s t x').
Proof. exact (TRANS (@lem3288765 A x s x' t) (@lem3288793 A x s t x')). Qed.
Lemma lem3288797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3288798 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term40 A x' x s t) = (term41 A x s t x').
Proof. exact (MK_COMB (@lem3288797) (@lem3288796 A x s t x')). Qed.
Lemma lem3288800 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3288801 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3288800 A s x t). Qed.
Lemma lem3288802 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term28 A x' s t) = (term29 A s x' t).
Proof. exact (@lem3288801 A s x' t). Qed.
Lemma lem3288806 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3288807 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3288806 A P x). Qed.
Lemma lem3288808 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3288807 A s x'). Qed.
Lemma lem3288809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3288810 {A : Type'} (s : A -> Prop) (x' : A) : (term42 A x' s) = (term43 A s x').
Proof. exact (MK_COMB (@lem3288809) (@lem3288808 A s x')). Qed.
Lemma lem3288812 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3288813 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3288812 A P x). Qed.
Lemma lem3288814 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3288813 A t x'). Qed.
Lemma lem3288815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3288816 {A : Type'} (t : A -> Prop) (x' : A) : (term23 A x' t) = (term38 A t x').
Proof. exact (MK_COMB (@lem3288815) (@lem3288814 A t x')). Qed.
Lemma lem3288817 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term29 A s x' t) = (term44 A s t x').
Proof. exact (MK_COMB (@lem3288810 A s x') (@lem3288816 A t x')). Qed.
Lemma lem3288820 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term28 A x' s t) = (term44 A s t x').
Proof. exact (TRANS (@lem3288802 A s x' t) (@lem3288817 A s t x')). Qed.
Lemma lem3288821 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term30 A x' x s t) = (term28 A x' s t)) = ((term39 A x s t x') = (term44 A s t x')).
Proof. exact (MK_COMB (@lem3288798 A x s t x') (@lem3288820 A s t x')). Qed.
Lemma lem3288824 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term45 A x s t) = (term46 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3288821 A x s t x')). Qed.
Lemma lem3288825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3288826 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term25 A x s t) = (term47 A x s t).
Proof. exact (MK_COMB (@lem3288825 A) (@lem3288824 A x s t)). Qed.
Lemma lem3288831 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term48 A x s t).
Proof. exact (MK_COMB (@lem3288755 A t x) (@lem3288826 A x s t)). Qed.
Lemma lem3288834 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term48 A x s t) = (term26 A x s t).
Proof. exact (SYM (@lem3288831 A x s t)). Qed.
Lemma lem3288836 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3288837 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term48 A x s t) = (term50 A x s t).
Proof. exact (@lem3288836 (term48 A x s t)). Qed.
Lemma lem3288838 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term50 A x s t) = (term48 A x s t).
Proof. exact (SYM (@lem3288837 A x s t)). Qed.
Lemma lem3288839 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term51 A x s t) : term51 A x s t.
Proof. exact (h1). Qed.
Lemma lem3288842 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) : term50 A x s t.
Proof. exact (h1). Qed.
Lemma lem3288843 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term52 A x s t.
Proof. exact (fun h0 : term50 A x s t => @lem3288842 A x s t h0). Qed.
Lemma lem3288844 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term52 A x s t) : term52 A x s t.
Proof. exact (h1). Qed.
Lemma lem3288845 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) : term50 A x s t.
Proof. exact (h1). Qed.
Lemma lem3288846 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) (h2 : term52 A x s t) : term50 A x s t.
Proof. exact (@lem3288844 A x s t h2 (@lem3288845 A x s t h1)). Qed.
Lemma lem3288847 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) : term53 A x s t.
Proof. exact (fun h0 : term52 A x s t => @lem3288846 A x s t h1 h0). Qed.
Lemma lem3288848 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term52 A x s t) : term52 A x s t.
Proof. exact (h1). Qed.
Lemma lem3288849 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) (h2 : term52 A x s t) : term50 A x s t.
Proof. exact (@lem3288847 A x s t h1 (@lem3288848 A x s t h2)). Qed.
Lemma lem3288850 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term52 A x s t) : term52 A x s t.
Proof. exact (fun h0 : term50 A x s t => @lem3288849 A x s t h0 h1). Qed.
Lemma lem3288851 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term54 A x s t.
Proof. exact (fun h0 : term52 A x s t => @lem3288850 A x s t h0). Qed.
Lemma lem3288854 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term52 A x s t.
Proof. exact (@lem3288851 A x s t (@lem3288843 A x s t)). Qed.
Lemma lem3288855 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term52 A x s t.
Proof. exact (@lem3288854 A x s t). Qed.
Lemma lem3288869 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3288870 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term50 A x s t) = (term55 A x s t).
Proof. exact (@lem3288869 (term51 A x s t)). Qed.
Lemma lem3288872 (t : Prop) : (term56 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3288873 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term55 A x s t) = (term48 A x s t).
Proof. exact (@lem3288872 (term48 A x s t)). Qed.
Lemma lem3288876 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term50 A x s t) = (term48 A x s t).
Proof. exact (TRANS (@lem3288870 A x s t) (@lem3288873 A x s t)). Qed.
Lemma lem3288887 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term58 A s t).
Proof. exact (fun_ext (fun x : A => @lem3288876 A x s t)). Qed.
Lemma lem3288888 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3288889 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term59 A s t) = (term60 A s t).
Proof. exact (MK_COMB (@lem3288888 A) (@lem3288887 A s t)). Qed.
Lemma lem3288894 {A : Type'} (t : A -> Prop) : (term61 A t) = (term62 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3288889 A s t)). Qed.
Lemma lem3288895 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3288896 {A : Type'} (t : A -> Prop) : (term63 A t) = (term64 A t).
Proof. exact (MK_COMB (@lem3288895 A) (@lem3288894 A t)). Qed.
Lemma lem3288901 {A : Type'} : (term65 A) = (term66 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3288896 A t)). Qed.
Lemma lem3288902 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3288911 {A : Type'} : (term67 A) = (term68 A).
Proof. exact (MK_COMB (@lem3288902 A) (@lem3288901 A)). Qed.
Lemma lem3288932 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term39 A x s t x') = (term44 A s t x')) = ((term39 A x s t x') = (term44 A s t x')).
Proof. exact (eq_refl ((term39 A x s t x') = (term44 A s t x'))). Qed.
Lemma lem3288933 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term46 A x s t) = (term46 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3288932 A x s t x')). Qed.
Lemma lem3288934 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3288935 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term47 A x s t) = (term47 A x s t).
Proof. exact (MK_COMB (@lem3288934 A) (@lem3288933 A x s t)). Qed.
Lemma lem3288938 {A : Type'} (t : A -> Prop) (x : A) : (term27 A t x) = (term27 A t x).
Proof. exact (eq_refl (term27 A t x)). Qed.
Lemma lem3288939 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term48 A x s t) = (term48 A x s t).
Proof. exact (MK_COMB (@lem3288938 A t x) (@lem3288935 A x s t)). Qed.
Lemma lem3288940 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (fun_ext (fun x : A => @lem3288939 A x s t)). Qed.
Lemma lem3288941 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3288942 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term60 A s t) = (term60 A s t).
Proof. exact (MK_COMB (@lem3288941 A) (@lem3288940 A s t)). Qed.
Lemma lem3288943 {A : Type'} (t : A -> Prop) : (term62 A t) = (term62 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3288942 A s t)). Qed.
Lemma lem3288944 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3288945 {A : Type'} (t : A -> Prop) : (term64 A t) = (term64 A t).
Proof. exact (MK_COMB (@lem3288944 A) (@lem3288943 A t)). Qed.
Lemma lem3288946 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3288945 A t)). Qed.
Lemma lem3288947 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3288948 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (MK_COMB (@lem3288947 A) (@lem3288946 A)). Qed.
Lemma lem3288983 {A : Type'} : (term67 A) = (term68 A).
Proof. exact (TRANS (@lem3288911 A) (@lem3288948 A)). Qed.
Lemma lem3288984 {A : Type'} : (term68 A) = (term67 A).
Proof. exact (SYM (@lem3288983 A)). Qed.
Lemma lem3288987 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3288988 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term39 A x s t x') = (term44 A s t x')) = (term69 A x s t x').
Proof. exact (@lem3288987 ((term39 A x s t x') = (term44 A s t x'))). Qed.
Lemma lem3288989 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term69 A x s t x') = ((term39 A x s t x') = (term44 A s t x')).
Proof. exact (SYM (@lem3288988 A x s t x')). Qed.
Lemma lem3288990 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term70 A x s t x') : term70 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3288996 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3289005 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term71 A x s x') = (term72 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3289012 {A : Type'} (t : A -> Prop) (x' : A) : (term73 A t x') = (t x').
Proof. exact (@lem16933 (t x')). Qed.
Lemma lem3289013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3289014 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term74 A x s x') = (term75 A x s x').
Proof. exact (MK_COMB (@lem3289013) (@lem3289005 A x s x')). Qed.
Lemma lem3289015 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term76 A x s t x') = (term77 A x s t x').
Proof. exact (MK_COMB (@lem3289014 A x s x') (@lem3289012 A t x')). Qed.
Lemma lem3289016 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term78 A x s t x') = (term76 A x s t x').
Proof. exact (@lem17045 (term35 A x s x') (term38 A t x')). Qed.
Lemma lem3289017 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term78 A x s t x') = (term77 A x s t x').
Proof. exact (TRANS (@lem3289016 A x s t x') (@lem3289015 A x s t x')). Qed.
Lemma lem3289026 {A : Type'} (t : A -> Prop) (x' : A) : (term73 A t x') = (t x').
Proof. exact (@lem16933 (t x')). Qed.
Lemma lem3289028 {A : Type'} (s : A -> Prop) (x' : A) : (term79 A s x') = (term79 A s x').
Proof. exact (eq_refl (term79 A s x')). Qed.
Lemma lem3289029 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term80 A s t x') = (term81 A s t x').
Proof. exact (MK_COMB (@lem3289028 A s x') (@lem3289026 A t x')). Qed.
Lemma lem3289030 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A s t x') = (term80 A s t x').
Proof. exact (@lem17045 (s x') (term38 A t x')). Qed.
Lemma lem3289031 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A s t x') = (term81 A s t x').
Proof. exact (TRANS (@lem3289030 A s t x') (@lem3289029 A s t x')). Qed.
Lemma lem3289034 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term44 A s t x') = (term44 A s t x').
Proof. exact (eq_refl (term44 A s t x')). Qed.
Lemma lem3289035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3289036 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term83 A x s t x') = (term84 A x s t x').
Proof. exact (MK_COMB (@lem3289035) (@lem3289017 A x s t x')). Qed.
Lemma lem3289037 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term85 A x s t x') = (term86 A x s t x').
Proof. exact (MK_COMB (@lem3289036 A x s t x') (@lem3289034 A s t x')). Qed.
Lemma lem3289039 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term87 A x s t x') = (term87 A x s t x').
Proof. exact (eq_refl (term87 A x s t x')). Qed.
Lemma lem3289040 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term88 A x s t x') = (term89 A x s t x').
Proof. exact (MK_COMB (@lem3289039 A x s t x') (@lem3289031 A s t x')). Qed.
Lemma lem3289041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3289042 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term90 A x s t x') = (term91 A x s t x').
Proof. exact (MK_COMB (@lem3289041) (@lem3289040 A x s t x')). Qed.
Lemma lem3289043 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term92 A x s t x') = (term93 A x s t x').
Proof. exact (MK_COMB (@lem3289042 A x s t x') (@lem3289037 A x s t x')). Qed.
Lemma lem3289044 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term70 A x s t x') = (term92 A x s t x').
Proof. exact (@lem17646 (term39 A x s t x') (term44 A s t x')). Qed.
Lemma lem3289049 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term70 A x s t x') = (term93 A x s t x').
Proof. exact (TRANS (@lem3289044 A x s t x') (@lem3289043 A x s t x')). Qed.
Lemma lem3289054 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3289126 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term70 A x s t x') : term93 A x s t x'.
Proof. exact (EQ_MP (@lem3289049 A x s t x') (@lem3288990 A x s t x' h1)). Qed.
Lemma lem3289127 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term89 A x s t x') : term89 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3289128 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term86 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3289129 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term89 A x s t x') : term81 A s t x'.
Proof. exact (proj2 (@lem3289127 A x s t x' h1)). Qed.
Lemma lem3289130 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term89 A x s t x') : term39 A x s t x'.
Proof. exact (proj1 (@lem3289127 A x s t x' h1)). Qed.
Lemma lem3289132 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term89 A x s t x') : term35 A x s x'.
Proof. exact (proj1 (@lem3289130 A x s t x' h1)). Qed.
Lemma lem3289139 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term44 A s t x'.
Proof. exact (proj2 (@lem3289128 A x s t x' h1)). Qed.
Lemma lem3289140 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term77 A x s t x'.
Proof. exact (proj1 (@lem3289128 A x s t x' h1)). Qed.
Lemma lem3289143 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term72 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3289150 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3289158 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3289174 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3289178 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3289190 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3289194 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') : term38 A s x'.
Proof. exact (h1). Qed.
Lemma lem3289210 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3289246 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3289248 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3289250 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term89 A x s t x') : term38 A t x'.
Proof. exact (proj2 (@lem3289130 A x s t x' h1)). Qed.
Lemma lem3289252 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3289258 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term89 A x s t x') : term38 A t x'.
Proof. exact (proj2 (@lem3289130 A x s t x' h1)). Qed.
Lemma lem3289260 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3289262 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3289268 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3289270 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') : term38 A s x'.
Proof. exact (h1). Qed.
Lemma lem3289274 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term89 A x s t x') : term38 A t x'.
Proof. exact (proj2 (@lem3289130 A x s t x' h1)). Qed.
Lemma lem3289278 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3289288 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term38 A s x'.
Proof. exact (proj2 (@lem3289143 A x s x' h1)). Qed.
Lemma lem3289294 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term38 A t x'.
Proof. exact (proj2 (@lem3289139 A x s t x' h1)). Qed.
Lemma lem3289296 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3289324 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3289325 {A : Type'} (t : A -> Prop) : (term94 A t) = (term94 A t).
Proof. exact (eq_refl (term94 A t)). Qed.
Lemma lem3289326 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term95 A t x') = (term95 A t x).
Proof. exact (MK_COMB (@lem3289325 A t) (@lem3289252 A x' x h1)). Qed.
Lemma lem3289327 {A : Type'} (t : A -> Prop) (x : A) : (term95 A t x) = (term38 A t x).
Proof. exact (eq_refl (term95 A t x)). Qed.
Lemma lem3289328 {A : Type'} (t : A -> Prop) (x' : A) : (term96 A t x') = (term96 A t x').
Proof. exact (eq_refl (term96 A t x')). Qed.
Lemma lem3289329 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term95 A t x)) = ((term95 A t x') = (term38 A t x)).
Proof. exact (MK_COMB (@lem3289328 A t x') (@lem3289327 A t x)). Qed.
Lemma lem3289330 {A : Type'} (t : A -> Prop) (x' : A) : (term95 A t x') = (term38 A t x').
Proof. exact (eq_refl (term95 A t x')). Qed.
Lemma lem3289331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3289332 {A : Type'} (t : A -> Prop) (x' : A) : (term96 A t x') = (term97 A t x').
Proof. exact (MK_COMB (@lem3289331) (@lem3289330 A t x')). Qed.
Lemma lem3289333 {A : Type'} (t : A -> Prop) (x : A) : (term38 A t x) = (term38 A t x).
Proof. exact (eq_refl (term38 A t x)). Qed.
Lemma lem3289334 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term38 A t x)) = ((term38 A t x') = (term38 A t x)).
Proof. exact (MK_COMB (@lem3289332 A t x') (@lem3289333 A t x)). Qed.
Lemma lem3289335 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term95 A t x)) = ((term38 A t x') = (term38 A t x)).
Proof. exact (TRANS (@lem3289329 A x' t x) (@lem3289334 A x' t x)). Qed.
Lemma lem3289336 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term38 A t x') = (term38 A t x).
Proof. exact (EQ_MP (@lem3289335 A x' t x) (@lem3289326 A t x' x h1)). Qed.
Lemma lem3289337 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term89 A x s t x') (h2 : x' = x) : term38 A t x.
Proof. exact (EQ_MP (@lem3289336 A t x' x h2) (@lem3289250 A x s t x' h1)). Qed.
Lemma lem3289379 {A : Type'} (t : A -> Prop) : (term94 A t) = (term94 A t).
Proof. exact (eq_refl (term94 A t)). Qed.
Lemma lem3289380 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term95 A t x') = (term95 A t x).
Proof. exact (MK_COMB (@lem3289379 A t) (@lem3289260 A x' x h1)). Qed.
Lemma lem3289381 {A : Type'} (t : A -> Prop) (x : A) : (term95 A t x) = (term38 A t x).
Proof. exact (eq_refl (term95 A t x)). Qed.
Lemma lem3289382 {A : Type'} (t : A -> Prop) (x' : A) : (term96 A t x') = (term96 A t x').
Proof. exact (eq_refl (term96 A t x')). Qed.
Lemma lem3289383 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term95 A t x)) = ((term95 A t x') = (term38 A t x)).
Proof. exact (MK_COMB (@lem3289382 A t x') (@lem3289381 A t x)). Qed.
Lemma lem3289384 {A : Type'} (t : A -> Prop) (x' : A) : (term95 A t x') = (term38 A t x').
Proof. exact (eq_refl (term95 A t x')). Qed.
Lemma lem3289385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3289386 {A : Type'} (t : A -> Prop) (x' : A) : (term96 A t x') = (term97 A t x').
Proof. exact (MK_COMB (@lem3289385) (@lem3289384 A t x')). Qed.
Lemma lem3289387 {A : Type'} (t : A -> Prop) (x : A) : (term38 A t x) = (term38 A t x).
Proof. exact (eq_refl (term38 A t x)). Qed.
Lemma lem3289388 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term38 A t x)) = ((term38 A t x') = (term38 A t x)).
Proof. exact (MK_COMB (@lem3289386 A t x') (@lem3289387 A t x)). Qed.
Lemma lem3289389 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term95 A t x)) = ((term38 A t x') = (term38 A t x)).
Proof. exact (TRANS (@lem3289383 A x' t x) (@lem3289388 A x' t x)). Qed.
Lemma lem3289390 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term38 A t x') = (term38 A t x).
Proof. exact (EQ_MP (@lem3289389 A x' t x) (@lem3289380 A t x' x h1)). Qed.
Lemma lem3289391 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term89 A x s t x') (h2 : x' = x) : term38 A t x.
Proof. exact (EQ_MP (@lem3289390 A t x' x h2) (@lem3289258 A x s t x' h1)). Qed.
Lemma lem3289392 {A : Type'} (t : A -> Prop) : (term98 A t) = (term98 A t).
Proof. exact (eq_refl (term98 A t)). Qed.
Lemma lem3289393 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term99 A t x') = (term99 A t x).
Proof. exact (MK_COMB (@lem3289392 A t) (@lem3289260 A x' x h1)). Qed.
Lemma lem3289394 {A : Type'} (t : A -> Prop) (x : A) : (term99 A t x) = (t x).
Proof. exact (eq_refl (term99 A t x)). Qed.
Lemma lem3289395 {A : Type'} (t : A -> Prop) (x' : A) : (term100 A t x') = (term100 A t x').
Proof. exact (eq_refl (term100 A t x')). Qed.
Lemma lem3289396 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (term99 A t x)) = ((term99 A t x') = (t x)).
Proof. exact (MK_COMB (@lem3289395 A t x') (@lem3289394 A t x)). Qed.
Lemma lem3289397 {A : Type'} (t : A -> Prop) (x' : A) : (term99 A t x') = (t x').
Proof. exact (eq_refl (term99 A t x')). Qed.
Lemma lem3289398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3289399 {A : Type'} (t : A -> Prop) (x' : A) : (term100 A t x') = (term101 A t x').
Proof. exact (MK_COMB (@lem3289398) (@lem3289397 A t x')). Qed.
Lemma lem3289400 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3289401 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (t x)) = ((t x') = (t x)).
Proof. exact (MK_COMB (@lem3289399 A t x') (@lem3289400 A t x)). Qed.
Lemma lem3289402 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (term99 A t x)) = ((t x') = (t x)).
Proof. exact (TRANS (@lem3289396 A x' t x) (@lem3289401 A x' t x)). Qed.
Lemma lem3289403 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (t x') = (t x).
Proof. exact (EQ_MP (@lem3289402 A x' t x) (@lem3289393 A t x' x h1)). Qed.
Lemma lem3289406 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3289407 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term102 A t x.
Proof. exact (fun h0 : term38 A t x => @lem3289406 A t x h1). Qed.
Lemma lem3289409 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289410 {A : Type'} (t : A -> Prop) (x : A) : (term102 A t x) = (t x).
Proof. exact (@lem3289409 (t x)). Qed.
Lemma lem3289411 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3289410 A t x) (@lem3289407 A t x h1)). Qed.
Lemma lem3289414 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3289416 {A : Type'} (t : A -> Prop) (x : A) : (term38 A t x) = (term104 A t x).
Proof. exact (@lem3289414 (t x)). Qed.
Lemma lem3289419 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term89 A x s t x') (h2 : x' = x) : term104 A t x.
Proof. exact (EQ_MP (@lem3289416 A t x) (@lem3289337 A s t x' x h1 h2)). Qed.
Lemma lem3289422 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (@lem3289419 A s t x' x h2 h3 (@lem3289411 A t x h1)). Qed.
Lemma lem3289423 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : term105.
Proof. exact (fun h0 : ~ False => @lem3289422 A s t x' x h1 h2 h3). Qed.
Lemma lem3289425 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289426 : term105 = False.
Proof. exact (@lem3289425 False). Qed.
Lemma lem3289427 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289426) (@lem3289423 A s t x' x h1 h2 h3)). Qed.
Lemma lem3289429 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3289403 A t x' x h2) (@lem3289262 A t x' h1)). Qed.
Lemma lem3289430 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : term102 A t x.
Proof. exact (fun h0 : term38 A t x => @lem3289429 A t x' x h1 h2). Qed.
Lemma lem3289432 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289433 {A : Type'} (t : A -> Prop) (x : A) : (term102 A t x) = (t x).
Proof. exact (@lem3289432 (t x)). Qed.
Lemma lem3289434 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3289433 A t x) (@lem3289430 A t x' x h1 h2)). Qed.
Lemma lem3289437 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3289439 {A : Type'} (t : A -> Prop) (x : A) : (term38 A t x) = (term104 A t x).
Proof. exact (@lem3289437 (t x)). Qed.
Lemma lem3289442 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term89 A x s t x') (h2 : x' = x) : term104 A t x.
Proof. exact (EQ_MP (@lem3289439 A t x) (@lem3289391 A s t x' x h1 h2)). Qed.
Lemma lem3289445 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (@lem3289442 A s t x' x h2 h3 (@lem3289434 A t x' x h1 h3)). Qed.
Lemma lem3289446 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : term105.
Proof. exact (fun h0 : ~ False => @lem3289445 A s t x' x h1 h2 h3). Qed.
Lemma lem3289448 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289449 : term105 = False.
Proof. exact (@lem3289448 False). Qed.
Lemma lem3289452 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3289453 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term102 A s x'.
Proof. exact (fun h0 : term38 A s x' => @lem3289452 A s x' h1). Qed.
Lemma lem3289455 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289456 {A : Type'} (s : A -> Prop) (x' : A) : (term102 A s x') = (s x').
Proof. exact (@lem3289455 (s x')). Qed.
Lemma lem3289457 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3289456 A s x') (@lem3289453 A s x' h1)). Qed.
Lemma lem3289460 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3289462 {A : Type'} (s : A -> Prop) (x' : A) : (term38 A s x') = (term104 A s x').
Proof. exact (@lem3289460 (s x')). Qed.
Lemma lem3289465 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') : term104 A s x'.
Proof. exact (EQ_MP (@lem3289462 A s x') (@lem3289270 A s x' h1)). Qed.
Lemma lem3289468 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (@lem3289465 A s x' h1 (@lem3289457 A s x' h2)). Qed.
Lemma lem3289469 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : term105.
Proof. exact (fun h0 : ~ False => @lem3289468 A s x' h1 h2). Qed.
Lemma lem3289471 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289472 : term105 = False.
Proof. exact (@lem3289471 False). Qed.
Lemma lem3289473 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3289472) (@lem3289469 A s x' h1 h2)). Qed.
Lemma lem3289475 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3289476 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term102 A t x'.
Proof. exact (fun h0 : term38 A t x' => @lem3289475 A t x' h1). Qed.
Lemma lem3289478 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289479 {A : Type'} (t : A -> Prop) (x' : A) : (term102 A t x') = (t x').
Proof. exact (@lem3289478 (t x')). Qed.
Lemma lem3289480 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3289479 A t x') (@lem3289476 A t x' h1)). Qed.
Lemma lem3289483 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3289485 {A : Type'} (t : A -> Prop) (x' : A) : (term38 A t x') = (term104 A t x').
Proof. exact (@lem3289483 (t x')). Qed.
Lemma lem3289488 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term89 A x s t x') : term104 A t x'.
Proof. exact (EQ_MP (@lem3289485 A t x') (@lem3289274 A x s t x' h1)). Qed.
Lemma lem3289491 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : False.
Proof. exact (@lem3289488 A x s t x' h2 (@lem3289480 A t x' h1)). Qed.
Lemma lem3289492 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : term105.
Proof. exact (fun h0 : ~ False => @lem3289491 A x s t x' h1 h2). Qed.
Lemma lem3289494 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289495 : term105 = False.
Proof. exact (@lem3289494 False). Qed.
Lemma lem3289496 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289495) (@lem3289492 A x s t x' h1 h2)). Qed.
Lemma lem3289524 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : s x'.
Proof. exact (proj1 (@lem3289139 A x s t x' h1)). Qed.
Lemma lem3289525 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term102 A s x'.
Proof. exact (fun h0 : term38 A s x' => @lem3289524 A x s t x' h1). Qed.
Lemma lem3289527 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289528 {A : Type'} (s : A -> Prop) (x' : A) : (term102 A s x') = (s x').
Proof. exact (@lem3289527 (s x')). Qed.
Lemma lem3289529 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : s x'.
Proof. exact (EQ_MP (@lem3289528 A s x') (@lem3289525 A x s t x' h1)). Qed.
Lemma lem3289532 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3289534 {A : Type'} (s : A -> Prop) (x' : A) : (term38 A s x') = (term104 A s x').
Proof. exact (@lem3289532 (s x')). Qed.
Lemma lem3289537 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term104 A s x'.
Proof. exact (EQ_MP (@lem3289534 A s x') (@lem3289288 A x s x' h1)). Qed.
Lemma lem3289540 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term72 A x s x') (h2 : term86 A x s t x') : False.
Proof. exact (@lem3289537 A x s x' h1 (@lem3289529 A x s t x' h2)). Qed.
Lemma lem3289541 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term72 A x s x') (h2 : term86 A x s t x') : term105.
Proof. exact (fun h0 : ~ False => @lem3289540 A x s t x' h1 h2). Qed.
Lemma lem3289543 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289544 : term105 = False.
Proof. exact (@lem3289543 False). Qed.
Lemma lem3289545 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term72 A x s x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289544) (@lem3289541 A x s t x' h1 h2)). Qed.
Lemma lem3289547 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3289548 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term102 A t x'.
Proof. exact (fun h0 : term38 A t x' => @lem3289547 A t x' h1). Qed.
Lemma lem3289550 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289551 {A : Type'} (t : A -> Prop) (x' : A) : (term102 A t x') = (t x').
Proof. exact (@lem3289550 (t x')). Qed.
Lemma lem3289552 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3289551 A t x') (@lem3289548 A t x' h1)). Qed.
Lemma lem3289555 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3289557 {A : Type'} (t : A -> Prop) (x' : A) : (term38 A t x') = (term104 A t x').
Proof. exact (@lem3289555 (t x')). Qed.
Lemma lem3289560 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term104 A t x'.
Proof. exact (EQ_MP (@lem3289557 A t x') (@lem3289294 A x s t x' h1)). Qed.
Lemma lem3289563 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (@lem3289560 A x s t x' h2 (@lem3289552 A t x' h1)). Qed.
Lemma lem3289564 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : term105.
Proof. exact (fun h0 : ~ False => @lem3289563 A x s t x' h1 h2). Qed.
Lemma lem3289566 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3289567 : term105 = False.
Proof. exact (@lem3289566 False). Qed.
Lemma lem3289568 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289567) (@lem3289564 A x s t x' h1 h2)). Qed.
Lemma lem3289569 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289449) (@lem3289446 A s t x' x h1 h2 h3)). Qed.
Lemma lem3289570 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3289427 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289324 A t x h1)). Qed.
Lemma lem3289572 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289570 A s t x' x h1 h2 h3) (@lem3289324 A t x h1)). Qed.
Lemma lem3289573 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3289568 A x s t x' h1 h2) (fun h3 : False => @lem3289296 A t x' h1)). Qed.
Lemma lem3289574 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289573 A x s t x' h1 h2) (@lem3289296 A t x' h1)). Qed.
Lemma lem3289575 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3289496 A x s t x' h1 h2) (fun h3 : False => @lem3289278 A t x' h1)). Qed.
Lemma lem3289576 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289575 A x s t x' h1 h2) (@lem3289278 A t x' h1)). Qed.
Lemma lem3289577 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (term38 A s x') = False.
Proof. exact (prop_ext (fun h3 : term38 A s x' => @lem3289473 A s x' h1 h2) (fun h3 : False => @lem3289270 A s x' h1)). Qed.
Lemma lem3289578 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3289577 A s x' h1 h2) (@lem3289270 A s x' h1)). Qed.
Lemma lem3289579 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3289578 A s x' h1 h2) (fun h3 : False => @lem3289268 A s x' h2)). Qed.
Lemma lem3289580 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3289579 A s x' h1 h2) (@lem3289268 A s x' h2)). Qed.
Lemma lem3289581 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3289569 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289262 A t x' h1)). Qed.
Lemma lem3289582 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289581 A s t x' x h1 h2 h3) (@lem3289262 A t x' h1)). Qed.
Lemma lem3289583 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3289582 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289260 A x' x h3)). Qed.
Lemma lem3289584 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289583 A s t x' x h1 h2 h3) (@lem3289260 A x' x h3)). Qed.
Lemma lem3289585 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3289572 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289252 A x' x h3)). Qed.
Lemma lem3289586 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289585 A s t x' x h1 h2 h3) (@lem3289252 A x' x h3)). Qed.
Lemma lem3289587 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3289586 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289248 A t x h1)). Qed.
Lemma lem3289588 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289587 A s t x' x h1 h2 h3) (@lem3289248 A t x h1)). Qed.
Lemma lem3289589 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3289574 A x s t x' h1 h2) (fun h3 : False => @lem3289246 A t x' h1)). Qed.
Lemma lem3289590 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289589 A x s t x' h1 h2) (@lem3289246 A t x' h1)). Qed.
Lemma lem3289591 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3289576 A x s t x' h1 h2) (fun h3 : False => @lem3289210 A t x' h1)). Qed.
Lemma lem3289592 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289591 A x s t x' h1 h2) (@lem3289210 A t x' h1)). Qed.
Lemma lem3289593 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (term38 A s x') = False.
Proof. exact (prop_ext (fun h3 : term38 A s x' => @lem3289580 A s x' h1 h2) (fun h3 : False => @lem3289194 A s x' h1)). Qed.
Lemma lem3289594 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3289593 A s x' h1 h2) (@lem3289194 A s x' h1)). Qed.
Lemma lem3289595 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3289594 A s x' h1 h2) (fun h3 : False => @lem3289190 A s x' h2)). Qed.
Lemma lem3289596 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3289595 A s x' h1 h2) (@lem3289190 A s x' h2)). Qed.
Lemma lem3289597 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3289584 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289178 A t x' h1)). Qed.
Lemma lem3289598 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289597 A s t x' x h1 h2 h3) (@lem3289178 A t x' h1)). Qed.
Lemma lem3289599 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3289598 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289174 A x' x h3)). Qed.
Lemma lem3289600 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289599 A s t x' x h1 h2 h3) (@lem3289174 A x' x h3)). Qed.
Lemma lem3289601 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3289588 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289158 A x' x h3)). Qed.
Lemma lem3289602 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289601 A s t x' x h1 h2 h3) (@lem3289158 A x' x h3)). Qed.
Lemma lem3289603 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3289602 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289150 A t x h1)). Qed.
Lemma lem3289604 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289603 A s t x' x h1 h2 h3) (@lem3289150 A t x h1)). Qed.
Lemma lem3289605 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3289590 A x s t x' h1 h2) (fun h3 : False => @lem3289246 A t x' h1)). Qed.
Lemma lem3289606 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289605 A x s t x' h1 h2) (@lem3289246 A t x' h1)). Qed.
Lemma lem3289607 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3289592 A x s t x' h1 h2) (fun h3 : False => @lem3289210 A t x' h1)). Qed.
Lemma lem3289608 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term89 A x s t x') : False.
Proof. exact (EQ_MP (@lem3289607 A x s t x' h1 h2) (@lem3289210 A t x' h1)). Qed.
Lemma lem3289609 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (term38 A s x') = False.
Proof. exact (prop_ext (fun h3 : term38 A s x' => @lem3289596 A s x' h1 h2) (fun h3 : False => @lem3289194 A s x' h1)). Qed.
Lemma lem3289610 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3289609 A s x' h1 h2) (@lem3289194 A s x' h1)). Qed.
Lemma lem3289611 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3289610 A s x' h1 h2) (fun h3 : False => @lem3289190 A s x' h2)). Qed.
Lemma lem3289612 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3289611 A s x' h1 h2) (@lem3289190 A s x' h2)). Qed.
Lemma lem3289613 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3289600 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289178 A t x' h1)). Qed.
Lemma lem3289614 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289613 A s t x' x h1 h2 h3) (@lem3289178 A t x' h1)). Qed.
Lemma lem3289615 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3289614 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289174 A x' x h3)). Qed.
Lemma lem3289616 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289615 A s t x' x h1 h2 h3) (@lem3289174 A x' x h3)). Qed.
Lemma lem3289617 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3289604 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289158 A x' x h3)). Qed.
Lemma lem3289618 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289617 A s t x' x h1 h2 h3) (@lem3289158 A x' x h3)). Qed.
Lemma lem3289619 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3289618 A s t x' x h1 h2 h3) (fun h4 : False => @lem3289150 A t x h1)). Qed.
Lemma lem3289620 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3289619 A s t x' x h1 h2 h3) (@lem3289150 A t x h1)). Qed.
Lemma lem3289621 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : False.
Proof. exact (or_elim (@lem3289140 A x s t x' h1) (fun h0 : term72 A x s x' => @lem3289545 A x s t x' h0 h1) (fun h0 : t x' => @lem3289606 A x s t x' h0 h1)). Qed.
Lemma lem3289622 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term89 A x s t x') : False.
Proof. exact (or_elim (@lem3289129 A x s t x' h2) (fun h0 : term38 A s x' => @lem3289612 A s x' h0 h1) (fun h0 : t x' => @lem3289608 A x s t x' h0 h2)). Qed.
Lemma lem3289623 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term89 A x s t x') (h3 : x' = x) : False.
Proof. exact (or_elim (@lem3289129 A x s t x' h2) (fun h0 : term38 A s x' => @lem3289620 A s t x' x h1 h2 h3) (fun h0 : t x' => @lem3289616 A s t x' x h0 h2 h3)). Qed.
Lemma lem3289624 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x) (h2 : term89 A x s t x') : False.
Proof. exact (or_elim (@lem3289132 A x s t x' h2) (fun h0 : x' = x => @lem3289623 A s t x' x h1 h2 h0) (fun h0 : s x' => @lem3289622 A x s t x' h0 h2)). Qed.
Lemma lem3289625 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term70 A x s t x') (h2 : t x) : False.
Proof. exact (or_elim (@lem3289126 A x s t x' h1) (fun h0 : term89 A x s t x' => @lem3289624 A x s t x' h2 h0) (fun h0 : term86 A x s t x' => @lem3289621 A x s t x' h0)). Qed.
Lemma lem3289626 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term70 A x s t x') (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3289625 A s x' t x h1 h2) (fun h3 : False => @lem3289054 A t x h2)). Qed.
Lemma lem3289627 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term70 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3289626 A s x' t x h1 h2) (@lem3289054 A t x h2)). Qed.
Lemma lem3289628 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term70 A x s t x') (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3289627 A s x' t x h1 h2) (fun h3 : False => @lem3288996 A t x h2)). Qed.
Lemma lem3289629 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term70 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3289628 A s x' t x h1 h2) (@lem3288996 A t x h2)). Qed.
Lemma lem3289630 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term70 A x s t x') (h2 : t x) : (term70 A x s t x') = False.
Proof. exact (prop_ext (fun h3 : term70 A x s t x' => @lem3289629 A s x' t x h1 h2) (fun h3 : False => @lem3288990 A x s t x' h1)). Qed.
Lemma lem3289631 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term70 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3289630 A s x' t x h1 h2) (@lem3288990 A x s t x' h1)). Qed.
Lemma lem3289632 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) : term69 A x s t x'.
Proof. exact (fun h0 : term70 A x s t x' => @lem3289631 A s x' t x h0 h1). Qed.
Lemma lem3289633 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) : (term39 A x s t x') = (term44 A s t x').
Proof. exact (EQ_MP (@lem3288989 A x s t x') (@lem3289632 A s x' t x h1)). Qed.
Lemma lem3289638 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) : term47 A x s t.
Proof. exact (fun x' : A => @lem3289633 A s x' t x h1). Qed.
Lemma lem3289639 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term48 A x s t.
Proof. exact (fun h0 : t x => @lem3289638 A s t x h0). Qed.
Lemma lem3289644 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term60 A s t.
Proof. exact (fun x : A => @lem3289639 A x s t). Qed.
Lemma lem3289649 {A : Type'} (t : A -> Prop) : term64 A t.
Proof. exact (fun s : A -> Prop => @lem3289644 A s t). Qed.
Lemma lem3289654 {A : Type'} : term68 A.
Proof. exact (fun t : A -> Prop => @lem3289649 A t). Qed.
Lemma lem3289655 {A : Type'} : term67 A.
Proof. exact (EQ_MP (@lem3288984 A) (@lem3289654 A)). Qed.
Lemma lem3289656 {A : Type'} (t : A -> Prop) : term106 A t.
Proof. exact (@lem3289655 A t). Qed.
Lemma lem3289657 {A : Type'} (t : A -> Prop) : (term106 A t) = (term63 A t).
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3289658 {A : Type'} (t : A -> Prop) : term63 A t.
Proof. exact (EQ_MP (@lem3289657 A t) (@lem3289656 A t)). Qed.
Lemma lem3289659 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term107 A t s.
Proof. exact (@lem3289658 A t s). Qed.
Lemma lem3289660 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A t s) = (term59 A s t).
Proof. exact (eq_refl (term107 A t s)). Qed.
Lemma lem3289661 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term59 A s t.
Proof. exact (EQ_MP (@lem3289660 A s t) (@lem3289659 A t s)). Qed.
Lemma lem3289662 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term108 A s t x.
Proof. exact (@lem3289661 A s t x). Qed.
Lemma lem3289663 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term108 A s t x) = (term50 A x s t).
Proof. exact (eq_refl (term108 A s t x)). Qed.
Lemma lem3289664 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term50 A x s t.
Proof. exact (EQ_MP (@lem3289663 A x s t) (@lem3289662 A s t x)). Qed.
Lemma lem3289666 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term50 A x s t.
Proof. exact (@lem3288855 A x s t (@lem3289664 A x s t)). Qed.
Lemma lem3289667 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term51 A x s t) : False.
Proof. exact (@lem3289666 A x s t (@lem3288839 A x s t h1)). Qed.
Lemma lem3289668 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term51 A x s t) : (term51 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term51 A x s t => @lem3289667 A x s t h1) (fun h2 : False => @lem3288839 A x s t h1)). Qed.
Lemma lem3289669 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term51 A x s t) : False.
Proof. exact (EQ_MP (@lem3289668 A x s t h1) (@lem3288839 A x s t h1)). Qed.
Lemma lem3289670 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term50 A x s t.
Proof. exact (fun h0 : term51 A x s t => @lem3289669 A x s t h0). Qed.
Lemma lem3289671 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term48 A x s t.
Proof. exact (EQ_MP (@lem3288838 A x s t) (@lem3289670 A x s t)). Qed.
Lemma lem3289672 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term26 A x s t.
Proof. exact (EQ_MP (@lem3288834 A x s t) (@lem3289671 A x s t)). Qed.
Lemma lem3289673 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term16 A x s t.
Proof. exact (EQ_MP (@lem3288747 A x s t) (@lem3289672 A x s t)). Qed.
Lemma lem3289679 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3289680 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (@lem3289679 A s t). Qed.
Lemma lem3289681 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (term7 A x s t)) = (term109 A x s t).
Proof. exact (@lem3289680 A (term9 A x s t) (term7 A x s t)). Qed.
Lemma lem3289690 {A : Type'} (x : A) (t : A -> Prop) : (term10 A x t) = (term10 A x t).
Proof. exact (eq_refl (term10 A x t)). Qed.
Lemma lem3289691 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term12 A x s t) = (term110 A x s t).
Proof. exact (MK_COMB (@lem3289690 A x t) (@lem3289681 A x s t)). Qed.
Lemma lem3289694 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term110 A x s t) = (term12 A x s t).
Proof. exact (SYM (@lem3289691 A x s t)). Qed.
Lemma lem3289698 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3289699 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3289698 A P x). Qed.
Lemma lem3289700 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3289699 A t x). Qed.
Lemma lem3289701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3289702 {A : Type'} (t : A -> Prop) (x : A) : (term23 A x t) = (term38 A t x).
Proof. exact (MK_COMB (@lem3289701) (@lem3289700 A t x)). Qed.
Lemma lem3289703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3289704 {A : Type'} (t : A -> Prop) (x : A) : (term10 A x t) = (term111 A t x).
Proof. exact (MK_COMB (@lem3289703) (@lem3289702 A t x)). Qed.
Lemma lem3289712 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3289713 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3289712 A s x t). Qed.
Lemma lem3289714 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term30 A x' x s t) = (term31 A x s x' t).
Proof. exact (@lem3289713 A (@INSERT A x s) x' t). Qed.
Lemma lem3289718 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3289719 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3289718 A y x s). Qed.
Lemma lem3289720 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term32 A x' x s) = (term33 A x x' s).
Proof. exact (@lem3289719 A x x' s). Qed.
Lemma lem3289726 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3289727 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3289726 A P x). Qed.
Lemma lem3289728 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3289727 A s x'). Qed.
Lemma lem3289729 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3289730 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term33 A x x' s) = (term35 A x s x').
Proof. exact (MK_COMB (@lem3289729 A x' x) (@lem3289728 A s x')). Qed.
Lemma lem3289733 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x' x s) = (term35 A x s x').
Proof. exact (TRANS (@lem3289720 A x x' s) (@lem3289730 A x s x')). Qed.
Lemma lem3289734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3289735 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term36 A x' x s) = (term37 A x s x').
Proof. exact (MK_COMB (@lem3289734) (@lem3289733 A x s x')). Qed.
Lemma lem3289737 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3289738 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3289737 A P x). Qed.
Lemma lem3289739 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3289738 A t x'). Qed.
Lemma lem3289740 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3289741 {A : Type'} (t : A -> Prop) (x' : A) : (term23 A x' t) = (term38 A t x').
Proof. exact (MK_COMB (@lem3289740) (@lem3289739 A t x')). Qed.
Lemma lem3289742 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term31 A x s x' t) = (term39 A x s t x').
Proof. exact (MK_COMB (@lem3289735 A x s x') (@lem3289741 A t x')). Qed.
Lemma lem3289745 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term30 A x' x s t) = (term39 A x s t x').
Proof. exact (TRANS (@lem3289714 A x s x' t) (@lem3289742 A x s t x')). Qed.
Lemma lem3289746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3289747 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term40 A x' x s t) = (term41 A x s t x').
Proof. exact (MK_COMB (@lem3289746) (@lem3289745 A x s t x')). Qed.
Lemma lem3289749 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3289750 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3289749 A y x s). Qed.
Lemma lem3289751 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x' x s t) = (term113 A x x' s t).
Proof. exact (@lem3289750 A x x' (@DIFF A s t)). Qed.
Lemma lem3289757 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3289758 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3289757 A s x t). Qed.
Lemma lem3289759 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term28 A x' s t) = (term29 A s x' t).
Proof. exact (@lem3289758 A s x' t). Qed.
Lemma lem3289763 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3289764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3289763 A P x). Qed.
Lemma lem3289765 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3289764 A s x'). Qed.
Lemma lem3289766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3289767 {A : Type'} (s : A -> Prop) (x' : A) : (term42 A x' s) = (term43 A s x').
Proof. exact (MK_COMB (@lem3289766) (@lem3289765 A s x')). Qed.
Lemma lem3289769 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3289770 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3289769 A P x). Qed.
Lemma lem3289771 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3289770 A t x'). Qed.
Lemma lem3289772 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3289773 {A : Type'} (t : A -> Prop) (x' : A) : (term23 A x' t) = (term38 A t x').
Proof. exact (MK_COMB (@lem3289772) (@lem3289771 A t x')). Qed.
Lemma lem3289774 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term29 A s x' t) = (term44 A s t x').
Proof. exact (MK_COMB (@lem3289767 A s x') (@lem3289773 A t x')). Qed.
Lemma lem3289777 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term28 A x' s t) = (term44 A s t x').
Proof. exact (TRANS (@lem3289759 A s x' t) (@lem3289774 A s t x')). Qed.
Lemma lem3289778 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3289779 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term113 A x x' s t) = (term114 A x s t x').
Proof. exact (MK_COMB (@lem3289778 A x' x) (@lem3289777 A s t x')). Qed.
Lemma lem3289782 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term112 A x' x s t) = (term114 A x s t x').
Proof. exact (TRANS (@lem3289751 A x x' s t) (@lem3289779 A x s t x')). Qed.
Lemma lem3289783 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term30 A x' x s t) = (term112 A x' x s t)) = ((term39 A x s t x') = (term114 A x s t x')).
Proof. exact (MK_COMB (@lem3289747 A x s t x') (@lem3289782 A x s t x')). Qed.
Lemma lem3289786 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term115 A x s t) = (term116 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3289783 A x s t x')). Qed.
Lemma lem3289787 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3289788 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term109 A x s t) = (term117 A x s t).
Proof. exact (MK_COMB (@lem3289787 A) (@lem3289786 A x s t)). Qed.
Lemma lem3289793 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term110 A x s t) = (term118 A x s t).
Proof. exact (MK_COMB (@lem3289704 A t x) (@lem3289788 A x s t)). Qed.
Lemma lem3289796 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term118 A x s t) = (term110 A x s t).
Proof. exact (SYM (@lem3289793 A x s t)). Qed.
Lemma lem3289798 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3289799 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term118 A x s t) = (term119 A x s t).
Proof. exact (@lem3289798 (term118 A x s t)). Qed.
Lemma lem3289800 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term119 A x s t) = (term118 A x s t).
Proof. exact (SYM (@lem3289799 A x s t)). Qed.
Lemma lem3289801 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term120 A x s t) : term120 A x s t.
Proof. exact (h1). Qed.
Lemma lem3289804 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) : term119 A x s t.
Proof. exact (h1). Qed.
Lemma lem3289805 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term121 A x s t.
Proof. exact (fun h0 : term119 A x s t => @lem3289804 A x s t h0). Qed.
Lemma lem3289806 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term121 A x s t) : term121 A x s t.
Proof. exact (h1). Qed.
Lemma lem3289807 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) : term119 A x s t.
Proof. exact (h1). Qed.
Lemma lem3289808 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) (h2 : term121 A x s t) : term119 A x s t.
Proof. exact (@lem3289806 A x s t h2 (@lem3289807 A x s t h1)). Qed.
Lemma lem3289809 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) : term122 A x s t.
Proof. exact (fun h0 : term121 A x s t => @lem3289808 A x s t h1 h0). Qed.
Lemma lem3289810 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term121 A x s t) : term121 A x s t.
Proof. exact (h1). Qed.
Lemma lem3289811 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term119 A x s t) (h2 : term121 A x s t) : term119 A x s t.
Proof. exact (@lem3289809 A x s t h1 (@lem3289810 A x s t h2)). Qed.
Lemma lem3289812 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term121 A x s t) : term121 A x s t.
Proof. exact (fun h0 : term119 A x s t => @lem3289811 A x s t h0 h1). Qed.
Lemma lem3289813 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term123 A x s t.
Proof. exact (fun h0 : term121 A x s t => @lem3289812 A x s t h0). Qed.
Lemma lem3289816 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term121 A x s t.
Proof. exact (@lem3289813 A x s t (@lem3289805 A x s t)). Qed.
Lemma lem3289817 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term121 A x s t.
Proof. exact (@lem3289816 A x s t). Qed.
Lemma lem3289831 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3289832 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term119 A x s t) = (term124 A x s t).
Proof. exact (@lem3289831 (term120 A x s t)). Qed.
Lemma lem3289834 (t : Prop) : (term56 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3289835 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term124 A x s t) = (term118 A x s t).
Proof. exact (@lem3289834 (term118 A x s t)). Qed.
Lemma lem3289838 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term119 A x s t) = (term118 A x s t).
Proof. exact (TRANS (@lem3289832 A x s t) (@lem3289835 A x s t)). Qed.
Lemma lem3289851 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term126 A s t).
Proof. exact (fun_ext (fun x : A => @lem3289838 A x s t)). Qed.
Lemma lem3289852 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3289853 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term127 A s t) = (term128 A s t).
Proof. exact (MK_COMB (@lem3289852 A) (@lem3289851 A s t)). Qed.
Lemma lem3289858 {A : Type'} (t : A -> Prop) : (term129 A t) = (term130 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3289853 A s t)). Qed.
Lemma lem3289859 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3289860 {A : Type'} (t : A -> Prop) : (term131 A t) = (term132 A t).
Proof. exact (MK_COMB (@lem3289859 A) (@lem3289858 A t)). Qed.
Lemma lem3289865 {A : Type'} : (term133 A) = (term134 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3289860 A t)). Qed.
Lemma lem3289866 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3289875 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (MK_COMB (@lem3289866 A) (@lem3289865 A)). Qed.
Lemma lem3289900 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term39 A x s t x') = (term114 A x s t x')) = ((term39 A x s t x') = (term114 A x s t x')).
Proof. exact (eq_refl ((term39 A x s t x') = (term114 A x s t x'))). Qed.
Lemma lem3289901 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term116 A x s t) = (term116 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3289900 A x s t x')). Qed.
Lemma lem3289902 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3289903 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term117 A x s t) = (term117 A x s t).
Proof. exact (MK_COMB (@lem3289902 A) (@lem3289901 A x s t)). Qed.
Lemma lem3289908 {A : Type'} (t : A -> Prop) (x : A) : (term111 A t x) = (term111 A t x).
Proof. exact (eq_refl (term111 A t x)). Qed.
Lemma lem3289909 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term118 A x s t) = (term118 A x s t).
Proof. exact (MK_COMB (@lem3289908 A t x) (@lem3289903 A x s t)). Qed.
Lemma lem3289910 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term126 A s t).
Proof. exact (fun_ext (fun x : A => @lem3289909 A x s t)). Qed.
Lemma lem3289911 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3289912 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term128 A s t) = (term128 A s t).
Proof. exact (MK_COMB (@lem3289911 A) (@lem3289910 A s t)). Qed.
Lemma lem3289913 {A : Type'} (t : A -> Prop) : (term130 A t) = (term130 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3289912 A s t)). Qed.
Lemma lem3289914 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3289915 {A : Type'} (t : A -> Prop) : (term132 A t) = (term132 A t).
Proof. exact (MK_COMB (@lem3289914 A) (@lem3289913 A t)). Qed.
Lemma lem3289916 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3289915 A t)). Qed.
Lemma lem3289917 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3289918 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (MK_COMB (@lem3289917 A) (@lem3289916 A)). Qed.
Lemma lem3289955 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (TRANS (@lem3289875 A) (@lem3289918 A)). Qed.
Lemma lem3289956 {A : Type'} : (term136 A) = (term135 A).
Proof. exact (SYM (@lem3289955 A)). Qed.
Lemma lem3289959 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3289960 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term39 A x s t x') = (term114 A x s t x')) = (term137 A x s t x').
Proof. exact (@lem3289959 ((term39 A x s t x') = (term114 A x s t x'))). Qed.
Lemma lem3289961 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term137 A x s t x') = ((term39 A x s t x') = (term114 A x s t x')).
Proof. exact (SYM (@lem3289960 A x s t x')). Qed.
Lemma lem3289962 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term138 A x s t x') : term138 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3289968 {A : Type'} (t : A -> Prop) (x : A) (h1 : term38 A t x) : term38 A t x.
Proof. exact (h1). Qed.
Lemma lem3289977 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term71 A x s x') = (term72 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3289984 {A : Type'} (t : A -> Prop) (x' : A) : (term73 A t x') = (t x').
Proof. exact (@lem16933 (t x')). Qed.
Lemma lem3289985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3289986 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term74 A x s x') = (term75 A x s x').
Proof. exact (MK_COMB (@lem3289985) (@lem3289977 A x s x')). Qed.
Lemma lem3289987 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term76 A x s t x') = (term77 A x s t x').
Proof. exact (MK_COMB (@lem3289986 A x s x') (@lem3289984 A t x')). Qed.
Lemma lem3289988 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term78 A x s t x') = (term76 A x s t x').
Proof. exact (@lem17045 (term35 A x s x') (term38 A t x')). Qed.
Lemma lem3289989 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term78 A x s t x') = (term77 A x s t x').
Proof. exact (TRANS (@lem3289988 A x s t x') (@lem3289987 A x s t x')). Qed.
Lemma lem3290000 {A : Type'} (t : A -> Prop) (x' : A) : (term73 A t x') = (t x').
Proof. exact (@lem16933 (t x')). Qed.
Lemma lem3290002 {A : Type'} (s : A -> Prop) (x' : A) : (term79 A s x') = (term79 A s x').
Proof. exact (eq_refl (term79 A s x')). Qed.
Lemma lem3290003 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term80 A s t x') = (term81 A s t x').
Proof. exact (MK_COMB (@lem3290002 A s x') (@lem3290000 A t x')). Qed.
Lemma lem3290004 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A s t x') = (term80 A s t x').
Proof. exact (@lem17045 (s x') (term38 A t x')). Qed.
Lemma lem3290005 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A s t x') = (term81 A s t x').
Proof. exact (TRANS (@lem3290004 A s t x') (@lem3290003 A s t x')). Qed.
Lemma lem3290010 {A : Type'} (x' : A) (x : A) : (term139 A x' x) = (term139 A x' x).
Proof. exact (eq_refl (term139 A x' x)). Qed.
Lemma lem3290011 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term140 A x s t x') = (term141 A x s t x').
Proof. exact (MK_COMB (@lem3290010 A x' x) (@lem3290005 A s t x')). Qed.
Lemma lem3290012 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term142 A x s t x') = (term140 A x s t x').
Proof. exact (@lem17160 (x' = x) (term44 A s t x')). Qed.
Lemma lem3290013 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term142 A x s t x') = (term141 A x s t x').
Proof. exact (TRANS (@lem3290012 A x s t x') (@lem3290011 A x s t x')). Qed.
Lemma lem3290016 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term114 A x s t x') = (term114 A x s t x').
Proof. exact (eq_refl (term114 A x s t x')). Qed.
Lemma lem3290017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3290018 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term83 A x s t x') = (term84 A x s t x').
Proof. exact (MK_COMB (@lem3290017) (@lem3289989 A x s t x')). Qed.
Lemma lem3290019 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term143 A x s t x') = (term144 A x s t x').
Proof. exact (MK_COMB (@lem3290018 A x s t x') (@lem3290016 A x s t x')). Qed.
Lemma lem3290021 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term87 A x s t x') = (term87 A x s t x').
Proof. exact (eq_refl (term87 A x s t x')). Qed.
Lemma lem3290022 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term145 A x s t x') = (term146 A x s t x').
Proof. exact (MK_COMB (@lem3290021 A x s t x') (@lem3290013 A x s t x')). Qed.
Lemma lem3290023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3290024 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term147 A x s t x') = (term148 A x s t x').
Proof. exact (MK_COMB (@lem3290023) (@lem3290022 A x s t x')). Qed.
Lemma lem3290025 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term149 A x s t x') = (term150 A x s t x').
Proof. exact (MK_COMB (@lem3290024 A x s t x') (@lem3290019 A x s t x')). Qed.
Lemma lem3290026 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term138 A x s t x') = (term149 A x s t x').
Proof. exact (@lem17646 (term39 A x s t x') (term114 A x s t x')). Qed.
Lemma lem3290031 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term138 A x s t x') = (term150 A x s t x').
Proof. exact (TRANS (@lem3290026 A x s t x') (@lem3290025 A x s t x')). Qed.
Lemma lem3290038 {A : Type'} (t : A -> Prop) (x : A) (h1 : term38 A t x) : term38 A t x.
Proof. exact (h1). Qed.
Lemma lem3290128 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term138 A x s t x') : term150 A x s t x'.
Proof. exact (EQ_MP (@lem3290031 A x s t x') (@lem3289962 A x s t x' h1)). Qed.
Lemma lem3290129 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term146 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3290130 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term144 A x s t x') : term144 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3290131 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term141 A x s t x'.
Proof. exact (proj2 (@lem3290129 A x s t x' h1)). Qed.
Lemma lem3290132 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term39 A x s t x'.
Proof. exact (proj1 (@lem3290129 A x s t x' h1)). Qed.
Lemma lem3290133 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term81 A s t x'.
Proof. exact (proj2 (@lem3290131 A x s t x' h1)). Qed.
Lemma lem3290136 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term35 A x s x'.
Proof. exact (proj1 (@lem3290132 A x s t x' h1)). Qed.
Lemma lem3290143 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term144 A x s t x') : term114 A x s t x'.
Proof. exact (proj2 (@lem3290130 A x s t x' h1)). Qed.
Lemma lem3290144 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term144 A x s t x') : term77 A x s t x'.
Proof. exact (proj1 (@lem3290130 A x s t x' h1)). Qed.
Lemma lem3290146 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : term44 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3290147 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term72 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3290153 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term72 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3290172 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3290192 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3290196 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290212 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3290216 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') : term38 A s x'.
Proof. exact (h1). Qed.
Lemma lem3290236 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290244 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3290256 {A : Type'} (t : A -> Prop) (x : A) (h1 : term38 A t x) : term38 A t x.
Proof. exact (h1). Qed.
Lemma lem3290260 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3290264 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290300 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290304 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term151 A x' x.
Proof. exact (proj1 (@lem3290131 A x s t x' h1)). Qed.
Lemma lem3290308 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3290316 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term38 A t x'.
Proof. exact (proj2 (@lem3290132 A x s t x' h1)). Qed.
Lemma lem3290318 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3290320 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290328 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3290330 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') : term38 A s x'.
Proof. exact (h1). Qed.
Lemma lem3290336 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term38 A t x'.
Proof. exact (proj2 (@lem3290132 A x s t x' h1)). Qed.
Lemma lem3290340 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290344 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3290346 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term151 A x' x.
Proof. exact (proj1 (@lem3290147 A x s x' h1)). Qed.
Lemma lem3290350 {A : Type'} (t : A -> Prop) (x : A) (h1 : term38 A t x) : term38 A t x.
Proof. exact (h1). Qed.
Lemma lem3290352 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3290354 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290364 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term38 A s x'.
Proof. exact (proj2 (@lem3290153 A x s x' h1)). Qed.
Lemma lem3290370 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : term38 A t x'.
Proof. exact (proj2 (@lem3290146 A s t x' h1)). Qed.
Lemma lem3290372 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290401 {A : Type'} (x : A) : (term152 A x) = (term152 A x).
Proof. exact (eq_refl (term152 A x)). Qed.
Lemma lem3290402 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term153 A x x') = (term154 A x).
Proof. exact (MK_COMB (@lem3290401 A x) (@lem3290308 A x' x h1)). Qed.
Lemma lem3290403 {A : Type'} (x : A) : (term154 A x) = (term155 A x).
Proof. exact (eq_refl (term154 A x)). Qed.
Lemma lem3290404 {A : Type'} (x : A) (x' : A) : (term156 A x x') = (term156 A x x').
Proof. exact (eq_refl (term156 A x x')). Qed.
Lemma lem3290405 {A : Type'} (x' : A) (x : A) : ((term153 A x x') = (term154 A x)) = ((term153 A x x') = (term155 A x)).
Proof. exact (MK_COMB (@lem3290404 A x x') (@lem3290403 A x)). Qed.
Lemma lem3290406 {A : Type'} (x' : A) (x : A) : (term153 A x x') = (term151 A x' x).
Proof. exact (eq_refl (term153 A x x')). Qed.
Lemma lem3290407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3290408 {A : Type'} (x' : A) (x : A) : (term156 A x x') = (term157 A x' x).
Proof. exact (MK_COMB (@lem3290407) (@lem3290406 A x' x)). Qed.
Lemma lem3290409 {A : Type'} (x : A) : (term155 A x) = (term155 A x).
Proof. exact (eq_refl (term155 A x)). Qed.
Lemma lem3290410 {A : Type'} (x' : A) (x : A) : ((term153 A x x') = (term155 A x)) = ((term151 A x' x) = (term155 A x)).
Proof. exact (MK_COMB (@lem3290408 A x' x) (@lem3290409 A x)). Qed.
Lemma lem3290411 {A : Type'} (x' : A) (x : A) : ((term153 A x x') = (term154 A x)) = ((term151 A x' x) = (term155 A x)).
Proof. exact (TRANS (@lem3290405 A x' x) (@lem3290410 A x' x)). Qed.
Lemma lem3290412 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term151 A x' x) = (term155 A x).
Proof. exact (EQ_MP (@lem3290411 A x' x) (@lem3290402 A x' x h1)). Qed.
Lemma lem3290413 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : term155 A x.
Proof. exact (EQ_MP (@lem3290412 A x' x h2) (@lem3290304 A x s t x' h1)). Qed.
Lemma lem3290481 {A : Type'} (t : A -> Prop) : (term94 A t) = (term94 A t).
Proof. exact (eq_refl (term94 A t)). Qed.
Lemma lem3290482 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term95 A t x') = (term95 A t x).
Proof. exact (MK_COMB (@lem3290481 A t) (@lem3290318 A x' x h1)). Qed.
Lemma lem3290483 {A : Type'} (t : A -> Prop) (x : A) : (term95 A t x) = (term38 A t x).
Proof. exact (eq_refl (term95 A t x)). Qed.
Lemma lem3290484 {A : Type'} (t : A -> Prop) (x' : A) : (term96 A t x') = (term96 A t x').
Proof. exact (eq_refl (term96 A t x')). Qed.
Lemma lem3290485 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term95 A t x)) = ((term95 A t x') = (term38 A t x)).
Proof. exact (MK_COMB (@lem3290484 A t x') (@lem3290483 A t x)). Qed.
Lemma lem3290486 {A : Type'} (t : A -> Prop) (x' : A) : (term95 A t x') = (term38 A t x').
Proof. exact (eq_refl (term95 A t x')). Qed.
Lemma lem3290487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3290488 {A : Type'} (t : A -> Prop) (x' : A) : (term96 A t x') = (term97 A t x').
Proof. exact (MK_COMB (@lem3290487) (@lem3290486 A t x')). Qed.
Lemma lem3290489 {A : Type'} (t : A -> Prop) (x : A) : (term38 A t x) = (term38 A t x).
Proof. exact (eq_refl (term38 A t x)). Qed.
Lemma lem3290490 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term38 A t x)) = ((term38 A t x') = (term38 A t x)).
Proof. exact (MK_COMB (@lem3290488 A t x') (@lem3290489 A t x)). Qed.
Lemma lem3290491 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term95 A t x') = (term95 A t x)) = ((term38 A t x') = (term38 A t x)).
Proof. exact (TRANS (@lem3290485 A x' t x) (@lem3290490 A x' t x)). Qed.
Lemma lem3290492 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term38 A t x') = (term38 A t x).
Proof. exact (EQ_MP (@lem3290491 A x' t x) (@lem3290482 A t x' x h1)). Qed.
Lemma lem3290493 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : term38 A t x.
Proof. exact (EQ_MP (@lem3290492 A t x' x h2) (@lem3290316 A x s t x' h1)). Qed.
Lemma lem3290494 {A : Type'} (t : A -> Prop) : (term98 A t) = (term98 A t).
Proof. exact (eq_refl (term98 A t)). Qed.
Lemma lem3290495 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term99 A t x') = (term99 A t x).
Proof. exact (MK_COMB (@lem3290494 A t) (@lem3290318 A x' x h1)). Qed.
Lemma lem3290496 {A : Type'} (t : A -> Prop) (x : A) : (term99 A t x) = (t x).
Proof. exact (eq_refl (term99 A t x)). Qed.
Lemma lem3290497 {A : Type'} (t : A -> Prop) (x' : A) : (term100 A t x') = (term100 A t x').
Proof. exact (eq_refl (term100 A t x')). Qed.
Lemma lem3290498 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (term99 A t x)) = ((term99 A t x') = (t x)).
Proof. exact (MK_COMB (@lem3290497 A t x') (@lem3290496 A t x)). Qed.
Lemma lem3290499 {A : Type'} (t : A -> Prop) (x' : A) : (term99 A t x') = (t x').
Proof. exact (eq_refl (term99 A t x')). Qed.
Lemma lem3290500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3290501 {A : Type'} (t : A -> Prop) (x' : A) : (term100 A t x') = (term101 A t x').
Proof. exact (MK_COMB (@lem3290500) (@lem3290499 A t x')). Qed.
Lemma lem3290502 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3290503 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (t x)) = ((t x') = (t x)).
Proof. exact (MK_COMB (@lem3290501 A t x') (@lem3290502 A t x)). Qed.
Lemma lem3290504 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (term99 A t x)) = ((t x') = (t x)).
Proof. exact (TRANS (@lem3290498 A x' t x) (@lem3290503 A x' t x)). Qed.
Lemma lem3290505 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (t x') = (t x).
Proof. exact (EQ_MP (@lem3290504 A x' t x) (@lem3290495 A t x' x h1)). Qed.
Lemma lem3290535 {A : Type'} (x : A) : (term152 A x) = (term152 A x).
Proof. exact (eq_refl (term152 A x)). Qed.
Lemma lem3290536 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term153 A x x') = (term154 A x).
Proof. exact (MK_COMB (@lem3290535 A x) (@lem3290344 A x' x h1)). Qed.
Lemma lem3290537 {A : Type'} (x : A) : (term154 A x) = (term155 A x).
Proof. exact (eq_refl (term154 A x)). Qed.
Lemma lem3290538 {A : Type'} (x : A) (x' : A) : (term156 A x x') = (term156 A x x').
Proof. exact (eq_refl (term156 A x x')). Qed.
Lemma lem3290539 {A : Type'} (x' : A) (x : A) : ((term153 A x x') = (term154 A x)) = ((term153 A x x') = (term155 A x)).
Proof. exact (MK_COMB (@lem3290538 A x x') (@lem3290537 A x)). Qed.
Lemma lem3290540 {A : Type'} (x' : A) (x : A) : (term153 A x x') = (term151 A x' x).
Proof. exact (eq_refl (term153 A x x')). Qed.
Lemma lem3290541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3290542 {A : Type'} (x' : A) (x : A) : (term156 A x x') = (term157 A x' x).
Proof. exact (MK_COMB (@lem3290541) (@lem3290540 A x' x)). Qed.
Lemma lem3290543 {A : Type'} (x : A) : (term155 A x) = (term155 A x).
Proof. exact (eq_refl (term155 A x)). Qed.
Lemma lem3290544 {A : Type'} (x' : A) (x : A) : ((term153 A x x') = (term155 A x)) = ((term151 A x' x) = (term155 A x)).
Proof. exact (MK_COMB (@lem3290542 A x' x) (@lem3290543 A x)). Qed.
Lemma lem3290545 {A : Type'} (x' : A) (x : A) : ((term153 A x x') = (term154 A x)) = ((term151 A x' x) = (term155 A x)).
Proof. exact (TRANS (@lem3290539 A x' x) (@lem3290544 A x' x)). Qed.
Lemma lem3290546 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term151 A x' x) = (term155 A x).
Proof. exact (EQ_MP (@lem3290545 A x' x) (@lem3290536 A x' x h1)). Qed.
Lemma lem3290547 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : term155 A x.
Proof. exact (EQ_MP (@lem3290546 A x' x h2) (@lem3290346 A x s x' h1)). Qed.
Lemma lem3290588 {A : Type'} (t : A -> Prop) (x : A) (h1 : term38 A t x) : term38 A t x.
Proof. exact (h1). Qed.
Lemma lem3290589 {A : Type'} (t : A -> Prop) : (term98 A t) = (term98 A t).
Proof. exact (eq_refl (term98 A t)). Qed.
Lemma lem3290590 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term99 A t x') = (term99 A t x).
Proof. exact (MK_COMB (@lem3290589 A t) (@lem3290352 A x' x h1)). Qed.
Lemma lem3290591 {A : Type'} (t : A -> Prop) (x : A) : (term99 A t x) = (t x).
Proof. exact (eq_refl (term99 A t x)). Qed.
Lemma lem3290592 {A : Type'} (t : A -> Prop) (x' : A) : (term100 A t x') = (term100 A t x').
Proof. exact (eq_refl (term100 A t x')). Qed.
Lemma lem3290593 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (term99 A t x)) = ((term99 A t x') = (t x)).
Proof. exact (MK_COMB (@lem3290592 A t x') (@lem3290591 A t x)). Qed.
Lemma lem3290594 {A : Type'} (t : A -> Prop) (x' : A) : (term99 A t x') = (t x').
Proof. exact (eq_refl (term99 A t x')). Qed.
Lemma lem3290595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3290596 {A : Type'} (t : A -> Prop) (x' : A) : (term100 A t x') = (term101 A t x').
Proof. exact (MK_COMB (@lem3290595) (@lem3290594 A t x')). Qed.
Lemma lem3290597 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3290598 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (t x)) = ((t x') = (t x)).
Proof. exact (MK_COMB (@lem3290596 A t x') (@lem3290597 A t x)). Qed.
Lemma lem3290599 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term99 A t x') = (term99 A t x)) = ((t x') = (t x)).
Proof. exact (TRANS (@lem3290593 A x' t x) (@lem3290598 A x' t x)). Qed.
Lemma lem3290600 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (t x') = (t x).
Proof. exact (EQ_MP (@lem3290599 A x' t x) (@lem3290590 A t x' x h1)). Qed.
Lemma lem3290629 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3290630 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3290629 A x). Qed.
Lemma lem3290631 {A : Type'} (x : A) : term158 A x.
Proof. exact (fun h0 : term155 A x => @lem3290630 A x). Qed.
Lemma lem3290633 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290634 {A : Type'} (x : A) : (term158 A x) = (x = x).
Proof. exact (@lem3290633 (x = x)). Qed.
Lemma lem3290635 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3290634 A x) (@lem3290631 A x)). Qed.
Lemma lem3290638 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3290640 {A : Type'} (x : A) : (term155 A x) = (term159 A x).
Proof. exact (@lem3290638 (x = x)). Qed.
Lemma lem3290643 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : term159 A x.
Proof. exact (EQ_MP (@lem3290640 A x) (@lem3290413 A s t x' x h1 h2)). Qed.
Lemma lem3290646 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3290643 A s t x' x h1 h2 (@lem3290635 A x)). Qed.
Lemma lem3290647 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : term105.
Proof. exact (fun h0 : ~ False => @lem3290646 A s t x' x h1 h2). Qed.
Lemma lem3290649 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290650 : term105 = False.
Proof. exact (@lem3290649 False). Qed.
Lemma lem3290667 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3290505 A t x' x h2) (@lem3290320 A t x' h1)). Qed.
Lemma lem3290668 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : term102 A t x.
Proof. exact (fun h0 : term38 A t x => @lem3290667 A t x' x h1 h2). Qed.
Lemma lem3290670 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290671 {A : Type'} (t : A -> Prop) (x : A) : (term102 A t x) = (t x).
Proof. exact (@lem3290670 (t x)). Qed.
Lemma lem3290672 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3290671 A t x) (@lem3290668 A t x' x h1 h2)). Qed.
Lemma lem3290675 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3290677 {A : Type'} (t : A -> Prop) (x : A) : (term38 A t x) = (term104 A t x).
Proof. exact (@lem3290675 (t x)). Qed.
Lemma lem3290680 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : term104 A t x.
Proof. exact (EQ_MP (@lem3290677 A t x) (@lem3290493 A s t x' x h1 h2)). Qed.
Lemma lem3290683 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : False.
Proof. exact (@lem3290680 A s t x' x h2 h3 (@lem3290672 A t x' x h1 h3)). Qed.
Lemma lem3290684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : term105.
Proof. exact (fun h0 : ~ False => @lem3290683 A s t x' x h1 h2 h3). Qed.
Lemma lem3290686 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290687 : term105 = False.
Proof. exact (@lem3290686 False). Qed.
Lemma lem3290716 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3290717 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term102 A s x'.
Proof. exact (fun h0 : term38 A s x' => @lem3290716 A s x' h1). Qed.
Lemma lem3290719 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290720 {A : Type'} (s : A -> Prop) (x' : A) : (term102 A s x') = (s x').
Proof. exact (@lem3290719 (s x')). Qed.
Lemma lem3290721 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3290720 A s x') (@lem3290717 A s x' h1)). Qed.
Lemma lem3290724 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3290726 {A : Type'} (s : A -> Prop) (x' : A) : (term38 A s x') = (term104 A s x').
Proof. exact (@lem3290724 (s x')). Qed.
Lemma lem3290729 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') : term104 A s x'.
Proof. exact (EQ_MP (@lem3290726 A s x') (@lem3290330 A s x' h1)). Qed.
Lemma lem3290732 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (@lem3290729 A s x' h1 (@lem3290721 A s x' h2)). Qed.
Lemma lem3290733 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : term105.
Proof. exact (fun h0 : ~ False => @lem3290732 A s x' h1 h2). Qed.
Lemma lem3290735 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290736 : term105 = False.
Proof. exact (@lem3290735 False). Qed.
Lemma lem3290737 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3290736) (@lem3290733 A s x' h1 h2)). Qed.
Lemma lem3290765 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290766 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term102 A t x'.
Proof. exact (fun h0 : term38 A t x' => @lem3290765 A t x' h1). Qed.
Lemma lem3290768 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290769 {A : Type'} (t : A -> Prop) (x' : A) : (term102 A t x') = (t x').
Proof. exact (@lem3290768 (t x')). Qed.
Lemma lem3290770 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3290769 A t x') (@lem3290766 A t x' h1)). Qed.
Lemma lem3290773 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3290775 {A : Type'} (t : A -> Prop) (x' : A) : (term38 A t x') = (term104 A t x').
Proof. exact (@lem3290773 (t x')). Qed.
Lemma lem3290778 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : term104 A t x'.
Proof. exact (EQ_MP (@lem3290775 A t x') (@lem3290336 A x s t x' h1)). Qed.
Lemma lem3290781 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : False.
Proof. exact (@lem3290778 A x s t x' h2 (@lem3290770 A t x' h1)). Qed.
Lemma lem3290782 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : term105.
Proof. exact (fun h0 : ~ False => @lem3290781 A x s t x' h1 h2). Qed.
Lemma lem3290784 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290785 : term105 = False.
Proof. exact (@lem3290784 False). Qed.
Lemma lem3290786 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : False.
Proof. exact (EQ_MP (@lem3290785) (@lem3290782 A x s t x' h1 h2)). Qed.
Lemma lem3290814 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3290815 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3290814 A x). Qed.
Lemma lem3290816 {A : Type'} (x : A) : term158 A x.
Proof. exact (fun h0 : term155 A x => @lem3290815 A x). Qed.
Lemma lem3290818 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290819 {A : Type'} (x : A) : (term158 A x) = (x = x).
Proof. exact (@lem3290818 (x = x)). Qed.
Lemma lem3290820 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3290819 A x) (@lem3290816 A x)). Qed.
Lemma lem3290823 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3290825 {A : Type'} (x : A) : (term155 A x) = (term159 A x).
Proof. exact (@lem3290823 (x = x)). Qed.
Lemma lem3290828 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : term159 A x.
Proof. exact (EQ_MP (@lem3290825 A x) (@lem3290547 A s x' x h1 h2)). Qed.
Lemma lem3290831 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3290828 A s x' x h1 h2 (@lem3290820 A x)). Qed.
Lemma lem3290832 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : term105.
Proof. exact (fun h0 : ~ False => @lem3290831 A s x' x h1 h2). Qed.
Lemma lem3290834 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290835 : term105 = False.
Proof. exact (@lem3290834 False). Qed.
Lemma lem3290838 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3290600 A t x' x h2) (@lem3290354 A t x' h1)). Qed.
Lemma lem3290839 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : term102 A t x.
Proof. exact (fun h0 : term38 A t x => @lem3290838 A t x' x h1 h2). Qed.
Lemma lem3290841 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290842 {A : Type'} (t : A -> Prop) (x : A) : (term102 A t x) = (t x).
Proof. exact (@lem3290841 (t x)). Qed.
Lemma lem3290843 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3290842 A t x) (@lem3290839 A t x' x h1 h2)). Qed.
Lemma lem3290846 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3290848 {A : Type'} (t : A -> Prop) (x : A) : (term38 A t x) = (term104 A t x).
Proof. exact (@lem3290846 (t x)). Qed.
Lemma lem3290851 {A : Type'} (t : A -> Prop) (x : A) (h1 : term38 A t x) : term104 A t x.
Proof. exact (EQ_MP (@lem3290848 A t x) (@lem3290588 A t x h1)). Qed.
Lemma lem3290854 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (@lem3290851 A t x h1 (@lem3290843 A t x' x h2 h3)). Qed.
Lemma lem3290855 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : term105.
Proof. exact (fun h0 : ~ False => @lem3290854 A t x' x h1 h2 h3). Qed.
Lemma lem3290857 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290858 : term105 = False.
Proof. exact (@lem3290857 False). Qed.
Lemma lem3290859 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290858) (@lem3290855 A t x' x h1 h2 h3)). Qed.
Lemma lem3290887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : s x'.
Proof. exact (proj1 (@lem3290146 A s t x' h1)). Qed.
Lemma lem3290888 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : term102 A s x'.
Proof. exact (fun h0 : term38 A s x' => @lem3290887 A s t x' h1). Qed.
Lemma lem3290890 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290891 {A : Type'} (s : A -> Prop) (x' : A) : (term102 A s x') = (s x').
Proof. exact (@lem3290890 (s x')). Qed.
Lemma lem3290892 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3290891 A s x') (@lem3290888 A s t x' h1)). Qed.
Lemma lem3290895 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3290897 {A : Type'} (s : A -> Prop) (x' : A) : (term38 A s x') = (term104 A s x').
Proof. exact (@lem3290895 (s x')). Qed.
Lemma lem3290900 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term72 A x s x') : term104 A s x'.
Proof. exact (EQ_MP (@lem3290897 A s x') (@lem3290364 A x s x' h1)). Qed.
Lemma lem3290903 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term72 A x s x') (h2 : term44 A s t x') : False.
Proof. exact (@lem3290900 A x s x' h1 (@lem3290892 A s t x' h2)). Qed.
Lemma lem3290904 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term72 A x s x') (h2 : term44 A s t x') : term105.
Proof. exact (fun h0 : ~ False => @lem3290903 A x s t x' h1 h2). Qed.
Lemma lem3290906 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290907 : term105 = False.
Proof. exact (@lem3290906 False). Qed.
Lemma lem3290908 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term72 A x s x') (h2 : term44 A s t x') : False.
Proof. exact (EQ_MP (@lem3290907) (@lem3290904 A x s t x' h1 h2)). Qed.
Lemma lem3290910 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3290911 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term102 A t x'.
Proof. exact (fun h0 : term38 A t x' => @lem3290910 A t x' h1). Qed.
Lemma lem3290913 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290914 {A : Type'} (t : A -> Prop) (x' : A) : (term102 A t x') = (t x').
Proof. exact (@lem3290913 (t x')). Qed.
Lemma lem3290915 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3290914 A t x') (@lem3290911 A t x' h1)). Qed.
Lemma lem3290918 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3290920 {A : Type'} (t : A -> Prop) (x' : A) : (term38 A t x') = (term104 A t x').
Proof. exact (@lem3290918 (t x')). Qed.
Lemma lem3290923 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') : term104 A t x'.
Proof. exact (EQ_MP (@lem3290920 A t x') (@lem3290370 A s t x' h1)). Qed.
Lemma lem3290926 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : False.
Proof. exact (@lem3290923 A s t x' h2 (@lem3290915 A t x' h1)). Qed.
Lemma lem3290927 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : term105.
Proof. exact (fun h0 : ~ False => @lem3290926 A s t x' h1 h2). Qed.
Lemma lem3290929 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3290930 : term105 = False.
Proof. exact (@lem3290929 False). Qed.
Lemma lem3290931 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : False.
Proof. exact (EQ_MP (@lem3290930) (@lem3290927 A s t x' h1 h2)). Qed.
Lemma lem3290932 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (term38 A t x) = False.
Proof. exact (prop_ext (fun h4 : term38 A t x => @lem3290859 A t x' x h1 h2 h3) (fun h4 : False => @lem3290588 A t x h1)). Qed.
Lemma lem3290934 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290932 A t x' x h1 h2 h3) (@lem3290588 A t x h1)). Qed.
Lemma lem3290935 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290835) (@lem3290832 A s x' x h1 h2)). Qed.
Lemma lem3290936 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290687) (@lem3290684 A s t x' x h1 h2 h3)). Qed.
Lemma lem3290937 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290650) (@lem3290647 A s t x' x h1 h2)). Qed.
Lemma lem3290938 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3290931 A s t x' h1 h2) (fun h3 : False => @lem3290372 A t x' h1)). Qed.
Lemma lem3290939 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : False.
Proof. exact (EQ_MP (@lem3290938 A s t x' h1 h2) (@lem3290372 A t x' h1)). Qed.
Lemma lem3290940 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3290934 A t x' x h1 h2 h3) (fun h4 : False => @lem3290354 A t x' h2)). Qed.
Lemma lem3290941 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290940 A t x' x h1 h2 h3) (@lem3290354 A t x' h2)). Qed.
Lemma lem3290942 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3290941 A t x' x h1 h2 h3) (fun h4 : False => @lem3290352 A x' x h3)). Qed.
Lemma lem3290943 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290942 A t x' x h1 h2 h3) (@lem3290352 A x' x h3)). Qed.
Lemma lem3290944 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (term38 A t x) = False.
Proof. exact (prop_ext (fun h4 : term38 A t x => @lem3290943 A t x' x h1 h2 h3) (fun h4 : False => @lem3290350 A t x h1)). Qed.
Lemma lem3290945 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290944 A t x' x h1 h2 h3) (@lem3290350 A t x h1)). Qed.
Lemma lem3290946 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3290935 A s x' x h1 h2) (fun h3 : False => @lem3290344 A x' x h2)). Qed.
Lemma lem3290947 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290946 A s x' x h1 h2) (@lem3290344 A x' x h2)). Qed.
Lemma lem3290948 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3290786 A x s t x' h1 h2) (fun h3 : False => @lem3290340 A t x' h1)). Qed.
Lemma lem3290949 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : False.
Proof. exact (EQ_MP (@lem3290948 A x s t x' h1 h2) (@lem3290340 A t x' h1)). Qed.
Lemma lem3290950 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (term38 A s x') = False.
Proof. exact (prop_ext (fun h3 : term38 A s x' => @lem3290737 A s x' h1 h2) (fun h3 : False => @lem3290330 A s x' h1)). Qed.
Lemma lem3290951 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3290950 A s x' h1 h2) (@lem3290330 A s x' h1)). Qed.
Lemma lem3290952 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3290951 A s x' h1 h2) (fun h3 : False => @lem3290328 A s x' h2)). Qed.
Lemma lem3290953 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3290952 A s x' h1 h2) (@lem3290328 A s x' h2)). Qed.
Lemma lem3290954 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3290936 A s t x' x h1 h2 h3) (fun h4 : False => @lem3290320 A t x' h1)). Qed.
Lemma lem3290955 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290954 A s t x' x h1 h2 h3) (@lem3290320 A t x' h1)). Qed.
Lemma lem3290956 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3290955 A s t x' x h1 h2 h3) (fun h4 : False => @lem3290318 A x' x h3)). Qed.
Lemma lem3290957 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290956 A s t x' x h1 h2 h3) (@lem3290318 A x' x h3)). Qed.
Lemma lem3290958 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3290937 A s t x' x h1 h2) (fun h3 : False => @lem3290308 A x' x h2)). Qed.
Lemma lem3290959 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290958 A s t x' x h1 h2) (@lem3290308 A x' x h2)). Qed.
Lemma lem3290960 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3290939 A s t x' h1 h2) (fun h3 : False => @lem3290300 A t x' h1)). Qed.
Lemma lem3290961 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : False.
Proof. exact (EQ_MP (@lem3290960 A s t x' h1 h2) (@lem3290300 A t x' h1)). Qed.
Lemma lem3290962 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3290945 A t x' x h1 h2 h3) (fun h4 : False => @lem3290264 A t x' h2)). Qed.
Lemma lem3290963 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290962 A t x' x h1 h2 h3) (@lem3290264 A t x' h2)). Qed.
Lemma lem3290964 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3290963 A t x' x h1 h2 h3) (fun h4 : False => @lem3290260 A x' x h3)). Qed.
Lemma lem3290965 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290964 A t x' x h1 h2 h3) (@lem3290260 A x' x h3)). Qed.
Lemma lem3290966 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (term38 A t x) = False.
Proof. exact (prop_ext (fun h4 : term38 A t x => @lem3290965 A t x' x h1 h2 h3) (fun h4 : False => @lem3290256 A t x h1)). Qed.
Lemma lem3290967 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290966 A t x' x h1 h2 h3) (@lem3290256 A t x h1)). Qed.
Lemma lem3290968 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3290947 A s x' x h1 h2) (fun h3 : False => @lem3290244 A x' x h2)). Qed.
Lemma lem3290969 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290968 A s x' x h1 h2) (@lem3290244 A x' x h2)). Qed.
Lemma lem3290970 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3290949 A x s t x' h1 h2) (fun h3 : False => @lem3290236 A t x' h1)). Qed.
Lemma lem3290971 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : False.
Proof. exact (EQ_MP (@lem3290970 A x s t x' h1 h2) (@lem3290236 A t x' h1)). Qed.
Lemma lem3290972 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (term38 A s x') = False.
Proof. exact (prop_ext (fun h3 : term38 A s x' => @lem3290953 A s x' h1 h2) (fun h3 : False => @lem3290216 A s x' h1)). Qed.
Lemma lem3290973 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3290972 A s x' h1 h2) (@lem3290216 A s x' h1)). Qed.
Lemma lem3290974 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3290973 A s x' h1 h2) (fun h3 : False => @lem3290212 A s x' h2)). Qed.
Lemma lem3290975 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3290974 A s x' h1 h2) (@lem3290212 A s x' h2)). Qed.
Lemma lem3290976 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3290957 A s t x' x h1 h2 h3) (fun h4 : False => @lem3290196 A t x' h1)). Qed.
Lemma lem3290977 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290976 A s t x' x h1 h2 h3) (@lem3290196 A t x' h1)). Qed.
Lemma lem3290978 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3290977 A s t x' x h1 h2 h3) (fun h4 : False => @lem3290192 A x' x h3)). Qed.
Lemma lem3290979 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290978 A s t x' x h1 h2 h3) (@lem3290192 A x' x h3)). Qed.
Lemma lem3290980 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3290959 A s t x' x h1 h2) (fun h3 : False => @lem3290172 A x' x h2)). Qed.
Lemma lem3290981 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290980 A s t x' x h1 h2) (@lem3290172 A x' x h2)). Qed.
Lemma lem3290982 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3290961 A s t x' h1 h2) (fun h3 : False => @lem3290300 A t x' h1)). Qed.
Lemma lem3290983 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term44 A s t x') : False.
Proof. exact (EQ_MP (@lem3290982 A s t x' h1 h2) (@lem3290300 A t x' h1)). Qed.
Lemma lem3290984 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3290967 A t x' x h1 h2 h3) (fun h4 : False => @lem3290264 A t x' h2)). Qed.
Lemma lem3290985 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290984 A t x' x h1 h2 h3) (@lem3290264 A t x' h2)). Qed.
Lemma lem3290986 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3290985 A t x' x h1 h2 h3) (fun h4 : False => @lem3290260 A x' x h3)). Qed.
Lemma lem3290987 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290986 A t x' x h1 h2 h3) (@lem3290260 A x' x h3)). Qed.
Lemma lem3290988 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : (term38 A t x) = False.
Proof. exact (prop_ext (fun h4 : term38 A t x => @lem3290987 A t x' x h1 h2 h3) (fun h4 : False => @lem3290256 A t x h1)). Qed.
Lemma lem3290989 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290988 A t x' x h1 h2 h3) (@lem3290256 A t x h1)). Qed.
Lemma lem3290990 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3290969 A s x' x h1 h2) (fun h3 : False => @lem3290244 A x' x h2)). Qed.
Lemma lem3290991 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term72 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290990 A s x' x h1 h2) (@lem3290244 A x' x h2)). Qed.
Lemma lem3290992 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3290971 A x s t x' h1 h2) (fun h3 : False => @lem3290236 A t x' h1)). Qed.
Lemma lem3290993 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term146 A x s t x') : False.
Proof. exact (EQ_MP (@lem3290992 A x s t x' h1 h2) (@lem3290236 A t x' h1)). Qed.
Lemma lem3290994 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (term38 A s x') = False.
Proof. exact (prop_ext (fun h3 : term38 A s x' => @lem3290975 A s x' h1 h2) (fun h3 : False => @lem3290216 A s x' h1)). Qed.
Lemma lem3290995 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3290994 A s x' h1 h2) (@lem3290216 A s x' h1)). Qed.
Lemma lem3290996 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3290995 A s x' h1 h2) (fun h3 : False => @lem3290212 A s x' h2)). Qed.
Lemma lem3290997 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term38 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3290996 A s x' h1 h2) (@lem3290212 A s x' h2)). Qed.
Lemma lem3290998 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : (t x') = False.
Proof. exact (prop_ext (fun h4 : t x' => @lem3290979 A s t x' x h1 h2 h3) (fun h4 : False => @lem3290196 A t x' h1)). Qed.
Lemma lem3290999 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3290998 A s t x' x h1 h2 h3) (@lem3290196 A t x' h1)). Qed.
Lemma lem3291000 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3290999 A s t x' x h1 h2 h3) (fun h4 : False => @lem3290192 A x' x h3)). Qed.
Lemma lem3291001 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x') (h2 : term146 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3291000 A s t x' x h1 h2 h3) (@lem3290192 A x' x h3)). Qed.
Lemma lem3291002 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3290981 A s t x' x h1 h2) (fun h3 : False => @lem3290172 A x' x h2)). Qed.
Lemma lem3291003 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3291002 A s t x' x h1 h2) (@lem3290172 A x' x h2)). Qed.
Lemma lem3291004 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term44 A s t x') (h2 : term144 A x s t x') : False.
Proof. exact (or_elim (@lem3290144 A x s t x' h2) (fun h0 : term72 A x s x' => @lem3290908 A x s t x' h0 h1) (fun h0 : t x' => @lem3290983 A s t x' h0 h1)). Qed.
Lemma lem3291005 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term38 A t x) (h2 : term144 A x s t x') (h3 : x' = x) : False.
Proof. exact (or_elim (@lem3290144 A x s t x' h2) (fun h0 : term72 A x s x' => @lem3290991 A s x' x h0 h3) (fun h0 : t x' => @lem3290989 A t x' x h1 h0 h3)). Qed.
Lemma lem3291006 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term38 A t x) (h2 : term144 A x s t x') : False.
Proof. exact (or_elim (@lem3290143 A x s t x' h2) (fun h0 : x' = x => @lem3291005 A s t x' x h1 h2 h0) (fun h0 : term44 A s t x' => @lem3291004 A x s t x' h0 h2)). Qed.
Lemma lem3291007 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term146 A x s t x') : False.
Proof. exact (or_elim (@lem3290133 A x s t x' h2) (fun h0 : term38 A s x' => @lem3290997 A s x' h0 h1) (fun h0 : t x' => @lem3290993 A x s t x' h0 h2)). Qed.
Lemma lem3291008 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term146 A x s t x') (h2 : x' = x) : False.
Proof. exact (or_elim (@lem3290133 A x s t x' h1) (fun h0 : term38 A s x' => @lem3291003 A s t x' x h1 h2) (fun h0 : t x' => @lem3291001 A s t x' x h0 h1 h2)). Qed.
Lemma lem3291009 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term146 A x s t x') : False.
Proof. exact (or_elim (@lem3290136 A x s t x' h1) (fun h0 : x' = x => @lem3291008 A s t x' x h1 h0) (fun h0 : s x' => @lem3291007 A x s t x' h0 h1)). Qed.
Lemma lem3291010 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term38 A t x) (h2 : term138 A x s t x') : False.
Proof. exact (or_elim (@lem3290128 A x s t x' h2) (fun h0 : term146 A x s t x' => @lem3291009 A x s t x' h0) (fun h0 : term144 A x s t x' => @lem3291006 A x s t x' h1 h0)). Qed.
Lemma lem3291011 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term38 A t x) (h2 : term138 A x s t x') : (term38 A t x) = False.
Proof. exact (prop_ext (fun h3 : term38 A t x => @lem3291010 A x s t x' h1 h2) (fun h3 : False => @lem3290038 A t x h1)). Qed.
Lemma lem3291012 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term38 A t x) (h2 : term138 A x s t x') : False.
Proof. exact (EQ_MP (@lem3291011 A x s t x' h1 h2) (@lem3290038 A t x h1)). Qed.
Lemma lem3291013 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term38 A t x) (h2 : term138 A x s t x') : (term38 A t x) = False.
Proof. exact (prop_ext (fun h3 : term38 A t x => @lem3291012 A x s t x' h1 h2) (fun h3 : False => @lem3289968 A t x h1)). Qed.
Lemma lem3291014 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term38 A t x) (h2 : term138 A x s t x') : False.
Proof. exact (EQ_MP (@lem3291013 A x s t x' h1 h2) (@lem3289968 A t x h1)). Qed.
Lemma lem3291015 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term38 A t x) (h2 : term138 A x s t x') : (term138 A x s t x') = False.
Proof. exact (prop_ext (fun h3 : term138 A x s t x' => @lem3291014 A x s t x' h1 h2) (fun h3 : False => @lem3289962 A x s t x' h2)). Qed.
Lemma lem3291016 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term38 A t x) (h2 : term138 A x s t x') : False.
Proof. exact (EQ_MP (@lem3291015 A x s t x' h1 h2) (@lem3289962 A x s t x' h2)). Qed.
Lemma lem3291017 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term38 A t x) : term137 A x s t x'.
Proof. exact (fun h0 : term138 A x s t x' => @lem3291016 A x s t x' h1 h0). Qed.
Lemma lem3291018 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term38 A t x) : (term39 A x s t x') = (term114 A x s t x').
Proof. exact (EQ_MP (@lem3289961 A x s t x') (@lem3291017 A s x' t x h1)). Qed.
Lemma lem3291023 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term38 A t x) : term117 A x s t.
Proof. exact (fun x' : A => @lem3291018 A s x' t x h1). Qed.
Lemma lem3291024 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term118 A x s t.
Proof. exact (fun h0 : term38 A t x => @lem3291023 A s t x h0). Qed.
Lemma lem3291029 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term128 A s t.
Proof. exact (fun x : A => @lem3291024 A x s t). Qed.
Lemma lem3291034 {A : Type'} (t : A -> Prop) : term132 A t.
Proof. exact (fun s : A -> Prop => @lem3291029 A s t). Qed.
Lemma lem3291039 {A : Type'} : term136 A.
Proof. exact (fun t : A -> Prop => @lem3291034 A t). Qed.
Lemma lem3291040 {A : Type'} : term135 A.
Proof. exact (EQ_MP (@lem3289956 A) (@lem3291039 A)). Qed.
Lemma lem3291041 {A : Type'} (t : A -> Prop) : term160 A t.
Proof. exact (@lem3291040 A t). Qed.
Lemma lem3291042 {A : Type'} (t : A -> Prop) : (term160 A t) = (term131 A t).
Proof. exact (eq_refl (term160 A t)). Qed.
Lemma lem3291043 {A : Type'} (t : A -> Prop) : term131 A t.
Proof. exact (EQ_MP (@lem3291042 A t) (@lem3291041 A t)). Qed.
Lemma lem3291044 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term161 A t s.
Proof. exact (@lem3291043 A t s). Qed.
Lemma lem3291045 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term161 A t s) = (term127 A s t).
Proof. exact (eq_refl (term161 A t s)). Qed.
Lemma lem3291046 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term127 A s t.
Proof. exact (EQ_MP (@lem3291045 A s t) (@lem3291044 A t s)). Qed.
Lemma lem3291047 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term162 A s t x.
Proof. exact (@lem3291046 A s t x). Qed.
Lemma lem3291048 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term162 A s t x) = (term119 A x s t).
Proof. exact (eq_refl (term162 A s t x)). Qed.
Lemma lem3291049 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term119 A x s t.
Proof. exact (EQ_MP (@lem3291048 A x s t) (@lem3291047 A s t x)). Qed.
Lemma lem3291051 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term119 A x s t.
Proof. exact (@lem3289817 A x s t (@lem3291049 A x s t)). Qed.
Lemma lem3291052 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term120 A x s t) : False.
Proof. exact (@lem3291051 A x s t (@lem3289801 A x s t h1)). Qed.
Lemma lem3291053 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term120 A x s t) : (term120 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term120 A x s t => @lem3291052 A x s t h1) (fun h2 : False => @lem3289801 A x s t h1)). Qed.
Lemma lem3291054 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term120 A x s t) : False.
Proof. exact (EQ_MP (@lem3291053 A x s t h1) (@lem3289801 A x s t h1)). Qed.
Lemma lem3291055 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term119 A x s t.
Proof. exact (fun h0 : term120 A x s t => @lem3291054 A x s t h0). Qed.
Lemma lem3291056 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term118 A x s t.
Proof. exact (EQ_MP (@lem3289800 A x s t) (@lem3291055 A x s t)). Qed.
Lemma lem3291057 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term110 A x s t.
Proof. exact (EQ_MP (@lem3289796 A x s t) (@lem3291056 A x s t)). Qed.
Lemma lem3291058 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term12 A x s t.
Proof. exact (EQ_MP (@lem3289694 A x s t) (@lem3291057 A x s t)). Qed.
Lemma lem3291061 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term9 A x s t) = (term7 A x s t).
Proof. exact (@lem3291058 A x s t (@lem3288710 A x t h1)). Qed.
Lemma lem3291062 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term23 A x t) = ((term9 A x s t) = (term7 A x s t)).
Proof. exact (prop_ext (fun h2 : term23 A x t => @lem3291061 A s x t h1) (fun h2 : (term9 A x s t) = (term7 A x s t) => @lem3288710 A x t h1)). Qed.
Lemma lem3291063 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term9 A x s t) = (term7 A x s t).
Proof. exact (EQ_MP (@lem3291062 A s x t h1) (@lem3288710 A x t h1)). Qed.
Lemma lem3291064 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term12 A x s t.
Proof. exact (fun h0 : term23 A x t => @lem3291063 A s x t h0). Qed.
Lemma lem3291065 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (term9 A x s t) = (@DIFF A s t).
Proof. exact (@lem3289673 A x s t (@lem3288693 A x t h1)). Qed.
Lemma lem3291066 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (@IN A x t) = ((term9 A x s t) = (@DIFF A s t)).
Proof. exact (prop_ext (fun h2 : @IN A x t => @lem3291065 A s x t h1) (fun h2 : (term9 A x s t) = (@DIFF A s t) => @lem3288693 A x t h1)). Qed.
Lemma lem3291067 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (term9 A x s t) = (@DIFF A s t).
Proof. exact (EQ_MP (@lem3291066 A s x t h1) (@lem3288693 A x t h1)). Qed.
Lemma lem3291068 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term16 A x s t.
Proof. exact (fun h0 : @IN A x t => @lem3291067 A s x t h0). Qed.
Lemma lem3291069 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term19 A x s t.
Proof. exact (conj (@lem3291068 A x s t) (@lem3291064 A x s t)). Qed.
Lemma lem3291070 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term9 A x s t) = (term20 A x s t).
Proof. exact (EQ_MP (@lem3288692 A x s t) (@lem3291069 A x s t)). Qed.
Lemma lem3291075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term163 A s t.
Proof. exact (fun x : A => @lem3291070 A x s t). Qed.
Lemma lem3291080 {A : Type'} (s : A -> Prop) : term164 A s.
Proof. exact (fun t : A -> Prop => @lem3291075 A s t). Qed.
Lemma lem3291085 {A : Type'} : term165 A.
Proof. exact (fun s : A -> Prop => @lem3291080 A s). Qed.
