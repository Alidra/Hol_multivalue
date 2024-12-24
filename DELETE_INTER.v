Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DELETE_INTER_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3319676 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3319677 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3319676 A s t). Qed.
Lemma lem3319678 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term1 A s x t) = (term2 A s t x)) = (term3 A s t x).
Proof. exact (@lem3319677 A (term1 A s x t) (term2 A s t x)). Qed.
Lemma lem3319687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term5 A s t).
Proof. exact (fun_ext (fun x : A => @lem3319678 A s t x)). Qed.
Lemma lem3319688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319689 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = (term7 A s t).
Proof. exact (MK_COMB (@lem3319688 A) (@lem3319687 A s t)). Qed.
Lemma lem3319694 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3319689 A s t)). Qed.
Lemma lem3319695 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3319696 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (MK_COMB (@lem3319695 A) (@lem3319694 A s)). Qed.
Lemma lem3319701 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3319696 A s)). Qed.
Lemma lem3319702 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3319703 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3319702 A) (@lem3319701 A)). Qed.
Lemma lem3319708 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3319703 A)). Qed.
Lemma lem3319728 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3319729 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3319728 A s x t). Qed.
Lemma lem3319730 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (t : A -> Prop) : (term18 A x' s x t) = (term19 A s x x' t).
Proof. exact (@lem3319729 A (@DELETE A s x) x' t). Qed.
Lemma lem3319734 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term20 A x s y) = (term21 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3319735 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term20 A x s y) = (term21 A s x y).
Proof. exact (@lem3319734 A s x y). Qed.
Lemma lem3319736 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term20 A x' s x) = (term21 A s x' x).
Proof. exact (@lem3319735 A s x' x). Qed.
Lemma lem3319740 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3319741 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3319740 A P x). Qed.
Lemma lem3319742 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3319741 A s x'). Qed.
Lemma lem3319743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3319744 {A : Type'} (s : A -> Prop) (x' : A) : (term22 A x' s) = (term23 A s x').
Proof. exact (MK_COMB (@lem3319743) (@lem3319742 A s x')). Qed.
Lemma lem3319747 {A : Type'} (x' : A) (x : A) : (term24 A x' x) = (term24 A x' x).
Proof. exact (eq_refl (term24 A x' x)). Qed.
Lemma lem3319748 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term21 A s x' x) = (term25 A s x' x).
Proof. exact (MK_COMB (@lem3319744 A s x') (@lem3319747 A x' x)). Qed.
Lemma lem3319751 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term20 A x' s x) = (term25 A s x' x).
Proof. exact (TRANS (@lem3319736 A s x' x) (@lem3319748 A s x' x)). Qed.
Lemma lem3319752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3319753 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term26 A x' s x) = (term27 A s x' x).
Proof. exact (MK_COMB (@lem3319752) (@lem3319751 A s x' x)). Qed.
Lemma lem3319755 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3319756 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3319755 A P x). Qed.
Lemma lem3319757 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3319756 A t x'). Qed.
Lemma lem3319758 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term19 A s x x' t) = (term28 A s x t x').
Proof. exact (MK_COMB (@lem3319753 A s x' x) (@lem3319757 A t x')). Qed.
Lemma lem3319761 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term18 A x' s x t) = (term28 A s x t x').
Proof. exact (TRANS (@lem3319730 A s x x' t) (@lem3319758 A s x t x')). Qed.
Lemma lem3319762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3319763 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term29 A x' s x t) = (term30 A s x t x').
Proof. exact (MK_COMB (@lem3319762) (@lem3319761 A s x t x')). Qed.
Lemma lem3319765 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term20 A x s y) = (term21 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3319766 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term20 A x s y) = (term21 A s x y).
Proof. exact (@lem3319765 A s x y). Qed.
Lemma lem3319767 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term31 A x' s t x) = (term32 A s t x' x).
Proof. exact (@lem3319766 A (@INTER A s t) x' x). Qed.
Lemma lem3319771 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3319772 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3319771 A s x t). Qed.
Lemma lem3319773 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term16 A x' s t) = (term17 A s x' t).
Proof. exact (@lem3319772 A s x' t). Qed.
Lemma lem3319777 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3319778 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3319777 A P x). Qed.
Lemma lem3319779 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3319778 A s x'). Qed.
Lemma lem3319780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3319781 {A : Type'} (s : A -> Prop) (x' : A) : (term22 A x' s) = (term23 A s x').
Proof. exact (MK_COMB (@lem3319780) (@lem3319779 A s x')). Qed.
Lemma lem3319783 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3319784 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3319783 A P x). Qed.
Lemma lem3319785 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3319784 A t x'). Qed.
Lemma lem3319786 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term17 A s x' t) = (term33 A s t x').
Proof. exact (MK_COMB (@lem3319781 A s x') (@lem3319785 A t x')). Qed.
Lemma lem3319789 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term16 A x' s t) = (term33 A s t x').
Proof. exact (TRANS (@lem3319773 A s x' t) (@lem3319786 A s t x')). Qed.
Lemma lem3319790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3319791 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term34 A x' s t) = (term35 A s t x').
Proof. exact (MK_COMB (@lem3319790) (@lem3319789 A s t x')). Qed.
Lemma lem3319794 {A : Type'} (x' : A) (x : A) : (term24 A x' x) = (term24 A x' x).
Proof. exact (eq_refl (term24 A x' x)). Qed.
Lemma lem3319795 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term32 A s t x' x) = (term36 A s t x' x).
Proof. exact (MK_COMB (@lem3319791 A s t x') (@lem3319794 A x' x)). Qed.
Lemma lem3319798 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term31 A x' s t x) = (term36 A s t x' x).
Proof. exact (TRANS (@lem3319767 A s t x' x) (@lem3319795 A s t x' x)). Qed.
Lemma lem3319799 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : ((term18 A x' s x t) = (term31 A x' s t x)) = ((term28 A s x t x') = (term36 A s t x' x)).
Proof. exact (MK_COMB (@lem3319763 A s x t x') (@lem3319798 A s t x' x)). Qed.
Lemma lem3319802 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term37 A s t x) = (term38 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3319799 A s t x' x)). Qed.
Lemma lem3319803 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319804 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term3 A s t x) = (term39 A s t x).
Proof. exact (MK_COMB (@lem3319803 A) (@lem3319802 A s t x)). Qed.
Lemma lem3319809 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term40 A s t).
Proof. exact (fun_ext (fun x : A => @lem3319804 A s t x)). Qed.
Lemma lem3319810 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319811 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3319810 A) (@lem3319809 A s t)). Qed.
Lemma lem3319816 {A : Type'} (s : A -> Prop) : (term9 A s) = (term42 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3319811 A s t)). Qed.
Lemma lem3319817 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3319818 {A : Type'} (s : A -> Prop) : (term11 A s) = (term43 A s).
Proof. exact (MK_COMB (@lem3319817 A) (@lem3319816 A s)). Qed.
Lemma lem3319823 {A : Type'} : (term13 A) = (term44 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3319818 A s)). Qed.
Lemma lem3319824 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3319825 {A : Type'} : (term15 A) = (term45 A).
Proof. exact (MK_COMB (@lem3319824 A) (@lem3319823 A)). Qed.
Lemma lem3319830 {A : Type'} : (term45 A) = (term15 A).
Proof. exact (SYM (@lem3319825 A)). Qed.
Lemma lem3319832 (p : Prop) : p = (term46 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3319833 {A : Type'} : (term45 A) = (term47 A).
Proof. exact (@lem3319832 (term45 A)). Qed.
Lemma lem3319834 {A : Type'} : (term47 A) = (term45 A).
Proof. exact (SYM (@lem3319833 A)). Qed.
Lemma lem3319835 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3319838 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (h1). Qed.
Lemma lem3319839 {A : Type'} : term49 A.
Proof. exact (fun h0 : term47 A => @lem3319838 A h0). Qed.
Lemma lem3319840 {A : Type'} (h1 : term49 A) : term49 A.
Proof. exact (h1). Qed.
Lemma lem3319841 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (h1). Qed.
Lemma lem3319842 {A : Type'} (h1 : term47 A) (h2 : term49 A) : term47 A.
Proof. exact (@lem3319840 A h2 (@lem3319841 A h1)). Qed.
Lemma lem3319843 {A : Type'} (h1 : term47 A) : term50 A.
Proof. exact (fun h0 : term49 A => @lem3319842 A h1 h0). Qed.
Lemma lem3319844 {A : Type'} (h1 : term49 A) : term49 A.
Proof. exact (h1). Qed.
Lemma lem3319845 {A : Type'} (h1 : term47 A) (h2 : term49 A) : term47 A.
Proof. exact (@lem3319843 A h1 (@lem3319844 A h2)). Qed.
Lemma lem3319846 {A : Type'} (h1 : term49 A) : term49 A.
Proof. exact (fun h0 : term47 A => @lem3319845 A h0 h1). Qed.
Lemma lem3319847 {A : Type'} : term51 A.
Proof. exact (fun h0 : term49 A => @lem3319846 A h0). Qed.
Lemma lem3319850 {A : Type'} : term49 A.
Proof. exact (@lem3319847 A (@lem3319839 A)). Qed.
Lemma lem3319851 {A : Type'} : term49 A.
Proof. exact (@lem3319850 A). Qed.
Lemma lem3319853 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3319854 {A : Type'} : (term47 A) = (term52 A).
Proof. exact (@lem3319853 (term48 A)). Qed.
Lemma lem3319856 (t : Prop) : (term53 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3319857 {A : Type'} : (term52 A) = (term45 A).
Proof. exact (@lem3319856 (term45 A)). Qed.
Lemma lem3319886 {A : Type'} : (term47 A) = (term45 A).
Proof. exact (TRANS (@lem3319854 A) (@lem3319857 A)). Qed.
Lemma lem3319911 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : ((term28 A s x t x') = (term36 A s t x' x)) = ((term28 A s x t x') = (term36 A s t x' x)).
Proof. exact (eq_refl ((term28 A s x t x') = (term36 A s t x' x))). Qed.
Lemma lem3319912 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term38 A s t x) = (term38 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3319911 A s t x' x)). Qed.
Lemma lem3319913 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term39 A s t x) = (term39 A s t x).
Proof. exact (MK_COMB (@lem3319913 A) (@lem3319912 A s t x)). Qed.
Lemma lem3319915 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term40 A s t).
Proof. exact (fun_ext (fun x : A => @lem3319914 A s t x)). Qed.
Lemma lem3319916 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3319917 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3319916 A) (@lem3319915 A s t)). Qed.
Lemma lem3319918 {A : Type'} (s : A -> Prop) : (term42 A s) = (term42 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3319917 A s t)). Qed.
Lemma lem3319919 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3319920 {A : Type'} (s : A -> Prop) : (term43 A s) = (term43 A s).
Proof. exact (MK_COMB (@lem3319919 A) (@lem3319918 A s)). Qed.
Lemma lem3319921 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3319920 A s)). Qed.
Lemma lem3319922 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3319923 {A : Type'} : (term45 A) = (term45 A).
Proof. exact (MK_COMB (@lem3319922 A) (@lem3319921 A)). Qed.
Lemma lem3319958 {A : Type'} : (term47 A) = (term45 A).
Proof. exact (TRANS (@lem3319886 A) (@lem3319923 A)). Qed.
Lemma lem3319959 {A : Type'} : (term45 A) = (term47 A).
Proof. exact (SYM (@lem3319958 A)). Qed.
Lemma lem3319961 (p : Prop) : p = (term46 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3319962 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : ((term28 A s x t x') = (term36 A s t x' x)) = (term54 A s t x' x).
Proof. exact (@lem3319961 ((term28 A s x t x') = (term36 A s t x' x))). Qed.
Lemma lem3319963 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term54 A s t x' x) = ((term28 A s x t x') = (term36 A s t x' x)).
Proof. exact (SYM (@lem3319962 A s t x' x)). Qed.
Lemma lem3319964 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term55 A s t x' x) : term55 A s t x' x.
Proof. exact (h1). Qed.
Lemma lem3319970 {A : Type'} (x' : A) (x : A) : (term56 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3319972 {A : Type'} (s : A -> Prop) (x' : A) : (term57 A s x') = (term57 A s x').
Proof. exact (eq_refl (term57 A s x')). Qed.
Lemma lem3319973 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term58 A s x' x) = (term59 A s x' x).
Proof. exact (MK_COMB (@lem3319972 A s x') (@lem3319970 A x' x)). Qed.
Lemma lem3319974 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term60 A s x' x) = (term58 A s x' x).
Proof. exact (@lem17045 (s x') (term24 A x' x)). Qed.
Lemma lem3319975 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term60 A s x' x) = (term59 A s x' x).
Proof. exact (TRANS (@lem3319974 A s x' x) (@lem3319973 A s x' x)). Qed.
Lemma lem3319979 {A : Type'} (t : A -> Prop) (x' : A) : (term61 A t x') = (term61 A t x').
Proof. exact (eq_refl (term61 A t x')). Qed.
Lemma lem3319981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3319982 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term62 A s x' x) = (term63 A s x' x).
Proof. exact (MK_COMB (@lem3319981) (@lem3319975 A s x' x)). Qed.
Lemma lem3319983 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term64 A s x t x') = (term65 A s x t x').
Proof. exact (MK_COMB (@lem3319982 A s x' x) (@lem3319979 A t x')). Qed.
Lemma lem3319984 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term66 A s x t x') = (term64 A s x t x').
Proof. exact (@lem17045 (term25 A s x' x) (t x')). Qed.
Lemma lem3319985 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term66 A s x t x') = (term65 A s x t x').
Proof. exact (TRANS (@lem3319984 A s x t x') (@lem3319983 A s x t x')). Qed.
Lemma lem3319997 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term67 A s t x') = (term68 A s t x').
Proof. exact (@lem17045 (s x') (t x')). Qed.
Lemma lem3320004 {A : Type'} (x' : A) (x : A) : (term56 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3320005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3320006 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term69 A s t x') = (term70 A s t x').
Proof. exact (MK_COMB (@lem3320005) (@lem3319997 A s t x')). Qed.
Lemma lem3320007 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term71 A s t x' x) = (term72 A s t x' x).
Proof. exact (MK_COMB (@lem3320006 A s t x') (@lem3320004 A x' x)). Qed.
Lemma lem3320008 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term73 A s t x' x) = (term71 A s t x' x).
Proof. exact (@lem17045 (term33 A s t x') (term24 A x' x)). Qed.
Lemma lem3320009 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term73 A s t x' x) = (term72 A s t x' x).
Proof. exact (TRANS (@lem3320008 A s t x' x) (@lem3320007 A s t x' x)). Qed.
Lemma lem3320012 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term36 A s t x' x) = (term36 A s t x' x).
Proof. exact (eq_refl (term36 A s t x' x)). Qed.
Lemma lem3320013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3320014 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term74 A s x t x') = (term75 A s x t x').
Proof. exact (MK_COMB (@lem3320013) (@lem3319985 A s x t x')). Qed.
Lemma lem3320015 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term76 A s t x' x) = (term77 A s t x' x).
Proof. exact (MK_COMB (@lem3320014 A s x t x') (@lem3320012 A s t x' x)). Qed.
Lemma lem3320017 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term78 A s x t x') = (term78 A s x t x').
Proof. exact (eq_refl (term78 A s x t x')). Qed.
Lemma lem3320018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term79 A s t x' x) = (term80 A s t x' x).
Proof. exact (MK_COMB (@lem3320017 A s x t x') (@lem3320009 A s t x' x)). Qed.
Lemma lem3320019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3320020 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term81 A s t x' x) = (term82 A s t x' x).
Proof. exact (MK_COMB (@lem3320019) (@lem3320018 A s t x' x)). Qed.
Lemma lem3320021 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term83 A s t x' x) = (term84 A s t x' x).
Proof. exact (MK_COMB (@lem3320020 A s t x' x) (@lem3320015 A s t x' x)). Qed.
Lemma lem3320022 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term55 A s t x' x) = (term83 A s t x' x).
Proof. exact (@lem17646 (term28 A s x t x') (term36 A s t x' x)). Qed.
Lemma lem3320027 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term55 A s t x' x) = (term84 A s t x' x).
Proof. exact (TRANS (@lem3320022 A s t x' x) (@lem3320021 A s t x' x)). Qed.
Lemma lem3320118 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term55 A s t x' x) : term84 A s t x' x.
Proof. exact (EQ_MP (@lem3320027 A s t x' x) (@lem3319964 A s t x' x h1)). Qed.
Lemma lem3320119 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : term80 A s t x' x.
Proof. exact (h1). Qed.
Lemma lem3320120 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : term77 A s t x' x.
Proof. exact (h1). Qed.
Lemma lem3320121 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : term72 A s t x' x.
Proof. exact (proj2 (@lem3320119 A s t x' x h1)). Qed.
Lemma lem3320122 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : term28 A s x t x'.
Proof. exact (proj1 (@lem3320119 A s t x' x h1)). Qed.
Lemma lem3320124 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : term25 A s x' x.
Proof. exact (proj1 (@lem3320122 A s t x' x h1)). Qed.
Lemma lem3320127 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term68 A s t x') : term68 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3320131 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : term36 A s t x' x.
Proof. exact (proj2 (@lem3320120 A s t x' x h1)). Qed.
Lemma lem3320132 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : term65 A s x t x'.
Proof. exact (proj1 (@lem3320120 A s t x' x h1)). Qed.
Lemma lem3320134 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : term33 A s t x'.
Proof. exact (proj1 (@lem3320131 A s t x' x h1)). Qed.
Lemma lem3320137 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term59 A s x' x) : term59 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3320156 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term61 A s x') : term61 A s x'.
Proof. exact (h1). Qed.
Lemma lem3320172 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term61 A t x') : term61 A t x'.
Proof. exact (h1). Qed.
Lemma lem3320188 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3320204 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term61 A s x') : term61 A s x'.
Proof. exact (h1). Qed.
Lemma lem3320220 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3320236 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term61 A t x') : term61 A t x'.
Proof. exact (h1). Qed.
Lemma lem3320244 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term61 A s x') : term61 A s x'.
Proof. exact (h1). Qed.
Lemma lem3320252 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term61 A t x') : term61 A t x'.
Proof. exact (h1). Qed.
Lemma lem3320258 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : term24 A x' x.
Proof. exact (proj2 (@lem3320124 A s t x' x h1)). Qed.
Lemma lem3320260 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3320268 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term61 A s x') : term61 A s x'.
Proof. exact (h1). Qed.
Lemma lem3320270 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : term24 A x' x.
Proof. exact (proj2 (@lem3320131 A s t x' x h1)). Qed.
Lemma lem3320276 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3320284 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term61 A t x') : term61 A t x'.
Proof. exact (h1). Qed.
Lemma lem3320325 {A : Type'} (x : A) : (term85 A x) = (term85 A x).
Proof. exact (eq_refl (term85 A x)). Qed.
Lemma lem3320326 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term86 A x x') = (term87 A x).
Proof. exact (MK_COMB (@lem3320325 A x) (@lem3320260 A x' x h1)). Qed.
Lemma lem3320327 {A : Type'} (x : A) : (term87 A x) = (term88 A x).
Proof. exact (eq_refl (term87 A x)). Qed.
Lemma lem3320328 {A : Type'} (x : A) (x' : A) : (term89 A x x') = (term89 A x x').
Proof. exact (eq_refl (term89 A x x')). Qed.
Lemma lem3320329 {A : Type'} (x' : A) (x : A) : ((term86 A x x') = (term87 A x)) = ((term86 A x x') = (term88 A x)).
Proof. exact (MK_COMB (@lem3320328 A x x') (@lem3320327 A x)). Qed.
Lemma lem3320330 {A : Type'} (x' : A) (x : A) : (term86 A x x') = (term24 A x' x).
Proof. exact (eq_refl (term86 A x x')). Qed.
Lemma lem3320331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3320332 {A : Type'} (x' : A) (x : A) : (term89 A x x') = (term90 A x' x).
Proof. exact (MK_COMB (@lem3320331) (@lem3320330 A x' x)). Qed.
Lemma lem3320333 {A : Type'} (x : A) : (term88 A x) = (term88 A x).
Proof. exact (eq_refl (term88 A x)). Qed.
Lemma lem3320334 {A : Type'} (x' : A) (x : A) : ((term86 A x x') = (term88 A x)) = ((term24 A x' x) = (term88 A x)).
Proof. exact (MK_COMB (@lem3320332 A x' x) (@lem3320333 A x)). Qed.
Lemma lem3320335 {A : Type'} (x' : A) (x : A) : ((term86 A x x') = (term87 A x)) = ((term24 A x' x) = (term88 A x)).
Proof. exact (TRANS (@lem3320329 A x' x) (@lem3320334 A x' x)). Qed.
Lemma lem3320336 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term24 A x' x) = (term88 A x).
Proof. exact (EQ_MP (@lem3320335 A x' x) (@lem3320326 A x' x h1)). Qed.
Lemma lem3320337 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : term88 A x.
Proof. exact (EQ_MP (@lem3320336 A x' x h2) (@lem3320258 A s t x' x h1)). Qed.
Lemma lem3320352 {A : Type'} (x : A) : (term85 A x) = (term85 A x).
Proof. exact (eq_refl (term85 A x)). Qed.
Lemma lem3320353 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term86 A x x') = (term87 A x).
Proof. exact (MK_COMB (@lem3320352 A x) (@lem3320276 A x' x h1)). Qed.
Lemma lem3320354 {A : Type'} (x : A) : (term87 A x) = (term88 A x).
Proof. exact (eq_refl (term87 A x)). Qed.
Lemma lem3320355 {A : Type'} (x : A) (x' : A) : (term89 A x x') = (term89 A x x').
Proof. exact (eq_refl (term89 A x x')). Qed.
Lemma lem3320356 {A : Type'} (x' : A) (x : A) : ((term86 A x x') = (term87 A x)) = ((term86 A x x') = (term88 A x)).
Proof. exact (MK_COMB (@lem3320355 A x x') (@lem3320354 A x)). Qed.
Lemma lem3320357 {A : Type'} (x' : A) (x : A) : (term86 A x x') = (term24 A x' x).
Proof. exact (eq_refl (term86 A x x')). Qed.
Lemma lem3320358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3320359 {A : Type'} (x' : A) (x : A) : (term89 A x x') = (term90 A x' x).
Proof. exact (MK_COMB (@lem3320358) (@lem3320357 A x' x)). Qed.
Lemma lem3320360 {A : Type'} (x : A) : (term88 A x) = (term88 A x).
Proof. exact (eq_refl (term88 A x)). Qed.
Lemma lem3320361 {A : Type'} (x' : A) (x : A) : ((term86 A x x') = (term88 A x)) = ((term24 A x' x) = (term88 A x)).
Proof. exact (MK_COMB (@lem3320359 A x' x) (@lem3320360 A x)). Qed.
Lemma lem3320362 {A : Type'} (x' : A) (x : A) : ((term86 A x x') = (term87 A x)) = ((term24 A x' x) = (term88 A x)).
Proof. exact (TRANS (@lem3320356 A x' x) (@lem3320361 A x' x)). Qed.
Lemma lem3320363 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term24 A x' x) = (term88 A x).
Proof. exact (EQ_MP (@lem3320362 A x' x) (@lem3320353 A x' x h1)). Qed.
Lemma lem3320364 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : term88 A x.
Proof. exact (EQ_MP (@lem3320363 A x' x h2) (@lem3320270 A s t x' x h1)). Qed.
Lemma lem3320418 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : s x'.
Proof. exact (proj1 (@lem3320124 A s t x' x h1)). Qed.
Lemma lem3320419 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : term91 A s x'.
Proof. exact (fun h0 : term61 A s x' => @lem3320418 A s t x' x h1). Qed.
Lemma lem3320421 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320422 {A : Type'} (s : A -> Prop) (x' : A) : (term91 A s x') = (s x').
Proof. exact (@lem3320421 (s x')). Qed.
Lemma lem3320423 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : s x'.
Proof. exact (EQ_MP (@lem3320422 A s x') (@lem3320419 A s t x' x h1)). Qed.
Lemma lem3320426 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3320428 {A : Type'} (s : A -> Prop) (x' : A) : (term61 A s x') = (term93 A s x').
Proof. exact (@lem3320426 (s x')). Qed.
Lemma lem3320431 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term61 A s x') : term93 A s x'.
Proof. exact (EQ_MP (@lem3320428 A s x') (@lem3320244 A s x' h1)). Qed.
Lemma lem3320434 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : False.
Proof. exact (@lem3320431 A s x' h1 (@lem3320423 A s t x' x h2)). Qed.
Lemma lem3320435 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : term94.
Proof. exact (fun h0 : ~ False => @lem3320434 A s t x' x h1 h2). Qed.
Lemma lem3320437 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320438 : term94 = False.
Proof. exact (@lem3320437 False). Qed.
Lemma lem3320439 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320438) (@lem3320435 A s t x' x h1 h2)). Qed.
Lemma lem3320467 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : t x'.
Proof. exact (proj2 (@lem3320122 A s t x' x h1)). Qed.
Lemma lem3320468 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : term91 A t x'.
Proof. exact (fun h0 : term61 A t x' => @lem3320467 A s t x' x h1). Qed.
Lemma lem3320470 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320471 {A : Type'} (t : A -> Prop) (x' : A) : (term91 A t x') = (t x').
Proof. exact (@lem3320470 (t x')). Qed.
Lemma lem3320472 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : t x'.
Proof. exact (EQ_MP (@lem3320471 A t x') (@lem3320468 A s t x' x h1)). Qed.
Lemma lem3320475 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3320477 {A : Type'} (t : A -> Prop) (x' : A) : (term61 A t x') = (term93 A t x').
Proof. exact (@lem3320475 (t x')). Qed.
Lemma lem3320480 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term61 A t x') : term93 A t x'.
Proof. exact (EQ_MP (@lem3320477 A t x') (@lem3320252 A t x' h1)). Qed.
Lemma lem3320483 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : False.
Proof. exact (@lem3320480 A t x' h1 (@lem3320472 A s t x' x h2)). Qed.
Lemma lem3320484 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : term94.
Proof. exact (fun h0 : ~ False => @lem3320483 A s t x' x h1 h2). Qed.
Lemma lem3320486 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320487 : term94 = False.
Proof. exact (@lem3320486 False). Qed.
Lemma lem3320488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320487) (@lem3320484 A s t x' x h1 h2)). Qed.
Lemma lem3320516 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3320517 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3320516 A x). Qed.
Lemma lem3320518 {A : Type'} (x : A) : term95 A x.
Proof. exact (fun h0 : term88 A x => @lem3320517 A x). Qed.
Lemma lem3320520 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320521 {A : Type'} (x : A) : (term95 A x) = (x = x).
Proof. exact (@lem3320520 (x = x)). Qed.
Lemma lem3320522 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3320521 A x) (@lem3320518 A x)). Qed.
Lemma lem3320525 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3320527 {A : Type'} (x : A) : (term88 A x) = (term96 A x).
Proof. exact (@lem3320525 (x = x)). Qed.
Lemma lem3320530 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : term96 A x.
Proof. exact (EQ_MP (@lem3320527 A x) (@lem3320337 A s t x' x h1 h2)). Qed.
Lemma lem3320533 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : False.
Proof. exact (@lem3320530 A s t x' x h1 h2 (@lem3320522 A x)). Qed.
Lemma lem3320534 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : term94.
Proof. exact (fun h0 : ~ False => @lem3320533 A s t x' x h1 h2). Qed.
Lemma lem3320536 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320537 : term94 = False.
Proof. exact (@lem3320536 False). Qed.
Lemma lem3320566 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : s x'.
Proof. exact (proj1 (@lem3320134 A s t x' x h1)). Qed.
Lemma lem3320567 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : term91 A s x'.
Proof. exact (fun h0 : term61 A s x' => @lem3320566 A s t x' x h1). Qed.
Lemma lem3320569 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320570 {A : Type'} (s : A -> Prop) (x' : A) : (term91 A s x') = (s x').
Proof. exact (@lem3320569 (s x')). Qed.
Lemma lem3320571 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : s x'.
Proof. exact (EQ_MP (@lem3320570 A s x') (@lem3320567 A s t x' x h1)). Qed.
Lemma lem3320574 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3320576 {A : Type'} (s : A -> Prop) (x' : A) : (term61 A s x') = (term93 A s x').
Proof. exact (@lem3320574 (s x')). Qed.
Lemma lem3320579 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term61 A s x') : term93 A s x'.
Proof. exact (EQ_MP (@lem3320576 A s x') (@lem3320268 A s x' h1)). Qed.
Lemma lem3320582 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : False.
Proof. exact (@lem3320579 A s x' h1 (@lem3320571 A s t x' x h2)). Qed.
Lemma lem3320583 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : term94.
Proof. exact (fun h0 : ~ False => @lem3320582 A s t x' x h1 h2). Qed.
Lemma lem3320585 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320586 : term94 = False.
Proof. exact (@lem3320585 False). Qed.
Lemma lem3320587 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320586) (@lem3320583 A s t x' x h1 h2)). Qed.
Lemma lem3320615 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3320616 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3320615 A x). Qed.
Lemma lem3320617 {A : Type'} (x : A) : term95 A x.
Proof. exact (fun h0 : term88 A x => @lem3320616 A x). Qed.
Lemma lem3320619 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320620 {A : Type'} (x : A) : (term95 A x) = (x = x).
Proof. exact (@lem3320619 (x = x)). Qed.
Lemma lem3320621 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3320620 A x) (@lem3320617 A x)). Qed.
Lemma lem3320624 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3320626 {A : Type'} (x : A) : (term88 A x) = (term96 A x).
Proof. exact (@lem3320624 (x = x)). Qed.
Lemma lem3320629 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : term96 A x.
Proof. exact (EQ_MP (@lem3320626 A x) (@lem3320364 A s t x' x h1 h2)). Qed.
Lemma lem3320632 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : False.
Proof. exact (@lem3320629 A s t x' x h1 h2 (@lem3320621 A x)). Qed.
Lemma lem3320633 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : term94.
Proof. exact (fun h0 : ~ False => @lem3320632 A s t x' x h1 h2). Qed.
Lemma lem3320635 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320636 : term94 = False.
Proof. exact (@lem3320635 False). Qed.
Lemma lem3320665 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : t x'.
Proof. exact (proj2 (@lem3320134 A s t x' x h1)). Qed.
Lemma lem3320666 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : term91 A t x'.
Proof. exact (fun h0 : term61 A t x' => @lem3320665 A s t x' x h1). Qed.
Lemma lem3320668 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320669 {A : Type'} (t : A -> Prop) (x' : A) : (term91 A t x') = (t x').
Proof. exact (@lem3320668 (t x')). Qed.
Lemma lem3320670 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : t x'.
Proof. exact (EQ_MP (@lem3320669 A t x') (@lem3320666 A s t x' x h1)). Qed.
Lemma lem3320673 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3320675 {A : Type'} (t : A -> Prop) (x' : A) : (term61 A t x') = (term93 A t x').
Proof. exact (@lem3320673 (t x')). Qed.
Lemma lem3320678 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term61 A t x') : term93 A t x'.
Proof. exact (EQ_MP (@lem3320675 A t x') (@lem3320284 A t x' h1)). Qed.
Lemma lem3320681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : False.
Proof. exact (@lem3320678 A t x' h1 (@lem3320670 A s t x' x h2)). Qed.
Lemma lem3320682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : term94.
Proof. exact (fun h0 : ~ False => @lem3320681 A s t x' x h1 h2). Qed.
Lemma lem3320684 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3320685 : term94 = False.
Proof. exact (@lem3320684 False). Qed.
Lemma lem3320686 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320685) (@lem3320682 A s t x' x h1 h2)). Qed.
Lemma lem3320687 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3320636) (@lem3320633 A s t x' x h1 h2)). Qed.
Lemma lem3320688 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3320537) (@lem3320534 A s t x' x h1 h2)). Qed.
Lemma lem3320689 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : (term61 A t x') = False.
Proof. exact (prop_ext (fun h3 : term61 A t x' => @lem3320686 A s t x' x h1 h2) (fun h3 : False => @lem3320284 A t x' h1)). Qed.
Lemma lem3320690 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320689 A s t x' x h1 h2) (@lem3320284 A t x' h1)). Qed.
Lemma lem3320691 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3320687 A s t x' x h1 h2) (fun h3 : False => @lem3320276 A x' x h2)). Qed.
Lemma lem3320692 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3320691 A s t x' x h1 h2) (@lem3320276 A x' x h2)). Qed.
Lemma lem3320693 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : (term61 A s x') = False.
Proof. exact (prop_ext (fun h3 : term61 A s x' => @lem3320587 A s t x' x h1 h2) (fun h3 : False => @lem3320268 A s x' h1)). Qed.
Lemma lem3320694 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320693 A s t x' x h1 h2) (@lem3320268 A s x' h1)). Qed.
Lemma lem3320695 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3320688 A s t x' x h1 h2) (fun h3 : False => @lem3320260 A x' x h2)). Qed.
Lemma lem3320696 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3320695 A s t x' x h1 h2) (@lem3320260 A x' x h2)). Qed.
Lemma lem3320697 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : (term61 A t x') = False.
Proof. exact (prop_ext (fun h3 : term61 A t x' => @lem3320488 A s t x' x h1 h2) (fun h3 : False => @lem3320252 A t x' h1)). Qed.
Lemma lem3320698 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320697 A s t x' x h1 h2) (@lem3320252 A t x' h1)). Qed.
Lemma lem3320699 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : (term61 A s x') = False.
Proof. exact (prop_ext (fun h3 : term61 A s x' => @lem3320439 A s t x' x h1 h2) (fun h3 : False => @lem3320244 A s x' h1)). Qed.
Lemma lem3320700 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320699 A s t x' x h1 h2) (@lem3320244 A s x' h1)). Qed.
Lemma lem3320701 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : (term61 A t x') = False.
Proof. exact (prop_ext (fun h3 : term61 A t x' => @lem3320690 A s t x' x h1 h2) (fun h3 : False => @lem3320236 A t x' h1)). Qed.
Lemma lem3320702 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320701 A s t x' x h1 h2) (@lem3320236 A t x' h1)). Qed.
Lemma lem3320703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3320692 A s t x' x h1 h2) (fun h3 : False => @lem3320220 A x' x h2)). Qed.
Lemma lem3320704 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3320703 A s t x' x h1 h2) (@lem3320220 A x' x h2)). Qed.
Lemma lem3320705 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : (term61 A s x') = False.
Proof. exact (prop_ext (fun h3 : term61 A s x' => @lem3320694 A s t x' x h1 h2) (fun h3 : False => @lem3320204 A s x' h1)). Qed.
Lemma lem3320706 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320705 A s t x' x h1 h2) (@lem3320204 A s x' h1)). Qed.
Lemma lem3320707 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3320696 A s t x' x h1 h2) (fun h3 : False => @lem3320188 A x' x h2)). Qed.
Lemma lem3320708 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3320707 A s t x' x h1 h2) (@lem3320188 A x' x h2)). Qed.
Lemma lem3320709 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : (term61 A t x') = False.
Proof. exact (prop_ext (fun h3 : term61 A t x' => @lem3320698 A s t x' x h1 h2) (fun h3 : False => @lem3320172 A t x' h1)). Qed.
Lemma lem3320710 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320709 A s t x' x h1 h2) (@lem3320172 A t x' h1)). Qed.
Lemma lem3320711 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : (term61 A s x') = False.
Proof. exact (prop_ext (fun h3 : term61 A s x' => @lem3320700 A s t x' x h1 h2) (fun h3 : False => @lem3320156 A s x' h1)). Qed.
Lemma lem3320712 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320711 A s t x' x h1 h2) (@lem3320156 A s x' h1)). Qed.
Lemma lem3320713 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : (term61 A t x') = False.
Proof. exact (prop_ext (fun h3 : term61 A t x' => @lem3320702 A s t x' x h1 h2) (fun h3 : False => @lem3320236 A t x' h1)). Qed.
Lemma lem3320714 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term77 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320713 A s t x' x h1 h2) (@lem3320236 A t x' h1)). Qed.
Lemma lem3320715 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3320704 A s t x' x h1 h2) (fun h3 : False => @lem3320220 A x' x h2)). Qed.
Lemma lem3320716 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3320715 A s t x' x h1 h2) (@lem3320220 A x' x h2)). Qed.
Lemma lem3320717 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : (term61 A s x') = False.
Proof. exact (prop_ext (fun h3 : term61 A s x' => @lem3320706 A s t x' x h1 h2) (fun h3 : False => @lem3320204 A s x' h1)). Qed.
Lemma lem3320718 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term77 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320717 A s t x' x h1 h2) (@lem3320204 A s x' h1)). Qed.
Lemma lem3320719 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3320708 A s t x' x h1 h2) (fun h3 : False => @lem3320188 A x' x h2)). Qed.
Lemma lem3320720 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3320719 A s t x' x h1 h2) (@lem3320188 A x' x h2)). Qed.
Lemma lem3320721 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : (term61 A t x') = False.
Proof. exact (prop_ext (fun h3 : term61 A t x' => @lem3320710 A s t x' x h1 h2) (fun h3 : False => @lem3320172 A t x' h1)). Qed.
Lemma lem3320722 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A t x') (h2 : term80 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320721 A s t x' x h1 h2) (@lem3320172 A t x' h1)). Qed.
Lemma lem3320723 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : (term61 A s x') = False.
Proof. exact (prop_ext (fun h3 : term61 A s x' => @lem3320712 A s t x' x h1 h2) (fun h3 : False => @lem3320156 A s x' h1)). Qed.
Lemma lem3320724 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term61 A s x') (h2 : term80 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320723 A s t x' x h1 h2) (@lem3320156 A s x' h1)). Qed.
Lemma lem3320725 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) (h2 : term59 A s x' x) : False.
Proof. exact (or_elim (@lem3320137 A s x' x h2) (fun h0 : term61 A s x' => @lem3320718 A s t x' x h0 h1) (fun h0 : x' = x => @lem3320716 A s t x' x h1 h0)). Qed.
Lemma lem3320726 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term77 A s t x' x) : False.
Proof. exact (or_elim (@lem3320132 A s t x' x h1) (fun h0 : term59 A s x' x => @lem3320725 A t s x' x h1 h0) (fun h0 : term61 A t x' => @lem3320714 A s t x' x h0 h1)). Qed.
Lemma lem3320727 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term80 A s t x' x) (h2 : term68 A s t x') : False.
Proof. exact (or_elim (@lem3320127 A s t x' h2) (fun h0 : term61 A s x' => @lem3320724 A s t x' x h0 h1) (fun h0 : term61 A t x' => @lem3320722 A s t x' x h0 h1)). Qed.
Lemma lem3320728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term80 A s t x' x) : False.
Proof. exact (or_elim (@lem3320121 A s t x' x h1) (fun h0 : term68 A s t x' => @lem3320727 A x s t x' h1 h0) (fun h0 : x' = x => @lem3320720 A s t x' x h1 h0)). Qed.
Lemma lem3320729 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term55 A s t x' x) : False.
Proof. exact (or_elim (@lem3320118 A s t x' x h1) (fun h0 : term80 A s t x' x => @lem3320728 A s t x' x h0) (fun h0 : term77 A s t x' x => @lem3320726 A s t x' x h0)). Qed.
Lemma lem3320730 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term55 A s t x' x) : (term55 A s t x' x) = False.
Proof. exact (prop_ext (fun h2 : term55 A s t x' x => @lem3320729 A s t x' x h1) (fun h2 : False => @lem3319964 A s t x' x h1)). Qed.
Lemma lem3320731 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term55 A s t x' x) : False.
Proof. exact (EQ_MP (@lem3320730 A s t x' x h1) (@lem3319964 A s t x' x h1)). Qed.
Lemma lem3320732 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : term54 A s t x' x.
Proof. exact (fun h0 : term55 A s t x' x => @lem3320731 A s t x' x h0). Qed.
Lemma lem3320733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term28 A s x t x') = (term36 A s t x' x).
Proof. exact (EQ_MP (@lem3319963 A s t x' x) (@lem3320732 A s t x' x)). Qed.
Lemma lem3320738 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term39 A s t x.
Proof. exact (fun x' : A => @lem3320733 A s t x' x). Qed.
Lemma lem3320743 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term41 A s t.
Proof. exact (fun x : A => @lem3320738 A s t x). Qed.
Lemma lem3320748 {A : Type'} (s : A -> Prop) : term43 A s.
Proof. exact (fun t : A -> Prop => @lem3320743 A s t). Qed.
Lemma lem3320753 {A : Type'} : term45 A.
Proof. exact (fun s : A -> Prop => @lem3320748 A s). Qed.
Lemma lem3320754 {A : Type'} : term47 A.
Proof. exact (EQ_MP (@lem3319959 A) (@lem3320753 A)). Qed.
Lemma lem3320756 {A : Type'} : term47 A.
Proof. exact (@lem3319851 A (@lem3320754 A)). Qed.
Lemma lem3320757 {A : Type'} (h1 : term48 A) : False.
Proof. exact (@lem3320756 A (@lem3319835 A h1)). Qed.
Lemma lem3320758 {A : Type'} (h1 : term48 A) : (term48 A) = False.
Proof. exact (prop_ext (fun h2 : term48 A => @lem3320757 A h1) (fun h2 : False => @lem3319835 A h1)). Qed.
Lemma lem3320759 {A : Type'} (h1 : term48 A) : False.
Proof. exact (EQ_MP (@lem3320758 A h1) (@lem3319835 A h1)). Qed.
Lemma lem3320760 {A : Type'} : term47 A.
Proof. exact (fun h0 : term48 A => @lem3320759 A h0). Qed.
Lemma lem3320761 {A : Type'} : term45 A.
Proof. exact (EQ_MP (@lem3319834 A) (@lem3320760 A)). Qed.
Lemma lem3320762 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3319830 A) (@lem3320761 A)). Qed.
Lemma lem3320763 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3319708 A) (@lem3320762 A)). Qed.
