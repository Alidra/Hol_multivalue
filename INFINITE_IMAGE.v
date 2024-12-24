Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_IMAGE_term_abbrevs.
Require Import CONTRAPOS_THM_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_spec.
Require Import INFINITE_spec.
Require Import INJECTIVE_ON_LEFT_INVERSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Require Import thm951_spec.
Require Import thm952_spec.
Lemma lem3624674 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem3624675 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem3624674 A B h1 f). Qed.
Lemma lem3624676 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem3624677 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem3624676 A B f) (@lem3624675 A B f h1)). Qed.
Lemma lem3624678 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term3 A B f s.
Proof. exact (@lem3624677 A B f h1 s). Qed.
Lemma lem3624679 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem3624680 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (EQ_MP (@lem3624679 A B f s) (@lem3624678 A B f s h1)). Qed.
Lemma lem3624681 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3624682 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) (h2 : @FINITE A s) : term5 A B f s.
Proof. exact (@lem3624680 A B f s h1 (@lem3624681 A s h2)). Qed.
Lemma lem3624683 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term6 A B f s.
Proof. exact (fun h0 : term0 A B => @lem3624682 A B f s h0 h1). Qed.
Lemma lem3624684 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem3624685 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) (h2 : @FINITE A s) : term5 A B f s.
Proof. exact (@lem3624683 A B f s h2 (@lem3624684 A B h1)). Qed.
Lemma lem3624686 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3624685 A B f s h1 h0). Qed.
Lemma lem3624687 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun s : A -> Prop => @lem3624686 A B f s h1). Qed.
Lemma lem3624688 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem3624687 A B f h1). Qed.
Lemma lem3624689 {A B : Type'} : term7 A B.
Proof. exact (fun h0 : term0 A B => @lem3624688 A B h0). Qed.
Lemma lem3624690 {A B : Type'} : term0 A B.
Proof. exact (@lem3624689 A B (@lem3615104 A B)). Qed.
Lemma lem3624691 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem3624690 A B f). Qed.
Lemma lem3624692 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem3624693 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem3624692 A B f) (@lem3624691 A B f)). Qed.
Lemma lem3624694 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem3624693 A B f s). Qed.
Lemma lem3624695 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem3624697 (t1 : Prop) : term8 t1.
Proof. exact (@lem10414 t1). Qed.
Lemma lem3624698 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (eq_refl (term8 t1)). Qed.
Lemma lem3624699 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem3624698 t1) (@lem3624697 t1)). Qed.
Lemma lem3624700 (t1 : Prop) (t2 : Prop) : term10 t1 t2.
Proof. exact (@lem3624699 t1 t2). Qed.
Lemma lem3624701 (t2 : Prop) (t1 : Prop) : (term10 t1 t2) = ((term11 t1 t2) = (t2 -> t1)).
Proof. exact (eq_refl (term10 t1 t2)). Qed.
Lemma lem3624703 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem3624704 {A : Type'} (s : A -> Prop) : (term12 A s) = ((@INFINITE A s) = (term13 A s)).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3624706 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term14 _91401 _91404 f.
Proof. exact (@lem3566182 _91401 _91404 f). Qed.
Lemma lem3624707 {_91401 _91404 : Type'} (f : _91401 -> _91404) : (term14 _91401 _91404 f) = (term15 _91401 _91404 f).
Proof. exact (eq_refl (term14 _91401 _91404 f)). Qed.
Lemma lem3624708 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term15 _91401 _91404 f.
Proof. exact (EQ_MP (@lem3624707 _91401 _91404 f) (@lem3624706 _91401 _91404 f)). Qed.
Lemma lem3624709 {_91401 _91404 : Type'} (f : _91401 -> _91404) (s : _91401 -> Prop) : term16 _91401 _91404 f s.
Proof. exact (@lem3624708 _91401 _91404 f s). Qed.
Lemma lem3624710 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term16 _91401 _91404 f s) = ((term17 _91401 _91404 s f) = (term18 _91401 _91404 s f)).
Proof. exact (eq_refl (term16 _91401 _91404 f s)). Qed.
Lemma lem3624713 (q : Prop) (p : Prop) (r : Prop) : (term19 p q r) = (term20 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem3624714 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term21 A B f s) = (term22 A B f s).
Proof. exact (@lem3624713 (term17 A B s f) (@INFINITE A s) (term23 A B f s)). Qed.
Lemma lem3624718 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term17 _91401 _91404 s f) = (term18 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3624710 _91401 _91404 s f) (@lem3624709 _91401 _91404 f s)). Qed.
Lemma lem3624719 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term17 A B s f) = (term18 A B s f).
Proof. exact (@lem3624718 A B s f). Qed.
Lemma lem3624732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3624733 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term24 A B s f) = (term25 A B s f).
Proof. exact (MK_COMB (@lem3624732) (@lem3624719 A B s f)). Qed.
Lemma lem3624736 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term26 A B f s) = (term26 A B f s).
Proof. exact (eq_refl (term26 A B f s)). Qed.
Lemma lem3624737 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term22 A B f s) = (term27 A B f s).
Proof. exact (MK_COMB (@lem3624733 A B s f) (@lem3624736 A B f s)). Qed.
Lemma lem3624740 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term21 A B f s) = (term27 A B f s).
Proof. exact (TRANS (@lem3624714 A B f s) (@lem3624737 A B f s)). Qed.
Lemma lem3624741 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term27 A B f s) = (term21 A B f s).
Proof. exact (SYM (@lem3624740 A B f s)). Qed.
Lemma lem3624742 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term18 A B s f) : term18 A B s f.
Proof. exact (h1). Qed.
Lemma lem3624743 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term28 A B s g f) : term28 A B s g f.
Proof. exact (h1). Qed.
Lemma lem3624747 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term13 A s).
Proof. exact (EQ_MP (@lem3624704 A s) (@lem3624703 A s)). Qed.
Lemma lem3624748 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term13 A s).
Proof. exact (@lem3624747 A s). Qed.
Lemma lem3624749 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3624750 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3624749) (@lem3624748 A s)). Qed.
Lemma lem3624752 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term13 A s).
Proof. exact (EQ_MP (@lem3624704 A s) (@lem3624703 A s)). Qed.
Lemma lem3624753 {B : Type'} (s : B -> Prop) : (@INFINITE B s) = (term13 B s).
Proof. exact (@lem3624752 B s). Qed.
Lemma lem3624754 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term23 A B f s) = (term31 A B f s).
Proof. exact (@lem3624753 B (@IMAGE A B f s)). Qed.
Lemma lem3624755 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term26 A B f s) = (term32 A B f s).
Proof. exact (MK_COMB (@lem3624750 A s) (@lem3624754 A B f s)). Qed.
Lemma lem3624757 (t2 : Prop) (t1 : Prop) : (term11 t1 t2) = (t2 -> t1).
Proof. exact (EQ_MP (@lem3624701 t2 t1) (@lem3624700 t1 t2)). Qed.
Lemma lem3624758 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term32 A B f s) = (term33 A B f s).
Proof. exact (@lem3624757 (term5 A B f s) (@FINITE A s)). Qed.
Lemma lem3624761 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term26 A B f s) = (term33 A B f s).
Proof. exact (TRANS (@lem3624755 A B f s) (@lem3624758 A B f s)). Qed.
Lemma lem3624762 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term33 A B f s) = (term26 A B f s).
Proof. exact (SYM (@lem3624761 A B f s)). Qed.
Lemma lem3624763 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term5 A B f s) : term5 A B f s.
Proof. exact (h1). Qed.
Lemma lem3624764 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : s = (term34 A B g f s)) : s = (term34 A B g f s).
Proof. exact (h1). Qed.
Lemma lem3624765 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (eq_refl (term35 A)). Qed.
Lemma lem3624766 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : s = (term34 A B g f s)) : (term36 A s) = (term37 A B g f s).
Proof. exact (MK_COMB (@lem3624765 A) (@lem3624764 A B g f s h1)). Qed.
Lemma lem3624767 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term37 A B g f s) = (term38 A B g f s).
Proof. exact (eq_refl (term37 A B g f s)). Qed.
Lemma lem3624768 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem3624769 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term36 A s) = (term37 A B g f s)) = ((term36 A s) = (term38 A B g f s)).
Proof. exact (MK_COMB (@lem3624768 A s) (@lem3624767 A B g f s)). Qed.
Lemma lem3624770 {A : Type'} (s : A -> Prop) : (term36 A s) = (@FINITE A s).
Proof. exact (eq_refl (term36 A s)). Qed.
Lemma lem3624771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3624772 {A : Type'} (s : A -> Prop) : (term39 A s) = (term40 A s).
Proof. exact (MK_COMB (@lem3624771) (@lem3624770 A s)). Qed.
Lemma lem3624773 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term38 A B g f s) = (term38 A B g f s).
Proof. exact (eq_refl (term38 A B g f s)). Qed.
Lemma lem3624774 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term36 A s) = (term38 A B g f s)) = ((@FINITE A s) = (term38 A B g f s)).
Proof. exact (MK_COMB (@lem3624772 A s) (@lem3624773 A B g f s)). Qed.
Lemma lem3624775 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term36 A s) = (term37 A B g f s)) = ((@FINITE A s) = (term38 A B g f s)).
Proof. exact (TRANS (@lem3624769 A B g f s) (@lem3624774 A B g f s)). Qed.
Lemma lem3624776 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : s = (term34 A B g f s)) : (@FINITE A s) = (term38 A B g f s).
Proof. exact (EQ_MP (@lem3624775 A B g f s) (@lem3624766 A B g f s h1)). Qed.
Lemma lem3624777 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : s = (term34 A B g f s)) : (term38 A B g f s) = (@FINITE A s).
Proof. exact (SYM (@lem3624776 A B g f s h1)). Qed.
Lemma lem3624788 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term28 A B s g f) (h2 : term5 A B f s) : term41 A B s g f.
Proof. exact (conj (@lem3624763 A B f s h2) (@lem3624743 A B s g f h1)). Qed.
Lemma lem3624806 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term42 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3624807 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term42 A s t).
Proof. exact (@lem3624806 A s t). Qed.
Lemma lem3624808 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (s = (term34 A B g f s)) = (term43 A B g f s).
Proof. exact (@lem3624807 A s (term34 A B g f s)). Qed.
Lemma lem3624817 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term44 A B s g f) = (term44 A B s g f).
Proof. exact (eq_refl (term44 A B s g f)). Qed.
Lemma lem3624818 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term45 A B g f s) = (term46 A B g f s).
Proof. exact (MK_COMB (@lem3624817 A B s g f) (@lem3624808 A B g f s)). Qed.
Lemma lem3624821 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term46 A B g f s) = (term45 A B g f s).
Proof. exact (SYM (@lem3624818 A B g f s)). Qed.
Lemma lem3624833 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3624834 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3624833 A P x). Qed.
Lemma lem3624835 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3624834 A s x). Qed.
Lemma lem3624836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3624837 {A : Type'} (s : A -> Prop) (x : A) : (term47 A x s) = (term48 A s x).
Proof. exact (MK_COMB (@lem3624836) (@lem3624835 A s x)). Qed.
Lemma lem3624840 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : ((term49 A B g f x) = x) = ((term49 A B g f x) = x).
Proof. exact (eq_refl ((term49 A B g f x) = x)). Qed.
Lemma lem3624841 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term50 A B s g f x) = (term51 A B s g f x).
Proof. exact (MK_COMB (@lem3624837 A s x) (@lem3624840 A B g f x)). Qed.
Lemma lem3624844 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term52 A B s g f) = (term53 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3624841 A B s g f x)). Qed.
Lemma lem3624845 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3624846 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term28 A B s g f) = (term54 A B s g f).
Proof. exact (MK_COMB (@lem3624845 A) (@lem3624844 A B s g f)). Qed.
Lemma lem3624851 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term55 A B f s) = (term55 A B f s).
Proof. exact (eq_refl (term55 A B f s)). Qed.
Lemma lem3624852 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term41 A B s g f) = (term56 A B s g f).
Proof. exact (MK_COMB (@lem3624851 A B f s) (@lem3624846 A B s g f)). Qed.
Lemma lem3624855 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3624856 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term44 A B s g f) = (term57 A B s g f).
Proof. exact (MK_COMB (@lem3624855) (@lem3624852 A B s g f)). Qed.
Lemma lem3624864 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3624865 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3624864 A P x). Qed.
Lemma lem3624866 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3624865 A s x). Qed.
Lemma lem3624867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3624868 {A : Type'} (s : A -> Prop) (x : A) : (term58 A x s) = (term59 A s x).
Proof. exact (MK_COMB (@lem3624867) (@lem3624866 A s x)). Qed.
Lemma lem3624870 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term60 A B y f s) = (term61 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3624871 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term62 A B y f s) = (term63 A B y f s).
Proof. exact (@lem3624870 B A y f s). Qed.
Lemma lem3624872 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term64 A B x g f s) = (term65 A B x g f s).
Proof. exact (@lem3624871 A B x g (@IMAGE A B f s)). Qed.
Lemma lem3624882 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term60 A B y f s) = (term61 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3624883 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term60 A B y f s) = (term61 A B y f s).
Proof. exact (@lem3624882 A B y f s). Qed.
Lemma lem3624884 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term60 A B x f s) = (term61 A B x f s).
Proof. exact (@lem3624883 A B x f s). Qed.
Lemma lem3624894 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3624895 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3624894 A P x). Qed.
Lemma lem3624896 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3624895 A s x). Qed.
Lemma lem3624897 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term66 A B x f x') = (term66 A B x f x').
Proof. exact (eq_refl (term66 A B x f x')). Qed.
Lemma lem3624898 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term67 A B x f x' s) = (term68 A B x f s x').
Proof. exact (MK_COMB (@lem3624897 A B x f x') (@lem3624896 A s x')). Qed.
Lemma lem3624901 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term69 A B x f s) = (term70 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3624898 A B x f s x')). Qed.
Lemma lem3624902 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3624903 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term61 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3624902 A) (@lem3624901 A B x f s)). Qed.
Lemma lem3624908 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term60 A B x f s) = (term71 A B x f s).
Proof. exact (TRANS (@lem3624884 A B x f s) (@lem3624903 A B x f s)). Qed.
Lemma lem3624909 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term72 A B x g x') = (term72 A B x g x').
Proof. exact (eq_refl (term72 A B x g x')). Qed.
Lemma lem3624910 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term73 A B x g x' f s) = (term74 A B x g x' f s).
Proof. exact (MK_COMB (@lem3624909 A B x g x') (@lem3624908 A B x' f s)). Qed.
Lemma lem3624913 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term75 A B x g f s) = (term76 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3624910 A B x g x' f s)). Qed.
Lemma lem3624914 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3624915 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term65 A B x g f s) = (term77 A B x g f s).
Proof. exact (MK_COMB (@lem3624914 B) (@lem3624913 A B x g f s)). Qed.
Lemma lem3624920 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term64 A B x g f s) = (term77 A B x g f s).
Proof. exact (TRANS (@lem3624872 A B x g f s) (@lem3624915 A B x g f s)). Qed.
Lemma lem3624921 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((@IN A x s) = (term64 A B x g f s)) = ((s x) = (term77 A B x g f s)).
Proof. exact (MK_COMB (@lem3624868 A s x) (@lem3624920 A B x g f s)). Qed.
Lemma lem3624924 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term78 A B g f s) = (term79 A B g f s).
Proof. exact (fun_ext (fun x : A => @lem3624921 A B x g f s)). Qed.
Lemma lem3624925 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3624926 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term43 A B g f s) = (term80 A B g f s).
Proof. exact (MK_COMB (@lem3624925 A) (@lem3624924 A B g f s)). Qed.
Lemma lem3624931 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term46 A B g f s) = (term81 A B g f s).
Proof. exact (MK_COMB (@lem3624856 A B s g f) (@lem3624926 A B g f s)). Qed.
Lemma lem3624934 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term81 A B g f s) = (term46 A B g f s).
Proof. exact (SYM (@lem3624931 A B g f s)). Qed.
Lemma lem3624936 (p : Prop) : p = (term82 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3624937 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term81 A B g f s) = (term83 A B g f s).
Proof. exact (@lem3624936 (term81 A B g f s)). Qed.
Lemma lem3624938 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term83 A B g f s) = (term81 A B g f s).
Proof. exact (SYM (@lem3624937 A B g f s)). Qed.
Lemma lem3624939 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term84 A B g f s) : term84 A B g f s.
Proof. exact (h1). Qed.
Lemma lem3624942 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term83 A B g f s) : term83 A B g f s.
Proof. exact (h1). Qed.
Lemma lem3624943 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term85 A B g f s.
Proof. exact (fun h0 : term83 A B g f s => @lem3624942 A B g f s h0). Qed.
Lemma lem3624944 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term85 A B g f s) : term85 A B g f s.
Proof. exact (h1). Qed.
Lemma lem3624945 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term83 A B g f s) : term83 A B g f s.
Proof. exact (h1). Qed.
Lemma lem3624946 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term83 A B g f s) (h2 : term85 A B g f s) : term83 A B g f s.
Proof. exact (@lem3624944 A B g f s h2 (@lem3624945 A B g f s h1)). Qed.
Lemma lem3624947 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term83 A B g f s) : term86 A B g f s.
Proof. exact (fun h0 : term85 A B g f s => @lem3624946 A B g f s h1 h0). Qed.
Lemma lem3624948 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term85 A B g f s) : term85 A B g f s.
Proof. exact (h1). Qed.
Lemma lem3624949 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term83 A B g f s) (h2 : term85 A B g f s) : term83 A B g f s.
Proof. exact (@lem3624947 A B g f s h1 (@lem3624948 A B g f s h2)). Qed.
Lemma lem3624950 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term85 A B g f s) : term85 A B g f s.
Proof. exact (fun h0 : term83 A B g f s => @lem3624949 A B g f s h0 h1). Qed.
Lemma lem3624951 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term87 A B g f s.
Proof. exact (fun h0 : term85 A B g f s => @lem3624950 A B g f s h0). Qed.
Lemma lem3624954 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term85 A B g f s.
Proof. exact (@lem3624951 A B g f s (@lem3624943 A B g f s)). Qed.
Lemma lem3624955 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term85 A B g f s.
Proof. exact (@lem3624954 A B g f s). Qed.
Lemma lem3624969 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3624970 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term83 A B g f s) = (term88 A B g f s).
Proof. exact (@lem3624969 (term84 A B g f s)). Qed.
Lemma lem3624972 (t : Prop) : (term89 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3624973 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term88 A B g f s) = (term81 A B g f s).
Proof. exact (@lem3624972 (term81 A B g f s)). Qed.
Lemma lem3624976 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term83 A B g f s) = (term81 A B g f s).
Proof. exact (TRANS (@lem3624970 A B g f s) (@lem3624973 A B g f s)). Qed.
Lemma lem3625073 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term90 A B f s) = (term91 A B f s).
Proof. exact (fun_ext (fun g : B -> A => @lem3624976 A B g f s)). Qed.
Lemma lem3625074 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem3625075 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term92 A B f s) = (term93 A B f s).
Proof. exact (MK_COMB (@lem3625074 A B) (@lem3625073 A B f s)). Qed.
Lemma lem3625080 {A B : Type'} (s : A -> Prop) : (term94 A B s) = (term95 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3625075 A B f s)). Qed.
Lemma lem3625081 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3625082 {A B : Type'} (s : A -> Prop) : (term96 A B s) = (term97 A B s).
Proof. exact (MK_COMB (@lem3625081 A B) (@lem3625080 A B s)). Qed.
Lemma lem3625087 {A B : Type'} : (term98 A B) = (term99 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3625082 A B s)). Qed.
Lemma lem3625088 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3625097 {A B : Type'} : (term100 A B) = (term101 A B).
Proof. exact (MK_COMB (@lem3625088 A) (@lem3625087 A B)). Qed.
Lemma lem3625102 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term68 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term68 A B x f s x')). Qed.
Lemma lem3625103 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term70 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3625102 A B x f s x')). Qed.
Lemma lem3625104 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3625105 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term71 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3625104 A) (@lem3625103 A B x f s)). Qed.
Lemma lem3625108 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term72 A B x g x') = (term72 A B x g x').
Proof. exact (eq_refl (term72 A B x g x')). Qed.
Lemma lem3625109 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term74 A B x g x' f s) = (term74 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625108 A B x g x') (@lem3625105 A B x' f s)). Qed.
Lemma lem3625110 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term76 A B x g f s) = (term76 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625109 A B x g x' f s)). Qed.
Lemma lem3625111 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625112 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term77 A B x g f s) = (term77 A B x g f s).
Proof. exact (MK_COMB (@lem3625111 B) (@lem3625110 A B x g f s)). Qed.
Lemma lem3625115 {A : Type'} (s : A -> Prop) (x : A) : (term59 A s x) = (term59 A s x).
Proof. exact (eq_refl (term59 A s x)). Qed.
Lemma lem3625116 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((s x) = (term77 A B x g f s)) = ((s x) = (term77 A B x g f s)).
Proof. exact (MK_COMB (@lem3625115 A s x) (@lem3625112 A B x g f s)). Qed.
Lemma lem3625117 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term79 A B g f s) = (term79 A B g f s).
Proof. exact (fun_ext (fun x : A => @lem3625116 A B x g f s)). Qed.
Lemma lem3625118 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625119 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term80 A B g f s) = (term80 A B g f s).
Proof. exact (MK_COMB (@lem3625118 A) (@lem3625117 A B g f s)). Qed.
Lemma lem3625124 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term51 A B s g f x) = (term51 A B s g f x).
Proof. exact (eq_refl (term51 A B s g f x)). Qed.
Lemma lem3625125 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term53 A B s g f) = (term53 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3625124 A B s g f x)). Qed.
Lemma lem3625126 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625127 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term54 A B s g f) = (term54 A B s g f).
Proof. exact (MK_COMB (@lem3625126 A) (@lem3625125 A B s g f)). Qed.
Lemma lem3625130 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term55 A B f s) = (term55 A B f s).
Proof. exact (eq_refl (term55 A B f s)). Qed.
Lemma lem3625131 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term56 A B s g f) = (term56 A B s g f).
Proof. exact (MK_COMB (@lem3625130 A B f s) (@lem3625127 A B s g f)). Qed.
Lemma lem3625132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3625133 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term57 A B s g f) = (term57 A B s g f).
Proof. exact (MK_COMB (@lem3625132) (@lem3625131 A B s g f)). Qed.
Lemma lem3625134 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term81 A B g f s) = (term81 A B g f s).
Proof. exact (MK_COMB (@lem3625133 A B s g f) (@lem3625119 A B g f s)). Qed.
Lemma lem3625135 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term91 A B f s) = (term91 A B f s).
Proof. exact (fun_ext (fun g : B -> A => @lem3625134 A B g f s)). Qed.
Lemma lem3625136 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem3625137 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term93 A B f s) = (term93 A B f s).
Proof. exact (MK_COMB (@lem3625136 A B) (@lem3625135 A B f s)). Qed.
Lemma lem3625138 {A B : Type'} (s : A -> Prop) : (term95 A B s) = (term95 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3625137 A B f s)). Qed.
Lemma lem3625139 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3625140 {A B : Type'} (s : A -> Prop) : (term97 A B s) = (term97 A B s).
Proof. exact (MK_COMB (@lem3625139 A B) (@lem3625138 A B s)). Qed.
Lemma lem3625141 {A B : Type'} : (term99 A B) = (term99 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3625140 A B s)). Qed.
Lemma lem3625142 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3625143 {A B : Type'} : (term101 A B) = (term101 A B).
Proof. exact (MK_COMB (@lem3625142 A) (@lem3625141 A B)). Qed.
Lemma lem3625198 {A B : Type'} : (term100 A B) = (term101 A B).
Proof. exact (TRANS (@lem3625097 A B) (@lem3625143 A B)). Qed.
Lemma lem3625199 {A B : Type'} : (term101 A B) = (term100 A B).
Proof. exact (SYM (@lem3625198 A B)). Qed.
Lemma lem3625200 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term56 A B s g f.
Proof. exact (h1). Qed.
Lemma lem3625202 (p : Prop) : p = (term82 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3625203 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((s x) = (term77 A B x g f s)) = (term102 A B x g f s).
Proof. exact (@lem3625202 ((s x) = (term77 A B x g f s))). Qed.
Lemma lem3625204 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term102 A B x g f s) = ((s x) = (term77 A B x g f s)).
Proof. exact (SYM (@lem3625203 A B x g f s)). Qed.
Lemma lem3625205 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x g f s) : term103 A B x g f s.
Proof. exact (h1). Qed.
Lemma lem3625213 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term51 A B s g f x) = (term104 A B s g f x).
Proof. exact (@lem17265 (s x) ((term49 A B g f x) = x)). Qed.
Lemma lem3625214 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term53 A B s g f) = (term105 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3625213 A B s g f x)). Qed.
Lemma lem3625215 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625216 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term54 A B s g f) = (term106 A B s g f).
Proof. exact (MK_COMB (@lem3625215 A) (@lem3625214 A B s g f)). Qed.
Lemma lem3625218 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term55 A B f s) = (term55 A B f s).
Proof. exact (eq_refl (term55 A B f s)). Qed.
Lemma lem3625271 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term56 A B s g f) = (term107 A B s g f).
Proof. exact (MK_COMB (@lem3625218 A B f s) (@lem3625216 A B s g f)). Qed.
Lemma lem3625272 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term107 A B s g f.
Proof. exact (EQ_MP (@lem3625271 A B s g f) (@lem3625200 A B s g f h1)). Qed.
Lemma lem3625285 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term108 A B x f s x') = (term109 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3625288 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term68 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term68 A B x f s x')). Qed.
Lemma lem3625289 {A : Type'} (P : A -> Prop) : (term110 A P) = (term111 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3625290 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term112 A B x f s) = (term113 A B x f s).
Proof. exact (@lem3625289 A (term70 A B x f s)). Qed.
Lemma lem3625291 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term114 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term114 A B x f s x')). Qed.
Lemma lem3625292 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3625293 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term115 A B x f s x') = (term108 A B x f s x').
Proof. exact (MK_COMB (@lem3625292) (@lem3625291 A B x f s x')). Qed.
Lemma lem3625294 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term115 A B x f s x') = (term109 A B x f s x').
Proof. exact (TRANS (@lem3625293 A B x f s x') (@lem3625285 A B x f s x')). Qed.
Lemma lem3625295 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term116 A B x f s) = (term117 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3625294 A B x f s x')). Qed.
Lemma lem3625296 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625297 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term113 A B x f s) = (term118 A B x f s).
Proof. exact (MK_COMB (@lem3625296 A) (@lem3625295 A B x f s)). Qed.
Lemma lem3625298 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term112 A B x f s) = (term118 A B x f s).
Proof. exact (TRANS (@lem3625290 A B x f s) (@lem3625297 A B x f s)). Qed.
Lemma lem3625299 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term70 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3625288 A B x f s x')). Qed.
Lemma lem3625300 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3625301 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term71 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3625300 A) (@lem3625299 A B x f s)). Qed.
Lemma lem3625303 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term119 A B x g x') = (term119 A B x g x').
Proof. exact (eq_refl (term119 A B x g x')). Qed.
Lemma lem3625304 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term120 A B x g x' f s) = (term121 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625303 A B x g x') (@lem3625298 A B x' f s)). Qed.
Lemma lem3625305 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term122 A B x g x' f s) = (term120 A B x g x' f s).
Proof. exact (@lem17045 (x = (g x')) (term71 A B x' f s)). Qed.
Lemma lem3625306 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term122 A B x g x' f s) = (term121 A B x g x' f s).
Proof. exact (TRANS (@lem3625305 A B x g x' f s) (@lem3625304 A B x g x' f s)). Qed.
Lemma lem3625308 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term72 A B x g x') = (term72 A B x g x').
Proof. exact (eq_refl (term72 A B x g x')). Qed.
Lemma lem3625309 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term74 A B x g x' f s) = (term74 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625308 A B x g x') (@lem3625301 A B x' f s)). Qed.
Lemma lem3625310 {B : Type'} (P : B -> Prop) : (term110 B P) = (term111 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3625311 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term123 A B x g f s) = (term124 A B x g f s).
Proof. exact (@lem3625310 B (term76 A B x g f s)). Qed.
Lemma lem3625312 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term125 A B x g f s x') = (term74 A B x g x' f s).
Proof. exact (eq_refl (term125 A B x g f s x')). Qed.
Lemma lem3625313 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3625314 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term126 A B x g f s x') = (term122 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625313) (@lem3625312 A B x g x' f s)). Qed.
Lemma lem3625315 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term126 A B x g f s x') = (term121 A B x g x' f s).
Proof. exact (TRANS (@lem3625314 A B x g x' f s) (@lem3625306 A B x g x' f s)). Qed.
Lemma lem3625316 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term127 A B x g f s) = (term128 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625315 A B x g x' f s)). Qed.
Lemma lem3625317 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3625318 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term124 A B x g f s) = (term129 A B x g f s).
Proof. exact (MK_COMB (@lem3625317 B) (@lem3625316 A B x g f s)). Qed.
Lemma lem3625319 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term123 A B x g f s) = (term129 A B x g f s).
Proof. exact (TRANS (@lem3625311 A B x g f s) (@lem3625318 A B x g f s)). Qed.
Lemma lem3625320 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term76 A B x g f s) = (term76 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625309 A B x g x' f s)). Qed.
Lemma lem3625321 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625322 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term77 A B x g f s) = (term77 A B x g f s).
Proof. exact (MK_COMB (@lem3625321 B) (@lem3625320 A B x g f s)). Qed.
Lemma lem3625324 {A : Type'} (s : A -> Prop) (x : A) : (term130 A s x) = (term130 A s x).
Proof. exact (eq_refl (term130 A s x)). Qed.
Lemma lem3625325 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term131 A B x g f s) = (term131 A B x g f s).
Proof. exact (MK_COMB (@lem3625324 A s x) (@lem3625322 A B x g f s)). Qed.
Lemma lem3625327 {A : Type'} (s : A -> Prop) (x : A) : (term132 A s x) = (term132 A s x).
Proof. exact (eq_refl (term132 A s x)). Qed.
Lemma lem3625328 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term133 A B x g f s) = (term134 A B x g f s).
Proof. exact (MK_COMB (@lem3625327 A s x) (@lem3625319 A B x g f s)). Qed.
Lemma lem3625329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3625330 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term135 A B x g f s) = (term136 A B x g f s).
Proof. exact (MK_COMB (@lem3625329) (@lem3625328 A B x g f s)). Qed.
Lemma lem3625331 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term137 A B x g f s) = (term138 A B x g f s).
Proof. exact (MK_COMB (@lem3625330 A B x g f s) (@lem3625325 A B x g f s)). Qed.
Lemma lem3625332 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term103 A B x g f s) = (term137 A B x g f s).
Proof. exact (@lem17646 (s x) (term77 A B x g f s)). Qed.
Lemma lem3625333 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term103 A B x g f s) = (term138 A B x g f s).
Proof. exact (TRANS (@lem3625332 A B x g f s) (@lem3625331 A B x g f s)). Qed.
Lemma lem3625512 {A : Type'} (P : Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3625513 {A : Type'} (P : Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (@lem3625512 A P Q). Qed.
Lemma lem3625514 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term141 A B x g x' f s) = (term142 A B x g x' f s).
Proof. exact (@lem3625513 A (x = (g x')) (term70 A B x' f s)). Qed.
Lemma lem3625515 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term114 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term114 A B x f s x')). Qed.
Lemma lem3625516 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term143 A B x f s) = (term70 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3625515 A B x f s x')). Qed.
Lemma lem3625517 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3625518 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term144 A B x f s) = (term71 A B x f s).
Proof. exact (MK_COMB (@lem3625517 A) (@lem3625516 A B x f s)). Qed.
Lemma lem3625519 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term72 A B x g x') = (term72 A B x g x').
Proof. exact (eq_refl (term72 A B x g x')). Qed.
Lemma lem3625520 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term141 A B x g x' f s) = (term74 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625519 A B x g x') (@lem3625518 A B x' f s)). Qed.
Lemma lem3625521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3625522 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term145 A B x g x' f s) = (term146 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625521) (@lem3625520 A B x g x' f s)). Qed.
Lemma lem3625523 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term114 A B x f s x') = (term68 A B x f s x').
Proof. exact (eq_refl (term114 A B x f s x')). Qed.
Lemma lem3625524 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term72 A B x g x') = (term72 A B x g x').
Proof. exact (eq_refl (term72 A B x g x')). Qed.
Lemma lem3625525 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term147 A B x g x' f s x'') = (term148 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3625524 A B x g x') (@lem3625523 A B x' f s x'')). Qed.
Lemma lem3625526 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term149 A B x g x' f s) = (term150 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3625525 A B x g x' f s x'')). Qed.
Lemma lem3625527 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3625528 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term142 A B x g x' f s) = (term151 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625527 A) (@lem3625526 A B x g x' f s)). Qed.
Lemma lem3625529 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term141 A B x g x' f s) = (term142 A B x g x' f s)) = ((term74 A B x g x' f s) = (term151 A B x g x' f s)).
Proof. exact (MK_COMB (@lem3625522 A B x g x' f s) (@lem3625528 A B x g x' f s)). Qed.
Lemma lem3625530 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term74 A B x g x' f s) = (term151 A B x g x' f s).
Proof. exact (EQ_MP (@lem3625529 A B x g x' f s) (@lem3625514 A B x g x' f s)). Qed.
Lemma lem3625531 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term76 A B x g f s) = (term152 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625530 A B x g x' f s)). Qed.
Lemma lem3625532 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625533 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term77 A B x g f s) = (term153 A B x g f s).
Proof. exact (MK_COMB (@lem3625532 B) (@lem3625531 A B x g f s)). Qed.
Lemma lem3625534 {A : Type'} (s : A -> Prop) (x : A) : (term130 A s x) = (term130 A s x).
Proof. exact (eq_refl (term130 A s x)). Qed.
Lemma lem3625535 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term131 A B x g f s) = (term154 A B x g f s).
Proof. exact (MK_COMB (@lem3625534 A s x) (@lem3625533 A B x g f s)). Qed.
Lemma lem3625537 {A : Type'} (P : Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3625538 {B : Type'} (P : Prop) (Q : B -> Prop) : (term139 B P Q) = (term140 B P Q).
Proof. exact (@lem3625537 B P Q). Qed.
Lemma lem3625539 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term155 A B x g f s) = (term156 A B x g f s).
Proof. exact (@lem3625538 B (term157 A s x) (term152 A B x g f s)). Qed.
Lemma lem3625540 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term158 A B x g f s x') = (term151 A B x g x' f s).
Proof. exact (eq_refl (term158 A B x g f s x')). Qed.
Lemma lem3625541 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term159 A B x g f s) = (term152 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625540 A B x g x' f s)). Qed.
Lemma lem3625542 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625543 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term160 A B x g f s) = (term153 A B x g f s).
Proof. exact (MK_COMB (@lem3625542 B) (@lem3625541 A B x g f s)). Qed.
Lemma lem3625544 {A : Type'} (s : A -> Prop) (x : A) : (term130 A s x) = (term130 A s x).
Proof. exact (eq_refl (term130 A s x)). Qed.
Lemma lem3625545 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term155 A B x g f s) = (term154 A B x g f s).
Proof. exact (MK_COMB (@lem3625544 A s x) (@lem3625543 A B x g f s)). Qed.
Lemma lem3625546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3625547 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term161 A B x g f s) = (term162 A B x g f s).
Proof. exact (MK_COMB (@lem3625546) (@lem3625545 A B x g f s)). Qed.
Lemma lem3625548 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term158 A B x g f s x') = (term151 A B x g x' f s).
Proof. exact (eq_refl (term158 A B x g f s x')). Qed.
Lemma lem3625549 {A : Type'} (s : A -> Prop) (x : A) : (term130 A s x) = (term130 A s x).
Proof. exact (eq_refl (term130 A s x)). Qed.
Lemma lem3625550 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term163 A B x g f s x') = (term164 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625549 A s x) (@lem3625548 A B x g x' f s)). Qed.
Lemma lem3625551 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term165 A B x g f s) = (term166 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625550 A B x g x' f s)). Qed.
Lemma lem3625552 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625553 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term156 A B x g f s) = (term167 A B x g f s).
Proof. exact (MK_COMB (@lem3625552 B) (@lem3625551 A B x g f s)). Qed.
Lemma lem3625554 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term155 A B x g f s) = (term156 A B x g f s)) = ((term154 A B x g f s) = (term167 A B x g f s)).
Proof. exact (MK_COMB (@lem3625547 A B x g f s) (@lem3625553 A B x g f s)). Qed.
Lemma lem3625555 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term154 A B x g f s) = (term167 A B x g f s).
Proof. exact (EQ_MP (@lem3625554 A B x g f s) (@lem3625539 A B x g f s)). Qed.
Lemma lem3625557 {A : Type'} (P : Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3625558 {A : Type'} (P : Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (@lem3625557 A P Q). Qed.
Lemma lem3625559 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term168 A B x g x' f s) = (term169 A B x g x' f s).
Proof. exact (@lem3625558 A (term157 A s x) (term150 A B x g x' f s)). Qed.
Lemma lem3625560 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term170 A B x g x' f s x'') = (term148 A B x g x' f s x'').
Proof. exact (eq_refl (term170 A B x g x' f s x'')). Qed.
Lemma lem3625561 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term171 A B x g x' f s) = (term150 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3625560 A B x g x' f s x'')). Qed.
Lemma lem3625562 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3625563 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term172 A B x g x' f s) = (term151 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625562 A) (@lem3625561 A B x g x' f s)). Qed.
Lemma lem3625564 {A : Type'} (s : A -> Prop) (x : A) : (term130 A s x) = (term130 A s x).
Proof. exact (eq_refl (term130 A s x)). Qed.
Lemma lem3625565 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term168 A B x g x' f s) = (term164 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625564 A s x) (@lem3625563 A B x g x' f s)). Qed.
Lemma lem3625566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3625567 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term173 A B x g x' f s) = (term174 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625566) (@lem3625565 A B x g x' f s)). Qed.
Lemma lem3625568 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term170 A B x g x' f s x'') = (term148 A B x g x' f s x'').
Proof. exact (eq_refl (term170 A B x g x' f s x'')). Qed.
Lemma lem3625569 {A : Type'} (s : A -> Prop) (x : A) : (term130 A s x) = (term130 A s x).
Proof. exact (eq_refl (term130 A s x)). Qed.
Lemma lem3625570 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term175 A B x g x' f s x'') = (term176 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3625569 A s x) (@lem3625568 A B x g x' f s x'')). Qed.
Lemma lem3625571 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term177 A B x g x' f s) = (term178 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3625570 A B x g x' f s x'')). Qed.
Lemma lem3625572 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3625573 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term169 A B x g x' f s) = (term179 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625572 A) (@lem3625571 A B x g x' f s)). Qed.
Lemma lem3625574 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term168 A B x g x' f s) = (term169 A B x g x' f s)) = ((term164 A B x g x' f s) = (term179 A B x g x' f s)).
Proof. exact (MK_COMB (@lem3625567 A B x g x' f s) (@lem3625573 A B x g x' f s)). Qed.
Lemma lem3625575 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term164 A B x g x' f s) = (term179 A B x g x' f s).
Proof. exact (EQ_MP (@lem3625574 A B x g x' f s) (@lem3625559 A B x g x' f s)). Qed.
Lemma lem3625576 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term166 A B x g f s) = (term180 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625575 A B x g x' f s)). Qed.
Lemma lem3625577 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625578 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term167 A B x g f s) = (term181 A B x g f s).
Proof. exact (MK_COMB (@lem3625577 B) (@lem3625576 A B x g f s)). Qed.
Lemma lem3625579 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term154 A B x g f s) = (term181 A B x g f s).
Proof. exact (TRANS (@lem3625555 A B x g f s) (@lem3625578 A B x g f s)). Qed.
Lemma lem3625580 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term131 A B x g f s) = (term181 A B x g f s).
Proof. exact (TRANS (@lem3625535 A B x g f s) (@lem3625579 A B x g f s)). Qed.
Lemma lem3625581 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (eq_refl (term136 A B x g f s)). Qed.
Lemma lem3625582 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term138 A B x g f s) = (term182 A B x g f s).
Proof. exact (MK_COMB (@lem3625581 A B x g f s) (@lem3625580 A B x g f s)). Qed.
Lemma lem3625584 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3625585 {B : Type'} (P : Prop) (Q : B -> Prop) : (term183 B P Q) = (term184 B P Q).
Proof. exact (@lem3625584 B P Q). Qed.
Lemma lem3625586 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term185 A B x g f s) = (term186 A B x g f s).
Proof. exact (@lem3625585 B (term134 A B x g f s) (term180 A B x g f s)). Qed.
Lemma lem3625587 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term187 A B x g f s x') = (term179 A B x g x' f s).
Proof. exact (eq_refl (term187 A B x g f s x')). Qed.
Lemma lem3625588 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term188 A B x g f s) = (term180 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625587 A B x g x' f s)). Qed.
Lemma lem3625589 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625590 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term189 A B x g f s) = (term181 A B x g f s).
Proof. exact (MK_COMB (@lem3625589 B) (@lem3625588 A B x g f s)). Qed.
Lemma lem3625591 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (eq_refl (term136 A B x g f s)). Qed.
Lemma lem3625592 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term185 A B x g f s) = (term182 A B x g f s).
Proof. exact (MK_COMB (@lem3625591 A B x g f s) (@lem3625590 A B x g f s)). Qed.
Lemma lem3625593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3625594 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term190 A B x g f s) = (term191 A B x g f s).
Proof. exact (MK_COMB (@lem3625593) (@lem3625592 A B x g f s)). Qed.
Lemma lem3625595 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term187 A B x g f s x') = (term179 A B x g x' f s).
Proof. exact (eq_refl (term187 A B x g f s x')). Qed.
Lemma lem3625596 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (eq_refl (term136 A B x g f s)). Qed.
Lemma lem3625597 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term192 A B x g f s x') = (term193 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625596 A B x g f s) (@lem3625595 A B x g x' f s)). Qed.
Lemma lem3625598 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term194 A B x g f s) = (term195 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625597 A B x g x' f s)). Qed.
Lemma lem3625599 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625600 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term186 A B x g f s) = (term196 A B x g f s).
Proof. exact (MK_COMB (@lem3625599 B) (@lem3625598 A B x g f s)). Qed.
Lemma lem3625601 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : ((term185 A B x g f s) = (term186 A B x g f s)) = ((term182 A B x g f s) = (term196 A B x g f s)).
Proof. exact (MK_COMB (@lem3625594 A B x g f s) (@lem3625600 A B x g f s)). Qed.
Lemma lem3625602 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term182 A B x g f s) = (term196 A B x g f s).
Proof. exact (EQ_MP (@lem3625601 A B x g f s) (@lem3625586 A B x g f s)). Qed.
Lemma lem3625604 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3625605 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (@lem3625604 A P Q). Qed.
Lemma lem3625606 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term197 A B x g x' f s) = (term198 A B x g x' f s).
Proof. exact (@lem3625605 A (term134 A B x g f s) (term178 A B x g x' f s)). Qed.
Lemma lem3625607 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term199 A B x g x' f s x'') = (term176 A B x g x' f s x'').
Proof. exact (eq_refl (term199 A B x g x' f s x'')). Qed.
Lemma lem3625608 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term200 A B x g x' f s) = (term178 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3625607 A B x g x' f s x'')). Qed.
Lemma lem3625609 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3625610 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term201 A B x g x' f s) = (term179 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625609 A) (@lem3625608 A B x g x' f s)). Qed.
Lemma lem3625611 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (eq_refl (term136 A B x g f s)). Qed.
Lemma lem3625612 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term197 A B x g x' f s) = (term193 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625611 A B x g f s) (@lem3625610 A B x g x' f s)). Qed.
Lemma lem3625613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3625614 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term202 A B x g x' f s) = (term203 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625613) (@lem3625612 A B x g x' f s)). Qed.
Lemma lem3625615 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term199 A B x g x' f s x'') = (term176 A B x g x' f s x'').
Proof. exact (eq_refl (term199 A B x g x' f s x'')). Qed.
Lemma lem3625616 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term136 A B x g f s).
Proof. exact (eq_refl (term136 A B x g f s)). Qed.
Lemma lem3625617 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term204 A B x g x' f s x'') = (term205 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3625616 A B x g f s) (@lem3625615 A B x g x' f s x'')). Qed.
Lemma lem3625618 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term206 A B x g x' f s) = (term207 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3625617 A B x g x' f s x'')). Qed.
Lemma lem3625619 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3625620 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term198 A B x g x' f s) = (term208 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625619 A) (@lem3625618 A B x g x' f s)). Qed.
Lemma lem3625621 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term197 A B x g x' f s) = (term198 A B x g x' f s)) = ((term193 A B x g x' f s) = (term208 A B x g x' f s)).
Proof. exact (MK_COMB (@lem3625614 A B x g x' f s) (@lem3625620 A B x g x' f s)). Qed.
Lemma lem3625622 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term193 A B x g x' f s) = (term208 A B x g x' f s).
Proof. exact (EQ_MP (@lem3625621 A B x g x' f s) (@lem3625606 A B x g x' f s)). Qed.
Lemma lem3625623 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term195 A B x g f s) = (term209 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625622 A B x g x' f s)). Qed.
Lemma lem3625624 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3625625 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term196 A B x g f s) = (term210 A B x g f s).
Proof. exact (MK_COMB (@lem3625624 B) (@lem3625623 A B x g f s)). Qed.
Lemma lem3625626 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term182 A B x g f s) = (term210 A B x g f s).
Proof. exact (TRANS (@lem3625602 A B x g f s) (@lem3625625 A B x g f s)). Qed.
Lemma lem3625628 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term138 A B x g f s) = (term210 A B x g f s).
Proof. exact (TRANS (@lem3625582 A B x g f s) (@lem3625626 A B x g f s)). Qed.
Lemma lem3625629 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term103 A B x g f s) = (term210 A B x g f s).
Proof. exact (TRANS (@lem3625333 A B x g f s) (@lem3625628 A B x g f s)). Qed.
Lemma lem3625630 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term103 A B x g f s) : term210 A B x g f s.
Proof. exact (EQ_MP (@lem3625629 A B x g f s) (@lem3625205 A B x g f s h1)). Qed.
Lemma lem3625631 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (h1 : term208 A B x g x' f s) : term208 A B x g x' f s.
Proof. exact (h1). Qed.
Lemma lem3625632 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term205 A B x g x' f s x'') : term205 A B x g x' f s x''.
Proof. exact (h1). Qed.
Lemma lem3625633 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem3625634 {A B : Type'} (g : B -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3625639 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3625641 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3625639 A B f x). Qed.
Lemma lem3625642 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term49 A B g f x) = (term211 A B g f x).
Proof. exact (MK_COMB (@lem3625634 A B g) (@lem3625641 A B f x)). Qed.
Lemma lem3625643 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3625644 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term212 A B g f x) = (term213 A B g f x).
Proof. exact (MK_COMB (@lem3625633 A) (@lem3625642 A B g f x)). Qed.
Lemma lem3625645 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : ((term49 A B g f x) = x) = ((term211 A B g f x) = x).
Proof. exact (MK_COMB (@lem3625644 A B g f x) (@lem3625643 A x)). Qed.
Lemma lem3625646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3625651 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3625652 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3625651 A Prop f x). Qed.
Lemma lem3625654 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3625652 A s x). Qed.
Lemma lem3625655 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (term214 A s x).
Proof. exact (MK_COMB (@lem3625646) (@lem3625654 A s x)). Qed.
Lemma lem3625656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3625657 {A : Type'} (s : A -> Prop) (x : A) : (term215 A s x) = (term216 A s x).
Proof. exact (MK_COMB (@lem3625656) (@lem3625655 A s x)). Qed.
Lemma lem3625658 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term104 A B s g f x) = (term217 A B s g f x).
Proof. exact (MK_COMB (@lem3625657 A s x) (@lem3625645 A B g f x)). Qed.
Lemma lem3625659 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term105 A B s g f) = (term218 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3625658 A B s g f x)). Qed.
Lemma lem3625660 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625661 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term106 A B s g f) = (term219 A B s g f).
Proof. exact (MK_COMB (@lem3625660 A) (@lem3625659 A B s g f)). Qed.
Lemma lem3625670 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term55 A B f s) = (term55 A B f s).
Proof. exact (eq_refl (term55 A B f s)). Qed.
Lemma lem3625671 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term107 A B s g f) = (term220 A B s g f).
Proof. exact (MK_COMB (@lem3625670 A B f s) (@lem3625661 A B s g f)). Qed.
Lemma lem3625672 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term220 A B s g f.
Proof. exact (EQ_MP (@lem3625671 A B s g f) (@lem3625272 A B s g f h1)). Qed.
Lemma lem3625677 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3625678 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3625677 A Prop f x). Qed.
Lemma lem3625680 {A : Type'} (s : A -> Prop) (x'' : A) : (s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3625678 A s x''). Qed.
Lemma lem3625687 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3625688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3625687 A B f x). Qed.
Lemma lem3625690 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (@I (A -> B) f x'').
Proof. exact (@lem3625688 A B f x''). Qed.
Lemma lem3625691 {B : Type'} (x' : B) : (@eq B x') = (@eq B x').
Proof. exact (eq_refl (@eq B x')). Qed.
Lemma lem3625692 {A B : Type'} (x' : B) (f : A -> B) (x'' : A) : (x' = (f x'')) = (x' = (@I (A -> B) f x'')).
Proof. exact (MK_COMB (@lem3625691 B x') (@lem3625690 A B f x'')). Qed.
Lemma lem3625693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3625694 {A B : Type'} (x' : B) (f : A -> B) (x'' : A) : (term66 A B x' f x'') = (term221 A B x' f x'').
Proof. exact (MK_COMB (@lem3625693) (@lem3625692 A B x' f x'')). Qed.
Lemma lem3625695 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term68 A B x' f s x'') = (term222 A B x' f s x'').
Proof. exact (MK_COMB (@lem3625694 A B x' f x'') (@lem3625680 A s x'')). Qed.
Lemma lem3625704 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term72 A B x g x') = (term72 A B x g x').
Proof. exact (eq_refl (term72 A B x g x')). Qed.
Lemma lem3625705 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term148 A B x g x' f s x'') = (term223 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3625704 A B x g x') (@lem3625695 A B x' f s x'')). Qed.
Lemma lem3625706 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3625711 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3625712 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3625711 A Prop f x). Qed.
Lemma lem3625714 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3625712 A s x). Qed.
Lemma lem3625715 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (term214 A s x).
Proof. exact (MK_COMB (@lem3625706) (@lem3625714 A s x)). Qed.
Lemma lem3625716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3625717 {A : Type'} (s : A -> Prop) (x : A) : (term130 A s x) = (term224 A s x).
Proof. exact (MK_COMB (@lem3625716) (@lem3625715 A s x)). Qed.
Lemma lem3625718 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term176 A B x g x' f s x'') = (term225 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3625717 A s x) (@lem3625705 A B x g x' f s x'')). Qed.
Lemma lem3625719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3625724 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3625725 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3625724 A Prop f x). Qed.
Lemma lem3625727 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3625725 A s x). Qed.
Lemma lem3625728 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (term214 A s x).
Proof. exact (MK_COMB (@lem3625719) (@lem3625727 A s x)). Qed.
Lemma lem3625729 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3625736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3625738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3625736 A B f x). Qed.
Lemma lem3625739 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem3625740 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (@I (A -> B) f x')).
Proof. exact (MK_COMB (@lem3625739 B x) (@lem3625738 A B f x')). Qed.
Lemma lem3625741 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term226 A B x f x') = (term227 A B x f x').
Proof. exact (MK_COMB (@lem3625729) (@lem3625740 A B x f x')). Qed.
Lemma lem3625742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3625743 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term228 A B x f x') = (term229 A B x f x').
Proof. exact (MK_COMB (@lem3625742) (@lem3625741 A B x f x')). Qed.
Lemma lem3625744 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term109 A B x f s x') = (term230 A B x f s x').
Proof. exact (MK_COMB (@lem3625743 A B x f x') (@lem3625728 A s x')). Qed.
Lemma lem3625745 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term117 A B x f s) = (term231 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3625744 A B x f s x')). Qed.
Lemma lem3625746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625747 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term118 A B x f s) = (term232 A B x f s).
Proof. exact (MK_COMB (@lem3625746 A) (@lem3625745 A B x f s)). Qed.
Lemma lem3625758 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term119 A B x g x') = (term119 A B x g x').
Proof. exact (eq_refl (term119 A B x g x')). Qed.
Lemma lem3625759 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term121 A B x g x' f s) = (term233 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625758 A B x g x') (@lem3625747 A B x' f s)). Qed.
Lemma lem3625760 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term128 A B x g f s) = (term234 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625759 A B x g x' f s)). Qed.
Lemma lem3625761 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3625762 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term129 A B x g f s) = (term235 A B x g f s).
Proof. exact (MK_COMB (@lem3625761 B) (@lem3625760 A B x g f s)). Qed.
Lemma lem3625767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3625768 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3625767 A Prop f x). Qed.
Lemma lem3625770 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3625768 A s x). Qed.
Lemma lem3625771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3625772 {A : Type'} (s : A -> Prop) (x : A) : (term132 A s x) = (term236 A s x).
Proof. exact (MK_COMB (@lem3625771) (@lem3625770 A s x)). Qed.
Lemma lem3625773 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term134 A B x g f s) = (term237 A B x g f s).
Proof. exact (MK_COMB (@lem3625772 A s x) (@lem3625762 A B x g f s)). Qed.
Lemma lem3625774 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3625775 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term136 A B x g f s) = (term238 A B x g f s).
Proof. exact (MK_COMB (@lem3625774) (@lem3625773 A B x g f s)). Qed.
Lemma lem3625776 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term205 A B x g x' f s x'') = (term239 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3625775 A B x g f s) (@lem3625718 A B x g x' f s x'')). Qed.
Lemma lem3625777 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term205 A B x g x' f s x'') : term239 A B x g x' f s x''.
Proof. exact (EQ_MP (@lem3625776 A B x g x' f s x'') (@lem3625632 A B x g x' f s x'' h1)). Qed.
Lemma lem3625778 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term219 A B s g f.
Proof. exact (proj2 (@lem3625672 A B s g f h1)). Qed.
Lemma lem3625780 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term237 A B x g f s.
Proof. exact (h1). Qed.
Lemma lem3625781 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term225 A B x g x' f s x''.
Proof. exact (h1). Qed.
Lemma lem3625782 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term235 A B x g f s.
Proof. exact (proj2 (@lem3625780 A B x g f s h1)). Qed.
Lemma lem3625784 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term223 A B x g x' f s x''.
Proof. exact (proj2 (@lem3625781 A B x g x' f s x'' h1)). Qed.
Lemma lem3625786 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term222 A B x' f s x''.
Proof. exact (proj2 (@lem3625784 A B x g x' f s x'' h1)). Qed.
Lemma lem3625801 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term217 A B s g f x) = (term217 A B s g f x).
Proof. exact (eq_refl (term217 A B s g f x)). Qed.
Lemma lem3625802 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term218 A B s g f) = (term218 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3625801 A B s g f x)). Qed.
Lemma lem3625803 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625805 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term219 A B s g f) = (term219 A B s g f).
Proof. exact (MK_COMB (@lem3625803 A) (@lem3625802 A B s g f)). Qed.
Lemma lem3625806 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term219 A B s g f.
Proof. exact (EQ_MP (@lem3625805 A B s g f) (@lem3625778 A B s g f h1)). Qed.
Lemma lem3625812 {A : Type'} (P : Prop) (Q : A -> Prop) : (term240 A P Q) = (term241 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3625813 {A : Type'} (P : Prop) (Q : A -> Prop) : (term240 A P Q) = (term241 A P Q).
Proof. exact (@lem3625812 A P Q). Qed.
Lemma lem3625814 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term242 A B x g x' f s) = (term243 A B x g x' f s).
Proof. exact (@lem3625813 A (term244 A B x g x') (term231 A B x' f s)). Qed.
Lemma lem3625815 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term245 A B x f s x') = (term230 A B x f s x').
Proof. exact (eq_refl (term245 A B x f s x')). Qed.
Lemma lem3625816 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term246 A B x f s) = (term231 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3625815 A B x f s x')). Qed.
Lemma lem3625817 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625818 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term247 A B x f s) = (term232 A B x f s).
Proof. exact (MK_COMB (@lem3625817 A) (@lem3625816 A B x f s)). Qed.
Lemma lem3625819 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term119 A B x g x') = (term119 A B x g x').
Proof. exact (eq_refl (term119 A B x g x')). Qed.
Lemma lem3625820 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term242 A B x g x' f s) = (term233 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625819 A B x g x') (@lem3625818 A B x' f s)). Qed.
Lemma lem3625821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3625822 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term248 A B x g x' f s) = (term249 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625821) (@lem3625820 A B x g x' f s)). Qed.
Lemma lem3625823 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term245 A B x f s x') = (term230 A B x f s x').
Proof. exact (eq_refl (term245 A B x f s x')). Qed.
Lemma lem3625824 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term119 A B x g x') = (term119 A B x g x').
Proof. exact (eq_refl (term119 A B x g x')). Qed.
Lemma lem3625825 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term250 A B x g x' f s x'') = (term251 A B x g x' f s x'').
Proof. exact (MK_COMB (@lem3625824 A B x g x') (@lem3625823 A B x' f s x'')). Qed.
Lemma lem3625826 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term252 A B x g x' f s) = (term253 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3625825 A B x g x' f s x'')). Qed.
Lemma lem3625827 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625828 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term243 A B x g x' f s) = (term254 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625827 A) (@lem3625826 A B x g x' f s)). Qed.
Lemma lem3625829 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term242 A B x g x' f s) = (term243 A B x g x' f s)) = ((term233 A B x g x' f s) = (term254 A B x g x' f s)).
Proof. exact (MK_COMB (@lem3625822 A B x g x' f s) (@lem3625828 A B x g x' f s)). Qed.
Lemma lem3625830 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term233 A B x g x' f s) = (term254 A B x g x' f s).
Proof. exact (EQ_MP (@lem3625829 A B x g x' f s) (@lem3625814 A B x g x' f s)). Qed.
Lemma lem3625831 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term234 A B x g f s) = (term255 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625830 A B x g x' f s)). Qed.
Lemma lem3625832 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3625833 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term235 A B x g f s) = (term256 A B x g f s).
Proof. exact (MK_COMB (@lem3625832 B) (@lem3625831 A B x g f s)). Qed.
Lemma lem3625846 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term251 A B x g x' f s x'') = (term251 A B x g x' f s x'').
Proof. exact (eq_refl (term251 A B x g x' f s x'')). Qed.
Lemma lem3625847 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term253 A B x g x' f s) = (term253 A B x g x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3625846 A B x g x' f s x'')). Qed.
Lemma lem3625848 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625849 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) : (term254 A B x g x' f s) = (term254 A B x g x' f s).
Proof. exact (MK_COMB (@lem3625848 A) (@lem3625847 A B x g x' f s)). Qed.
Lemma lem3625850 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term255 A B x g f s) = (term255 A B x g f s).
Proof. exact (fun_ext (fun x' : B => @lem3625849 A B x g x' f s)). Qed.
Lemma lem3625851 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3625852 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term256 A B x g f s) = (term256 A B x g f s).
Proof. exact (MK_COMB (@lem3625851 B) (@lem3625850 A B x g f s)). Qed.
Lemma lem3625853 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) : (term235 A B x g f s) = (term256 A B x g f s).
Proof. exact (TRANS (@lem3625833 A B x g f s) (@lem3625852 A B x g f s)). Qed.
Lemma lem3625854 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term256 A B x g f s.
Proof. exact (EQ_MP (@lem3625853 A B x g f s) (@lem3625782 A B x g f s h1)). Qed.
Lemma lem3625866 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term217 A B s g f x) = (term217 A B s g f x).
Proof. exact (eq_refl (term217 A B s g f x)). Qed.
Lemma lem3625867 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term218 A B s g f) = (term218 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3625866 A B s g f x)). Qed.
Lemma lem3625868 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3625870 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term219 A B s g f) = (term219 A B s g f).
Proof. exact (MK_COMB (@lem3625868 A) (@lem3625867 A B s g f)). Qed.
Lemma lem3625871 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term219 A B s g f.
Proof. exact (EQ_MP (@lem3625870 A B s g f) (@lem3625778 A B s g f h1)). Qed.
Lemma lem3625888 {A B : Type'} (_39472 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term257 A B s g f _39472.
Proof. exact (@lem3625806 A B s g f h1 _39472). Qed.
Lemma lem3625889 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39472 : A) : (term257 A B s g f _39472) = (term217 A B s g f _39472).
Proof. exact (eq_refl (term257 A B s g f _39472)). Qed.
Lemma lem3625891 {A B : Type'} (_39473 : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term258 A B x g f s _39473.
Proof. exact (@lem3625854 A B x g f s h1 _39473). Qed.
Lemma lem3625892 {A B : Type'} (x : A) (g : B -> A) (_39473 : B) (f : A -> B) (s : A -> Prop) : (term258 A B x g f s _39473) = (term254 A B x g _39473 f s).
Proof. exact (eq_refl (term258 A B x g f s _39473)). Qed.
Lemma lem3625893 {A B : Type'} (_39473 : B) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term254 A B x g _39473 f s.
Proof. exact (EQ_MP (@lem3625892 A B x g _39473 f s) (@lem3625891 A B _39473 x g f s h1)). Qed.
Lemma lem3625894 {A B : Type'} (_39473 : B) (_39474 : A) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term259 A B x g _39473 f s _39474.
Proof. exact (@lem3625893 A B _39473 x g f s h1 _39474). Qed.
Lemma lem3625895 {A B : Type'} (x : A) (g : B -> A) (_39473 : B) (f : A -> B) (s : A -> Prop) (_39474 : A) : (term259 A B x g _39473 f s _39474) = (term251 A B x g _39473 f s _39474).
Proof. exact (eq_refl (term259 A B x g _39473 f s _39474)). Qed.
Lemma lem3625897 {A B : Type'} (_39475 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term257 A B s g f _39475.
Proof. exact (@lem3625871 A B s g f h1 _39475). Qed.
Lemma lem3625898 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39475 : A) : (term257 A B s g f _39475) = (term217 A B s g f _39475).
Proof. exact (eq_refl (term257 A B s g f _39475)). Qed.
Lemma lem3625907 {A B : Type'} (_39472 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term217 A B s g f _39472.
Proof. exact (EQ_MP (@lem3625889 A B s g f _39472) (@lem3625888 A B _39472 s g f h1)). Qed.
Lemma lem3625919 {A B : Type'} (_39473 : B) (_39474 : A) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term251 A B x g _39473 f s _39474.
Proof. exact (EQ_MP (@lem3625895 A B x g _39473 f s _39474) (@lem3625894 A B _39473 _39474 x g f s h1)). Qed.
Lemma lem3625931 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : x = (g x').
Proof. exact (proj1 (@lem3625784 A B x g x' f s x'' h1)). Qed.
Lemma lem3625933 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : x' = (@I (A -> B) f x'').
Proof. exact (proj1 (@lem3625786 A B x g x' f s x'' h1)). Qed.
Lemma lem3625991 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term214 A s x.
Proof. exact (proj1 (@lem3625781 A B x g x' f s x'' h1)). Qed.
Lemma lem3625992 {A B : Type'} (x : A) (g : B -> A) : (term260 A B x g) = (term260 A B x g).
Proof. exact (eq_refl (term260 A B x g)). Qed.
Lemma lem3625993 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : (term261 A B x g x') = (term262 A B x g f x'').
Proof. exact (MK_COMB (@lem3625992 A B x g) (@lem3625933 A B x g x' f s x'' h1)). Qed.
Lemma lem3625994 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (x'' : A) : (term262 A B x g f x'') = (x = (term211 A B g f x'')).
Proof. exact (eq_refl (term262 A B x g f x'')). Qed.
Lemma lem3625995 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term263 A B x g x') = (term263 A B x g x').
Proof. exact (eq_refl (term263 A B x g x')). Qed.
Lemma lem3625996 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (x'' : A) : ((term261 A B x g x') = (term262 A B x g f x'')) = ((term261 A B x g x') = (x = (term211 A B g f x''))).
Proof. exact (MK_COMB (@lem3625995 A B x g x') (@lem3625994 A B x g f x'')). Qed.
Lemma lem3625997 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term261 A B x g x') = (x = (g x')).
Proof. exact (eq_refl (term261 A B x g x')). Qed.
Lemma lem3625998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3625999 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term263 A B x g x') = (term264 A B x g x').
Proof. exact (MK_COMB (@lem3625998) (@lem3625997 A B x g x')). Qed.
Lemma lem3626000 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (x'' : A) : (x = (term211 A B g f x'')) = (x = (term211 A B g f x'')).
Proof. exact (eq_refl (x = (term211 A B g f x''))). Qed.
Lemma lem3626001 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (x'' : A) : ((term261 A B x g x') = (x = (term211 A B g f x''))) = ((x = (g x')) = (x = (term211 A B g f x''))).
Proof. exact (MK_COMB (@lem3625999 A B x g x') (@lem3626000 A B x g f x'')). Qed.
Lemma lem3626002 {A B : Type'} (x' : B) (x : A) (g : B -> A) (f : A -> B) (x'' : A) : ((term261 A B x g x') = (term262 A B x g f x'')) = ((x = (g x')) = (x = (term211 A B g f x''))).
Proof. exact (TRANS (@lem3625996 A B x' x g f x'') (@lem3626001 A B x' x g f x'')). Qed.
Lemma lem3626003 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : (x = (g x')) = (x = (term211 A B g f x'')).
Proof. exact (EQ_MP (@lem3626002 A B x' x g f x'') (@lem3625993 A B x g x' f s x'' h1)). Qed.
Lemma lem3626004 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : x = (term211 A B g f x'').
Proof. exact (EQ_MP (@lem3626003 A B x g x' f s x'' h1) (@lem3625931 A B x g x' f s x'' h1)). Qed.
Lemma lem3626060 {A B : Type'} (_39475 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term217 A B s g f _39475.
Proof. exact (EQ_MP (@lem3625898 A B s g f _39475) (@lem3625897 A B _39475 s g f h1)). Qed.
Lemma lem3626061 {A : Type'} (s : A -> Prop) : (term265 A s) = (term265 A s).
Proof. exact (eq_refl (term265 A s)). Qed.
Lemma lem3626062 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : (term266 A s x) = (term267 A B s g f x'').
Proof. exact (MK_COMB (@lem3626061 A s) (@lem3626004 A B x g x' f s x'' h1)). Qed.
Lemma lem3626063 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : (term267 A B s g f x'') = (term268 A B s g f x'').
Proof. exact (eq_refl (term267 A B s g f x'')). Qed.
Lemma lem3626064 {A : Type'} (s : A -> Prop) (x : A) : (term269 A s x) = (term269 A s x).
Proof. exact (eq_refl (term269 A s x)). Qed.
Lemma lem3626065 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : ((term266 A s x) = (term267 A B s g f x'')) = ((term266 A s x) = (term268 A B s g f x'')).
Proof. exact (MK_COMB (@lem3626064 A s x) (@lem3626063 A B s g f x'')). Qed.
Lemma lem3626066 {A : Type'} (s : A -> Prop) (x : A) : (term266 A s x) = (term214 A s x).
Proof. exact (eq_refl (term266 A s x)). Qed.
Lemma lem3626067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3626068 {A : Type'} (s : A -> Prop) (x : A) : (term269 A s x) = (term270 A s x).
Proof. exact (MK_COMB (@lem3626067) (@lem3626066 A s x)). Qed.
Lemma lem3626069 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : (term268 A B s g f x'') = (term268 A B s g f x'').
Proof. exact (eq_refl (term268 A B s g f x'')). Qed.
Lemma lem3626070 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : ((term266 A s x) = (term268 A B s g f x'')) = ((term214 A s x) = (term268 A B s g f x'')).
Proof. exact (MK_COMB (@lem3626068 A s x) (@lem3626069 A B s g f x'')). Qed.
Lemma lem3626071 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : ((term266 A s x) = (term267 A B s g f x'')) = ((term214 A s x) = (term268 A B s g f x'')).
Proof. exact (TRANS (@lem3626065 A B x s g f x'') (@lem3626070 A B x s g f x'')). Qed.
Lemma lem3626072 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : (term214 A s x) = (term268 A B s g f x'').
Proof. exact (EQ_MP (@lem3626071 A B x s g f x'') (@lem3626062 A B x g x' f s x'' h1)). Qed.
Lemma lem3626073 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term268 A B s g f x''.
Proof. exact (EQ_MP (@lem3626072 A B x g x' f s x'' h1) (@lem3625991 A B x g x' f s x'' h1)). Qed.
Lemma lem3626164 {A : Type'} (x : A) (y : A) (z : A) : term271 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem3626168 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem3625780 A B x g f s h1)). Qed.
Lemma lem3626169 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term272 A s x.
Proof. exact (fun h0 : term214 A s x => @lem3626168 A B x g f s h1). Qed.
Lemma lem3626171 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626172 {A : Type'} (s : A -> Prop) (x : A) : (term272 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3626171 (@I (A -> Prop) s x)). Qed.
Lemma lem3626173 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3626172 A s x) (@lem3626169 A B x g f s h1)). Qed.
Lemma lem3626179 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3626180 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39472 : A) : (term217 A B s g f _39472) = (term274 A B g f s _39472).
Proof. exact (@lem3626179 ((term211 A B g f _39472) = _39472) (term214 A s _39472)). Qed.
Lemma lem3626188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3626189 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39472 : A) : (term275 A B s g f _39472) = (term276 A B g f s _39472).
Proof. exact (MK_COMB (@lem3626188) (@lem3626180 A B g f s _39472)). Qed.
Lemma lem3626197 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39472 : A) : (term274 A B g f s _39472) = (term274 A B g f s _39472).
Proof. exact (eq_refl (term274 A B g f s _39472)). Qed.
Lemma lem3626198 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39472 : A) : ((term217 A B s g f _39472) = (term274 A B g f s _39472)) = ((term274 A B g f s _39472) = (term274 A B g f s _39472)).
Proof. exact (MK_COMB (@lem3626189 A B g f s _39472) (@lem3626197 A B g f s _39472)). Qed.
Lemma lem3626200 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3626201 (x : Prop) : (x = x) = True.
Proof. exact (@lem3626200 Prop x). Qed.
Lemma lem3626202 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39472 : A) : ((term274 A B g f s _39472) = (term274 A B g f s _39472)) = True.
Proof. exact (@lem3626201 (term274 A B g f s _39472)). Qed.
Lemma lem3626203 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39472 : A) : ((term217 A B s g f _39472) = (term274 A B g f s _39472)) = True.
Proof. exact (TRANS (@lem3626198 A B g f s _39472) (@lem3626202 A B g f s _39472)). Qed.
Lemma lem3626204 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39472 : A) : True = ((term217 A B s g f _39472) = (term274 A B g f s _39472)).
Proof. exact (SYM (@lem3626203 A B g f s _39472)). Qed.
Lemma lem3626205 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39472 : A) : (term217 A B s g f _39472) = (term274 A B g f s _39472).
Proof. exact (EQ_MP (@lem3626204 A B g f s _39472) (@lem0)). Qed.
Lemma lem3626206 {A B : Type'} (_39472 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term274 A B g f s _39472.
Proof. exact (EQ_MP (@lem3626205 A B g f s _39472) (@lem3625907 A B _39472 s g f h1)). Qed.
Lemma lem3626208 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3626209 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39472 : A) : (term274 A B g f s _39472) = (term278 A B s g f _39472).
Proof. exact (@lem3626208 (term214 A s _39472) ((term211 A B g f _39472) = _39472)). Qed.
Lemma lem3626211 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626212 {A : Type'} (s : A -> Prop) (_39472 : A) : (term279 A s _39472) = (@I (A -> Prop) s _39472).
Proof. exact (@lem3626211 (@I (A -> Prop) s _39472)). Qed.
Lemma lem3626213 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3626214 {A : Type'} (s : A -> Prop) (_39472 : A) : (term280 A s _39472) = (term281 A s _39472).
Proof. exact (MK_COMB (@lem3626213) (@lem3626212 A s _39472)). Qed.
Lemma lem3626215 {A B : Type'} (g : B -> A) (f : A -> B) (_39472 : A) : ((term211 A B g f _39472) = _39472) = ((term211 A B g f _39472) = _39472).
Proof. exact (eq_refl ((term211 A B g f _39472) = _39472)). Qed.
Lemma lem3626216 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39472 : A) : (term278 A B s g f _39472) = (term282 A B s g f _39472).
Proof. exact (MK_COMB (@lem3626214 A s _39472) (@lem3626215 A B g f _39472)). Qed.
Lemma lem3626217 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39472 : A) : (term274 A B g f s _39472) = (term282 A B s g f _39472).
Proof. exact (TRANS (@lem3626209 A B s g f _39472) (@lem3626216 A B s g f _39472)). Qed.
Lemma lem3626220 {A B : Type'} (_39472 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term282 A B s g f _39472.
Proof. exact (EQ_MP (@lem3626217 A B s g f _39472) (@lem3626206 A B _39472 s g f h1)). Qed.
Lemma lem3626221 {A B : Type'} (_39472 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term282 A B s g f _39472.
Proof. exact (@lem3626220 A B _39472 s g f h1). Qed.
Lemma lem3626222 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term282 A B s g f x.
Proof. exact (@lem3626221 A B x s g f h1). Qed.
Lemma lem3626225 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : (term211 A B g f x) = x.
Proof. exact (@lem3626222 A B x s g f h1 (@lem3626173 A B x g f s h2)). Qed.
Lemma lem3626226 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : term283 A B g f x.
Proof. exact (fun h0 : term284 A B g f x => @lem3626225 A B x g f s h1 h2). Qed.
Lemma lem3626228 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626229 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term283 A B g f x) = ((term211 A B g f x) = x).
Proof. exact (@lem3626228 ((term211 A B g f x) = x)). Qed.
Lemma lem3626230 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : (term211 A B g f x) = x.
Proof. exact (EQ_MP (@lem3626229 A B g f x) (@lem3626226 A B x g f s h1 h2)). Qed.
Lemma lem3626232 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3626233 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3626232 A x). Qed.
Lemma lem3626234 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term211 A B g f x) = (term211 A B g f x).
Proof. exact (@lem3626233 A (term211 A B g f x)). Qed.
Lemma lem3626235 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : term285 A B g f x.
Proof. exact (fun h0 : term286 A B g f x => @lem3626234 A B g f x). Qed.
Lemma lem3626237 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626238 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term285 A B g f x) = ((term211 A B g f x) = (term211 A B g f x)).
Proof. exact (@lem3626237 ((term211 A B g f x) = (term211 A B g f x))). Qed.
Lemma lem3626239 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term211 A B g f x) = (term211 A B g f x).
Proof. exact (EQ_MP (@lem3626238 A B g f x) (@lem3626235 A B g f x)). Qed.
Lemma lem3626257 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3626258 {A : Type'} (y : A) (x : A) (z : A) : (term287 A x y z) = (term288 A y x z).
Proof. exact (@lem3626257 (y = z) (term289 A x z)). Qed.
Lemma lem3626268 {A : Type'} (x : A) (y : A) : (term290 A x y) = (term290 A x y).
Proof. exact (eq_refl (term290 A x y)). Qed.
Lemma lem3626269 {A : Type'} (y : A) (x : A) (z : A) : (term271 A x y z) = (term291 A y x z).
Proof. exact (MK_COMB (@lem3626268 A x y) (@lem3626258 A y x z)). Qed.
Lemma lem3626273 (q : Prop) (p : Prop) (r : Prop) : (term292 p q r) = (term292 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3626274 {A : Type'} (y : A) (x : A) (z : A) : (term291 A y x z) = (term293 A y x z).
Proof. exact (@lem3626273 (y = z) (term289 A x y) (term289 A x z)). Qed.
Lemma lem3626296 {A : Type'} (y : A) (x : A) (z : A) : (term271 A x y z) = (term293 A y x z).
Proof. exact (TRANS (@lem3626269 A y x z) (@lem3626274 A y x z)). Qed.
Lemma lem3626297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3626298 {A : Type'} (y : A) (x : A) (z : A) : (term294 A x y z) = (term295 A y x z).
Proof. exact (MK_COMB (@lem3626297) (@lem3626296 A y x z)). Qed.
Lemma lem3626320 {A : Type'} (y : A) (x : A) (z : A) : (term293 A y x z) = (term293 A y x z).
Proof. exact (eq_refl (term293 A y x z)). Qed.
Lemma lem3626321 {A : Type'} (y : A) (x : A) (z : A) : ((term271 A x y z) = (term293 A y x z)) = ((term293 A y x z) = (term293 A y x z)).
Proof. exact (MK_COMB (@lem3626298 A y x z) (@lem3626320 A y x z)). Qed.
Lemma lem3626323 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3626324 (x : Prop) : (x = x) = True.
Proof. exact (@lem3626323 Prop x). Qed.
Lemma lem3626325 {A : Type'} (y : A) (x : A) (z : A) : ((term293 A y x z) = (term293 A y x z)) = True.
Proof. exact (@lem3626324 (term293 A y x z)). Qed.
Lemma lem3626326 {A : Type'} (y : A) (x : A) (z : A) : ((term271 A x y z) = (term293 A y x z)) = True.
Proof. exact (TRANS (@lem3626321 A y x z) (@lem3626325 A y x z)). Qed.
Lemma lem3626327 {A : Type'} (y : A) (x : A) (z : A) : True = ((term271 A x y z) = (term293 A y x z)).
Proof. exact (SYM (@lem3626326 A y x z)). Qed.
Lemma lem3626328 {A : Type'} (y : A) (x : A) (z : A) : (term271 A x y z) = (term293 A y x z).
Proof. exact (EQ_MP (@lem3626327 A y x z) (@lem0)). Qed.
Lemma lem3626329 {A : Type'} (y : A) (x : A) (z : A) : term293 A y x z.
Proof. exact (EQ_MP (@lem3626328 A y x z) (@lem3626164 A x y z)). Qed.
Lemma lem3626331 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3626332 {A : Type'} (x : A) (y : A) (z : A) : (term293 A y x z) = (term296 A x y z).
Proof. exact (@lem3626331 (term297 A y x z) (y = z)). Qed.
Lemma lem3626334 (a : Prop) (b : Prop) : (term298 a b) = (term299 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3626335 {A : Type'} (y : A) (x : A) (z : A) : (term300 A y x z) = (term301 A y x z).
Proof. exact (@lem3626334 (term289 A x y) (term289 A x z)). Qed.
Lemma lem3626337 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626338 {A : Type'} (x : A) (y : A) : (term302 A x y) = (x = y).
Proof. exact (@lem3626337 (x = y)). Qed.
Lemma lem3626339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3626340 {A : Type'} (x : A) (y : A) : (term303 A x y) = (term304 A x y).
Proof. exact (MK_COMB (@lem3626339) (@lem3626338 A x y)). Qed.
Lemma lem3626342 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626343 {A : Type'} (x : A) (z : A) : (term302 A x z) = (x = z).
Proof. exact (@lem3626342 (x = z)). Qed.
Lemma lem3626344 {A : Type'} (y : A) (x : A) (z : A) : (term301 A y x z) = (term305 A y x z).
Proof. exact (MK_COMB (@lem3626340 A x y) (@lem3626343 A x z)). Qed.
Lemma lem3626345 {A : Type'} (y : A) (x : A) (z : A) : (term300 A y x z) = (term305 A y x z).
Proof. exact (TRANS (@lem3626335 A y x z) (@lem3626344 A y x z)). Qed.
Lemma lem3626346 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3626347 {A : Type'} (y : A) (x : A) (z : A) : (term306 A y x z) = (term307 A y x z).
Proof. exact (MK_COMB (@lem3626346) (@lem3626345 A y x z)). Qed.
Lemma lem3626348 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3626349 {A : Type'} (x : A) (y : A) (z : A) : (term296 A x y z) = (term308 A x y z).
Proof. exact (MK_COMB (@lem3626347 A y x z) (@lem3626348 A y z)). Qed.
Lemma lem3626350 {A : Type'} (x : A) (y : A) (z : A) : (term293 A y x z) = (term308 A x y z).
Proof. exact (TRANS (@lem3626332 A x y z) (@lem3626349 A x y z)). Qed.
Lemma lem3626352 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : term309 A B g f x.
Proof. exact (conj (@lem3626230 A B x g f s h1 h2) (@lem3626239 A B g f x)). Qed.
Lemma lem3626354 {A : Type'} (x : A) (y : A) (z : A) : term308 A x y z.
Proof. exact (EQ_MP (@lem3626350 A x y z) (@lem3626329 A y x z)). Qed.
Lemma lem3626355 {A : Type'} (x : A) (y : A) (z : A) : term308 A x y z.
Proof. exact (@lem3626354 A x y z). Qed.
Lemma lem3626356 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : term310 A B g f x.
Proof. exact (@lem3626355 A (term211 A B g f x) x (term211 A B g f x)). Qed.
Lemma lem3626359 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : x = (term211 A B g f x).
Proof. exact (@lem3626356 A B g f x (@lem3626352 A B x g f s h1 h2)). Qed.
Lemma lem3626360 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : term311 A B g f x.
Proof. exact (fun h0 : term312 A B g f x => @lem3626359 A B x g f s h1 h2). Qed.
Lemma lem3626362 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626363 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term311 A B g f x) = (x = (term211 A B g f x)).
Proof. exact (@lem3626362 (x = (term211 A B g f x))). Qed.
Lemma lem3626364 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : x = (term211 A B g f x).
Proof. exact (EQ_MP (@lem3626363 A B g f x) (@lem3626360 A B x g f s h1 h2)). Qed.
Lemma lem3626366 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3626367 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3626366 B x). Qed.
Lemma lem3626368 {A B : Type'} (f : A -> B) (x : A) : (@I (A -> B) f x) = (@I (A -> B) f x).
Proof. exact (@lem3626367 B (@I (A -> B) f x)). Qed.
Lemma lem3626369 {A B : Type'} (f : A -> B) (x : A) : term313 A B f x.
Proof. exact (fun h0 : term314 A B f x => @lem3626368 A B f x). Qed.
Lemma lem3626371 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626372 {A B : Type'} (f : A -> B) (x : A) : (term313 A B f x) = ((@I (A -> B) f x) = (@I (A -> B) f x)).
Proof. exact (@lem3626371 ((@I (A -> B) f x) = (@I (A -> B) f x))). Qed.
Lemma lem3626373 {A B : Type'} (f : A -> B) (x : A) : (@I (A -> B) f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem3626372 A B f x) (@lem3626369 A B f x)). Qed.
Lemma lem3626375 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem3625780 A B x g f s h1)). Qed.
Lemma lem3626376 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term272 A s x.
Proof. exact (fun h0 : term214 A s x => @lem3626375 A B x g f s h1). Qed.
Lemma lem3626378 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626379 {A : Type'} (s : A -> Prop) (x : A) : (term272 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3626378 (@I (A -> Prop) s x)). Qed.
Lemma lem3626380 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3626379 A s x) (@lem3626376 A B x g f s h1)). Qed.
Lemma lem3626382 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3626383 {A B : Type'} (_39473 : B) (f : A -> B) (s : A -> Prop) (_39474 : A) : (term230 A B _39473 f s _39474) = (term317 A B _39473 f s _39474).
Proof. exact (@lem3626382 (_39473 = (@I (A -> B) f _39474)) (@I (A -> Prop) s _39474)). Qed.
Lemma lem3626384 {A B : Type'} (x : A) (g : B -> A) (_39473 : B) : (term119 A B x g _39473) = (term119 A B x g _39473).
Proof. exact (eq_refl (term119 A B x g _39473)). Qed.
Lemma lem3626385 {A B : Type'} (x : A) (g : B -> A) (_39473 : B) (f : A -> B) (s : A -> Prop) (_39474 : A) : (term251 A B x g _39473 f s _39474) = (term318 A B x g _39473 f s _39474).
Proof. exact (MK_COMB (@lem3626384 A B x g _39473) (@lem3626383 A B _39473 f s _39474)). Qed.
Lemma lem3626387 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3626388 {A B : Type'} (x : A) (g : B -> A) (_39473 : B) (f : A -> B) (s : A -> Prop) (_39474 : A) : (term318 A B x g _39473 f s _39474) = (term319 A B x g _39473 f s _39474).
Proof. exact (@lem3626387 (x = (g _39473)) (term222 A B _39473 f s _39474)). Qed.
Lemma lem3626389 {A B : Type'} (x : A) (g : B -> A) (_39473 : B) (f : A -> B) (s : A -> Prop) (_39474 : A) : (term251 A B x g _39473 f s _39474) = (term319 A B x g _39473 f s _39474).
Proof. exact (TRANS (@lem3626385 A B x g _39473 f s _39474) (@lem3626388 A B x g _39473 f s _39474)). Qed.
Lemma lem3626391 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3626392 {A B : Type'} (x : A) (g : B -> A) (_39473 : B) (f : A -> B) (s : A -> Prop) (_39474 : A) : (term319 A B x g _39473 f s _39474) = (term320 A B x g _39473 f s _39474).
Proof. exact (@lem3626391 (term223 A B x g _39473 f s _39474)). Qed.
Lemma lem3626393 {A B : Type'} (x : A) (g : B -> A) (_39473 : B) (f : A -> B) (s : A -> Prop) (_39474 : A) : (term251 A B x g _39473 f s _39474) = (term320 A B x g _39473 f s _39474).
Proof. exact (TRANS (@lem3626389 A B x g _39473 f s _39474) (@lem3626392 A B x g _39473 f s _39474)). Qed.
Lemma lem3626395 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term321 A B f s x.
Proof. exact (conj (@lem3626373 A B f x) (@lem3626380 A B x g f s h1)). Qed.
Lemma lem3626396 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : term322 A B g f s x.
Proof. exact (conj (@lem3626364 A B x g f s h1 h2) (@lem3626395 A B x g f s h2)). Qed.
Lemma lem3626398 {A B : Type'} (_39473 : B) (_39474 : A) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term320 A B x g _39473 f s _39474.
Proof. exact (EQ_MP (@lem3626393 A B x g _39473 f s _39474) (@lem3625919 A B _39473 _39474 x g f s h1)). Qed.
Lemma lem3626399 {A B : Type'} (_39473 : B) (_39474 : A) (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term320 A B x g _39473 f s _39474.
Proof. exact (@lem3626398 A B _39473 _39474 x g f s h1). Qed.
Lemma lem3626400 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term237 A B x g f s) : term323 A B g f s x.
Proof. exact (@lem3626399 A B (@I (A -> B) f x) x x g f s h1). Qed.
Lemma lem3626403 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : False.
Proof. exact (@lem3626400 A B x g f s h2 (@lem3626396 A B x g f s h1 h2)). Qed.
Lemma lem3626404 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : term324.
Proof. exact (fun h0 : ~ False => @lem3626403 A B x g f s h1 h2). Qed.
Lemma lem3626406 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626407 : term324 = False.
Proof. exact (@lem3626406 False). Qed.
Lemma lem3626408 {A B : Type'} (x : A) (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term56 A B s g f) (h2 : term237 A B x g f s) : False.
Proof. exact (EQ_MP (@lem3626407) (@lem3626404 A B x g f s h1 h2)). Qed.
Lemma lem3626409 {A : Type'} : (@I (A -> Prop)) = (@I (A -> Prop)).
Proof. exact (eq_refl (@I (A -> Prop))). Qed.
Lemma lem3626410 {A : Type'} (_39514 : A -> Prop) (_39516 : A -> Prop) (h1 : _39514 = _39516) : _39514 = _39516.
Proof. exact (h1). Qed.
Lemma lem3626411 {A : Type'} (_39515 : A) (_39517 : A) (h1 : _39515 = _39517) : _39515 = _39517.
Proof. exact (h1). Qed.
Lemma lem3626412 {A : Type'} (_39514 : A -> Prop) (_39516 : A -> Prop) (h1 : _39514 = _39516) : (@I (A -> Prop) _39514) = (@I (A -> Prop) _39516).
Proof. exact (MK_COMB (@lem3626409 A) (@lem3626410 A _39514 _39516 h1)). Qed.
Lemma lem3626413 {A : Type'} (_39515 : A) (_39517 : A) (_39514 : A -> Prop) (_39516 : A -> Prop) (h1 : _39515 = _39517) (h2 : _39514 = _39516) : (@I (A -> Prop) _39514 _39515) = (@I (A -> Prop) _39516 _39517).
Proof. exact (MK_COMB (@lem3626412 A _39514 _39516 h2) (@lem3626411 A _39515 _39517 h1)). Qed.
Lemma lem3626415 (b : Prop) (a : Prop) : term325 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3626416 {A : Type'} (_39516 : A -> Prop) (_39517 : A) (_39514 : A -> Prop) (_39515 : A) : term326 A _39516 _39517 _39514 _39515.
Proof. exact (@lem3626415 (@I (A -> Prop) _39516 _39517) (@I (A -> Prop) _39514 _39515)). Qed.
Lemma lem3626417 {A : Type'} (_39515 : A) (_39517 : A) (_39514 : A -> Prop) (_39516 : A -> Prop) (h1 : _39515 = _39517) (h2 : _39514 = _39516) : term327 A _39516 _39517 _39514 _39515.
Proof. exact (@lem3626416 A _39516 _39517 _39514 _39515 (@lem3626413 A _39515 _39517 _39514 _39516 h1 h2)). Qed.
Lemma lem3626418 {A : Type'} (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) (_39517 : A) (h1 : _39515 = _39517) : term328 A _39516 _39517 _39514 _39515.
Proof. exact (fun h0 : _39514 = _39516 => @lem3626417 A _39515 _39517 _39514 _39516 h1 h0). Qed.
Lemma lem3626420 (a : Prop) (b : Prop) : (a -> b) = (term329 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3626421 {A : Type'} (_39516 : A -> Prop) (_39517 : A) (_39514 : A -> Prop) (_39515 : A) : (term328 A _39516 _39517 _39514 _39515) = (term330 A _39516 _39517 _39514 _39515).
Proof. exact (@lem3626420 (_39514 = _39516) (term327 A _39516 _39517 _39514 _39515)). Qed.
Lemma lem3626422 {A : Type'} (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) (_39517 : A) (h1 : _39515 = _39517) : term330 A _39516 _39517 _39514 _39515.
Proof. exact (EQ_MP (@lem3626421 A _39516 _39517 _39514 _39515) (@lem3626418 A _39516 _39514 _39515 _39517 h1)). Qed.
Lemma lem3626423 {A : Type'} (_39516 : A -> Prop) (_39517 : A) (_39514 : A -> Prop) (_39515 : A) : term331 A _39516 _39517 _39514 _39515.
Proof. exact (fun h0 : _39515 = _39517 => @lem3626422 A _39516 _39514 _39515 _39517 h0). Qed.
Lemma lem3626425 (a : Prop) (b : Prop) : (a -> b) = (term329 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3626426 {A : Type'} (_39516 : A -> Prop) (_39517 : A) (_39514 : A -> Prop) (_39515 : A) : (term331 A _39516 _39517 _39514 _39515) = (term332 A _39516 _39517 _39514 _39515).
Proof. exact (@lem3626425 (_39515 = _39517) (term330 A _39516 _39517 _39514 _39515)). Qed.
Lemma lem3626427 {A : Type'} (_39516 : A -> Prop) (_39517 : A) (_39514 : A -> Prop) (_39515 : A) : term332 A _39516 _39517 _39514 _39515.
Proof. exact (EQ_MP (@lem3626426 A _39516 _39517 _39514 _39515) (@lem3626423 A _39516 _39517 _39514 _39515)). Qed.
Lemma lem3626485 {A : Type'} (x : A) (y : A) (z : A) : term271 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem3626489 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : @I (A -> Prop) s x''.
Proof. exact (proj2 (@lem3625786 A B x g x' f s x'' h1)). Qed.
Lemma lem3626490 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term272 A s x''.
Proof. exact (fun h0 : term214 A s x'' => @lem3626489 A B x g x' f s x'' h1). Qed.
Lemma lem3626492 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626493 {A : Type'} (s : A -> Prop) (x'' : A) : (term272 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3626492 (@I (A -> Prop) s x'')). Qed.
Lemma lem3626494 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem3626493 A s x'') (@lem3626490 A B x g x' f s x'' h1)). Qed.
Lemma lem3626500 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3626501 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39475 : A) : (term217 A B s g f _39475) = (term274 A B g f s _39475).
Proof. exact (@lem3626500 ((term211 A B g f _39475) = _39475) (term214 A s _39475)). Qed.
Lemma lem3626509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3626510 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39475 : A) : (term275 A B s g f _39475) = (term276 A B g f s _39475).
Proof. exact (MK_COMB (@lem3626509) (@lem3626501 A B g f s _39475)). Qed.
Lemma lem3626518 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39475 : A) : (term274 A B g f s _39475) = (term274 A B g f s _39475).
Proof. exact (eq_refl (term274 A B g f s _39475)). Qed.
Lemma lem3626519 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39475 : A) : ((term217 A B s g f _39475) = (term274 A B g f s _39475)) = ((term274 A B g f s _39475) = (term274 A B g f s _39475)).
Proof. exact (MK_COMB (@lem3626510 A B g f s _39475) (@lem3626518 A B g f s _39475)). Qed.
Lemma lem3626521 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3626522 (x : Prop) : (x = x) = True.
Proof. exact (@lem3626521 Prop x). Qed.
Lemma lem3626523 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39475 : A) : ((term274 A B g f s _39475) = (term274 A B g f s _39475)) = True.
Proof. exact (@lem3626522 (term274 A B g f s _39475)). Qed.
Lemma lem3626524 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39475 : A) : ((term217 A B s g f _39475) = (term274 A B g f s _39475)) = True.
Proof. exact (TRANS (@lem3626519 A B g f s _39475) (@lem3626523 A B g f s _39475)). Qed.
Lemma lem3626525 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39475 : A) : True = ((term217 A B s g f _39475) = (term274 A B g f s _39475)).
Proof. exact (SYM (@lem3626524 A B g f s _39475)). Qed.
Lemma lem3626526 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39475 : A) : (term217 A B s g f _39475) = (term274 A B g f s _39475).
Proof. exact (EQ_MP (@lem3626525 A B g f s _39475) (@lem0)). Qed.
Lemma lem3626527 {A B : Type'} (_39475 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term274 A B g f s _39475.
Proof. exact (EQ_MP (@lem3626526 A B g f s _39475) (@lem3626060 A B _39475 s g f h1)). Qed.
Lemma lem3626529 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3626530 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39475 : A) : (term274 A B g f s _39475) = (term278 A B s g f _39475).
Proof. exact (@lem3626529 (term214 A s _39475) ((term211 A B g f _39475) = _39475)). Qed.
Lemma lem3626532 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626533 {A : Type'} (s : A -> Prop) (_39475 : A) : (term279 A s _39475) = (@I (A -> Prop) s _39475).
Proof. exact (@lem3626532 (@I (A -> Prop) s _39475)). Qed.
Lemma lem3626534 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3626535 {A : Type'} (s : A -> Prop) (_39475 : A) : (term280 A s _39475) = (term281 A s _39475).
Proof. exact (MK_COMB (@lem3626534) (@lem3626533 A s _39475)). Qed.
Lemma lem3626536 {A B : Type'} (g : B -> A) (f : A -> B) (_39475 : A) : ((term211 A B g f _39475) = _39475) = ((term211 A B g f _39475) = _39475).
Proof. exact (eq_refl ((term211 A B g f _39475) = _39475)). Qed.
Lemma lem3626537 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39475 : A) : (term278 A B s g f _39475) = (term282 A B s g f _39475).
Proof. exact (MK_COMB (@lem3626535 A s _39475) (@lem3626536 A B g f _39475)). Qed.
Lemma lem3626538 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39475 : A) : (term274 A B g f s _39475) = (term282 A B s g f _39475).
Proof. exact (TRANS (@lem3626530 A B s g f _39475) (@lem3626537 A B s g f _39475)). Qed.
Lemma lem3626541 {A B : Type'} (_39475 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term282 A B s g f _39475.
Proof. exact (EQ_MP (@lem3626538 A B s g f _39475) (@lem3626527 A B _39475 s g f h1)). Qed.
Lemma lem3626542 {A B : Type'} (_39475 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term282 A B s g f _39475.
Proof. exact (@lem3626541 A B _39475 s g f h1). Qed.
Lemma lem3626543 {A B : Type'} (x'' : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term282 A B s g f x''.
Proof. exact (@lem3626542 A B x'' s g f h1). Qed.
Lemma lem3626546 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : (term211 A B g f x'') = x''.
Proof. exact (@lem3626543 A B x'' s g f h1 (@lem3626494 A B x g x' f s x'' h2)). Qed.
Lemma lem3626547 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : term283 A B g f x''.
Proof. exact (fun h0 : term284 A B g f x'' => @lem3626546 A B x g x' f s x'' h1 h2). Qed.
Lemma lem3626549 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626550 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term283 A B g f x'') = ((term211 A B g f x'') = x'').
Proof. exact (@lem3626549 ((term211 A B g f x'') = x'')). Qed.
Lemma lem3626551 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : (term211 A B g f x'') = x''.
Proof. exact (EQ_MP (@lem3626550 A B g f x'') (@lem3626547 A B x g x' f s x'' h1 h2)). Qed.
Lemma lem3626553 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3626554 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3626553 A x). Qed.
Lemma lem3626555 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term211 A B g f x'') = (term211 A B g f x'').
Proof. exact (@lem3626554 A (term211 A B g f x'')). Qed.
Lemma lem3626556 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : term285 A B g f x''.
Proof. exact (fun h0 : term286 A B g f x'' => @lem3626555 A B g f x''). Qed.
Lemma lem3626558 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626559 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term285 A B g f x'') = ((term211 A B g f x'') = (term211 A B g f x'')).
Proof. exact (@lem3626558 ((term211 A B g f x'') = (term211 A B g f x''))). Qed.
Lemma lem3626560 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term211 A B g f x'') = (term211 A B g f x'').
Proof. exact (EQ_MP (@lem3626559 A B g f x'') (@lem3626556 A B g f x'')). Qed.
Lemma lem3626578 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3626579 {A : Type'} (y : A) (x : A) (z : A) : (term287 A x y z) = (term288 A y x z).
Proof. exact (@lem3626578 (y = z) (term289 A x z)). Qed.
Lemma lem3626589 {A : Type'} (x : A) (y : A) : (term290 A x y) = (term290 A x y).
Proof. exact (eq_refl (term290 A x y)). Qed.
Lemma lem3626590 {A : Type'} (y : A) (x : A) (z : A) : (term271 A x y z) = (term291 A y x z).
Proof. exact (MK_COMB (@lem3626589 A x y) (@lem3626579 A y x z)). Qed.
Lemma lem3626594 (q : Prop) (p : Prop) (r : Prop) : (term292 p q r) = (term292 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3626595 {A : Type'} (y : A) (x : A) (z : A) : (term291 A y x z) = (term293 A y x z).
Proof. exact (@lem3626594 (y = z) (term289 A x y) (term289 A x z)). Qed.
Lemma lem3626617 {A : Type'} (y : A) (x : A) (z : A) : (term271 A x y z) = (term293 A y x z).
Proof. exact (TRANS (@lem3626590 A y x z) (@lem3626595 A y x z)). Qed.
Lemma lem3626618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3626619 {A : Type'} (y : A) (x : A) (z : A) : (term294 A x y z) = (term295 A y x z).
Proof. exact (MK_COMB (@lem3626618) (@lem3626617 A y x z)). Qed.
Lemma lem3626641 {A : Type'} (y : A) (x : A) (z : A) : (term293 A y x z) = (term293 A y x z).
Proof. exact (eq_refl (term293 A y x z)). Qed.
Lemma lem3626642 {A : Type'} (y : A) (x : A) (z : A) : ((term271 A x y z) = (term293 A y x z)) = ((term293 A y x z) = (term293 A y x z)).
Proof. exact (MK_COMB (@lem3626619 A y x z) (@lem3626641 A y x z)). Qed.
Lemma lem3626644 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3626645 (x : Prop) : (x = x) = True.
Proof. exact (@lem3626644 Prop x). Qed.
Lemma lem3626646 {A : Type'} (y : A) (x : A) (z : A) : ((term293 A y x z) = (term293 A y x z)) = True.
Proof. exact (@lem3626645 (term293 A y x z)). Qed.
Lemma lem3626647 {A : Type'} (y : A) (x : A) (z : A) : ((term271 A x y z) = (term293 A y x z)) = True.
Proof. exact (TRANS (@lem3626642 A y x z) (@lem3626646 A y x z)). Qed.
Lemma lem3626648 {A : Type'} (y : A) (x : A) (z : A) : True = ((term271 A x y z) = (term293 A y x z)).
Proof. exact (SYM (@lem3626647 A y x z)). Qed.
Lemma lem3626649 {A : Type'} (y : A) (x : A) (z : A) : (term271 A x y z) = (term293 A y x z).
Proof. exact (EQ_MP (@lem3626648 A y x z) (@lem0)). Qed.
Lemma lem3626650 {A : Type'} (y : A) (x : A) (z : A) : term293 A y x z.
Proof. exact (EQ_MP (@lem3626649 A y x z) (@lem3626485 A x y z)). Qed.
Lemma lem3626652 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3626653 {A : Type'} (x : A) (y : A) (z : A) : (term293 A y x z) = (term296 A x y z).
Proof. exact (@lem3626652 (term297 A y x z) (y = z)). Qed.
Lemma lem3626655 (a : Prop) (b : Prop) : (term298 a b) = (term299 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3626656 {A : Type'} (y : A) (x : A) (z : A) : (term300 A y x z) = (term301 A y x z).
Proof. exact (@lem3626655 (term289 A x y) (term289 A x z)). Qed.
Lemma lem3626658 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626659 {A : Type'} (x : A) (y : A) : (term302 A x y) = (x = y).
Proof. exact (@lem3626658 (x = y)). Qed.
Lemma lem3626660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3626661 {A : Type'} (x : A) (y : A) : (term303 A x y) = (term304 A x y).
Proof. exact (MK_COMB (@lem3626660) (@lem3626659 A x y)). Qed.
Lemma lem3626663 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626664 {A : Type'} (x : A) (z : A) : (term302 A x z) = (x = z).
Proof. exact (@lem3626663 (x = z)). Qed.
Lemma lem3626665 {A : Type'} (y : A) (x : A) (z : A) : (term301 A y x z) = (term305 A y x z).
Proof. exact (MK_COMB (@lem3626661 A x y) (@lem3626664 A x z)). Qed.
Lemma lem3626666 {A : Type'} (y : A) (x : A) (z : A) : (term300 A y x z) = (term305 A y x z).
Proof. exact (TRANS (@lem3626656 A y x z) (@lem3626665 A y x z)). Qed.
Lemma lem3626667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3626668 {A : Type'} (y : A) (x : A) (z : A) : (term306 A y x z) = (term307 A y x z).
Proof. exact (MK_COMB (@lem3626667) (@lem3626666 A y x z)). Qed.
Lemma lem3626669 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3626670 {A : Type'} (x : A) (y : A) (z : A) : (term296 A x y z) = (term308 A x y z).
Proof. exact (MK_COMB (@lem3626668 A y x z) (@lem3626669 A y z)). Qed.
Lemma lem3626671 {A : Type'} (x : A) (y : A) (z : A) : (term293 A y x z) = (term308 A x y z).
Proof. exact (TRANS (@lem3626653 A x y z) (@lem3626670 A x y z)). Qed.
Lemma lem3626673 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : term309 A B g f x''.
Proof. exact (conj (@lem3626551 A B x g x' f s x'' h1 h2) (@lem3626560 A B g f x'')). Qed.
Lemma lem3626675 {A : Type'} (x : A) (y : A) (z : A) : term308 A x y z.
Proof. exact (EQ_MP (@lem3626671 A x y z) (@lem3626650 A y x z)). Qed.
Lemma lem3626676 {A : Type'} (x : A) (y : A) (z : A) : term308 A x y z.
Proof. exact (@lem3626675 A x y z). Qed.
Lemma lem3626677 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : term310 A B g f x''.
Proof. exact (@lem3626676 A (term211 A B g f x'') x'' (term211 A B g f x'')). Qed.
Lemma lem3626680 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : x'' = (term211 A B g f x'').
Proof. exact (@lem3626677 A B g f x'' (@lem3626673 A B x g x' f s x'' h1 h2)). Qed.
Lemma lem3626681 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : term311 A B g f x''.
Proof. exact (fun h0 : term312 A B g f x'' => @lem3626680 A B x g x' f s x'' h1 h2). Qed.
Lemma lem3626683 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626684 {A B : Type'} (g : B -> A) (f : A -> B) (x'' : A) : (term311 A B g f x'') = (x'' = (term211 A B g f x'')).
Proof. exact (@lem3626683 (x'' = (term211 A B g f x''))). Qed.
Lemma lem3626685 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : x'' = (term211 A B g f x'').
Proof. exact (EQ_MP (@lem3626684 A B g f x'') (@lem3626681 A B x g x' f s x'' h1 h2)). Qed.
Lemma lem3626687 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem3626688 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem3626687 A x). Qed.
Lemma lem3626689 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem3626688 A s). Qed.
Lemma lem3626690 {A : Type'} (s : A -> Prop) : term333 A s.
Proof. exact (fun h0 : term334 A s => @lem3626689 A s). Qed.
Lemma lem3626692 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626693 {A : Type'} (s : A -> Prop) : (term333 A s) = (s = s).
Proof. exact (@lem3626692 (s = s)). Qed.
Lemma lem3626694 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3626693 A s) (@lem3626690 A s)). Qed.
Lemma lem3626696 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : @I (A -> Prop) s x''.
Proof. exact (proj2 (@lem3625786 A B x g x' f s x'' h1)). Qed.
Lemma lem3626697 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term272 A s x''.
Proof. exact (fun h0 : term214 A s x'' => @lem3626696 A B x g x' f s x'' h1). Qed.
Lemma lem3626699 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626700 {A : Type'} (s : A -> Prop) (x'' : A) : (term272 A s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3626699 (@I (A -> Prop) s x'')). Qed.
Lemma lem3626701 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : @I (A -> Prop) s x''.
Proof. exact (EQ_MP (@lem3626700 A s x'') (@lem3626697 A B x g x' f s x'' h1)). Qed.
Lemma lem3626719 (q : Prop) (p : Prop) (r : Prop) : (term292 p q r) = (term292 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3626720 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term330 A _39516 _39517 _39514 _39515) = (term335 A _39517 _39516 _39514 _39515).
Proof. exact (@lem3626719 (@I (A -> Prop) _39516 _39517) (term336 A _39514 _39516) (term214 A _39514 _39515)). Qed.
Lemma lem3626738 {A : Type'} (_39515 : A) (_39517 : A) : (term290 A _39515 _39517) = (term290 A _39515 _39517).
Proof. exact (eq_refl (term290 A _39515 _39517)). Qed.
Lemma lem3626739 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term332 A _39516 _39517 _39514 _39515) = (term337 A _39517 _39516 _39514 _39515).
Proof. exact (MK_COMB (@lem3626738 A _39515 _39517) (@lem3626720 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626743 (q : Prop) (p : Prop) (r : Prop) : (term292 p q r) = (term292 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3626744 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term337 A _39517 _39516 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515).
Proof. exact (@lem3626743 (@I (A -> Prop) _39516 _39517) (term289 A _39515 _39517) (term339 A _39516 _39514 _39515)). Qed.
Lemma lem3626774 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term332 A _39516 _39517 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515).
Proof. exact (TRANS (@lem3626739 A _39517 _39516 _39514 _39515) (@lem3626744 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3626776 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term340 A _39516 _39517 _39514 _39515) = (term341 A _39517 _39516 _39514 _39515).
Proof. exact (MK_COMB (@lem3626775) (@lem3626774 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626806 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term338 A _39517 _39516 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515).
Proof. exact (eq_refl (term338 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626807 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : ((term332 A _39516 _39517 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515)) = ((term338 A _39517 _39516 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515)).
Proof. exact (MK_COMB (@lem3626776 A _39517 _39516 _39514 _39515) (@lem3626806 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3626810 (x : Prop) : (x = x) = True.
Proof. exact (@lem3626809 Prop x). Qed.
Lemma lem3626811 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : ((term338 A _39517 _39516 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515)) = True.
Proof. exact (@lem3626810 (term338 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626812 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : ((term332 A _39516 _39517 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515)) = True.
Proof. exact (TRANS (@lem3626807 A _39517 _39516 _39514 _39515) (@lem3626811 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626813 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : True = ((term332 A _39516 _39517 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515)).
Proof. exact (SYM (@lem3626812 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626814 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term332 A _39516 _39517 _39514 _39515) = (term338 A _39517 _39516 _39514 _39515).
Proof. exact (EQ_MP (@lem3626813 A _39517 _39516 _39514 _39515) (@lem0)). Qed.
Lemma lem3626815 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : term338 A _39517 _39516 _39514 _39515.
Proof. exact (EQ_MP (@lem3626814 A _39517 _39516 _39514 _39515) (@lem3626427 A _39516 _39517 _39514 _39515)). Qed.
Lemma lem3626817 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3626818 {A : Type'} (_39514 : A -> Prop) (_39515 : A) (_39516 : A -> Prop) (_39517 : A) : (term338 A _39517 _39516 _39514 _39515) = (term342 A _39514 _39515 _39516 _39517).
Proof. exact (@lem3626817 (term343 A _39517 _39516 _39514 _39515) (@I (A -> Prop) _39516 _39517)). Qed.
Lemma lem3626820 (a : Prop) (b : Prop) : (term298 a b) = (term299 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3626821 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term344 A _39517 _39516 _39514 _39515) = (term345 A _39517 _39516 _39514 _39515).
Proof. exact (@lem3626820 (term289 A _39515 _39517) (term339 A _39516 _39514 _39515)). Qed.
Lemma lem3626823 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626824 {A : Type'} (_39515 : A) (_39517 : A) : (term302 A _39515 _39517) = (_39515 = _39517).
Proof. exact (@lem3626823 (_39515 = _39517)). Qed.
Lemma lem3626825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3626826 {A : Type'} (_39515 : A) (_39517 : A) : (term303 A _39515 _39517) = (term304 A _39515 _39517).
Proof. exact (MK_COMB (@lem3626825) (@lem3626824 A _39515 _39517)). Qed.
Lemma lem3626828 (a : Prop) (b : Prop) : (term298 a b) = (term299 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3626829 {A : Type'} (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term346 A _39516 _39514 _39515) = (term347 A _39516 _39514 _39515).
Proof. exact (@lem3626828 (term336 A _39514 _39516) (term214 A _39514 _39515)). Qed.
Lemma lem3626831 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626832 {A : Type'} (_39514 : A -> Prop) (_39516 : A -> Prop) : (term348 A _39514 _39516) = (_39514 = _39516).
Proof. exact (@lem3626831 (_39514 = _39516)). Qed.
Lemma lem3626833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3626834 {A : Type'} (_39514 : A -> Prop) (_39516 : A -> Prop) : (term349 A _39514 _39516) = (term350 A _39514 _39516).
Proof. exact (MK_COMB (@lem3626833) (@lem3626832 A _39514 _39516)). Qed.
Lemma lem3626836 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3626837 {A : Type'} (_39514 : A -> Prop) (_39515 : A) : (term279 A _39514 _39515) = (@I (A -> Prop) _39514 _39515).
Proof. exact (@lem3626836 (@I (A -> Prop) _39514 _39515)). Qed.
Lemma lem3626838 {A : Type'} (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term347 A _39516 _39514 _39515) = (term351 A _39516 _39514 _39515).
Proof. exact (MK_COMB (@lem3626834 A _39514 _39516) (@lem3626837 A _39514 _39515)). Qed.
Lemma lem3626839 {A : Type'} (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term346 A _39516 _39514 _39515) = (term351 A _39516 _39514 _39515).
Proof. exact (TRANS (@lem3626829 A _39516 _39514 _39515) (@lem3626838 A _39516 _39514 _39515)). Qed.
Lemma lem3626840 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term345 A _39517 _39516 _39514 _39515) = (term352 A _39517 _39516 _39514 _39515).
Proof. exact (MK_COMB (@lem3626826 A _39515 _39517) (@lem3626839 A _39516 _39514 _39515)). Qed.
Lemma lem3626841 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term344 A _39517 _39516 _39514 _39515) = (term352 A _39517 _39516 _39514 _39515).
Proof. exact (TRANS (@lem3626821 A _39517 _39516 _39514 _39515) (@lem3626840 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3626843 {A : Type'} (_39517 : A) (_39516 : A -> Prop) (_39514 : A -> Prop) (_39515 : A) : (term353 A _39517 _39516 _39514 _39515) = (term354 A _39517 _39516 _39514 _39515).
Proof. exact (MK_COMB (@lem3626842) (@lem3626841 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626844 {A : Type'} (_39516 : A -> Prop) (_39517 : A) : (@I (A -> Prop) _39516 _39517) = (@I (A -> Prop) _39516 _39517).
Proof. exact (eq_refl (@I (A -> Prop) _39516 _39517)). Qed.
Lemma lem3626845 {A : Type'} (_39514 : A -> Prop) (_39515 : A) (_39516 : A -> Prop) (_39517 : A) : (term342 A _39514 _39515 _39516 _39517) = (term355 A _39514 _39515 _39516 _39517).
Proof. exact (MK_COMB (@lem3626843 A _39517 _39516 _39514 _39515) (@lem3626844 A _39516 _39517)). Qed.
Lemma lem3626846 {A : Type'} (_39514 : A -> Prop) (_39515 : A) (_39516 : A -> Prop) (_39517 : A) : (term338 A _39517 _39516 _39514 _39515) = (term355 A _39514 _39515 _39516 _39517).
Proof. exact (TRANS (@lem3626818 A _39514 _39515 _39516 _39517) (@lem3626845 A _39514 _39515 _39516 _39517)). Qed.
Lemma lem3626848 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term356 A s x''.
Proof. exact (conj (@lem3626694 A s) (@lem3626701 A B x g x' f s x'' h1)). Qed.
Lemma lem3626849 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : term357 A B g f s x''.
Proof. exact (conj (@lem3626685 A B x g x' f s x'' h1 h2) (@lem3626848 A B x g x' f s x'' h2)). Qed.
Lemma lem3626851 {A : Type'} (_39514 : A -> Prop) (_39515 : A) (_39516 : A -> Prop) (_39517 : A) : term355 A _39514 _39515 _39516 _39517.
Proof. exact (EQ_MP (@lem3626846 A _39514 _39515 _39516 _39517) (@lem3626815 A _39517 _39516 _39514 _39515)). Qed.
Lemma lem3626852 {A : Type'} (_39514 : A -> Prop) (_39515 : A) (_39516 : A -> Prop) (_39517 : A) : term355 A _39514 _39515 _39516 _39517.
Proof. exact (@lem3626851 A _39514 _39515 _39516 _39517). Qed.
Lemma lem3626853 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : term358 A B s g f x''.
Proof. exact (@lem3626852 A s x'' s (term211 A B g f x'')). Qed.
Lemma lem3626856 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : term359 A B s g f x''.
Proof. exact (@lem3626853 A B s g f x'' (@lem3626849 A B x g x' f s x'' h1 h2)). Qed.
Lemma lem3626857 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : term360 A B s g f x''.
Proof. exact (fun h0 : term268 A B s g f x'' => @lem3626856 A B x g x' f s x'' h1 h2). Qed.
Lemma lem3626859 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626860 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : (term360 A B s g f x'') = (term359 A B s g f x'').
Proof. exact (@lem3626859 (term359 A B s g f x'')). Qed.
Lemma lem3626861 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : term359 A B s g f x''.
Proof. exact (EQ_MP (@lem3626860 A B s g f x'') (@lem3626857 A B x g x' f s x'' h1 h2)). Qed.
Lemma lem3626864 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3626866 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x'' : A) : (term268 A B s g f x'') = (term361 A B s g f x'').
Proof. exact (@lem3626864 (term359 A B s g f x'')). Qed.
Lemma lem3626869 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term225 A B x g x' f s x'') : term361 A B s g f x''.
Proof. exact (EQ_MP (@lem3626866 A B s g f x'') (@lem3626073 A B x g x' f s x'' h1)). Qed.
Lemma lem3626872 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : False.
Proof. exact (@lem3626869 A B x g x' f s x'' h2 (@lem3626861 A B x g x' f s x'' h1 h2)). Qed.
Lemma lem3626873 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : term324.
Proof. exact (fun h0 : ~ False => @lem3626872 A B x g x' f s x'' h1 h2). Qed.
Lemma lem3626875 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3626876 : term324 = False.
Proof. exact (@lem3626875 False). Qed.
Lemma lem3626879 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term225 A B x g x' f s x'') : False.
Proof. exact (EQ_MP (@lem3626876) (@lem3626873 A B x g x' f s x'' h1 h2)). Qed.
Lemma lem3626880 {A B : Type'} (x : A) (g : B -> A) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) (h1 : term56 A B s g f) (h2 : term205 A B x g x' f s x'') : False.
Proof. exact (or_elim (@lem3625777 A B x g x' f s x'' h2) (fun h0 : term237 A B x g f s => @lem3626408 A B x g f s h1 h0) (fun h0 : term225 A B x g x' f s x'' => @lem3626879 A B x g x' f s x'' h1 h0)). Qed.
Lemma lem3626881 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term208 A B x g x' f s) (h2 : term56 A B s g f) : False.
Proof. exact (ex_elim (@lem3625631 A B x g x' f s h1) (fun x'' : A => fun h0 : term207 A B x g x' f s x'' => @lem3626880 A B x g x' f s x'' h2 h0)). Qed.
Lemma lem3626882 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term103 A B x g f s) (h2 : term56 A B s g f) : False.
Proof. exact (ex_elim (@lem3625630 A B x g f s h1) (fun x' : B => fun h0 : term209 A B x g f s x' => @lem3626881 A B x x' s g f h0 h2)). Qed.
Lemma lem3626883 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term103 A B x g f s) (h2 : term56 A B s g f) : (term103 A B x g f s) = False.
Proof. exact (prop_ext (fun h3 : term103 A B x g f s => @lem3626882 A B x s g f h1 h2) (fun h3 : False => @lem3625205 A B x g f s h1)). Qed.
Lemma lem3626884 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term103 A B x g f s) (h2 : term56 A B s g f) : False.
Proof. exact (EQ_MP (@lem3626883 A B x s g f h1 h2) (@lem3625205 A B x g f s h1)). Qed.
Lemma lem3626885 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term102 A B x g f s.
Proof. exact (fun h0 : term103 A B x g f s => @lem3626884 A B x s g f h0 h1). Qed.
Lemma lem3626886 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : (s x) = (term77 A B x g f s).
Proof. exact (EQ_MP (@lem3625204 A B x g f s) (@lem3626885 A B x s g f h1)). Qed.
Lemma lem3626891 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term56 A B s g f) : term80 A B g f s.
Proof. exact (fun x : A => @lem3626886 A B x s g f h1). Qed.
Lemma lem3626892 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term81 A B g f s.
Proof. exact (fun h0 : term56 A B s g f => @lem3626891 A B s g f h0). Qed.
Lemma lem3626897 {A B : Type'} (f : A -> B) (s : A -> Prop) : term93 A B f s.
Proof. exact (fun g : B -> A => @lem3626892 A B g f s). Qed.
Lemma lem3626902 {A B : Type'} (s : A -> Prop) : term97 A B s.
Proof. exact (fun f : A -> B => @lem3626897 A B f s). Qed.
Lemma lem3626907 {A B : Type'} : term101 A B.
Proof. exact (fun s : A -> Prop => @lem3626902 A B s). Qed.
Lemma lem3626908 {A B : Type'} : term100 A B.
Proof. exact (EQ_MP (@lem3625199 A B) (@lem3626907 A B)). Qed.
Lemma lem3626909 {A B : Type'} (s : A -> Prop) : term362 A B s.
Proof. exact (@lem3626908 A B s). Qed.
Lemma lem3626910 {A B : Type'} (s : A -> Prop) : (term362 A B s) = (term96 A B s).
Proof. exact (eq_refl (term362 A B s)). Qed.
Lemma lem3626911 {A B : Type'} (s : A -> Prop) : term96 A B s.
Proof. exact (EQ_MP (@lem3626910 A B s) (@lem3626909 A B s)). Qed.
Lemma lem3626912 {A B : Type'} (s : A -> Prop) (f : A -> B) : term363 A B s f.
Proof. exact (@lem3626911 A B s f). Qed.
Lemma lem3626913 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term363 A B s f) = (term92 A B f s).
Proof. exact (eq_refl (term363 A B s f)). Qed.
Lemma lem3626914 {A B : Type'} (f : A -> B) (s : A -> Prop) : term92 A B f s.
Proof. exact (EQ_MP (@lem3626913 A B f s) (@lem3626912 A B s f)). Qed.
Lemma lem3626915 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : B -> A) : term364 A B f s g.
Proof. exact (@lem3626914 A B f s g). Qed.
Lemma lem3626916 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : (term364 A B f s g) = (term83 A B g f s).
Proof. exact (eq_refl (term364 A B f s g)). Qed.
Lemma lem3626917 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term83 A B g f s.
Proof. exact (EQ_MP (@lem3626916 A B g f s) (@lem3626915 A B f s g)). Qed.
Lemma lem3626919 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term83 A B g f s.
Proof. exact (@lem3624955 A B g f s (@lem3626917 A B g f s)). Qed.
Lemma lem3626920 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term84 A B g f s) : False.
Proof. exact (@lem3626919 A B g f s (@lem3624939 A B g f s h1)). Qed.
Lemma lem3626921 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term84 A B g f s) : (term84 A B g f s) = False.
Proof. exact (prop_ext (fun h2 : term84 A B g f s => @lem3626920 A B g f s h1) (fun h2 : False => @lem3624939 A B g f s h1)). Qed.
Lemma lem3626922 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term84 A B g f s) : False.
Proof. exact (EQ_MP (@lem3626921 A B g f s h1) (@lem3624939 A B g f s h1)). Qed.
Lemma lem3626923 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term83 A B g f s.
Proof. exact (fun h0 : term84 A B g f s => @lem3626922 A B g f s h0). Qed.
Lemma lem3626924 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term81 A B g f s.
Proof. exact (EQ_MP (@lem3624938 A B g f s) (@lem3626923 A B g f s)). Qed.
Lemma lem3626925 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term46 A B g f s.
Proof. exact (EQ_MP (@lem3624934 A B g f s) (@lem3626924 A B g f s)). Qed.
Lemma lem3626926 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term45 A B g f s.
Proof. exact (EQ_MP (@lem3624821 A B g f s) (@lem3626925 A B g f s)). Qed.
Lemma lem3626927 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term28 A B s g f) (h2 : term5 A B f s) : s = (term34 A B g f s).
Proof. exact (@lem3626926 A B g f s (@lem3624788 A B g f s h1 h2)). Qed.
Lemma lem3626929 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem3624695 A B f s) (@lem3624694 A B f s)). Qed.
Lemma lem3626930 {A B : Type'} (f : B -> A) (s : B -> Prop) : term365 A B f s.
Proof. exact (@lem3626929 B A f s). Qed.
Lemma lem3626931 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) : term366 A B g f s.
Proof. exact (@lem3626930 A B g (@IMAGE A B f s)). Qed.
Lemma lem3626937 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term5 A B f s) = ((term5 A B f s) = True).
Proof. exact (@lem7 (term5 A B f s)). Qed.
Lemma lem3626940 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term5 A B f s) : (term5 A B f s) = True.
Proof. exact (EQ_MP (@lem3626937 A B f s) (@lem3624763 A B f s h1)). Qed.
Lemma lem3626941 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term5 A B f s) : True = (term5 A B f s).
Proof. exact (SYM (@lem3626940 A B f s h1)). Qed.
Lemma lem3626942 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term5 A B f s) : term5 A B f s.
Proof. exact (EQ_MP (@lem3626941 A B f s h1) (@lem0)). Qed.
Lemma lem3626943 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term5 A B f s) : term38 A B g f s.
Proof. exact (@lem3626931 A B g f s (@lem3626942 A B f s h1)). Qed.
Lemma lem3626944 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term5 A B f s) (h2 : s = (term34 A B g f s)) : @FINITE A s.
Proof. exact (EQ_MP (@lem3624777 A B g f s h2) (@lem3626943 A B g f s h1)). Qed.
Lemma lem3626945 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term28 A B s g f) (h2 : term5 A B f s) : (s = (term34 A B g f s)) = (@FINITE A s).
Proof. exact (prop_ext (fun h3 : s = (term34 A B g f s) => @lem3626944 A B g f s h2 h3) (fun h3 : @FINITE A s => @lem3626927 A B g f s h1 h2)). Qed.
Lemma lem3626946 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (h1 : term28 A B s g f) (h2 : term5 A B f s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3626945 A B g f s h1 h2) (@lem3626927 A B g f s h1 h2)). Qed.
Lemma lem3626947 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term28 A B s g f) : term33 A B f s.
Proof. exact (fun h0 : term5 A B f s => @lem3626946 A B g f s h1 h0). Qed.
Lemma lem3626948 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term28 A B s g f) : term26 A B f s.
Proof. exact (EQ_MP (@lem3624762 A B f s) (@lem3626947 A B s g f h1)). Qed.
Lemma lem3626949 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term18 A B s f) : term26 A B f s.
Proof. exact (ex_elim (@lem3624742 A B s f h1) (fun g : B -> A => fun h0 : term367 A B s f g => @lem3626948 A B s g f h0)). Qed.
Lemma lem3626950 {A B : Type'} (f : A -> B) (s : A -> Prop) : term27 A B f s.
Proof. exact (fun h0 : term18 A B s f => @lem3626949 A B s f h0). Qed.
Lemma lem3626951 {A B : Type'} (f : A -> B) (s : A -> Prop) : term21 A B f s.
Proof. exact (EQ_MP (@lem3624741 A B f s) (@lem3626950 A B f s)). Qed.
Lemma lem3626956 {A B : Type'} (f : A -> B) : term368 A B f.
Proof. exact (fun s : A -> Prop => @lem3626951 A B f s). Qed.
Lemma lem3626961 {A B : Type'} : term369 A B.
Proof. exact (fun f : A -> B => @lem3626956 A B f). Qed.
