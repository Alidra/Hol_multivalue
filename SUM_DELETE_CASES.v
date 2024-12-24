Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_DELETE_CASES_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUM_DELETE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem7122635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7122636 {_132966 : Type'} (s : _132966 -> Prop) (t : _132966 -> Prop) : (s = t) = (term0 _132966 s t).
Proof. exact (@lem7122635 _132966 s t). Qed.
Lemma lem7122637 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : ((@DELETE _132966 s a) = s) = (term1 _132966 a s).
Proof. exact (@lem7122636 _132966 (@DELETE _132966 s a) s). Qed.
Lemma lem7122646 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term2 _132966 a s) = (term2 _132966 a s).
Proof. exact (eq_refl (term2 _132966 a s)). Qed.
Lemma lem7122647 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term3 _132966 a s) = (term4 _132966 a s).
Proof. exact (MK_COMB (@lem7122646 _132966 a s) (@lem7122637 _132966 a s)). Qed.
Lemma lem7122650 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term4 _132966 a s) = (term3 _132966 a s).
Proof. exact (SYM (@lem7122647 _132966 a s)). Qed.
Lemma lem7122654 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7122655 {_132966 : Type'} (P : _132966 -> Prop) (x : _132966) : (@IN _132966 x P) = (P x).
Proof. exact (@lem7122654 _132966 P x). Qed.
Lemma lem7122656 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : (@IN _132966 a s) = (s a).
Proof. exact (@lem7122655 _132966 s a). Qed.
Lemma lem7122657 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7122658 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : (term5 _132966 a s) = (term6 _132966 s a).
Proof. exact (MK_COMB (@lem7122657) (@lem7122656 _132966 s a)). Qed.
Lemma lem7122659 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7122660 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : (term2 _132966 a s) = (term7 _132966 s a).
Proof. exact (MK_COMB (@lem7122659) (@lem7122658 _132966 s a)). Qed.
Lemma lem7122668 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term8 A x s y) = (term9 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem7122669 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (y : _132966) : (term8 _132966 x s y) = (term9 _132966 s x y).
Proof. exact (@lem7122668 _132966 s x y). Qed.
Lemma lem7122670 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) : (term8 _132966 x s a) = (term9 _132966 s x a).
Proof. exact (@lem7122669 _132966 s x a). Qed.
Lemma lem7122674 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7122675 {_132966 : Type'} (P : _132966 -> Prop) (x : _132966) : (@IN _132966 x P) = (P x).
Proof. exact (@lem7122674 _132966 P x). Qed.
Lemma lem7122676 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (@IN _132966 x s) = (s x).
Proof. exact (@lem7122675 _132966 s x). Qed.
Lemma lem7122677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7122678 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term10 _132966 x s) = (term11 _132966 s x).
Proof. exact (MK_COMB (@lem7122677) (@lem7122676 _132966 s x)). Qed.
Lemma lem7122681 {_132966 : Type'} (x : _132966) (a : _132966) : (term12 _132966 x a) = (term12 _132966 x a).
Proof. exact (eq_refl (term12 _132966 x a)). Qed.
Lemma lem7122682 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) : (term9 _132966 s x a) = (term13 _132966 s x a).
Proof. exact (MK_COMB (@lem7122678 _132966 s x) (@lem7122681 _132966 x a)). Qed.
Lemma lem7122685 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) : (term8 _132966 x s a) = (term13 _132966 s x a).
Proof. exact (TRANS (@lem7122670 _132966 s x a) (@lem7122682 _132966 s x a)). Qed.
Lemma lem7122686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7122687 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) : (term14 _132966 x s a) = (term15 _132966 s x a).
Proof. exact (MK_COMB (@lem7122686) (@lem7122685 _132966 s x a)). Qed.
Lemma lem7122689 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7122690 {_132966 : Type'} (P : _132966 -> Prop) (x : _132966) : (@IN _132966 x P) = (P x).
Proof. exact (@lem7122689 _132966 P x). Qed.
Lemma lem7122691 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (@IN _132966 x s) = (s x).
Proof. exact (@lem7122690 _132966 s x). Qed.
Lemma lem7122692 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : ((term8 _132966 x s a) = (@IN _132966 x s)) = ((term13 _132966 s x a) = (s x)).
Proof. exact (MK_COMB (@lem7122687 _132966 s x a) (@lem7122691 _132966 s x)). Qed.
Lemma lem7122695 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term16 _132966 a s) = (term17 _132966 a s).
Proof. exact (fun_ext (fun x : _132966 => @lem7122692 _132966 a s x)). Qed.
Lemma lem7122696 {_132966 : Type'} : (@all _132966) = (@all _132966).
Proof. exact (eq_refl (@all _132966)). Qed.
Lemma lem7122697 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term1 _132966 a s) = (term18 _132966 a s).
Proof. exact (MK_COMB (@lem7122696 _132966) (@lem7122695 _132966 a s)). Qed.
Lemma lem7122702 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term4 _132966 a s) = (term19 _132966 a s).
Proof. exact (MK_COMB (@lem7122660 _132966 s a) (@lem7122697 _132966 a s)). Qed.
Lemma lem7122705 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term19 _132966 a s) = (term4 _132966 a s).
Proof. exact (SYM (@lem7122702 _132966 a s)). Qed.
Lemma lem7122707 (p : Prop) : p = (term20 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7122708 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term19 _132966 a s) = (term21 _132966 a s).
Proof. exact (@lem7122707 (term19 _132966 a s)). Qed.
Lemma lem7122709 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term21 _132966 a s) = (term19 _132966 a s).
Proof. exact (SYM (@lem7122708 _132966 a s)). Qed.
Lemma lem7122710 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term22 _132966 a s) : term22 _132966 a s.
Proof. exact (h1). Qed.
Lemma lem7122713 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term21 _132966 a s) : term21 _132966 a s.
Proof. exact (h1). Qed.
Lemma lem7122714 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term23 _132966 a s.
Proof. exact (fun h0 : term21 _132966 a s => @lem7122713 _132966 a s h0). Qed.
Lemma lem7122715 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term23 _132966 a s) : term23 _132966 a s.
Proof. exact (h1). Qed.
Lemma lem7122716 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term21 _132966 a s) : term21 _132966 a s.
Proof. exact (h1). Qed.
Lemma lem7122717 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term21 _132966 a s) (h2 : term23 _132966 a s) : term21 _132966 a s.
Proof. exact (@lem7122715 _132966 a s h2 (@lem7122716 _132966 a s h1)). Qed.
Lemma lem7122718 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term21 _132966 a s) : term24 _132966 a s.
Proof. exact (fun h0 : term23 _132966 a s => @lem7122717 _132966 a s h1 h0). Qed.
Lemma lem7122719 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term23 _132966 a s) : term23 _132966 a s.
Proof. exact (h1). Qed.
Lemma lem7122720 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term21 _132966 a s) (h2 : term23 _132966 a s) : term21 _132966 a s.
Proof. exact (@lem7122718 _132966 a s h1 (@lem7122719 _132966 a s h2)). Qed.
Lemma lem7122721 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term23 _132966 a s) : term23 _132966 a s.
Proof. exact (fun h0 : term21 _132966 a s => @lem7122720 _132966 a s h0 h1). Qed.
Lemma lem7122722 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term25 _132966 a s.
Proof. exact (fun h0 : term23 _132966 a s => @lem7122721 _132966 a s h0). Qed.
Lemma lem7122725 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term23 _132966 a s.
Proof. exact (@lem7122722 _132966 a s (@lem7122714 _132966 a s)). Qed.
Lemma lem7122726 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term23 _132966 a s.
Proof. exact (@lem7122725 _132966 a s). Qed.
Lemma lem7122736 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7122737 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term21 _132966 a s) = (term26 _132966 a s).
Proof. exact (@lem7122736 (term22 _132966 a s)). Qed.
Lemma lem7122739 (t : Prop) : (term27 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7122740 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term26 _132966 a s) = (term19 _132966 a s).
Proof. exact (@lem7122739 (term19 _132966 a s)). Qed.
Lemma lem7122743 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term21 _132966 a s) = (term19 _132966 a s).
Proof. exact (TRANS (@lem7122737 _132966 a s) (@lem7122740 _132966 a s)). Qed.
Lemma lem7122750 {_132966 : Type'} (s : _132966 -> Prop) : (term28 _132966 s) = (term29 _132966 s).
Proof. exact (fun_ext (fun a : _132966 => @lem7122743 _132966 a s)). Qed.
Lemma lem7122751 {_132966 : Type'} : (@all _132966) = (@all _132966).
Proof. exact (eq_refl (@all _132966)). Qed.
Lemma lem7122752 {_132966 : Type'} (s : _132966 -> Prop) : (term30 _132966 s) = (term31 _132966 s).
Proof. exact (MK_COMB (@lem7122751 _132966) (@lem7122750 _132966 s)). Qed.
Lemma lem7122757 {_132966 : Type'} : (term32 _132966) = (term33 _132966).
Proof. exact (fun_ext (fun s : _132966 -> Prop => @lem7122752 _132966 s)). Qed.
Lemma lem7122758 {_132966 : Type'} : (@all (_132966 -> Prop)) = (@all (_132966 -> Prop)).
Proof. exact (eq_refl (@all (_132966 -> Prop))). Qed.
Lemma lem7122767 {_132966 : Type'} : (term34 _132966) = (term35 _132966).
Proof. exact (MK_COMB (@lem7122758 _132966) (@lem7122757 _132966)). Qed.
Lemma lem7122778 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : ((term13 _132966 s x a) = (s x)) = ((term13 _132966 s x a) = (s x)).
Proof. exact (eq_refl ((term13 _132966 s x a) = (s x))). Qed.
Lemma lem7122779 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term17 _132966 a s) = (term17 _132966 a s).
Proof. exact (fun_ext (fun x : _132966 => @lem7122778 _132966 a s x)). Qed.
Lemma lem7122780 {_132966 : Type'} : (@all _132966) = (@all _132966).
Proof. exact (eq_refl (@all _132966)). Qed.
Lemma lem7122781 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term18 _132966 a s) = (term18 _132966 a s).
Proof. exact (MK_COMB (@lem7122780 _132966) (@lem7122779 _132966 a s)). Qed.
Lemma lem7122786 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : (term7 _132966 s a) = (term7 _132966 s a).
Proof. exact (eq_refl (term7 _132966 s a)). Qed.
Lemma lem7122787 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term19 _132966 a s) = (term19 _132966 a s).
Proof. exact (MK_COMB (@lem7122786 _132966 s a) (@lem7122781 _132966 a s)). Qed.
Lemma lem7122788 {_132966 : Type'} (s : _132966 -> Prop) : (term29 _132966 s) = (term29 _132966 s).
Proof. exact (fun_ext (fun a : _132966 => @lem7122787 _132966 a s)). Qed.
Lemma lem7122789 {_132966 : Type'} : (@all _132966) = (@all _132966).
Proof. exact (eq_refl (@all _132966)). Qed.
Lemma lem7122790 {_132966 : Type'} (s : _132966 -> Prop) : (term31 _132966 s) = (term31 _132966 s).
Proof. exact (MK_COMB (@lem7122789 _132966) (@lem7122788 _132966 s)). Qed.
Lemma lem7122791 {_132966 : Type'} : (term33 _132966) = (term33 _132966).
Proof. exact (fun_ext (fun s : _132966 -> Prop => @lem7122790 _132966 s)). Qed.
Lemma lem7122792 {_132966 : Type'} : (@all (_132966 -> Prop)) = (@all (_132966 -> Prop)).
Proof. exact (eq_refl (@all (_132966 -> Prop))). Qed.
Lemma lem7122793 {_132966 : Type'} : (term35 _132966) = (term35 _132966).
Proof. exact (MK_COMB (@lem7122792 _132966) (@lem7122791 _132966)). Qed.
Lemma lem7122818 {_132966 : Type'} : (term34 _132966) = (term35 _132966).
Proof. exact (TRANS (@lem7122767 _132966) (@lem7122793 _132966)). Qed.
Lemma lem7122819 {_132966 : Type'} : (term35 _132966) = (term34 _132966).
Proof. exact (SYM (@lem7122818 _132966)). Qed.
Lemma lem7122822 (p : Prop) : p = (term20 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7122823 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : ((term13 _132966 s x a) = (s x)) = (term36 _132966 a s x).
Proof. exact (@lem7122822 ((term13 _132966 s x a) = (s x))). Qed.
Lemma lem7122824 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : (term36 _132966 a s x) = ((term13 _132966 s x a) = (s x)).
Proof. exact (SYM (@lem7122823 _132966 a s x)). Qed.
Lemma lem7122825 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term37 _132966 a s x) : term37 _132966 a s x.
Proof. exact (h1). Qed.
Lemma lem7122831 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : term6 _132966 s a.
Proof. exact (h1). Qed.
Lemma lem7122837 {_132966 : Type'} (x : _132966) (a : _132966) : (term38 _132966 x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem7122839 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term39 _132966 s x) = (term39 _132966 s x).
Proof. exact (eq_refl (term39 _132966 s x)). Qed.
Lemma lem7122840 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) : (term40 _132966 s x a) = (term41 _132966 s x a).
Proof. exact (MK_COMB (@lem7122839 _132966 s x) (@lem7122837 _132966 x a)). Qed.
Lemma lem7122841 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) : (term42 _132966 s x a) = (term40 _132966 s x a).
Proof. exact (@lem17045 (s x) (term12 _132966 x a)). Qed.
Lemma lem7122842 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) : (term42 _132966 s x a) = (term41 _132966 s x a).
Proof. exact (TRANS (@lem7122841 _132966 s x a) (@lem7122840 _132966 s x a)). Qed.
Lemma lem7122847 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem7122848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7122849 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) : (term43 _132966 s x a) = (term44 _132966 s x a).
Proof. exact (MK_COMB (@lem7122848) (@lem7122842 _132966 s x a)). Qed.
Lemma lem7122850 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : (term45 _132966 a s x) = (term46 _132966 a s x).
Proof. exact (MK_COMB (@lem7122849 _132966 s x a) (@lem7122847 _132966 s x)). Qed.
Lemma lem7122855 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : (term47 _132966 a s x) = (term47 _132966 a s x).
Proof. exact (eq_refl (term47 _132966 a s x)). Qed.
Lemma lem7122856 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : (term48 _132966 a s x) = (term49 _132966 a s x).
Proof. exact (MK_COMB (@lem7122855 _132966 a s x) (@lem7122850 _132966 a s x)). Qed.
Lemma lem7122857 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : (term37 _132966 a s x) = (term48 _132966 a s x).
Proof. exact (@lem17646 (term13 _132966 s x a) (s x)). Qed.
Lemma lem7122862 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) : (term37 _132966 a s x) = (term49 _132966 a s x).
Proof. exact (TRANS (@lem7122857 _132966 a s x) (@lem7122856 _132966 a s x)). Qed.
Lemma lem7122869 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : term6 _132966 s a.
Proof. exact (h1). Qed.
Lemma lem7122913 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term37 _132966 a s x) : term49 _132966 a s x.
Proof. exact (EQ_MP (@lem7122862 _132966 a s x) (@lem7122825 _132966 a s x h1)). Qed.
Lemma lem7122914 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : term50 _132966 a s x.
Proof. exact (h1). Qed.
Lemma lem7122915 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term46 _132966 a s x) : term46 _132966 a s x.
Proof. exact (h1). Qed.
Lemma lem7122917 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : term13 _132966 s x a.
Proof. exact (proj1 (@lem7122914 _132966 a s x h1)). Qed.
Lemma lem7122921 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term46 _132966 a s x) : term41 _132966 s x a.
Proof. exact (proj1 (@lem7122915 _132966 a s x h1)). Qed.
Lemma lem7122951 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) : term6 _132966 s x.
Proof. exact (h1). Qed.
Lemma lem7122955 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : term6 _132966 s a.
Proof. exact (h1). Qed.
Lemma lem7122963 {_132966 : Type'} (x : _132966) (a : _132966) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem7122967 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : term6 _132966 s x.
Proof. exact (proj2 (@lem7122914 _132966 a s x h1)). Qed.
Lemma lem7122977 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) : term6 _132966 s x.
Proof. exact (h1). Qed.
Lemma lem7122979 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : term6 _132966 s a.
Proof. exact (h1). Qed.
Lemma lem7122981 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term46 _132966 a s x) : s x.
Proof. exact (proj2 (@lem7122915 _132966 a s x h1)). Qed.
Lemma lem7122983 {_132966 : Type'} (x : _132966) (a : _132966) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem7123011 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : term6 _132966 s a.
Proof. exact (h1). Qed.
Lemma lem7123012 {_132966 : Type'} (s : _132966 -> Prop) : (term51 _132966 s) = (term51 _132966 s).
Proof. exact (eq_refl (term51 _132966 s)). Qed.
Lemma lem7123013 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : x = a) : (term52 _132966 s x) = (term52 _132966 s a).
Proof. exact (MK_COMB (@lem7123012 _132966 s) (@lem7122983 _132966 x a h1)). Qed.
Lemma lem7123014 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : (term52 _132966 s a) = (s a).
Proof. exact (eq_refl (term52 _132966 s a)). Qed.
Lemma lem7123015 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term53 _132966 s x) = (term53 _132966 s x).
Proof. exact (eq_refl (term53 _132966 s x)). Qed.
Lemma lem7123016 {_132966 : Type'} (x : _132966) (s : _132966 -> Prop) (a : _132966) : ((term52 _132966 s x) = (term52 _132966 s a)) = ((term52 _132966 s x) = (s a)).
Proof. exact (MK_COMB (@lem7123015 _132966 s x) (@lem7123014 _132966 s a)). Qed.
Lemma lem7123017 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term52 _132966 s x) = (s x).
Proof. exact (eq_refl (term52 _132966 s x)). Qed.
Lemma lem7123018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7123019 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term53 _132966 s x) = (term54 _132966 s x).
Proof. exact (MK_COMB (@lem7123018) (@lem7123017 _132966 s x)). Qed.
Lemma lem7123020 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem7123021 {_132966 : Type'} (x : _132966) (s : _132966 -> Prop) (a : _132966) : ((term52 _132966 s x) = (s a)) = ((s x) = (s a)).
Proof. exact (MK_COMB (@lem7123019 _132966 s x) (@lem7123020 _132966 s a)). Qed.
Lemma lem7123022 {_132966 : Type'} (x : _132966) (s : _132966 -> Prop) (a : _132966) : ((term52 _132966 s x) = (term52 _132966 s a)) = ((s x) = (s a)).
Proof. exact (TRANS (@lem7123016 _132966 x s a) (@lem7123021 _132966 x s a)). Qed.
Lemma lem7123023 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : x = a) : (s x) = (s a).
Proof. exact (EQ_MP (@lem7123022 _132966 x s a) (@lem7123013 _132966 s x a h1)). Qed.
Lemma lem7123040 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : s x.
Proof. exact (proj1 (@lem7122917 _132966 a s x h1)). Qed.
Lemma lem7123041 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : term55 _132966 s x.
Proof. exact (fun h0 : term6 _132966 s x => @lem7123040 _132966 a s x h1). Qed.
Lemma lem7123043 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7123044 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term55 _132966 s x) = (s x).
Proof. exact (@lem7123043 (s x)). Qed.
Lemma lem7123045 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : s x.
Proof. exact (EQ_MP (@lem7123044 _132966 s x) (@lem7123041 _132966 a s x h1)). Qed.
Lemma lem7123048 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7123050 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term6 _132966 s x) = (term57 _132966 s x).
Proof. exact (@lem7123048 (s x)). Qed.
Lemma lem7123053 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : term57 _132966 s x.
Proof. exact (EQ_MP (@lem7123050 _132966 s x) (@lem7122967 _132966 a s x h1)). Qed.
Lemma lem7123056 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : False.
Proof. exact (@lem7123053 _132966 a s x h1 (@lem7123045 _132966 a s x h1)). Qed.
Lemma lem7123057 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : term58.
Proof. exact (fun h0 : ~ False => @lem7123056 _132966 a s x h1). Qed.
Lemma lem7123059 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7123060 : term58 = False.
Proof. exact (@lem7123059 False). Qed.
Lemma lem7123061 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term50 _132966 a s x) : False.
Proof. exact (EQ_MP (@lem7123060) (@lem7123057 _132966 a s x h1)). Qed.
Lemma lem7123063 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term46 _132966 a s x) : s x.
Proof. exact (proj2 (@lem7122915 _132966 a s x h1)). Qed.
Lemma lem7123064 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term46 _132966 a s x) : term55 _132966 s x.
Proof. exact (fun h0 : term6 _132966 s x => @lem7123063 _132966 a s x h1). Qed.
Lemma lem7123066 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7123067 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term55 _132966 s x) = (s x).
Proof. exact (@lem7123066 (s x)). Qed.
Lemma lem7123068 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term46 _132966 a s x) : s x.
Proof. exact (EQ_MP (@lem7123067 _132966 s x) (@lem7123064 _132966 a s x h1)). Qed.
Lemma lem7123071 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7123073 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) : (term6 _132966 s x) = (term57 _132966 s x).
Proof. exact (@lem7123071 (s x)). Qed.
Lemma lem7123076 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) : term57 _132966 s x.
Proof. exact (EQ_MP (@lem7123073 _132966 s x) (@lem7122977 _132966 s x h1)). Qed.
Lemma lem7123079 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : False.
Proof. exact (@lem7123076 _132966 s x h1 (@lem7123068 _132966 a s x h2)). Qed.
Lemma lem7123080 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : term58.
Proof. exact (fun h0 : ~ False => @lem7123079 _132966 a s x h1 h2). Qed.
Lemma lem7123082 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7123083 : term58 = False.
Proof. exact (@lem7123082 False). Qed.
Lemma lem7123084 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : False.
Proof. exact (EQ_MP (@lem7123083) (@lem7123080 _132966 a s x h1 h2)). Qed.
Lemma lem7123086 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term46 _132966 a s x) (h2 : x = a) : s a.
Proof. exact (EQ_MP (@lem7123023 _132966 s x a h2) (@lem7122981 _132966 a s x h1)). Qed.
Lemma lem7123087 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term46 _132966 a s x) (h2 : x = a) : term55 _132966 s a.
Proof. exact (fun h0 : term6 _132966 s a => @lem7123086 _132966 s x a h1 h2). Qed.
Lemma lem7123089 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7123090 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : (term55 _132966 s a) = (s a).
Proof. exact (@lem7123089 (s a)). Qed.
Lemma lem7123091 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term46 _132966 a s x) (h2 : x = a) : s a.
Proof. exact (EQ_MP (@lem7123090 _132966 s a) (@lem7123087 _132966 s x a h1 h2)). Qed.
Lemma lem7123094 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7123096 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : (term6 _132966 s a) = (term57 _132966 s a).
Proof. exact (@lem7123094 (s a)). Qed.
Lemma lem7123099 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : term57 _132966 s a.
Proof. exact (EQ_MP (@lem7123096 _132966 s a) (@lem7123011 _132966 s a h1)). Qed.
Lemma lem7123102 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (@lem7123099 _132966 s a h1 (@lem7123091 _132966 s x a h2 h3)). Qed.
Lemma lem7123103 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : term58.
Proof. exact (fun h0 : ~ False => @lem7123102 _132966 s x a h1 h2 h3). Qed.
Lemma lem7123105 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7123106 : term58 = False.
Proof. exact (@lem7123105 False). Qed.
Lemma lem7123107 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7123106) (@lem7123103 _132966 s x a h1 h2 h3)). Qed.
Lemma lem7123108 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : (term6 _132966 s a) = False.
Proof. exact (prop_ext (fun h4 : term6 _132966 s a => @lem7123107 _132966 s x a h1 h2 h3) (fun h4 : False => @lem7123011 _132966 s a h1)). Qed.
Lemma lem7123110 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7123108 _132966 s x a h1 h2 h3) (@lem7123011 _132966 s a h1)). Qed.
Lemma lem7123111 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem7123110 _132966 s x a h1 h2 h3) (fun h4 : False => @lem7122983 _132966 x a h3)). Qed.
Lemma lem7123112 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7123111 _132966 s x a h1 h2 h3) (@lem7122983 _132966 x a h3)). Qed.
Lemma lem7123113 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : (term6 _132966 s a) = False.
Proof. exact (prop_ext (fun h4 : term6 _132966 s a => @lem7123112 _132966 s x a h1 h2 h3) (fun h4 : False => @lem7122979 _132966 s a h1)). Qed.
Lemma lem7123114 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7123113 _132966 s x a h1 h2 h3) (@lem7122979 _132966 s a h1)). Qed.
Lemma lem7123115 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : (term6 _132966 s x) = False.
Proof. exact (prop_ext (fun h3 : term6 _132966 s x => @lem7123084 _132966 a s x h1 h2) (fun h3 : False => @lem7122977 _132966 s x h1)). Qed.
Lemma lem7123116 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : False.
Proof. exact (EQ_MP (@lem7123115 _132966 a s x h1 h2) (@lem7122977 _132966 s x h1)). Qed.
Lemma lem7123117 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem7123114 _132966 s x a h1 h2 h3) (fun h4 : False => @lem7122963 _132966 x a h3)). Qed.
Lemma lem7123118 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7123117 _132966 s x a h1 h2 h3) (@lem7122963 _132966 x a h3)). Qed.
Lemma lem7123119 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : (term6 _132966 s a) = False.
Proof. exact (prop_ext (fun h4 : term6 _132966 s a => @lem7123118 _132966 s x a h1 h2 h3) (fun h4 : False => @lem7122955 _132966 s a h1)). Qed.
Lemma lem7123120 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7123119 _132966 s x a h1 h2 h3) (@lem7122955 _132966 s a h1)). Qed.
Lemma lem7123121 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : (term6 _132966 s x) = False.
Proof. exact (prop_ext (fun h3 : term6 _132966 s x => @lem7123116 _132966 a s x h1 h2) (fun h3 : False => @lem7122951 _132966 s x h1)). Qed.
Lemma lem7123122 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : False.
Proof. exact (EQ_MP (@lem7123121 _132966 a s x h1 h2) (@lem7122951 _132966 s x h1)). Qed.
Lemma lem7123123 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem7123120 _132966 s x a h1 h2 h3) (fun h4 : False => @lem7122963 _132966 x a h3)). Qed.
Lemma lem7123124 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7123123 _132966 s x a h1 h2 h3) (@lem7122963 _132966 x a h3)). Qed.
Lemma lem7123125 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : (term6 _132966 s a) = False.
Proof. exact (prop_ext (fun h4 : term6 _132966 s a => @lem7123124 _132966 s x a h1 h2 h3) (fun h4 : False => @lem7122955 _132966 s a h1)). Qed.
Lemma lem7123126 {_132966 : Type'} (s : _132966 -> Prop) (x : _132966) (a : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem7123125 _132966 s x a h1 h2 h3) (@lem7122955 _132966 s a h1)). Qed.
Lemma lem7123127 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : (term6 _132966 s x) = False.
Proof. exact (prop_ext (fun h3 : term6 _132966 s x => @lem7123122 _132966 a s x h1 h2) (fun h3 : False => @lem7122951 _132966 s x h1)). Qed.
Lemma lem7123128 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s x) (h2 : term46 _132966 a s x) : False.
Proof. exact (EQ_MP (@lem7123127 _132966 a s x h1 h2) (@lem7122951 _132966 s x h1)). Qed.
Lemma lem7123129 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s a) (h2 : term46 _132966 a s x) : False.
Proof. exact (or_elim (@lem7122921 _132966 a s x h2) (fun h0 : term6 _132966 s x => @lem7123128 _132966 a s x h0 h2) (fun h0 : x = a => @lem7123126 _132966 s x a h1 h2 h0)). Qed.
Lemma lem7123130 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s a) (h2 : term37 _132966 a s x) : False.
Proof. exact (or_elim (@lem7122913 _132966 a s x h2) (fun h0 : term50 _132966 a s x => @lem7123061 _132966 a s x h0) (fun h0 : term46 _132966 a s x => @lem7123129 _132966 a s x h1 h0)). Qed.
Lemma lem7123131 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s a) (h2 : term37 _132966 a s x) : (term6 _132966 s a) = False.
Proof. exact (prop_ext (fun h3 : term6 _132966 s a => @lem7123130 _132966 a s x h1 h2) (fun h3 : False => @lem7122869 _132966 s a h1)). Qed.
Lemma lem7123132 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s a) (h2 : term37 _132966 a s x) : False.
Proof. exact (EQ_MP (@lem7123131 _132966 a s x h1 h2) (@lem7122869 _132966 s a h1)). Qed.
Lemma lem7123133 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s a) (h2 : term37 _132966 a s x) : (term6 _132966 s a) = False.
Proof. exact (prop_ext (fun h3 : term6 _132966 s a => @lem7123132 _132966 a s x h1 h2) (fun h3 : False => @lem7122831 _132966 s a h1)). Qed.
Lemma lem7123134 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s a) (h2 : term37 _132966 a s x) : False.
Proof. exact (EQ_MP (@lem7123133 _132966 a s x h1 h2) (@lem7122831 _132966 s a h1)). Qed.
Lemma lem7123135 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s a) (h2 : term37 _132966 a s x) : (term37 _132966 a s x) = False.
Proof. exact (prop_ext (fun h3 : term37 _132966 a s x => @lem7123134 _132966 a s x h1 h2) (fun h3 : False => @lem7122825 _132966 a s x h2)). Qed.
Lemma lem7123136 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (x : _132966) (h1 : term6 _132966 s a) (h2 : term37 _132966 a s x) : False.
Proof. exact (EQ_MP (@lem7123135 _132966 a s x h1 h2) (@lem7122825 _132966 a s x h2)). Qed.
Lemma lem7123137 {_132966 : Type'} (x : _132966) (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : term36 _132966 a s x.
Proof. exact (fun h0 : term37 _132966 a s x => @lem7123136 _132966 a s x h1 h0). Qed.
Lemma lem7123138 {_132966 : Type'} (x : _132966) (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : (term13 _132966 s x a) = (s x).
Proof. exact (EQ_MP (@lem7122824 _132966 a s x) (@lem7123137 _132966 x s a h1)). Qed.
Lemma lem7123143 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) (h1 : term6 _132966 s a) : term18 _132966 a s.
Proof. exact (fun x : _132966 => @lem7123138 _132966 x s a h1). Qed.
Lemma lem7123144 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term19 _132966 a s.
Proof. exact (fun h0 : term6 _132966 s a => @lem7123143 _132966 s a h0). Qed.
Lemma lem7123149 {_132966 : Type'} (s : _132966 -> Prop) : term31 _132966 s.
Proof. exact (fun a : _132966 => @lem7123144 _132966 a s). Qed.
Lemma lem7123154 {_132966 : Type'} : term35 _132966.
Proof. exact (fun s : _132966 -> Prop => @lem7123149 _132966 s). Qed.
Lemma lem7123155 {_132966 : Type'} : term34 _132966.
Proof. exact (EQ_MP (@lem7122819 _132966) (@lem7123154 _132966)). Qed.
Lemma lem7123156 {_132966 : Type'} (s : _132966 -> Prop) : term59 _132966 s.
Proof. exact (@lem7123155 _132966 s). Qed.
Lemma lem7123157 {_132966 : Type'} (s : _132966 -> Prop) : (term59 _132966 s) = (term30 _132966 s).
Proof. exact (eq_refl (term59 _132966 s)). Qed.
Lemma lem7123158 {_132966 : Type'} (s : _132966 -> Prop) : term30 _132966 s.
Proof. exact (EQ_MP (@lem7123157 _132966 s) (@lem7123156 _132966 s)). Qed.
Lemma lem7123159 {_132966 : Type'} (s : _132966 -> Prop) (a : _132966) : term60 _132966 s a.
Proof. exact (@lem7123158 _132966 s a). Qed.
Lemma lem7123160 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : (term60 _132966 s a) = (term21 _132966 a s).
Proof. exact (eq_refl (term60 _132966 s a)). Qed.
Lemma lem7123161 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term21 _132966 a s.
Proof. exact (EQ_MP (@lem7123160 _132966 a s) (@lem7123159 _132966 s a)). Qed.
Lemma lem7123163 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term21 _132966 a s.
Proof. exact (@lem7122726 _132966 a s (@lem7123161 _132966 a s)). Qed.
Lemma lem7123164 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term22 _132966 a s) : False.
Proof. exact (@lem7123163 _132966 a s (@lem7122710 _132966 a s h1)). Qed.
Lemma lem7123165 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term22 _132966 a s) : (term22 _132966 a s) = False.
Proof. exact (prop_ext (fun h2 : term22 _132966 a s => @lem7123164 _132966 a s h1) (fun h2 : False => @lem7122710 _132966 a s h1)). Qed.
Lemma lem7123166 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term22 _132966 a s) : False.
Proof. exact (EQ_MP (@lem7123165 _132966 a s h1) (@lem7122710 _132966 a s h1)). Qed.
Lemma lem7123167 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term21 _132966 a s.
Proof. exact (fun h0 : term22 _132966 a s => @lem7123166 _132966 a s h0). Qed.
Lemma lem7123168 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term19 _132966 a s.
Proof. exact (EQ_MP (@lem7122709 _132966 a s) (@lem7123167 _132966 a s)). Qed.
Lemma lem7123169 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term4 _132966 a s.
Proof. exact (EQ_MP (@lem7122705 _132966 a s) (@lem7123168 _132966 a s)). Qed.
Lemma lem7123170 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term3 _132966 a s.
Proof. exact (EQ_MP (@lem7122650 _132966 a s) (@lem7123169 _132966 a s)). Qed.
Lemma lem7123171 {_133013 : Type'} (s : _133013 -> Prop) (h1 : @FINITE _133013 s) : @FINITE _133013 s.
Proof. exact (h1). Qed.
Lemma lem7123172 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term61 _476 _475 _474 _477) = (term62 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem7123173 {_133013 : Type'} (_474 : real) (_475 : Prop) (s : _133013 -> Prop) (a : _133013) (f : _133013 -> real) (_477 : real) : (term63 _133013 s a f _475 _474 _477) = (term64 _133013 _474 _475 s a f _477).
Proof. exact (@lem7123172 _474 _475 (term65 _133013 s a f) _477). Qed.
Lemma lem7123174 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : (term66 _133013 a s f) = (term67 _133013 a s f).
Proof. exact (@lem7123173 _133013 (term68 _133013 s f a) (@IN _133013 a s) s a f (@sum _133013 s f)). Qed.
Lemma lem7123175 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : (term69 _133013 a s f) = ((term70 _133013 s a f) = (@sum _133013 s f)).
Proof. exact (eq_refl (term69 _133013 a s f)). Qed.
Lemma lem7123176 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) : (term2 _133013 a s) = (term2 _133013 a s).
Proof. exact (eq_refl (term2 _133013 a s)). Qed.
Lemma lem7123177 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : (term71 _133013 a s f) = (term72 _133013 a s f).
Proof. exact (MK_COMB (@lem7123176 _133013 a s) (@lem7123175 _133013 a s f)). Qed.
Lemma lem7123178 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) (a : _133013) : (term73 _133013 s f a) = ((term70 _133013 s a f) = (term68 _133013 s f a)).
Proof. exact (eq_refl (term73 _133013 s f a)). Qed.
Lemma lem7123179 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) : (term74 _133013 a s) = (term74 _133013 a s).
Proof. exact (eq_refl (term74 _133013 a s)). Qed.
Lemma lem7123180 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) (a : _133013) : (term75 _133013 s f a) = (term76 _133013 s f a).
Proof. exact (MK_COMB (@lem7123179 _133013 a s) (@lem7123178 _133013 s f a)). Qed.
Lemma lem7123181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7123182 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) (a : _133013) : (term77 _133013 s f a) = (term78 _133013 s f a).
Proof. exact (MK_COMB (@lem7123181) (@lem7123180 _133013 s f a)). Qed.
Lemma lem7123183 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : (term67 _133013 a s f) = (term79 _133013 a s f).
Proof. exact (MK_COMB (@lem7123182 _133013 s f a) (@lem7123177 _133013 a s f)). Qed.
Lemma lem7123184 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : (term66 _133013 a s f) = ((term70 _133013 s a f) = (term80 _133013 a s f)).
Proof. exact (eq_refl (term66 _133013 a s f)). Qed.
Lemma lem7123185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7123186 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : (term81 _133013 a s f) = (term82 _133013 a s f).
Proof. exact (MK_COMB (@lem7123185) (@lem7123184 _133013 a s f)). Qed.
Lemma lem7123187 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : ((term66 _133013 a s f) = (term67 _133013 a s f)) = (((term70 _133013 s a f) = (term80 _133013 a s f)) = (term79 _133013 a s f)).
Proof. exact (MK_COMB (@lem7123186 _133013 a s f) (@lem7123183 _133013 a s f)). Qed.
Lemma lem7123188 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : ((term70 _133013 s a f) = (term80 _133013 a s f)) = (term79 _133013 a s f).
Proof. exact (EQ_MP (@lem7123187 _133013 a s f) (@lem7123174 _133013 a s f)). Qed.
Lemma lem7123189 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : (term79 _133013 a s f) = ((term70 _133013 s a f) = (term80 _133013 a s f)).
Proof. exact (SYM (@lem7123188 _133013 a s f)). Qed.
Lemma lem7123190 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : @IN _133013 a s) : @IN _133013 a s.
Proof. exact (h1). Qed.
Lemma lem7123207 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : term5 _133013 a s.
Proof. exact (h1). Qed.
Lemma lem7123224 {_132960 : Type'} (f : _132960 -> real) : term83 _132960 f.
Proof. exact (@lem7122619 _132960 f). Qed.
Lemma lem7123225 {_132960 : Type'} (f : _132960 -> real) : (term83 _132960 f) = (term84 _132960 f).
Proof. exact (eq_refl (term83 _132960 f)). Qed.
Lemma lem7123226 {_132960 : Type'} (f : _132960 -> real) : term84 _132960 f.
Proof. exact (EQ_MP (@lem7123225 _132960 f) (@lem7123224 _132960 f)). Qed.
Lemma lem7123227 {_132960 : Type'} (f : _132960 -> real) (s : _132960 -> Prop) : term85 _132960 f s.
Proof. exact (@lem7123226 _132960 f s). Qed.
Lemma lem7123228 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : (term85 _132960 f s) = (term86 _132960 s f).
Proof. exact (eq_refl (term85 _132960 f s)). Qed.
Lemma lem7123229 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : term86 _132960 s f.
Proof. exact (EQ_MP (@lem7123228 _132960 s f) (@lem7123227 _132960 f s)). Qed.
Lemma lem7123230 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : term87 _132960 s f a.
Proof. exact (@lem7123229 _132960 s f a). Qed.
Lemma lem7123231 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : (term87 _132960 s f a) = (term88 _132960 s f a).
Proof. exact (eq_refl (term87 _132960 s f a)). Qed.
Lemma lem7123232 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : term88 _132960 s f a.
Proof. exact (EQ_MP (@lem7123231 _132960 s f a) (@lem7123230 _132960 s f a)). Qed.
Lemma lem7123233 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term89 _132960 a s) : term89 _132960 a s.
Proof. exact (h1). Qed.
Lemma lem7123234 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (h1 : term89 _132960 a s) : (term70 _132960 s a f) = (term68 _132960 s f a).
Proof. exact (@lem7123232 _132960 s f a (@lem7123233 _132960 a s h1)). Qed.
Lemma lem7123247 {_133013 : Type'} (s : _133013 -> Prop) : (@FINITE _133013 s) = ((@FINITE _133013 s) = True).
Proof. exact (@lem7 (@FINITE _133013 s)). Qed.
Lemma lem7123249 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) : (@IN _133013 a s) = ((@IN _133013 a s) = True).
Proof. exact (@lem7 (@IN _133013 a s)). Qed.
Lemma lem7123254 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : term88 _132960 s f a.
Proof. exact (fun h0 : term89 _132960 a s => @lem7123234 _132960 f a s h0). Qed.
Lemma lem7123255 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) (a : _133013) : term88 _133013 s f a.
Proof. exact (@lem7123254 _133013 s f a). Qed.
Lemma lem7123259 {_133013 : Type'} (s : _133013 -> Prop) (h1 : @FINITE _133013 s) : (@FINITE _133013 s) = True.
Proof. exact (EQ_MP (@lem7123247 _133013 s) (@lem7123171 _133013 s h1)). Qed.
Lemma lem7123260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7123261 {_133013 : Type'} (s : _133013 -> Prop) (h1 : @FINITE _133013 s) : (term90 _133013 s) = (and True).
Proof. exact (MK_COMB (@lem7123260) (@lem7123259 _133013 s h1)). Qed.
Lemma lem7123263 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : @IN _133013 a s) : (@IN _133013 a s) = True.
Proof. exact (EQ_MP (@lem7123249 _133013 a s) (@lem7123190 _133013 a s h1)). Qed.
Lemma lem7123264 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : (term89 _133013 a s) = (True /\ True).
Proof. exact (MK_COMB (@lem7123261 _133013 s h1) (@lem7123263 _133013 a s h2)). Qed.
Lemma lem7123266 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7123267 : (True /\ True) = True.
Proof. exact (@lem7123266 True). Qed.
Lemma lem7123268 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : (term89 _133013 a s) = True.
Proof. exact (TRANS (@lem7123264 _133013 a s h1 h2) (@lem7123267)). Qed.
Lemma lem7123269 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : True = (term89 _133013 a s).
Proof. exact (SYM (@lem7123268 _133013 a s h1 h2)). Qed.
Lemma lem7123270 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : term89 _133013 a s.
Proof. exact (EQ_MP (@lem7123269 _133013 a s h1 h2) (@lem0)). Qed.
Lemma lem7123271 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : (term70 _133013 s a f) = (term68 _133013 s f a).
Proof. exact (@lem7123255 _133013 s f a (@lem7123270 _133013 a s h1 h2)). Qed.
Lemma lem7123272 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7123273 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : (term91 _133013 s a f) = (term92 _133013 s f a).
Proof. exact (MK_COMB (@lem7123272) (@lem7123271 _133013 f a s h1 h2)). Qed.
Lemma lem7123274 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) (a : _133013) : (term68 _133013 s f a) = (term68 _133013 s f a).
Proof. exact (eq_refl (term68 _133013 s f a)). Qed.
Lemma lem7123275 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : ((term70 _133013 s a f) = (term68 _133013 s f a)) = ((term68 _133013 s f a) = (term68 _133013 s f a)).
Proof. exact (MK_COMB (@lem7123273 _133013 f a s h1 h2) (@lem7123274 _133013 s f a)). Qed.
Lemma lem7123277 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7123278 (x : real) : (x = x) = True.
Proof. exact (@lem7123277 real x). Qed.
Lemma lem7123279 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) (a : _133013) : ((term68 _133013 s f a) = (term68 _133013 s f a)) = True.
Proof. exact (@lem7123278 (term68 _133013 s f a)). Qed.
Lemma lem7123280 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : ((term70 _133013 s a f) = (term68 _133013 s f a)) = True.
Proof. exact (TRANS (@lem7123275 _133013 f a s h1 h2) (@lem7123279 _133013 s f a)). Qed.
Lemma lem7123281 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : True = ((term70 _133013 s a f) = (term68 _133013 s f a)).
Proof. exact (SYM (@lem7123280 _133013 f a s h1 h2)). Qed.
Lemma lem7123299 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term5 _132966 a s) : term5 _132966 a s.
Proof. exact (h1). Qed.
Lemma lem7123300 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) (h1 : term5 _132966 a s) : (@DELETE _132966 s a) = s.
Proof. exact (@lem7123170 _132966 a s (@lem7123299 _132966 a s h1)). Qed.
Lemma lem7123308 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) : term93 _133013 a s.
Proof. exact (@lem82 (@IN _133013 a s)). Qed.
Lemma lem7123330 {_132966 : Type'} (a : _132966) (s : _132966 -> Prop) : term3 _132966 a s.
Proof. exact (fun h0 : term5 _132966 a s => @lem7123300 _132966 a s h0). Qed.
Lemma lem7123331 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) : term3 _133013 a s.
Proof. exact (@lem7123330 _133013 a s). Qed.
Lemma lem7123333 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (@IN _133013 a s) = False.
Proof. exact (@lem7123308 _133013 a s (@lem7123207 _133013 a s h1)). Qed.
Lemma lem7123334 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7123335 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (term5 _133013 a s) = (~ False).
Proof. exact (MK_COMB (@lem7123334) (@lem7123333 _133013 a s h1)). Qed.
Lemma lem7123337 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7123338 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (term5 _133013 a s) = True.
Proof. exact (TRANS (@lem7123335 _133013 a s h1) (@lem7123337)). Qed.
Lemma lem7123339 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : True = (term5 _133013 a s).
Proof. exact (SYM (@lem7123338 _133013 a s h1)). Qed.
Lemma lem7123340 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : term5 _133013 a s.
Proof. exact (EQ_MP (@lem7123339 _133013 a s h1) (@lem0)). Qed.
Lemma lem7123341 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (@DELETE _133013 s a) = s.
Proof. exact (@lem7123331 _133013 a s (@lem7123340 _133013 a s h1)). Qed.
Lemma lem7123342 {_133013 : Type'} : (@sum _133013) = (@sum _133013).
Proof. exact (eq_refl (@sum _133013)). Qed.
Lemma lem7123343 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (term94 _133013 s a) = (@sum _133013 s).
Proof. exact (MK_COMB (@lem7123342 _133013) (@lem7123341 _133013 a s h1)). Qed.
Lemma lem7123344 {_133013 : Type'} (f : _133013 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7123345 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (term70 _133013 s a f) = (@sum _133013 s f).
Proof. exact (MK_COMB (@lem7123343 _133013 a s h1) (@lem7123344 _133013 f)). Qed.
Lemma lem7123346 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7123347 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (term91 _133013 s a f) = (term95 _133013 s f).
Proof. exact (MK_COMB (@lem7123346) (@lem7123345 _133013 f a s h1)). Qed.
Lemma lem7123348 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) : (@sum _133013 s f) = (@sum _133013 s f).
Proof. exact (eq_refl (@sum _133013 s f)). Qed.
Lemma lem7123349 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : ((term70 _133013 s a f) = (@sum _133013 s f)) = ((@sum _133013 s f) = (@sum _133013 s f)).
Proof. exact (MK_COMB (@lem7123347 _133013 f a s h1) (@lem7123348 _133013 s f)). Qed.
Lemma lem7123351 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7123352 (x : real) : (x = x) = True.
Proof. exact (@lem7123351 real x). Qed.
Lemma lem7123353 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) : ((@sum _133013 s f) = (@sum _133013 s f)) = True.
Proof. exact (@lem7123352 (@sum _133013 s f)). Qed.
Lemma lem7123354 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : ((term70 _133013 s a f) = (@sum _133013 s f)) = True.
Proof. exact (TRANS (@lem7123349 _133013 f a s h1) (@lem7123353 _133013 s f)). Qed.
Lemma lem7123355 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : True = ((term70 _133013 s a f) = (@sum _133013 s f)).
Proof. exact (SYM (@lem7123354 _133013 f a s h1)). Qed.
Lemma lem7123357 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (term70 _133013 s a f) = (@sum _133013 s f).
Proof. exact (EQ_MP (@lem7123355 _133013 f a s h1) (@lem0)). Qed.
Lemma lem7123358 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (term5 _133013 a s) = ((term70 _133013 s a f) = (@sum _133013 s f)).
Proof. exact (prop_ext (fun h2 : term5 _133013 a s => @lem7123357 _133013 f a s h1) (fun h2 : (term70 _133013 s a f) = (@sum _133013 s f) => @lem7123207 _133013 a s h1)). Qed.
Lemma lem7123359 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : term5 _133013 a s) : (term70 _133013 s a f) = (@sum _133013 s f).
Proof. exact (EQ_MP (@lem7123358 _133013 f a s h1) (@lem7123207 _133013 a s h1)). Qed.
Lemma lem7123360 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : term72 _133013 a s f.
Proof. exact (fun h0 : term5 _133013 a s => @lem7123359 _133013 f a s h0). Qed.
Lemma lem7123361 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : (term70 _133013 s a f) = (term68 _133013 s f a).
Proof. exact (EQ_MP (@lem7123281 _133013 f a s h1 h2) (@lem0)). Qed.
Lemma lem7123362 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : (@IN _133013 a s) = ((term70 _133013 s a f) = (term68 _133013 s f a)).
Proof. exact (prop_ext (fun h3 : @IN _133013 a s => @lem7123361 _133013 f a s h1 h2) (fun h3 : (term70 _133013 s a f) = (term68 _133013 s f a) => @lem7123190 _133013 a s h2)). Qed.
Lemma lem7123363 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) (h2 : @IN _133013 a s) : (term70 _133013 s a f) = (term68 _133013 s f a).
Proof. exact (EQ_MP (@lem7123362 _133013 f a s h1 h2) (@lem7123190 _133013 a s h2)). Qed.
Lemma lem7123364 {_133013 : Type'} (f : _133013 -> real) (a : _133013) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) : term76 _133013 s f a.
Proof. exact (fun h0 : @IN _133013 a s => @lem7123363 _133013 f a s h1 h0). Qed.
Lemma lem7123365 {_133013 : Type'} (a : _133013) (f : _133013 -> real) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) : term79 _133013 a s f.
Proof. exact (conj (@lem7123364 _133013 f a s h1) (@lem7123360 _133013 a s f)). Qed.
Lemma lem7123366 {_133013 : Type'} (a : _133013) (f : _133013 -> real) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) : (term70 _133013 s a f) = (term80 _133013 a s f).
Proof. exact (EQ_MP (@lem7123189 _133013 a s f) (@lem7123365 _133013 a f s h1)). Qed.
Lemma lem7123367 {_133013 : Type'} (a : _133013) (f : _133013 -> real) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) : (@FINITE _133013 s) = ((term70 _133013 s a f) = (term80 _133013 a s f)).
Proof. exact (prop_ext (fun h2 : @FINITE _133013 s => @lem7123366 _133013 a f s h1) (fun h2 : (term70 _133013 s a f) = (term80 _133013 a s f) => @lem7123171 _133013 s h1)). Qed.
Lemma lem7123368 {_133013 : Type'} (a : _133013) (f : _133013 -> real) (s : _133013 -> Prop) (h1 : @FINITE _133013 s) : (term70 _133013 s a f) = (term80 _133013 a s f).
Proof. exact (EQ_MP (@lem7123367 _133013 a f s h1) (@lem7123171 _133013 s h1)). Qed.
Lemma lem7123369 {_133013 : Type'} (a : _133013) (s : _133013 -> Prop) (f : _133013 -> real) : term96 _133013 a s f.
Proof. exact (fun h0 : @FINITE _133013 s => @lem7123368 _133013 a f s h0). Qed.
Lemma lem7123374 {_133013 : Type'} (s : _133013 -> Prop) (f : _133013 -> real) : term97 _133013 s f.
Proof. exact (fun a : _133013 => @lem7123369 _133013 a s f). Qed.
Lemma lem7123379 {_133013 : Type'} (f : _133013 -> real) : term98 _133013 f.
Proof. exact (fun s : _133013 -> Prop => @lem7123374 _133013 s f). Qed.
Lemma lem7123384 {_133013 : Type'} : term99 _133013.
Proof. exact (fun f : _133013 -> real => @lem7123379 _133013 f). Qed.
