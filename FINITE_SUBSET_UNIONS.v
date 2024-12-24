Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUBSET_UNIONS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_spec.
Require Import IN_UNIONS_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import RIGHT_IMP_EXISTS_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import SUBSET_spec.
Require Import UNIONS_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Lemma lem3754707 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem3754708 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3754709 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem3754708 A P) (@lem3754707 A P)). Qed.
Lemma lem3754710 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem3754709 A P Q). Qed.
Lemma lem3754711 {A : Type'} (P : A -> Prop) (Q : Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem3754713 {A B : Type'} (P : type1413 A B) : term5 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem3754714 {A B : Type'} (P : type1413 A B) : (term5 A B P) = ((term6 A B P) = (term7 A B P)).
Proof. exact (eq_refl (term5 A B P)). Qed.
Lemma lem3754716 {A : Type'} (P : Prop) : term8 A P.
Proof. exact (@lem12262 A P). Qed.
Lemma lem3754717 {A : Type'} (P : Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem3754718 {A : Type'} (P : Prop) : term9 A P.
Proof. exact (EQ_MP (@lem3754717 A P) (@lem3754716 A P)). Qed.
Lemma lem3754719 {A : Type'} (P : Prop) (Q : A -> Prop) : term10 A P Q.
Proof. exact (@lem3754718 A P Q). Qed.
Lemma lem3754720 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = ((term11 A P Q) = (term12 A P Q)).
Proof. exact (eq_refl (term10 A P Q)). Qed.
Lemma lem3754722 {A : Type'} (s : type686 A) : term13 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3754723 {A : Type'} (s : type686 A) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem3754724 {A : Type'} (s : type686 A) : term14 A s.
Proof. exact (EQ_MP (@lem3754723 A s) (@lem3754722 A s)). Qed.
Lemma lem3754725 {A : Type'} (s : type686 A) (x : A) : term15 A s x.
Proof. exact (@lem3754724 A s x). Qed.
Lemma lem3754726 {A : Type'} (s : type686 A) (x : A) : (term15 A s x) = ((term16 A x s) = (term17 A s x)).
Proof. exact (eq_refl (term15 A s x)). Qed.
Lemma lem3754728 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem3754729 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem3754730 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (EQ_MP (@lem3754729 A s) (@lem3754728 A s)). Qed.
Lemma lem3754731 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term20 A s t.
Proof. exact (@lem3754730 A s t). Qed.
Lemma lem3754732 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = ((@SUBSET A s t) = (term21 A s t)).
Proof. exact (eq_refl (term20 A s t)). Qed.
Lemma lem3754734 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term22 A s f) : term22 A s f.
Proof. exact (h1). Qed.
Lemma lem3754735 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A s f) : term23 A s f.
Proof. exact (h1). Qed.
Lemma lem3754736 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3754738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3754732 A s t) (@lem3754731 A s t)). Qed.
Lemma lem3754739 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (@lem3754738 A s t). Qed.
Lemma lem3754740 {A : Type'} (s : A -> Prop) (f : type686 A) : (term23 A s f) = (term24 A s f).
Proof. exact (@lem3754739 A s (@UNIONS A f)). Qed.
Lemma lem3754741 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term23 A s f) : term24 A s f.
Proof. exact (EQ_MP (@lem3754740 A s f) (@lem3754735 A s f h1)). Qed.
Lemma lem3754743 {A : Type'} (s : type686 A) (x : A) : (term16 A x s) = (term17 A s x).
Proof. exact (EQ_MP (@lem3754726 A s x) (@lem3754725 A s x)). Qed.
Lemma lem3754744 {A : Type'} (s : type686 A) (x : A) : (term16 A x s) = (term17 A s x).
Proof. exact (@lem3754743 A s x). Qed.
Lemma lem3754745 {A : Type'} (f : type686 A) (x : A) : (term16 A x f) = (term17 A f x).
Proof. exact (@lem3754744 A f x). Qed.
Lemma lem3754746 {A : Type'} (x : A) (s : A -> Prop) : (term25 A x s) = (term25 A x s).
Proof. exact (eq_refl (term25 A x s)). Qed.
Lemma lem3754747 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term26 A s x f) = (term27 A s f x).
Proof. exact (MK_COMB (@lem3754746 A x s) (@lem3754745 A f x)). Qed.
Lemma lem3754749 {A : Type'} (P : Prop) (Q : A -> Prop) : (term11 A P Q) = (term12 A P Q).
Proof. exact (EQ_MP (@lem3754720 A P Q) (@lem3754719 A P Q)). Qed.
Lemma lem3754750 {A : Type'} (P : Prop) (Q : type686 A) : (term28 A P Q) = (term29 A P Q).
Proof. exact (@lem3754749 (A -> Prop) P Q). Qed.
Lemma lem3754751 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term30 A s f x) = (term31 A s f x).
Proof. exact (@lem3754750 A (@IN A x s) (term32 A f x)). Qed.
Lemma lem3754752 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) : (term33 A f x t) = (term34 A f x t).
Proof. exact (eq_refl (term33 A f x t)). Qed.
Lemma lem3754753 {A : Type'} (f : type686 A) (x : A) : (term35 A f x) = (term32 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3754752 A f x t)). Qed.
Lemma lem3754754 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3754755 {A : Type'} (f : type686 A) (x : A) : (term36 A f x) = (term17 A f x).
Proof. exact (MK_COMB (@lem3754754 A) (@lem3754753 A f x)). Qed.
Lemma lem3754756 {A : Type'} (x : A) (s : A -> Prop) : (term25 A x s) = (term25 A x s).
Proof. exact (eq_refl (term25 A x s)). Qed.
Lemma lem3754757 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term30 A s f x) = (term27 A s f x).
Proof. exact (MK_COMB (@lem3754756 A x s) (@lem3754755 A f x)). Qed.
Lemma lem3754758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3754759 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term37 A s f x) = (term38 A s f x).
Proof. exact (MK_COMB (@lem3754758) (@lem3754757 A s f x)). Qed.
Lemma lem3754760 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) : (term33 A f x t) = (term34 A f x t).
Proof. exact (eq_refl (term33 A f x t)). Qed.
Lemma lem3754761 {A : Type'} (x : A) (s : A -> Prop) : (term25 A x s) = (term25 A x s).
Proof. exact (eq_refl (term25 A x s)). Qed.
Lemma lem3754762 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) (t : A -> Prop) : (term39 A s f x t) = (term40 A s f x t).
Proof. exact (MK_COMB (@lem3754761 A x s) (@lem3754760 A f x t)). Qed.
Lemma lem3754763 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term41 A s f x) = (term42 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3754762 A s f x t)). Qed.
Lemma lem3754764 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3754765 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term31 A s f x) = (term43 A s f x).
Proof. exact (MK_COMB (@lem3754764 A) (@lem3754763 A s f x)). Qed.
Lemma lem3754766 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term30 A s f x) = (term31 A s f x)) = ((term27 A s f x) = (term43 A s f x)).
Proof. exact (MK_COMB (@lem3754759 A s f x) (@lem3754765 A s f x)). Qed.
Lemma lem3754767 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term27 A s f x) = (term43 A s f x).
Proof. exact (EQ_MP (@lem3754766 A s f x) (@lem3754751 A s f x)). Qed.
Lemma lem3754768 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term26 A s x f) = (term43 A s f x).
Proof. exact (TRANS (@lem3754747 A s f x) (@lem3754767 A s f x)). Qed.
Lemma lem3754769 {A : Type'} (s : A -> Prop) (f : type686 A) : (term44 A s f) = (term45 A s f).
Proof. exact (fun_ext (fun x : A => @lem3754768 A s f x)). Qed.
Lemma lem3754770 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3754771 {A : Type'} (s : A -> Prop) (f : type686 A) : (term24 A s f) = (term46 A s f).
Proof. exact (MK_COMB (@lem3754770 A) (@lem3754769 A s f)). Qed.
Lemma lem3754772 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3754773 {A : Type'} (s : A -> Prop) (f : type686 A) : (term47 A s f) = (term48 A s f).
Proof. exact (MK_COMB (@lem3754772) (@lem3754771 A s f)). Qed.
Lemma lem3754774 {A : Type'} (f : type686 A) (s : A -> Prop) : (term49 A f s) = (term49 A f s).
Proof. exact (eq_refl (term49 A f s)). Qed.
Lemma lem3754775 {A : Type'} (f : type686 A) (s : A -> Prop) : (term50 A f s) = (term51 A f s).
Proof. exact (MK_COMB (@lem3754773 A s f) (@lem3754774 A f s)). Qed.
Lemma lem3754776 {A : Type'} (f : type686 A) (s : A -> Prop) : (term51 A f s) = (term50 A f s).
Proof. exact (SYM (@lem3754775 A f s)). Qed.
Lemma lem3754780 {A B : Type'} (P : type1413 A B) : (term6 A B P) = (term7 A B P).
Proof. exact (EQ_MP (@lem3754714 A B P) (@lem3754713 A B P)). Qed.
Lemma lem3754781 {A : Type'} (P : type1364 A) : (term52 A P) = (term53 A P).
Proof. exact (@lem3754780 A (A -> Prop) P). Qed.
Lemma lem3754782 {A : Type'} (s : A -> Prop) (f : type686 A) : (term54 A s f) = (term55 A s f).
Proof. exact (@lem3754781 A (term56 A s f)). Qed.
Lemma lem3754783 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term57 A s f x) = (term42 A s f x).
Proof. exact (eq_refl (term57 A s f x)). Qed.
Lemma lem3754784 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3754785 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) (t : A -> Prop) : (term58 A s f x t) = (term59 A s f x t).
Proof. exact (MK_COMB (@lem3754783 A s f x) (@lem3754784 A t)). Qed.
Lemma lem3754786 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) (t : A -> Prop) : (term59 A s f x t) = (term40 A s f x t).
Proof. exact (eq_refl (term59 A s f x t)). Qed.
Lemma lem3754787 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) (t : A -> Prop) : (term58 A s f x t) = (term40 A s f x t).
Proof. exact (TRANS (@lem3754785 A s f x t) (@lem3754786 A s f x t)). Qed.
Lemma lem3754788 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term60 A s f x) = (term42 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3754787 A s f x t)). Qed.
Lemma lem3754789 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3754790 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term61 A s f x) = (term43 A s f x).
Proof. exact (MK_COMB (@lem3754789 A) (@lem3754788 A s f x)). Qed.
Lemma lem3754791 {A : Type'} (s : A -> Prop) (f : type686 A) : (term62 A s f) = (term45 A s f).
Proof. exact (fun_ext (fun x : A => @lem3754790 A s f x)). Qed.
Lemma lem3754792 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3754793 {A : Type'} (s : A -> Prop) (f : type686 A) : (term54 A s f) = (term46 A s f).
Proof. exact (MK_COMB (@lem3754792 A) (@lem3754791 A s f)). Qed.
Lemma lem3754794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3754795 {A : Type'} (s : A -> Prop) (f : type686 A) : (term63 A s f) = (term64 A s f).
Proof. exact (MK_COMB (@lem3754794) (@lem3754793 A s f)). Qed.
Lemma lem3754796 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term57 A s f x) = (term42 A s f x).
Proof. exact (eq_refl (term57 A s f x)). Qed.
Lemma lem3754797 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3754798 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term65 A s f t x) = (term66 A s f t x).
Proof. exact (MK_COMB (@lem3754796 A s f x) (@lem3754797 A t x)). Qed.
Lemma lem3754799 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term66 A s f t x) = (term67 A s f t x).
Proof. exact (eq_refl (term66 A s f t x)). Qed.
Lemma lem3754800 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) (x : A) : (term65 A s f t x) = (term67 A s f t x).
Proof. exact (TRANS (@lem3754798 A s f t x) (@lem3754799 A s f t x)). Qed.
Lemma lem3754801 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term68 A s f t) = (term69 A s f t).
Proof. exact (fun_ext (fun x : A => @lem3754800 A s f t x)). Qed.
Lemma lem3754802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3754803 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term70 A s f t) = (term71 A s f t).
Proof. exact (MK_COMB (@lem3754802 A) (@lem3754801 A s f t)). Qed.
Lemma lem3754804 {A : Type'} (s : A -> Prop) (f : type686 A) : (term72 A s f) = (term73 A s f).
Proof. exact (fun_ext (fun t : type1402 A => @lem3754803 A s f t)). Qed.
Lemma lem3754805 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3754806 {A : Type'} (s : A -> Prop) (f : type686 A) : (term55 A s f) = (term74 A s f).
Proof. exact (MK_COMB (@lem3754805 A) (@lem3754804 A s f)). Qed.
Lemma lem3754807 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term54 A s f) = (term55 A s f)) = ((term46 A s f) = (term74 A s f)).
Proof. exact (MK_COMB (@lem3754795 A s f) (@lem3754806 A s f)). Qed.
Lemma lem3754808 {A : Type'} (s : A -> Prop) (f : type686 A) : (term46 A s f) = (term74 A s f).
Proof. exact (EQ_MP (@lem3754807 A s f) (@lem3754782 A s f)). Qed.
Lemma lem3754821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3754822 {A : Type'} (s : A -> Prop) (f : type686 A) : (term48 A s f) = (term75 A s f).
Proof. exact (MK_COMB (@lem3754821) (@lem3754808 A s f)). Qed.
Lemma lem3754831 {A : Type'} (f : type686 A) (s : A -> Prop) : (term49 A f s) = (term49 A f s).
Proof. exact (eq_refl (term49 A f s)). Qed.
Lemma lem3754832 {A : Type'} (f : type686 A) (s : A -> Prop) : (term51 A f s) = (term76 A f s).
Proof. exact (MK_COMB (@lem3754822 A s f) (@lem3754831 A f s)). Qed.
Lemma lem3754834 {A : Type'} (P : A -> Prop) (Q : Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem3754711 A P Q) (@lem3754710 A P Q)). Qed.
Lemma lem3754835 {A : Type'} (P : type421 A) (Q : Prop) : (term77 A P Q) = (term78 A P Q).
Proof. exact (@lem3754834 (type1402 A) P Q). Qed.
Lemma lem3754836 {A : Type'} (f : type686 A) (s : A -> Prop) : (term79 A f s) = (term80 A f s).
Proof. exact (@lem3754835 A (term73 A s f) (term49 A f s)). Qed.
Lemma lem3754837 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term81 A s f t) = (term71 A s f t).
Proof. exact (eq_refl (term81 A s f t)). Qed.
Lemma lem3754838 {A : Type'} (s : A -> Prop) (f : type686 A) : (term82 A s f) = (term73 A s f).
Proof. exact (fun_ext (fun t : type1402 A => @lem3754837 A s f t)). Qed.
Lemma lem3754839 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem3754840 {A : Type'} (s : A -> Prop) (f : type686 A) : (term83 A s f) = (term74 A s f).
Proof. exact (MK_COMB (@lem3754839 A) (@lem3754838 A s f)). Qed.
Lemma lem3754841 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3754842 {A : Type'} (s : A -> Prop) (f : type686 A) : (term84 A s f) = (term75 A s f).
Proof. exact (MK_COMB (@lem3754841) (@lem3754840 A s f)). Qed.
Lemma lem3754843 {A : Type'} (f : type686 A) (s : A -> Prop) : (term49 A f s) = (term49 A f s).
Proof. exact (eq_refl (term49 A f s)). Qed.
Lemma lem3754844 {A : Type'} (f : type686 A) (s : A -> Prop) : (term79 A f s) = (term76 A f s).
Proof. exact (MK_COMB (@lem3754842 A s f) (@lem3754843 A f s)). Qed.
Lemma lem3754845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3754846 {A : Type'} (f : type686 A) (s : A -> Prop) : (term85 A f s) = (term86 A f s).
Proof. exact (MK_COMB (@lem3754845) (@lem3754844 A f s)). Qed.
Lemma lem3754847 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term81 A s f t) = (term71 A s f t).
Proof. exact (eq_refl (term81 A s f t)). Qed.
Lemma lem3754848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3754849 {A : Type'} (s : A -> Prop) (f : type686 A) (t : type1402 A) : (term87 A s f t) = (term88 A s f t).
Proof. exact (MK_COMB (@lem3754848) (@lem3754847 A s f t)). Qed.
Lemma lem3754850 {A : Type'} (f : type686 A) (s : A -> Prop) : (term49 A f s) = (term49 A f s).
Proof. exact (eq_refl (term49 A f s)). Qed.
Lemma lem3754851 {A : Type'} (t : type1402 A) (f : type686 A) (s : A -> Prop) : (term89 A t f s) = (term90 A t f s).
Proof. exact (MK_COMB (@lem3754849 A s f t) (@lem3754850 A f s)). Qed.
Lemma lem3754852 {A : Type'} (f : type686 A) (s : A -> Prop) : (term91 A f s) = (term92 A f s).
Proof. exact (fun_ext (fun t : type1402 A => @lem3754851 A t f s)). Qed.
Lemma lem3754853 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem3754854 {A : Type'} (f : type686 A) (s : A -> Prop) : (term80 A f s) = (term93 A f s).
Proof. exact (MK_COMB (@lem3754853 A) (@lem3754852 A f s)). Qed.
Lemma lem3754855 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term79 A f s) = (term80 A f s)) = ((term76 A f s) = (term93 A f s)).
Proof. exact (MK_COMB (@lem3754846 A f s) (@lem3754854 A f s)). Qed.
Lemma lem3754856 {A : Type'} (f : type686 A) (s : A -> Prop) : (term76 A f s) = (term93 A f s).
Proof. exact (EQ_MP (@lem3754855 A f s) (@lem3754836 A f s)). Qed.
Lemma lem3754879 {A : Type'} (f : type686 A) (s : A -> Prop) : (term51 A f s) = (term93 A f s).
Proof. exact (TRANS (@lem3754832 A f s) (@lem3754856 A f s)). Qed.
Lemma lem3754880 {A : Type'} (f : type686 A) (s : A -> Prop) : (term93 A f s) = (term51 A f s).
Proof. exact (SYM (@lem3754879 A f s)). Qed.
Lemma lem3754881 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) (h1 : term71 A s f u) : term71 A s f u.
Proof. exact (h1). Qed.
Lemma lem3754882 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term94 _89422 _89438 f.
Proof. exact (@lem3452302 _89422 _89438 f). Qed.
Lemma lem3754883 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term94 _89422 _89438 f) = (term95 _89422 _89438 f).
Proof. exact (eq_refl (term94 _89422 _89438 f)). Qed.
Lemma lem3754884 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term95 _89422 _89438 f.
Proof. exact (EQ_MP (@lem3754883 _89422 _89438 f) (@lem3754882 _89422 _89438 f)). Qed.
Lemma lem3754885 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) : term96 _89422 _89438 f s.
Proof. exact (@lem3754884 _89422 _89438 f s). Qed.
Lemma lem3754886 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term96 _89422 _89438 f s) = ((term97 _89422 _89438 f s) = (term98 _89422 _89438 s f)).
Proof. exact (eq_refl (term96 _89422 _89438 f s)). Qed.
Lemma lem3754888 {A B : Type'} (f : A -> B) : term99 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem3754889 {A B : Type'} (f : A -> B) : (term99 A B f) = (term100 A B f).
Proof. exact (eq_refl (term99 A B f)). Qed.
Lemma lem3754890 {A B : Type'} (f : A -> B) : term100 A B f.
Proof. exact (EQ_MP (@lem3754889 A B f) (@lem3754888 A B f)). Qed.
Lemma lem3754891 {A B : Type'} (f : A -> B) (s : A -> Prop) : term101 A B f s.
Proof. exact (@lem3754890 A B f s). Qed.
Lemma lem3754892 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term101 A B f s) = (term102 A B f s).
Proof. exact (eq_refl (term101 A B f s)). Qed.
Lemma lem3754893 {A B : Type'} (f : A -> B) (s : A -> Prop) : term102 A B f s.
Proof. exact (EQ_MP (@lem3754892 A B f s) (@lem3754891 A B f s)). Qed.
Lemma lem3754894 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3754895 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term103 A B f s.
Proof. exact (@lem3754893 A B f s (@lem3754894 A s h1)). Qed.
Lemma lem3754896 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term103 A B f s) = ((term103 A B f s) = True).
Proof. exact (@lem7 (term103 A B f s)). Qed.
Lemma lem3754897 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term103 A B f s) = True.
Proof. exact (EQ_MP (@lem3754896 A B f s) (@lem3754895 A B f s h1)). Qed.
Lemma lem3754903 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3754929 {A B : Type'} (f : A -> B) (s : A -> Prop) : term104 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3754897 A B f s h0). Qed.
Lemma lem3754930 {A : Type'} (f : type1402 A) (s : A -> Prop) : term105 A f s.
Proof. exact (@lem3754929 A (A -> Prop) f s). Qed.
Lemma lem3754931 {A : Type'} (u : type1402 A) (s : A -> Prop) : term105 A u s.
Proof. exact (@lem3754930 A u s). Qed.
Lemma lem3754933 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3754903 A s) (@lem3754736 A s h1)). Qed.
Lemma lem3754934 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3754933 A s h1)). Qed.
Lemma lem3754935 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3754934 A s h1) (@lem0)). Qed.
Lemma lem3754936 {A : Type'} (u : type1402 A) (s : A -> Prop) (h1 : @FINITE A s) : (term106 A u s) = True.
Proof. exact (@lem3754931 A u s (@lem3754935 A s h1)). Qed.
Lemma lem3754937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3754938 {A : Type'} (u : type1402 A) (s : A -> Prop) (h1 : @FINITE A s) : (term107 A u s) = (and True).
Proof. exact (MK_COMB (@lem3754937) (@lem3754936 A u s h1)). Qed.
Lemma lem3754942 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term97 _89422 _89438 f s) = (term98 _89422 _89438 s f).
Proof. exact (EQ_MP (@lem3754886 _89422 _89438 s f) (@lem3754885 _89422 _89438 f s)). Qed.
Lemma lem3754943 {A : Type'} (s : A -> Prop) (f : type1402 A) : (term108 A f s) = (term109 A s f).
Proof. exact (@lem3754942 A A s f). Qed.
Lemma lem3754944 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term108 A u s) = (term109 A s u).
Proof. exact (@lem3754943 A s u). Qed.
Lemma lem3754957 {A : Type'} (s : A -> Prop) : (@SUBSET A s) = (@SUBSET A s).
Proof. exact (eq_refl (@SUBSET A s)). Qed.
Lemma lem3754958 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term110 A u s) = (term111 A s u).
Proof. exact (MK_COMB (@lem3754957 A s) (@lem3754944 A s u)). Qed.
Lemma lem3754971 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term112 A u s f) = (term112 A u s f).
Proof. exact (eq_refl (term112 A u s f)). Qed.
Lemma lem3754972 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term113 A f u s) = (term114 A f s u).
Proof. exact (MK_COMB (@lem3754971 A u s f) (@lem3754958 A s u)). Qed.
Lemma lem3754987 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : @FINITE A s) : (term115 A f u s) = (term116 A f s u).
Proof. exact (MK_COMB (@lem3754938 A u s h1) (@lem3754972 A f s u)). Qed.
Lemma lem3754989 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3754990 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term116 A f s u) = (term114 A f s u).
Proof. exact (@lem3754989 (term114 A f s u)). Qed.
Lemma lem3755005 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : @FINITE A s) : (term115 A f u s) = (term114 A f s u).
Proof. exact (TRANS (@lem3754987 A f u s h1) (@lem3754990 A f s u)). Qed.
Lemma lem3755006 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : @FINITE A s) : (term114 A f s u) = (term115 A f u s).
Proof. exact (SYM (@lem3755005 A f u s h1)). Qed.
Lemma lem3755017 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term71 A s f u) (h2 : @FINITE A s) : term117 A f u s.
Proof. exact (conj (@lem3754881 A s f u h1) (@lem3754736 A s h2)). Qed.
Lemma lem3755033 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3755034 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term118 A s t).
Proof. exact (@lem3755033 (A -> Prop) s t). Qed.
Lemma lem3755035 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term119 A u s f) = (term120 A u s f).
Proof. exact (@lem3755034 A (@IMAGE A (A -> Prop) u s) f). Qed.
Lemma lem3755042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755043 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term112 A u s f) = (term121 A u s f).
Proof. exact (MK_COMB (@lem3755042) (@lem3755035 A u s f)). Qed.
Lemma lem3755045 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3755046 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (@lem3755045 A s t). Qed.
Lemma lem3755047 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term111 A s u) = (term122 A s u).
Proof. exact (@lem3755046 A s (term109 A s u)). Qed.
Lemma lem3755064 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term114 A f s u) = (term123 A f s u).
Proof. exact (MK_COMB (@lem3755043 A u s f) (@lem3755047 A s u)). Qed.
Lemma lem3755067 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) : (term124 A f u s) = (term124 A f u s).
Proof. exact (eq_refl (term124 A f u s)). Qed.
Lemma lem3755068 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term125 A f s u) = (term126 A f s u).
Proof. exact (MK_COMB (@lem3755067 A f u s) (@lem3755064 A f s u)). Qed.
Lemma lem3755071 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term126 A f s u) = (term125 A f s u).
Proof. exact (SYM (@lem3755068 A f s u)). Qed.
Lemma lem3755083 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3755084 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3755083 A P x). Qed.
Lemma lem3755085 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3755084 A s x). Qed.
Lemma lem3755086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3755087 {A : Type'} (s : A -> Prop) (x : A) : (term25 A x s) = (term127 A s x).
Proof. exact (MK_COMB (@lem3755086) (@lem3755085 A s x)). Qed.
Lemma lem3755091 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3755092 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3755091 (A -> Prop) P x). Qed.
Lemma lem3755093 {A : Type'} (f : type686 A) (u : type1402 A) (x : A) : (term128 A u x f) = (term129 A f u x).
Proof. exact (@lem3755092 A f (u x)). Qed.
Lemma lem3755094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755095 {A : Type'} (f : type686 A) (u : type1402 A) (x : A) : (term130 A u x f) = (term131 A f u x).
Proof. exact (MK_COMB (@lem3755094) (@lem3755093 A f u x)). Qed.
Lemma lem3755097 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3755098 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3755097 A P x). Qed.
Lemma lem3755099 {A : Type'} (u : type1402 A) (x : A) : (term132 A u x) = (u x x).
Proof. exact (@lem3755098 A (u x) x). Qed.
Lemma lem3755100 {A : Type'} (f : type686 A) (u : type1402 A) (x : A) : (term133 A f u x) = (term134 A f u x).
Proof. exact (MK_COMB (@lem3755095 A f u x) (@lem3755099 A u x)). Qed.
Lemma lem3755103 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) (x : A) : (term67 A s f u x) = (term135 A s f u x).
Proof. exact (MK_COMB (@lem3755087 A s x) (@lem3755100 A f u x)). Qed.
Lemma lem3755106 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term69 A s f u) = (term136 A s f u).
Proof. exact (fun_ext (fun x : A => @lem3755103 A s f u x)). Qed.
Lemma lem3755107 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3755108 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term71 A s f u) = (term137 A s f u).
Proof. exact (MK_COMB (@lem3755107 A) (@lem3755106 A s f u)). Qed.
Lemma lem3755113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755114 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term138 A s f u) = (term139 A s f u).
Proof. exact (MK_COMB (@lem3755113) (@lem3755108 A s f u)). Qed.
Lemma lem3755115 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3755116 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) : (term117 A f u s) = (term140 A f u s).
Proof. exact (MK_COMB (@lem3755114 A s f u) (@lem3755115 A s)). Qed.
Lemma lem3755119 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3755120 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) : (term124 A f u s) = (term141 A f u s).
Proof. exact (MK_COMB (@lem3755119) (@lem3755116 A f u s)). Qed.
Lemma lem3755130 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term142 A B y f s) = (term143 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3755131 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term144 A y f s) = (term145 A y f s).
Proof. exact (@lem3755130 A (A -> Prop) y f s). Qed.
Lemma lem3755132 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term144 A x u s) = (term145 A x u s).
Proof. exact (@lem3755131 A x u s). Qed.
Lemma lem3755142 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3755143 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3755142 A P x). Qed.
Lemma lem3755144 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3755143 A s x). Qed.
Lemma lem3755145 {A : Type'} (x : A -> Prop) (u : type1402 A) (x' : A) : (term146 A x u x') = (term146 A x u x').
Proof. exact (eq_refl (term146 A x u x')). Qed.
Lemma lem3755146 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) (x' : A) : (term147 A x u x' s) = (term148 A x u s x').
Proof. exact (MK_COMB (@lem3755145 A x u x') (@lem3755144 A s x')). Qed.
Lemma lem3755149 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term149 A x u s) = (term150 A x u s).
Proof. exact (fun_ext (fun x' : A => @lem3755146 A x u s x')). Qed.
Lemma lem3755150 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755151 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term145 A x u s) = (term151 A x u s).
Proof. exact (MK_COMB (@lem3755150 A) (@lem3755149 A x u s)). Qed.
Lemma lem3755156 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term144 A x u s) = (term151 A x u s).
Proof. exact (TRANS (@lem3755132 A x u s) (@lem3755151 A x u s)). Qed.
Lemma lem3755157 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3755158 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term152 A x u s) = (term153 A x u s).
Proof. exact (MK_COMB (@lem3755157) (@lem3755156 A x u s)). Qed.
Lemma lem3755160 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3755161 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3755160 (A -> Prop) P x). Qed.
Lemma lem3755162 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3755161 A f x). Qed.
Lemma lem3755163 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term154 A u s x f) = (term155 A u s f x).
Proof. exact (MK_COMB (@lem3755158 A x u s) (@lem3755162 A f x)). Qed.
Lemma lem3755166 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term156 A u s f) = (term157 A u s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3755163 A u s f x)). Qed.
Lemma lem3755167 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3755168 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term120 A u s f) = (term158 A u s f).
Proof. exact (MK_COMB (@lem3755167 A) (@lem3755166 A u s f)). Qed.
Lemma lem3755173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755174 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term121 A u s f) = (term159 A u s f).
Proof. exact (MK_COMB (@lem3755173) (@lem3755168 A u s f)). Qed.
Lemma lem3755182 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3755183 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3755182 A P x). Qed.
Lemma lem3755184 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3755183 A s x). Qed.
Lemma lem3755185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3755186 {A : Type'} (s : A -> Prop) (x : A) : (term25 A x s) = (term127 A s x).
Proof. exact (MK_COMB (@lem3755185) (@lem3755184 A s x)). Qed.
Lemma lem3755188 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term160 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3755189 {A : Type'} (p : A -> Prop) (x : A) : (term160 A x p) = (p x).
Proof. exact (@lem3755188 A p x). Qed.
Lemma lem3755190 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term161 A x s u) = (term162 A s u x).
Proof. exact (@lem3755189 A (term163 A s u) x). Qed.
Lemma lem3755191 {A : Type'} (s : A -> Prop) (y : A) (u : type1402 A) : (term162 A s u y) = (term164 A s y u).
Proof. exact (eq_refl (term162 A s u y)). Qed.
Lemma lem3755192 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem3755193 {A : Type'} (GEN_PVAR_47 : A) (s : A -> Prop) (y : A) (u : type1402 A) : (term165 A GEN_PVAR_47 s u y) = (term166 A GEN_PVAR_47 s y u).
Proof. exact (MK_COMB (@lem3755192 A GEN_PVAR_47) (@lem3755191 A s y u)). Qed.
Lemma lem3755194 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3755195 {A : Type'} (GEN_PVAR_47 : A) (s : A -> Prop) (u : type1402 A) (y : A) : (term167 A GEN_PVAR_47 s u y) = (term168 A GEN_PVAR_47 s u y).
Proof. exact (MK_COMB (@lem3755193 A GEN_PVAR_47 s y u) (@lem3755194 A y)). Qed.
Lemma lem3755196 {A : Type'} (GEN_PVAR_47 : A) (s : A -> Prop) (u : type1402 A) : (term169 A GEN_PVAR_47 s u) = (term170 A GEN_PVAR_47 s u).
Proof. exact (fun_ext (fun y : A => @lem3755195 A GEN_PVAR_47 s u y)). Qed.
Lemma lem3755197 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755198 {A : Type'} (GEN_PVAR_47 : A) (s : A -> Prop) (u : type1402 A) : (term171 A GEN_PVAR_47 s u) = (term172 A GEN_PVAR_47 s u).
Proof. exact (MK_COMB (@lem3755197 A) (@lem3755196 A GEN_PVAR_47 s u)). Qed.
Lemma lem3755199 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term173 A s u) = (term174 A s u).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem3755198 A GEN_PVAR_47 s u)). Qed.
Lemma lem3755200 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3755201 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term175 A s u) = (term109 A s u).
Proof. exact (MK_COMB (@lem3755200 A) (@lem3755199 A s u)). Qed.
Lemma lem3755202 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3755203 {A : Type'} (x : A) (s : A -> Prop) (u : type1402 A) : (term161 A x s u) = (term176 A x s u).
Proof. exact (MK_COMB (@lem3755202 A x) (@lem3755201 A s u)). Qed.
Lemma lem3755204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3755205 {A : Type'} (x : A) (s : A -> Prop) (u : type1402 A) : (term177 A x s u) = (term178 A x s u).
Proof. exact (MK_COMB (@lem3755204) (@lem3755203 A x s u)). Qed.
Lemma lem3755206 {A : Type'} (s : A -> Prop) (x : A) (u : type1402 A) : (term162 A s u x) = (term164 A s x u).
Proof. exact (eq_refl (term162 A s u x)). Qed.
Lemma lem3755207 {A : Type'} (s : A -> Prop) (x : A) (u : type1402 A) : ((term161 A x s u) = (term162 A s u x)) = ((term176 A x s u) = (term164 A s x u)).
Proof. exact (MK_COMB (@lem3755205 A x s u) (@lem3755206 A s x u)). Qed.
Lemma lem3755208 {A : Type'} (s : A -> Prop) (x : A) (u : type1402 A) : (term176 A x s u) = (term164 A s x u).
Proof. exact (EQ_MP (@lem3755207 A s x u) (@lem3755190 A s u x)). Qed.
Lemma lem3755216 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3755217 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3755216 A P x). Qed.
Lemma lem3755218 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3755217 A s x'). Qed.
Lemma lem3755219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755220 {A : Type'} (s : A -> Prop) (x' : A) : (term179 A x' s) = (term180 A s x').
Proof. exact (MK_COMB (@lem3755219) (@lem3755218 A s x')). Qed.
Lemma lem3755222 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3755223 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3755222 A P x). Qed.
Lemma lem3755224 {A : Type'} (u : type1402 A) (x' : A) (x : A) : (term181 A x u x') = (u x' x).
Proof. exact (@lem3755223 A (u x') x). Qed.
Lemma lem3755225 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (x : A) : (term182 A s x u x') = (term183 A s u x' x).
Proof. exact (MK_COMB (@lem3755220 A s x') (@lem3755224 A u x' x)). Qed.
Lemma lem3755228 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term184 A s x u) = (term185 A s u x).
Proof. exact (fun_ext (fun x' : A => @lem3755225 A s u x' x)). Qed.
Lemma lem3755229 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755230 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term164 A s x u) = (term186 A s u x).
Proof. exact (MK_COMB (@lem3755229 A) (@lem3755228 A s u x)). Qed.
Lemma lem3755235 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term176 A x s u) = (term186 A s u x).
Proof. exact (TRANS (@lem3755208 A s x u) (@lem3755230 A s u x)). Qed.
Lemma lem3755236 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term187 A x s u) = (term188 A s u x).
Proof. exact (MK_COMB (@lem3755186 A s x) (@lem3755235 A s u x)). Qed.
Lemma lem3755239 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term189 A s u) = (term190 A s u).
Proof. exact (fun_ext (fun x : A => @lem3755236 A s u x)). Qed.
Lemma lem3755240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3755241 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term122 A s u) = (term191 A s u).
Proof. exact (MK_COMB (@lem3755240 A) (@lem3755239 A s u)). Qed.
Lemma lem3755246 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term123 A f s u) = (term192 A f s u).
Proof. exact (MK_COMB (@lem3755174 A u s f) (@lem3755241 A s u)). Qed.
Lemma lem3755249 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term126 A f s u) = (term193 A f s u).
Proof. exact (MK_COMB (@lem3755120 A f u s) (@lem3755246 A f s u)). Qed.
Lemma lem3755252 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term193 A f s u) = (term126 A f s u).
Proof. exact (SYM (@lem3755249 A f s u)). Qed.
Lemma lem3755254 (p : Prop) : p = (term194 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3755255 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term193 A f s u) = (term195 A f s u).
Proof. exact (@lem3755254 (term193 A f s u)). Qed.
Lemma lem3755256 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term195 A f s u) = (term193 A f s u).
Proof. exact (SYM (@lem3755255 A f s u)). Qed.
Lemma lem3755257 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term196 A f s u) : term196 A f s u.
Proof. exact (h1). Qed.
Lemma lem3755260 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term195 A f s u) : term195 A f s u.
Proof. exact (h1). Qed.
Lemma lem3755261 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term197 A f s u.
Proof. exact (fun h0 : term195 A f s u => @lem3755260 A f s u h0). Qed.
Lemma lem3755262 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term197 A f s u) : term197 A f s u.
Proof. exact (h1). Qed.
Lemma lem3755263 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term195 A f s u) : term195 A f s u.
Proof. exact (h1). Qed.
Lemma lem3755264 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term195 A f s u) (h2 : term197 A f s u) : term195 A f s u.
Proof. exact (@lem3755262 A f s u h2 (@lem3755263 A f s u h1)). Qed.
Lemma lem3755265 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term195 A f s u) : term198 A f s u.
Proof. exact (fun h0 : term197 A f s u => @lem3755264 A f s u h1 h0). Qed.
Lemma lem3755266 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term197 A f s u) : term197 A f s u.
Proof. exact (h1). Qed.
Lemma lem3755267 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term195 A f s u) (h2 : term197 A f s u) : term195 A f s u.
Proof. exact (@lem3755265 A f s u h1 (@lem3755266 A f s u h2)). Qed.
Lemma lem3755268 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term197 A f s u) : term197 A f s u.
Proof. exact (fun h0 : term195 A f s u => @lem3755267 A f s u h0 h1). Qed.
Lemma lem3755269 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term199 A f s u.
Proof. exact (fun h0 : term197 A f s u => @lem3755268 A f s u h0). Qed.
Lemma lem3755272 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term197 A f s u.
Proof. exact (@lem3755269 A f s u (@lem3755261 A f s u)). Qed.
Lemma lem3755273 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term197 A f s u.
Proof. exact (@lem3755272 A f s u). Qed.
Lemma lem3755287 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3755288 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term195 A f s u) = (term200 A f s u).
Proof. exact (@lem3755287 (term196 A f s u)). Qed.
Lemma lem3755290 (t : Prop) : (term201 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3755291 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term200 A f s u) = (term193 A f s u).
Proof. exact (@lem3755290 (term193 A f s u)). Qed.
Lemma lem3755294 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term195 A f s u) = (term193 A f s u).
Proof. exact (TRANS (@lem3755288 A f s u) (@lem3755291 A f s u)). Qed.
Lemma lem3755383 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term202 A s u) = (term203 A s u).
Proof. exact (fun_ext (fun f : type686 A => @lem3755294 A f s u)). Qed.
Lemma lem3755384 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3755385 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term204 A s u) = (term205 A s u).
Proof. exact (MK_COMB (@lem3755384 A) (@lem3755383 A s u)). Qed.
Lemma lem3755390 {A : Type'} (u : type1402 A) : (term206 A u) = (term207 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3755385 A s u)). Qed.
Lemma lem3755391 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3755392 {A : Type'} (u : type1402 A) : (term208 A u) = (term209 A u).
Proof. exact (MK_COMB (@lem3755391 A) (@lem3755390 A u)). Qed.
Lemma lem3755397 {A : Type'} : (term210 A) = (term211 A).
Proof. exact (fun_ext (fun u : type1402 A => @lem3755392 A u)). Qed.
Lemma lem3755398 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem3755407 {A : Type'} : (term212 A) = (term213 A).
Proof. exact (MK_COMB (@lem3755398 A) (@lem3755397 A)). Qed.
Lemma lem3755412 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (x : A) : (term183 A s u x' x) = (term183 A s u x' x).
Proof. exact (eq_refl (term183 A s u x' x)). Qed.
Lemma lem3755413 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term185 A s u x) = (term185 A s u x).
Proof. exact (fun_ext (fun x' : A => @lem3755412 A s u x' x)). Qed.
Lemma lem3755414 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755415 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term186 A s u x) = (term186 A s u x).
Proof. exact (MK_COMB (@lem3755414 A) (@lem3755413 A s u x)). Qed.
Lemma lem3755418 {A : Type'} (s : A -> Prop) (x : A) : (term127 A s x) = (term127 A s x).
Proof. exact (eq_refl (term127 A s x)). Qed.
Lemma lem3755419 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term188 A s u x) = (term188 A s u x).
Proof. exact (MK_COMB (@lem3755418 A s x) (@lem3755415 A s u x)). Qed.
Lemma lem3755420 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term190 A s u) = (term190 A s u).
Proof. exact (fun_ext (fun x : A => @lem3755419 A s u x)). Qed.
Lemma lem3755421 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3755422 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term191 A s u) = (term191 A s u).
Proof. exact (MK_COMB (@lem3755421 A) (@lem3755420 A s u)). Qed.
Lemma lem3755423 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3755428 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) (x' : A) : (term148 A x u s x') = (term148 A x u s x').
Proof. exact (eq_refl (term148 A x u s x')). Qed.
Lemma lem3755429 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term150 A x u s) = (term150 A x u s).
Proof. exact (fun_ext (fun x' : A => @lem3755428 A x u s x')). Qed.
Lemma lem3755430 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755431 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term151 A x u s) = (term151 A x u s).
Proof. exact (MK_COMB (@lem3755430 A) (@lem3755429 A x u s)). Qed.
Lemma lem3755432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3755433 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term153 A x u s) = (term153 A x u s).
Proof. exact (MK_COMB (@lem3755432) (@lem3755431 A x u s)). Qed.
Lemma lem3755434 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term155 A u s f x) = (term155 A u s f x).
Proof. exact (MK_COMB (@lem3755433 A x u s) (@lem3755423 A f x)). Qed.
Lemma lem3755435 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term157 A u s f) = (term157 A u s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3755434 A u s f x)). Qed.
Lemma lem3755436 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3755437 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term158 A u s f) = (term158 A u s f).
Proof. exact (MK_COMB (@lem3755436 A) (@lem3755435 A u s f)). Qed.
Lemma lem3755438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755439 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term159 A u s f) = (term159 A u s f).
Proof. exact (MK_COMB (@lem3755438) (@lem3755437 A u s f)). Qed.
Lemma lem3755440 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term192 A f s u) = (term192 A f s u).
Proof. exact (MK_COMB (@lem3755439 A u s f) (@lem3755422 A s u)). Qed.
Lemma lem3755441 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3755450 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) (x : A) : (term135 A s f u x) = (term135 A s f u x).
Proof. exact (eq_refl (term135 A s f u x)). Qed.
Lemma lem3755451 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term136 A s f u) = (term136 A s f u).
Proof. exact (fun_ext (fun x : A => @lem3755450 A s f u x)). Qed.
Lemma lem3755452 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3755453 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term137 A s f u) = (term137 A s f u).
Proof. exact (MK_COMB (@lem3755452 A) (@lem3755451 A s f u)). Qed.
Lemma lem3755454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755455 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term139 A s f u) = (term139 A s f u).
Proof. exact (MK_COMB (@lem3755454) (@lem3755453 A s f u)). Qed.
Lemma lem3755456 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) : (term140 A f u s) = (term140 A f u s).
Proof. exact (MK_COMB (@lem3755455 A s f u) (@lem3755441 A s)). Qed.
Lemma lem3755457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3755458 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) : (term141 A f u s) = (term141 A f u s).
Proof. exact (MK_COMB (@lem3755457) (@lem3755456 A f u s)). Qed.
Lemma lem3755459 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term193 A f s u) = (term193 A f s u).
Proof. exact (MK_COMB (@lem3755458 A f u s) (@lem3755440 A f s u)). Qed.
Lemma lem3755460 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term203 A s u) = (term203 A s u).
Proof. exact (fun_ext (fun f : type686 A => @lem3755459 A f s u)). Qed.
Lemma lem3755461 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3755462 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term205 A s u) = (term205 A s u).
Proof. exact (MK_COMB (@lem3755461 A) (@lem3755460 A s u)). Qed.
Lemma lem3755463 {A : Type'} (u : type1402 A) : (term207 A u) = (term207 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3755462 A s u)). Qed.
Lemma lem3755464 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3755465 {A : Type'} (u : type1402 A) : (term209 A u) = (term209 A u).
Proof. exact (MK_COMB (@lem3755464 A) (@lem3755463 A u)). Qed.
Lemma lem3755466 {A : Type'} : (term211 A) = (term211 A).
Proof. exact (fun_ext (fun u : type1402 A => @lem3755465 A u)). Qed.
Lemma lem3755467 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem3755468 {A : Type'} : (term213 A) = (term213 A).
Proof. exact (MK_COMB (@lem3755467 A) (@lem3755466 A)). Qed.
Lemma lem3755537 {A : Type'} : (term212 A) = (term213 A).
Proof. exact (TRANS (@lem3755407 A) (@lem3755468 A)). Qed.
Lemma lem3755538 {A : Type'} : (term213 A) = (term212 A).
Proof. exact (SYM (@lem3755537 A)). Qed.
Lemma lem3755539 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term140 A f u s.
Proof. exact (h1). Qed.
Lemma lem3755541 (p : Prop) : p = (term194 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3755542 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term192 A f s u) = (term214 A f s u).
Proof. exact (@lem3755541 (term192 A f s u)). Qed.
Lemma lem3755543 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term214 A f s u) = (term192 A f s u).
Proof. exact (SYM (@lem3755542 A f s u)). Qed.
Lemma lem3755544 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term215 A f s u) : term215 A f s u.
Proof. exact (h1). Qed.
Lemma lem3755555 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) (x : A) : (term135 A s f u x) = (term216 A s f u x).
Proof. exact (@lem17265 (s x) (term134 A f u x)). Qed.
Lemma lem3755556 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term136 A s f u) = (term217 A s f u).
Proof. exact (fun_ext (fun x : A => @lem3755555 A s f u x)). Qed.
Lemma lem3755557 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3755558 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term137 A s f u) = (term218 A s f u).
Proof. exact (MK_COMB (@lem3755557 A) (@lem3755556 A s f u)). Qed.
Lemma lem3755559 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3755560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755561 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term139 A s f u) = (term219 A s f u).
Proof. exact (MK_COMB (@lem3755560) (@lem3755558 A s f u)). Qed.
Lemma lem3755614 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) : (term140 A f u s) = (term220 A f u s).
Proof. exact (MK_COMB (@lem3755561 A s f u) (@lem3755559 A s)). Qed.
Lemma lem3755615 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term220 A f u s.
Proof. exact (EQ_MP (@lem3755614 A f u s) (@lem3755539 A f u s h1)). Qed.
Lemma lem3755620 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) (x' : A) : (term148 A x u s x') = (term148 A x u s x').
Proof. exact (eq_refl (term148 A x u s x')). Qed.
Lemma lem3755621 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term150 A x u s) = (term150 A x u s).
Proof. exact (fun_ext (fun x' : A => @lem3755620 A x u s x')). Qed.
Lemma lem3755622 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755623 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term151 A x u s) = (term151 A x u s).
Proof. exact (MK_COMB (@lem3755622 A) (@lem3755621 A x u s)). Qed.
Lemma lem3755624 {A : Type'} (f : type686 A) (x : A -> Prop) : (term221 A f x) = (term221 A f x).
Proof. exact (eq_refl (term221 A f x)). Qed.
Lemma lem3755625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755626 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term222 A x u s) = (term222 A x u s).
Proof. exact (MK_COMB (@lem3755625) (@lem3755623 A x u s)). Qed.
Lemma lem3755627 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term223 A u s f x) = (term223 A u s f x).
Proof. exact (MK_COMB (@lem3755626 A x u s) (@lem3755624 A f x)). Qed.
Lemma lem3755628 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term224 A u s f x) = (term223 A u s f x).
Proof. exact (@lem17362 (term151 A x u s) (f x)). Qed.
Lemma lem3755629 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term224 A u s f x) = (term223 A u s f x).
Proof. exact (TRANS (@lem3755628 A u s f x) (@lem3755627 A u s f x)). Qed.
Lemma lem3755630 {A : Type'} (P : type686 A) : (term225 A P) = (term226 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3755631 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term227 A u s f) = (term228 A u s f).
Proof. exact (@lem3755630 A (term157 A u s f)). Qed.
Lemma lem3755632 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term229 A u s f x) = (term155 A u s f x).
Proof. exact (eq_refl (term229 A u s f x)). Qed.
Lemma lem3755633 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3755634 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term230 A u s f x) = (term224 A u s f x).
Proof. exact (MK_COMB (@lem3755633) (@lem3755632 A u s f x)). Qed.
Lemma lem3755635 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term230 A u s f x) = (term223 A u s f x).
Proof. exact (TRANS (@lem3755634 A u s f x) (@lem3755629 A u s f x)). Qed.
Lemma lem3755636 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term231 A u s f) = (term232 A u s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3755635 A u s f x)). Qed.
Lemma lem3755637 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3755638 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term228 A u s f) = (term233 A u s f).
Proof. exact (MK_COMB (@lem3755637 A) (@lem3755636 A u s f)). Qed.
Lemma lem3755639 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term227 A u s f) = (term233 A u s f).
Proof. exact (TRANS (@lem3755631 A u s f) (@lem3755638 A u s f)). Qed.
Lemma lem3755647 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (x : A) : (term234 A s u x' x) = (term235 A s u x' x).
Proof. exact (@lem17045 (s x') (u x' x)). Qed.
Lemma lem3755648 {A : Type'} (P : A -> Prop) : (term236 A P) = (term237 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3755649 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term238 A s u x) = (term239 A s u x).
Proof. exact (@lem3755648 A (term185 A s u x)). Qed.
Lemma lem3755650 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (x : A) : (term240 A s u x x') = (term183 A s u x' x).
Proof. exact (eq_refl (term240 A s u x x')). Qed.
Lemma lem3755651 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3755652 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (x : A) : (term241 A s u x x') = (term234 A s u x' x).
Proof. exact (MK_COMB (@lem3755651) (@lem3755650 A s u x' x)). Qed.
Lemma lem3755653 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (x : A) : (term241 A s u x x') = (term235 A s u x' x).
Proof. exact (TRANS (@lem3755652 A s u x' x) (@lem3755647 A s u x' x)). Qed.
Lemma lem3755654 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term242 A s u x) = (term243 A s u x).
Proof. exact (fun_ext (fun x' : A => @lem3755653 A s u x' x)). Qed.
Lemma lem3755655 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3755656 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term239 A s u x) = (term244 A s u x).
Proof. exact (MK_COMB (@lem3755655 A) (@lem3755654 A s u x)). Qed.
Lemma lem3755657 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term238 A s u x) = (term244 A s u x).
Proof. exact (TRANS (@lem3755649 A s u x) (@lem3755656 A s u x)). Qed.
Lemma lem3755659 {A : Type'} (s : A -> Prop) (x : A) : (term180 A s x) = (term180 A s x).
Proof. exact (eq_refl (term180 A s x)). Qed.
Lemma lem3755660 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term245 A s u x) = (term246 A s u x).
Proof. exact (MK_COMB (@lem3755659 A s x) (@lem3755657 A s u x)). Qed.
Lemma lem3755661 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term247 A s u x) = (term245 A s u x).
Proof. exact (@lem17362 (s x) (term186 A s u x)). Qed.
Lemma lem3755662 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term247 A s u x) = (term246 A s u x).
Proof. exact (TRANS (@lem3755661 A s u x) (@lem3755660 A s u x)). Qed.
Lemma lem3755663 {A : Type'} (P : A -> Prop) : (term248 A P) = (term249 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3755664 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term250 A s u) = (term251 A s u).
Proof. exact (@lem3755663 A (term190 A s u)). Qed.
Lemma lem3755665 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term252 A s u x) = (term188 A s u x).
Proof. exact (eq_refl (term252 A s u x)). Qed.
Lemma lem3755666 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3755667 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term253 A s u x) = (term247 A s u x).
Proof. exact (MK_COMB (@lem3755666) (@lem3755665 A s u x)). Qed.
Lemma lem3755668 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term253 A s u x) = (term246 A s u x).
Proof. exact (TRANS (@lem3755667 A s u x) (@lem3755662 A s u x)). Qed.
Lemma lem3755669 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term254 A s u) = (term255 A s u).
Proof. exact (fun_ext (fun x : A => @lem3755668 A s u x)). Qed.
Lemma lem3755670 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755671 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term251 A s u) = (term256 A s u).
Proof. exact (MK_COMB (@lem3755670 A) (@lem3755669 A s u)). Qed.
Lemma lem3755672 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term250 A s u) = (term256 A s u).
Proof. exact (TRANS (@lem3755664 A s u) (@lem3755671 A s u)). Qed.
Lemma lem3755673 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3755674 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term257 A u s f) = (term258 A u s f).
Proof. exact (MK_COMB (@lem3755673) (@lem3755639 A u s f)). Qed.
Lemma lem3755675 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term259 A f s u) = (term260 A f s u).
Proof. exact (MK_COMB (@lem3755674 A u s f) (@lem3755672 A s u)). Qed.
Lemma lem3755676 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term215 A f s u) = (term259 A f s u).
Proof. exact (@lem17045 (term158 A u s f) (term191 A s u)). Qed.
Lemma lem3755677 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term215 A f s u) = (term260 A f s u).
Proof. exact (TRANS (@lem3755676 A f s u) (@lem3755675 A f s u)). Qed.
Lemma lem3755836 {A : Type'} (P : A -> Prop) (Q : Prop) : (term261 A P Q) = (term262 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3755837 {A : Type'} (P : A -> Prop) (Q : Prop) : (term261 A P Q) = (term262 A P Q).
Proof. exact (@lem3755836 A P Q). Qed.
Lemma lem3755838 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term263 A u s f x) = (term264 A u s f x).
Proof. exact (@lem3755837 A (term150 A x u s) (term221 A f x)). Qed.
Lemma lem3755839 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) (x' : A) : (term265 A x u s x') = (term148 A x u s x').
Proof. exact (eq_refl (term265 A x u s x')). Qed.
Lemma lem3755840 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term266 A x u s) = (term150 A x u s).
Proof. exact (fun_ext (fun x' : A => @lem3755839 A x u s x')). Qed.
Lemma lem3755841 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755842 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term267 A x u s) = (term151 A x u s).
Proof. exact (MK_COMB (@lem3755841 A) (@lem3755840 A x u s)). Qed.
Lemma lem3755843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755844 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) : (term268 A x u s) = (term222 A x u s).
Proof. exact (MK_COMB (@lem3755843) (@lem3755842 A x u s)). Qed.
Lemma lem3755845 {A : Type'} (f : type686 A) (x : A -> Prop) : (term221 A f x) = (term221 A f x).
Proof. exact (eq_refl (term221 A f x)). Qed.
Lemma lem3755846 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term263 A u s f x) = (term223 A u s f x).
Proof. exact (MK_COMB (@lem3755844 A x u s) (@lem3755845 A f x)). Qed.
Lemma lem3755847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3755848 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term269 A u s f x) = (term270 A u s f x).
Proof. exact (MK_COMB (@lem3755847) (@lem3755846 A u s f x)). Qed.
Lemma lem3755849 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) (x' : A) : (term265 A x u s x') = (term148 A x u s x').
Proof. exact (eq_refl (term265 A x u s x')). Qed.
Lemma lem3755850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755851 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) (x' : A) : (term271 A x u s x') = (term272 A x u s x').
Proof. exact (MK_COMB (@lem3755850) (@lem3755849 A x u s x')). Qed.
Lemma lem3755852 {A : Type'} (f : type686 A) (x : A -> Prop) : (term221 A f x) = (term221 A f x).
Proof. exact (eq_refl (term221 A f x)). Qed.
Lemma lem3755853 {A : Type'} (u : type1402 A) (s : A -> Prop) (x : A) (f : type686 A) (x' : A -> Prop) : (term273 A u s x f x') = (term274 A u s x f x').
Proof. exact (MK_COMB (@lem3755851 A x' u s x) (@lem3755852 A f x')). Qed.
Lemma lem3755854 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term275 A u s f x) = (term276 A u s f x).
Proof. exact (fun_ext (fun x' : A => @lem3755853 A u s x' f x)). Qed.
Lemma lem3755855 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755856 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term264 A u s f x) = (term277 A u s f x).
Proof. exact (MK_COMB (@lem3755855 A) (@lem3755854 A u s f x)). Qed.
Lemma lem3755857 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : ((term263 A u s f x) = (term264 A u s f x)) = ((term223 A u s f x) = (term277 A u s f x)).
Proof. exact (MK_COMB (@lem3755848 A u s f x) (@lem3755856 A u s f x)). Qed.
Lemma lem3755858 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term223 A u s f x) = (term277 A u s f x).
Proof. exact (EQ_MP (@lem3755857 A u s f x) (@lem3755838 A u s f x)). Qed.
Lemma lem3755859 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term232 A u s f) = (term278 A u s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3755858 A u s f x)). Qed.
Lemma lem3755860 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3755861 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term233 A u s f) = (term279 A u s f).
Proof. exact (MK_COMB (@lem3755860 A) (@lem3755859 A u s f)). Qed.
Lemma lem3755862 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3755863 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term258 A u s f) = (term280 A u s f).
Proof. exact (MK_COMB (@lem3755862) (@lem3755861 A u s f)). Qed.
Lemma lem3755864 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term256 A s u) = (term256 A s u).
Proof. exact (eq_refl (term256 A s u)). Qed.
Lemma lem3755865 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term260 A f s u) = (term281 A f s u).
Proof. exact (MK_COMB (@lem3755863 A u s f) (@lem3755864 A s u)). Qed.
Lemma lem3755869 {A : Type'} (P : A -> Prop) (Q : Prop) : (term282 A P Q) = (term283 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3755870 {A : Type'} (P : type686 A) (Q : Prop) : (term284 A P Q) = (term285 A P Q).
Proof. exact (@lem3755869 (A -> Prop) P Q). Qed.
Lemma lem3755871 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term286 A f s u) = (term287 A f s u).
Proof. exact (@lem3755870 A (term278 A u s f) (term256 A s u)). Qed.
Lemma lem3755872 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term288 A u s f x) = (term277 A u s f x).
Proof. exact (eq_refl (term288 A u s f x)). Qed.
Lemma lem3755873 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term289 A u s f) = (term278 A u s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3755872 A u s f x)). Qed.
Lemma lem3755874 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3755875 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term290 A u s f) = (term279 A u s f).
Proof. exact (MK_COMB (@lem3755874 A) (@lem3755873 A u s f)). Qed.
Lemma lem3755876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3755877 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) : (term291 A u s f) = (term280 A u s f).
Proof. exact (MK_COMB (@lem3755876) (@lem3755875 A u s f)). Qed.
Lemma lem3755878 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term256 A s u) = (term256 A s u).
Proof. exact (eq_refl (term256 A s u)). Qed.
Lemma lem3755879 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term286 A f s u) = (term281 A f s u).
Proof. exact (MK_COMB (@lem3755877 A u s f) (@lem3755878 A s u)). Qed.
Lemma lem3755880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3755881 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term292 A f s u) = (term293 A f s u).
Proof. exact (MK_COMB (@lem3755880) (@lem3755879 A f s u)). Qed.
Lemma lem3755882 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term288 A u s f x) = (term277 A u s f x).
Proof. exact (eq_refl (term288 A u s f x)). Qed.
Lemma lem3755883 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3755884 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term294 A u s f x) = (term295 A u s f x).
Proof. exact (MK_COMB (@lem3755883) (@lem3755882 A u s f x)). Qed.
Lemma lem3755885 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term256 A s u) = (term256 A s u).
Proof. exact (eq_refl (term256 A s u)). Qed.
Lemma lem3755886 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) : (term296 A f x s u) = (term297 A f x s u).
Proof. exact (MK_COMB (@lem3755884 A u s f x) (@lem3755885 A s u)). Qed.
Lemma lem3755887 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term298 A f s u) = (term299 A f s u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3755886 A f x s u)). Qed.
Lemma lem3755888 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3755889 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term287 A f s u) = (term300 A f s u).
Proof. exact (MK_COMB (@lem3755888 A) (@lem3755887 A f s u)). Qed.
Lemma lem3755890 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : ((term286 A f s u) = (term287 A f s u)) = ((term281 A f s u) = (term300 A f s u)).
Proof. exact (MK_COMB (@lem3755881 A f s u) (@lem3755889 A f s u)). Qed.
Lemma lem3755891 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term281 A f s u) = (term300 A f s u).
Proof. exact (EQ_MP (@lem3755890 A f s u) (@lem3755871 A f s u)). Qed.
Lemma lem3755893 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term301 A P Q) = (term302 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3755894 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term301 A P Q) = (term302 A P Q).
Proof. exact (@lem3755893 A P Q). Qed.
Lemma lem3755895 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) : (term303 A f x s u) = (term304 A f x s u).
Proof. exact (@lem3755894 A (term276 A u s f x) (term255 A s u)). Qed.
Lemma lem3755896 {A : Type'} (u : type1402 A) (s : A -> Prop) (x : A) (f : type686 A) (x' : A -> Prop) : (term305 A u s f x' x) = (term274 A u s x f x').
Proof. exact (eq_refl (term305 A u s f x' x)). Qed.
Lemma lem3755897 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term306 A u s f x) = (term276 A u s f x).
Proof. exact (fun_ext (fun x' : A => @lem3755896 A u s x' f x)). Qed.
Lemma lem3755898 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755899 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term307 A u s f x) = (term277 A u s f x).
Proof. exact (MK_COMB (@lem3755898 A) (@lem3755897 A u s f x)). Qed.
Lemma lem3755900 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3755901 {A : Type'} (u : type1402 A) (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term308 A u s f x) = (term295 A u s f x).
Proof. exact (MK_COMB (@lem3755900) (@lem3755899 A u s f x)). Qed.
Lemma lem3755902 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term309 A s u x) = (term246 A s u x).
Proof. exact (eq_refl (term309 A s u x)). Qed.
Lemma lem3755903 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term310 A s u) = (term255 A s u).
Proof. exact (fun_ext (fun x : A => @lem3755902 A s u x)). Qed.
Lemma lem3755904 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755905 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term311 A s u) = (term256 A s u).
Proof. exact (MK_COMB (@lem3755904 A) (@lem3755903 A s u)). Qed.
Lemma lem3755906 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) : (term303 A f x s u) = (term297 A f x s u).
Proof. exact (MK_COMB (@lem3755901 A u s f x) (@lem3755905 A s u)). Qed.
Lemma lem3755907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3755908 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) : (term312 A f x s u) = (term313 A f x s u).
Proof. exact (MK_COMB (@lem3755907) (@lem3755906 A f x s u)). Qed.
Lemma lem3755909 {A : Type'} (u : type1402 A) (s : A -> Prop) (x : A) (f : type686 A) (x' : A -> Prop) : (term305 A u s f x' x) = (term274 A u s x f x').
Proof. exact (eq_refl (term305 A u s f x' x)). Qed.
Lemma lem3755910 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3755911 {A : Type'} (u : type1402 A) (s : A -> Prop) (x : A) (f : type686 A) (x' : A -> Prop) : (term314 A u s f x' x) = (term315 A u s x f x').
Proof. exact (MK_COMB (@lem3755910) (@lem3755909 A u s x f x')). Qed.
Lemma lem3755912 {A : Type'} (s : A -> Prop) (u : type1402 A) (x : A) : (term309 A s u x) = (term246 A s u x).
Proof. exact (eq_refl (term309 A s u x)). Qed.
Lemma lem3755913 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) (x' : A) : (term316 A f x s u x') = (term317 A f x s u x').
Proof. exact (MK_COMB (@lem3755911 A u s x' f x) (@lem3755912 A s u x')). Qed.
Lemma lem3755914 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) : (term318 A f x s u) = (term319 A f x s u).
Proof. exact (fun_ext (fun x' : A => @lem3755913 A f x s u x')). Qed.
Lemma lem3755915 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3755916 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) : (term304 A f x s u) = (term320 A f x s u).
Proof. exact (MK_COMB (@lem3755915 A) (@lem3755914 A f x s u)). Qed.
Lemma lem3755917 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) : ((term303 A f x s u) = (term304 A f x s u)) = ((term297 A f x s u) = (term320 A f x s u)).
Proof. exact (MK_COMB (@lem3755908 A f x s u) (@lem3755916 A f x s u)). Qed.
Lemma lem3755918 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) : (term297 A f x s u) = (term320 A f x s u).
Proof. exact (EQ_MP (@lem3755917 A f x s u) (@lem3755895 A f x s u)). Qed.
Lemma lem3755919 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term299 A f s u) = (term321 A f s u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3755918 A f x s u)). Qed.
Lemma lem3755920 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3755921 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term300 A f s u) = (term322 A f s u).
Proof. exact (MK_COMB (@lem3755920 A) (@lem3755919 A f s u)). Qed.
Lemma lem3755922 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term281 A f s u) = (term322 A f s u).
Proof. exact (TRANS (@lem3755891 A f s u) (@lem3755921 A f s u)). Qed.
Lemma lem3755924 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term260 A f s u) = (term322 A f s u).
Proof. exact (TRANS (@lem3755865 A f s u) (@lem3755922 A f s u)). Qed.
Lemma lem3755925 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term215 A f s u) = (term322 A f s u).
Proof. exact (TRANS (@lem3755677 A f s u) (@lem3755924 A f s u)). Qed.
Lemma lem3755926 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term215 A f s u) : term322 A f s u.
Proof. exact (EQ_MP (@lem3755925 A f s u) (@lem3755544 A f s u h1)). Qed.
Lemma lem3755927 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) (h1 : term320 A f x s u) : term320 A f x s u.
Proof. exact (h1). Qed.
Lemma lem3755928 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term317 A f x s u x') : term317 A f x s u x'.
Proof. exact (h1). Qed.
Lemma lem3755931 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3755938 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3755939 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3755938 A Prop f x). Qed.
Lemma lem3755941 {A : Type'} (u : type1402 A) (x : A) : (u x x) = (term323 A u x).
Proof. exact (@lem3755939 A (u x) x). Qed.
Lemma lem3755948 {A : Type'} (f : type686 A) (u : type1402 A) (x : A) : (term131 A f u x) = (term131 A f u x).
Proof. exact (eq_refl (term131 A f u x)). Qed.
Lemma lem3755949 {A : Type'} (f : type686 A) (u : type1402 A) (x : A) : (term134 A f u x) = (term324 A f u x).
Proof. exact (MK_COMB (@lem3755948 A f u x) (@lem3755941 A u x)). Qed.
Lemma lem3755950 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3755955 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3755956 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3755955 A Prop f x). Qed.
Lemma lem3755958 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3755956 A s x). Qed.
Lemma lem3755959 {A : Type'} (s : A -> Prop) (x : A) : (term325 A s x) = (term326 A s x).
Proof. exact (MK_COMB (@lem3755950) (@lem3755958 A s x)). Qed.
Lemma lem3755960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3755961 {A : Type'} (s : A -> Prop) (x : A) : (term327 A s x) = (term328 A s x).
Proof. exact (MK_COMB (@lem3755960) (@lem3755959 A s x)). Qed.
Lemma lem3755962 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) (x : A) : (term216 A s f u x) = (term329 A s f u x).
Proof. exact (MK_COMB (@lem3755961 A s x) (@lem3755949 A f u x)). Qed.
Lemma lem3755963 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term217 A s f u) = (term330 A s f u).
Proof. exact (fun_ext (fun x : A => @lem3755962 A s f u x)). Qed.
Lemma lem3755964 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3755965 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term218 A s f u) = (term331 A s f u).
Proof. exact (MK_COMB (@lem3755964 A) (@lem3755963 A s f u)). Qed.
Lemma lem3755966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3755967 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) : (term219 A s f u) = (term332 A s f u).
Proof. exact (MK_COMB (@lem3755966) (@lem3755965 A s f u)). Qed.
Lemma lem3755968 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) : (term220 A f u s) = (term333 A f u s).
Proof. exact (MK_COMB (@lem3755967 A s f u) (@lem3755931 A s)). Qed.
Lemma lem3755969 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term333 A f u s.
Proof. exact (EQ_MP (@lem3755968 A f u s) (@lem3755615 A f u s h1)). Qed.
Lemma lem3755970 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3755977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3755978 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3755977 A Prop f x). Qed.
Lemma lem3755980 {A : Type'} (u : type1402 A) (x'' : A) (x' : A) : (u x'' x') = (term334 A u x'' x').
Proof. exact (@lem3755978 A (u x'') x'). Qed.
Lemma lem3755981 {A : Type'} (u : type1402 A) (x'' : A) (x' : A) : (term335 A u x'' x') = (term336 A u x'' x').
Proof. exact (MK_COMB (@lem3755970) (@lem3755980 A u x'' x')). Qed.
Lemma lem3755982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3755987 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3755988 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3755987 A Prop f x). Qed.
Lemma lem3755990 {A : Type'} (s : A -> Prop) (x'' : A) : (s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem3755988 A s x''). Qed.
Lemma lem3755991 {A : Type'} (s : A -> Prop) (x'' : A) : (term325 A s x'') = (term326 A s x'').
Proof. exact (MK_COMB (@lem3755982) (@lem3755990 A s x'')). Qed.
Lemma lem3755992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3755993 {A : Type'} (s : A -> Prop) (x'' : A) : (term327 A s x'') = (term328 A s x'').
Proof. exact (MK_COMB (@lem3755992) (@lem3755991 A s x'')). Qed.
Lemma lem3755994 {A : Type'} (s : A -> Prop) (u : type1402 A) (x'' : A) (x' : A) : (term235 A s u x'' x') = (term337 A s u x'' x').
Proof. exact (MK_COMB (@lem3755993 A s x'') (@lem3755981 A u x'' x')). Qed.
Lemma lem3755995 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) : (term243 A s u x') = (term338 A s u x').
Proof. exact (fun_ext (fun x'' : A => @lem3755994 A s u x'' x')). Qed.
Lemma lem3755996 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3755997 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) : (term244 A s u x') = (term339 A s u x').
Proof. exact (MK_COMB (@lem3755996 A) (@lem3755995 A s u x')). Qed.
Lemma lem3756002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3756003 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3756002 A Prop f x). Qed.
Lemma lem3756005 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3756003 A s x'). Qed.
Lemma lem3756006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3756007 {A : Type'} (s : A -> Prop) (x' : A) : (term180 A s x') = (term340 A s x').
Proof. exact (MK_COMB (@lem3756006) (@lem3756005 A s x')). Qed.
Lemma lem3756008 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) : (term246 A s u x') = (term341 A s u x').
Proof. exact (MK_COMB (@lem3756007 A s x') (@lem3755997 A s u x')). Qed.
Lemma lem3756013 {A : Type'} (f : type686 A) (x : A -> Prop) : (term221 A f x) = (term221 A f x).
Proof. exact (eq_refl (term221 A f x)). Qed.
Lemma lem3756018 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3756019 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3756018 A Prop f x). Qed.
Lemma lem3756021 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3756019 A s x'). Qed.
Lemma lem3756030 {A : Type'} (x : A -> Prop) (u : type1402 A) (x' : A) : (term146 A x u x') = (term146 A x u x').
Proof. exact (eq_refl (term146 A x u x')). Qed.
Lemma lem3756031 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) (x' : A) : (term148 A x u s x') = (term342 A x u s x').
Proof. exact (MK_COMB (@lem3756030 A x u x') (@lem3756021 A s x')). Qed.
Lemma lem3756032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3756033 {A : Type'} (x : A -> Prop) (u : type1402 A) (s : A -> Prop) (x' : A) : (term272 A x u s x') = (term343 A x u s x').
Proof. exact (MK_COMB (@lem3756032) (@lem3756031 A x u s x')). Qed.
Lemma lem3756034 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) : (term274 A u s x' f x) = (term344 A u s x' f x).
Proof. exact (MK_COMB (@lem3756033 A x u s x') (@lem3756013 A f x)). Qed.
Lemma lem3756035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3756036 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) : (term315 A u s x' f x) = (term345 A u s x' f x).
Proof. exact (MK_COMB (@lem3756035) (@lem3756034 A u s x' f x)). Qed.
Lemma lem3756037 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) (x' : A) : (term317 A f x s u x') = (term346 A f x s u x').
Proof. exact (MK_COMB (@lem3756036 A u s x' f x) (@lem3756008 A s u x')). Qed.
Lemma lem3756038 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term317 A f x s u x') : term346 A f x s u x'.
Proof. exact (EQ_MP (@lem3756037 A f x s u x') (@lem3755928 A f x s u x' h1)). Qed.
Lemma lem3756040 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term331 A s f u.
Proof. exact (proj1 (@lem3755969 A f u s h1)). Qed.
Lemma lem3756041 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : term344 A u s x' f x.
Proof. exact (h1). Qed.
Lemma lem3756042 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term341 A s u x'.
Proof. exact (h1). Qed.
Lemma lem3756044 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : term342 A x u s x'.
Proof. exact (proj1 (@lem3756041 A u s x' f x h1)). Qed.
Lemma lem3756047 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term339 A s u x'.
Proof. exact (proj2 (@lem3756042 A s u x' h1)). Qed.
Lemma lem3756066 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x : A) : (term329 A s f u x) = (term347 A f s u x).
Proof. exact (@lem19490 (term129 A f u x) (term326 A s x) (term323 A u x)). Qed.
Lemma lem3756067 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term330 A s f u) = (term348 A f s u).
Proof. exact (fun_ext (fun x : A => @lem3756066 A f s u x)). Qed.
Lemma lem3756068 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3756070 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term331 A s f u) = (term349 A f s u).
Proof. exact (MK_COMB (@lem3756068 A) (@lem3756067 A f s u)). Qed.
Lemma lem3756071 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term349 A f s u.
Proof. exact (EQ_MP (@lem3756070 A f s u) (@lem3756040 A f u s h1)). Qed.
Lemma lem3756105 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x : A) : (term329 A s f u x) = (term347 A f s u x).
Proof. exact (@lem19490 (term129 A f u x) (term326 A s x) (term323 A u x)). Qed.
Lemma lem3756106 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term330 A s f u) = (term348 A f s u).
Proof. exact (fun_ext (fun x : A => @lem3756105 A f s u x)). Qed.
Lemma lem3756107 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3756109 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term331 A s f u) = (term349 A f s u).
Proof. exact (MK_COMB (@lem3756107 A) (@lem3756106 A f s u)). Qed.
Lemma lem3756110 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term349 A f s u.
Proof. exact (EQ_MP (@lem3756109 A f s u) (@lem3756040 A f u s h1)). Qed.
Lemma lem3756126 {A : Type'} (s : A -> Prop) (u : type1402 A) (x'' : A) (x' : A) : (term337 A s u x'' x') = (term337 A s u x'' x').
Proof. exact (eq_refl (term337 A s u x'' x')). Qed.
Lemma lem3756127 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) : (term338 A s u x') = (term338 A s u x').
Proof. exact (fun_ext (fun x'' : A => @lem3756126 A s u x'' x')). Qed.
Lemma lem3756128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3756130 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) : (term339 A s u x') = (term339 A s u x').
Proof. exact (MK_COMB (@lem3756128 A) (@lem3756127 A s u x')). Qed.
Lemma lem3756131 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term339 A s u x'.
Proof. exact (EQ_MP (@lem3756130 A s u x') (@lem3756047 A s u x' h1)). Qed.
Lemma lem3756132 {A : Type'} (_43188 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term350 A f s u _43188.
Proof. exact (@lem3756071 A f u s h1 _43188). Qed.
Lemma lem3756133 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (_43188 : A) : (term350 A f s u _43188) = (term347 A f s u _43188).
Proof. exact (eq_refl (term350 A f s u _43188)). Qed.
Lemma lem3756134 {A : Type'} (_43188 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term347 A f s u _43188.
Proof. exact (EQ_MP (@lem3756133 A f s u _43188) (@lem3756132 A _43188 f u s h1)). Qed.
Lemma lem3756135 {A : Type'} (_43189 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term350 A f s u _43189.
Proof. exact (@lem3756110 A f u s h1 _43189). Qed.
Lemma lem3756136 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (_43189 : A) : (term350 A f s u _43189) = (term347 A f s u _43189).
Proof. exact (eq_refl (term350 A f s u _43189)). Qed.
Lemma lem3756137 {A : Type'} (_43189 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term347 A f s u _43189.
Proof. exact (EQ_MP (@lem3756136 A f s u _43189) (@lem3756135 A _43189 f u s h1)). Qed.
Lemma lem3756138 {A : Type'} (_43190 : A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term351 A s u x' _43190.
Proof. exact (@lem3756131 A s u x' h1 _43190). Qed.
Lemma lem3756139 {A : Type'} (s : A -> Prop) (u : type1402 A) (_43190 : A) (x' : A) : (term351 A s u x' _43190) = (term337 A s u _43190 x').
Proof. exact (eq_refl (term351 A s u x' _43190)). Qed.
Lemma lem3756148 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : term221 A f x.
Proof. exact (proj2 (@lem3756041 A u s x' f x h1)). Qed.
Lemma lem3756150 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : x = (u x').
Proof. exact (proj1 (@lem3756044 A u s x' f x h1)). Qed.
Lemma lem3756174 {A : Type'} (_43190 : A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term337 A s u _43190 x'.
Proof. exact (EQ_MP (@lem3756139 A s u _43190 x') (@lem3756138 A _43190 s u x' h1)). Qed.
Lemma lem3756186 {A : Type'} (_43189 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term352 A s u _43189.
Proof. exact (proj2 (@lem3756137 A _43189 f u s h1)). Qed.
Lemma lem3756215 {A : Type'} (f : type686 A) : (term353 A f) = (term353 A f).
Proof. exact (eq_refl (term353 A f)). Qed.
Lemma lem3756216 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : (term354 A f x) = (term355 A f u x').
Proof. exact (MK_COMB (@lem3756215 A f) (@lem3756150 A u s x' f x h1)). Qed.
Lemma lem3756217 {A : Type'} (f : type686 A) (u : type1402 A) (x' : A) : (term355 A f u x') = (term356 A f u x').
Proof. exact (eq_refl (term355 A f u x')). Qed.
Lemma lem3756218 {A : Type'} (f : type686 A) (x : A -> Prop) : (term357 A f x) = (term357 A f x).
Proof. exact (eq_refl (term357 A f x)). Qed.
Lemma lem3756219 {A : Type'} (x : A -> Prop) (f : type686 A) (u : type1402 A) (x' : A) : ((term354 A f x) = (term355 A f u x')) = ((term354 A f x) = (term356 A f u x')).
Proof. exact (MK_COMB (@lem3756218 A f x) (@lem3756217 A f u x')). Qed.
Lemma lem3756220 {A : Type'} (f : type686 A) (x : A -> Prop) : (term354 A f x) = (term221 A f x).
Proof. exact (eq_refl (term354 A f x)). Qed.
Lemma lem3756221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3756222 {A : Type'} (f : type686 A) (x : A -> Prop) : (term357 A f x) = (term358 A f x).
Proof. exact (MK_COMB (@lem3756221) (@lem3756220 A f x)). Qed.
Lemma lem3756223 {A : Type'} (f : type686 A) (u : type1402 A) (x' : A) : (term356 A f u x') = (term356 A f u x').
Proof. exact (eq_refl (term356 A f u x')). Qed.
Lemma lem3756224 {A : Type'} (x : A -> Prop) (f : type686 A) (u : type1402 A) (x' : A) : ((term354 A f x) = (term356 A f u x')) = ((term221 A f x) = (term356 A f u x')).
Proof. exact (MK_COMB (@lem3756222 A f x) (@lem3756223 A f u x')). Qed.
Lemma lem3756225 {A : Type'} (x : A -> Prop) (f : type686 A) (u : type1402 A) (x' : A) : ((term354 A f x) = (term355 A f u x')) = ((term221 A f x) = (term356 A f u x')).
Proof. exact (TRANS (@lem3756219 A x f u x') (@lem3756224 A x f u x')). Qed.
Lemma lem3756226 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : (term221 A f x) = (term356 A f u x').
Proof. exact (EQ_MP (@lem3756225 A x f u x') (@lem3756216 A u s x' f x h1)). Qed.
Lemma lem3756227 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : term356 A f u x'.
Proof. exact (EQ_MP (@lem3756226 A u s x' f x h1) (@lem3756148 A u s x' f x h1)). Qed.
Lemma lem3756255 {A : Type'} (_43188 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term359 A s f u _43188.
Proof. exact (proj1 (@lem3756134 A _43188 f u s h1)). Qed.
Lemma lem3756271 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : @I (A -> Prop) s x'.
Proof. exact (proj2 (@lem3756044 A u s x' f x h1)). Qed.
Lemma lem3756272 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : term360 A s x'.
Proof. exact (fun h0 : term326 A s x' => @lem3756271 A u s x' f x h1). Qed.
Lemma lem3756274 (p : Prop) : (term361 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756275 {A : Type'} (s : A -> Prop) (x' : A) : (term360 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3756274 (@I (A -> Prop) s x')). Qed.
Lemma lem3756276 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem3756275 A s x') (@lem3756272 A u s x' f x h1)). Qed.
Lemma lem3756282 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3756283 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (_43188 : A) : (term359 A s f u _43188) = (term362 A f u s _43188).
Proof. exact (@lem3756282 (term129 A f u _43188) (term326 A s _43188)). Qed.
Lemma lem3756289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3756290 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (_43188 : A) : (term363 A s f u _43188) = (term364 A f u s _43188).
Proof. exact (MK_COMB (@lem3756289) (@lem3756283 A f u s _43188)). Qed.
Lemma lem3756296 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (_43188 : A) : (term362 A f u s _43188) = (term362 A f u s _43188).
Proof. exact (eq_refl (term362 A f u s _43188)). Qed.
Lemma lem3756297 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (_43188 : A) : ((term359 A s f u _43188) = (term362 A f u s _43188)) = ((term362 A f u s _43188) = (term362 A f u s _43188)).
Proof. exact (MK_COMB (@lem3756290 A f u s _43188) (@lem3756296 A f u s _43188)). Qed.
Lemma lem3756299 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3756300 (x : Prop) : (x = x) = True.
Proof. exact (@lem3756299 Prop x). Qed.
Lemma lem3756301 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (_43188 : A) : ((term362 A f u s _43188) = (term362 A f u s _43188)) = True.
Proof. exact (@lem3756300 (term362 A f u s _43188)). Qed.
Lemma lem3756302 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (_43188 : A) : ((term359 A s f u _43188) = (term362 A f u s _43188)) = True.
Proof. exact (TRANS (@lem3756297 A f u s _43188) (@lem3756301 A f u s _43188)). Qed.
Lemma lem3756303 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (_43188 : A) : True = ((term359 A s f u _43188) = (term362 A f u s _43188)).
Proof. exact (SYM (@lem3756302 A f u s _43188)). Qed.
Lemma lem3756304 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (_43188 : A) : (term359 A s f u _43188) = (term362 A f u s _43188).
Proof. exact (EQ_MP (@lem3756303 A f u s _43188) (@lem0)). Qed.
Lemma lem3756305 {A : Type'} (_43188 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term362 A f u s _43188.
Proof. exact (EQ_MP (@lem3756304 A f u s _43188) (@lem3756255 A _43188 f u s h1)). Qed.
Lemma lem3756307 (b : Prop) (a : Prop) : (a \/ b) = (term365 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3756308 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) (_43188 : A) : (term362 A f u s _43188) = (term366 A s f u _43188).
Proof. exact (@lem3756307 (term326 A s _43188) (term129 A f u _43188)). Qed.
Lemma lem3756310 (a : Prop) : (term201 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3756311 {A : Type'} (s : A -> Prop) (_43188 : A) : (term367 A s _43188) = (@I (A -> Prop) s _43188).
Proof. exact (@lem3756310 (@I (A -> Prop) s _43188)). Qed.
Lemma lem3756312 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3756313 {A : Type'} (s : A -> Prop) (_43188 : A) : (term368 A s _43188) = (term369 A s _43188).
Proof. exact (MK_COMB (@lem3756312) (@lem3756311 A s _43188)). Qed.
Lemma lem3756314 {A : Type'} (f : type686 A) (u : type1402 A) (_43188 : A) : (term129 A f u _43188) = (term129 A f u _43188).
Proof. exact (eq_refl (term129 A f u _43188)). Qed.
Lemma lem3756315 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) (_43188 : A) : (term366 A s f u _43188) = (term370 A s f u _43188).
Proof. exact (MK_COMB (@lem3756313 A s _43188) (@lem3756314 A f u _43188)). Qed.
Lemma lem3756316 {A : Type'} (s : A -> Prop) (f : type686 A) (u : type1402 A) (_43188 : A) : (term362 A f u s _43188) = (term370 A s f u _43188).
Proof. exact (TRANS (@lem3756308 A s f u _43188) (@lem3756315 A s f u _43188)). Qed.
Lemma lem3756319 {A : Type'} (_43188 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term370 A s f u _43188.
Proof. exact (EQ_MP (@lem3756316 A s f u _43188) (@lem3756305 A _43188 f u s h1)). Qed.
Lemma lem3756320 {A : Type'} (_43188 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term370 A s f u _43188.
Proof. exact (@lem3756319 A _43188 f u s h1). Qed.
Lemma lem3756321 {A : Type'} (x' : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term370 A s f u x'.
Proof. exact (@lem3756320 A x' f u s h1). Qed.
Lemma lem3756324 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term140 A f u s) (h2 : term344 A u s x' f x) : term129 A f u x'.
Proof. exact (@lem3756321 A x' f u s h1 (@lem3756276 A u s x' f x h2)). Qed.
Lemma lem3756325 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term140 A f u s) (h2 : term344 A u s x' f x) : term371 A f u x'.
Proof. exact (fun h0 : term356 A f u x' => @lem3756324 A u s x' f x h1 h2). Qed.
Lemma lem3756327 (p : Prop) : (term361 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756328 {A : Type'} (f : type686 A) (u : type1402 A) (x' : A) : (term371 A f u x') = (term129 A f u x').
Proof. exact (@lem3756327 (term129 A f u x')). Qed.
Lemma lem3756329 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term140 A f u s) (h2 : term344 A u s x' f x) : term129 A f u x'.
Proof. exact (EQ_MP (@lem3756328 A f u x') (@lem3756325 A u s x' f x h1 h2)). Qed.
Lemma lem3756332 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3756334 {A : Type'} (f : type686 A) (u : type1402 A) (x' : A) : (term356 A f u x') = (term372 A f u x').
Proof. exact (@lem3756332 (term129 A f u x')). Qed.
Lemma lem3756337 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term344 A u s x' f x) : term372 A f u x'.
Proof. exact (EQ_MP (@lem3756334 A f u x') (@lem3756227 A u s x' f x h1)). Qed.
Lemma lem3756340 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term140 A f u s) (h2 : term344 A u s x' f x) : False.
Proof. exact (@lem3756337 A u s x' f x h2 (@lem3756329 A u s x' f x h1 h2)). Qed.
Lemma lem3756341 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term140 A f u s) (h2 : term344 A u s x' f x) : term373.
Proof. exact (fun h0 : ~ False => @lem3756340 A u s x' f x h1 h2). Qed.
Lemma lem3756343 (p : Prop) : (term361 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756344 : term373 = False.
Proof. exact (@lem3756343 False). Qed.
Lemma lem3756347 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem3756042 A s u x' h1)). Qed.
Lemma lem3756348 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term360 A s x'.
Proof. exact (fun h0 : term326 A s x' => @lem3756347 A s u x' h1). Qed.
Lemma lem3756350 (p : Prop) : (term361 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756351 {A : Type'} (s : A -> Prop) (x' : A) : (term360 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3756350 (@I (A -> Prop) s x')). Qed.
Lemma lem3756352 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem3756351 A s x') (@lem3756348 A s u x' h1)). Qed.
Lemma lem3756354 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem3756042 A s u x' h1)). Qed.
Lemma lem3756355 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term360 A s x'.
Proof. exact (fun h0 : term326 A s x' => @lem3756354 A s u x' h1). Qed.
Lemma lem3756357 (p : Prop) : (term361 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756358 {A : Type'} (s : A -> Prop) (x' : A) : (term360 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3756357 (@I (A -> Prop) s x')). Qed.
Lemma lem3756359 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem3756358 A s x') (@lem3756355 A s u x' h1)). Qed.
Lemma lem3756365 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3756366 {A : Type'} (u : type1402 A) (s : A -> Prop) (_43189 : A) : (term352 A s u _43189) = (term374 A u s _43189).
Proof. exact (@lem3756365 (term323 A u _43189) (term326 A s _43189)). Qed.
Lemma lem3756372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3756373 {A : Type'} (u : type1402 A) (s : A -> Prop) (_43189 : A) : (term375 A s u _43189) = (term376 A u s _43189).
Proof. exact (MK_COMB (@lem3756372) (@lem3756366 A u s _43189)). Qed.
Lemma lem3756379 {A : Type'} (u : type1402 A) (s : A -> Prop) (_43189 : A) : (term374 A u s _43189) = (term374 A u s _43189).
Proof. exact (eq_refl (term374 A u s _43189)). Qed.
Lemma lem3756380 {A : Type'} (u : type1402 A) (s : A -> Prop) (_43189 : A) : ((term352 A s u _43189) = (term374 A u s _43189)) = ((term374 A u s _43189) = (term374 A u s _43189)).
Proof. exact (MK_COMB (@lem3756373 A u s _43189) (@lem3756379 A u s _43189)). Qed.
Lemma lem3756382 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3756383 (x : Prop) : (x = x) = True.
Proof. exact (@lem3756382 Prop x). Qed.
Lemma lem3756384 {A : Type'} (u : type1402 A) (s : A -> Prop) (_43189 : A) : ((term374 A u s _43189) = (term374 A u s _43189)) = True.
Proof. exact (@lem3756383 (term374 A u s _43189)). Qed.
Lemma lem3756385 {A : Type'} (u : type1402 A) (s : A -> Prop) (_43189 : A) : ((term352 A s u _43189) = (term374 A u s _43189)) = True.
Proof. exact (TRANS (@lem3756380 A u s _43189) (@lem3756384 A u s _43189)). Qed.
Lemma lem3756386 {A : Type'} (u : type1402 A) (s : A -> Prop) (_43189 : A) : True = ((term352 A s u _43189) = (term374 A u s _43189)).
Proof. exact (SYM (@lem3756385 A u s _43189)). Qed.
Lemma lem3756387 {A : Type'} (u : type1402 A) (s : A -> Prop) (_43189 : A) : (term352 A s u _43189) = (term374 A u s _43189).
Proof. exact (EQ_MP (@lem3756386 A u s _43189) (@lem0)). Qed.
Lemma lem3756388 {A : Type'} (_43189 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term374 A u s _43189.
Proof. exact (EQ_MP (@lem3756387 A u s _43189) (@lem3756186 A _43189 f u s h1)). Qed.
Lemma lem3756390 (b : Prop) (a : Prop) : (a \/ b) = (term365 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3756391 {A : Type'} (s : A -> Prop) (u : type1402 A) (_43189 : A) : (term374 A u s _43189) = (term377 A s u _43189).
Proof. exact (@lem3756390 (term326 A s _43189) (term323 A u _43189)). Qed.
Lemma lem3756393 (a : Prop) : (term201 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3756394 {A : Type'} (s : A -> Prop) (_43189 : A) : (term367 A s _43189) = (@I (A -> Prop) s _43189).
Proof. exact (@lem3756393 (@I (A -> Prop) s _43189)). Qed.
Lemma lem3756395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3756396 {A : Type'} (s : A -> Prop) (_43189 : A) : (term368 A s _43189) = (term369 A s _43189).
Proof. exact (MK_COMB (@lem3756395) (@lem3756394 A s _43189)). Qed.
Lemma lem3756397 {A : Type'} (u : type1402 A) (_43189 : A) : (term323 A u _43189) = (term323 A u _43189).
Proof. exact (eq_refl (term323 A u _43189)). Qed.
Lemma lem3756398 {A : Type'} (s : A -> Prop) (u : type1402 A) (_43189 : A) : (term377 A s u _43189) = (term378 A s u _43189).
Proof. exact (MK_COMB (@lem3756396 A s _43189) (@lem3756397 A u _43189)). Qed.
Lemma lem3756399 {A : Type'} (s : A -> Prop) (u : type1402 A) (_43189 : A) : (term374 A u s _43189) = (term378 A s u _43189).
Proof. exact (TRANS (@lem3756391 A s u _43189) (@lem3756398 A s u _43189)). Qed.
Lemma lem3756402 {A : Type'} (_43189 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term378 A s u _43189.
Proof. exact (EQ_MP (@lem3756399 A s u _43189) (@lem3756388 A _43189 f u s h1)). Qed.
Lemma lem3756403 {A : Type'} (_43189 : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term378 A s u _43189.
Proof. exact (@lem3756402 A _43189 f u s h1). Qed.
Lemma lem3756404 {A : Type'} (x' : A) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term378 A s u x'.
Proof. exact (@lem3756403 A x' f u s h1). Qed.
Lemma lem3756407 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term140 A f u s) (h2 : term341 A s u x') : term323 A u x'.
Proof. exact (@lem3756404 A x' f u s h1 (@lem3756359 A s u x' h2)). Qed.
Lemma lem3756408 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term140 A f u s) (h2 : term341 A s u x') : term379 A u x'.
Proof. exact (fun h0 : term380 A u x' => @lem3756407 A f s u x' h1 h2). Qed.
Lemma lem3756410 (p : Prop) : (term361 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756411 {A : Type'} (u : type1402 A) (x' : A) : (term379 A u x') = (term323 A u x').
Proof. exact (@lem3756410 (term323 A u x')). Qed.
Lemma lem3756412 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term140 A f u s) (h2 : term341 A s u x') : term323 A u x'.
Proof. exact (EQ_MP (@lem3756411 A u x') (@lem3756408 A f s u x' h1 h2)). Qed.
Lemma lem3756414 (a : Prop) (b : Prop) : (term381 a b) = (term382 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3756415 {A : Type'} (s : A -> Prop) (u : type1402 A) (_43190 : A) (x' : A) : (term337 A s u _43190 x') = (term383 A s u _43190 x').
Proof. exact (@lem3756414 (@I (A -> Prop) s _43190) (term334 A u _43190 x')). Qed.
Lemma lem3756417 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3756418 {A : Type'} (s : A -> Prop) (u : type1402 A) (_43190 : A) (x' : A) : (term383 A s u _43190 x') = (term384 A s u _43190 x').
Proof. exact (@lem3756417 (term385 A s u _43190 x')). Qed.
Lemma lem3756419 {A : Type'} (s : A -> Prop) (u : type1402 A) (_43190 : A) (x' : A) : (term337 A s u _43190 x') = (term384 A s u _43190 x').
Proof. exact (TRANS (@lem3756415 A s u _43190 x') (@lem3756418 A s u _43190 x')). Qed.
Lemma lem3756421 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term140 A f u s) (h2 : term341 A s u x') : term386 A s u x'.
Proof. exact (conj (@lem3756352 A s u x' h2) (@lem3756412 A f s u x' h1 h2)). Qed.
Lemma lem3756423 {A : Type'} (_43190 : A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term384 A s u _43190 x'.
Proof. exact (EQ_MP (@lem3756419 A s u _43190 x') (@lem3756174 A _43190 s u x' h1)). Qed.
Lemma lem3756424 {A : Type'} (_43190 : A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term384 A s u _43190 x'.
Proof. exact (@lem3756423 A _43190 s u x' h1). Qed.
Lemma lem3756425 {A : Type'} (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term341 A s u x') : term387 A s u x'.
Proof. exact (@lem3756424 A x' s u x' h1). Qed.
Lemma lem3756428 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term140 A f u s) (h2 : term341 A s u x') : False.
Proof. exact (@lem3756425 A s u x' h2 (@lem3756421 A f s u x' h1 h2)). Qed.
Lemma lem3756429 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term140 A f u s) (h2 : term341 A s u x') : term373.
Proof. exact (fun h0 : ~ False => @lem3756428 A f s u x' h1 h2). Qed.
Lemma lem3756431 (p : Prop) : (term361 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756432 : term373 = False.
Proof. exact (@lem3756431 False). Qed.
Lemma lem3756433 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term140 A f u s) (h2 : term341 A s u x') : False.
Proof. exact (EQ_MP (@lem3756432) (@lem3756429 A f s u x' h1 h2)). Qed.
Lemma lem3756434 {A : Type'} (u : type1402 A) (s : A -> Prop) (x' : A) (f : type686 A) (x : A -> Prop) (h1 : term140 A f u s) (h2 : term344 A u s x' f x) : False.
Proof. exact (EQ_MP (@lem3756344) (@lem3756341 A u s x' f x h1 h2)). Qed.
Lemma lem3756435 {A : Type'} (f : type686 A) (x : A -> Prop) (s : A -> Prop) (u : type1402 A) (x' : A) (h1 : term140 A f u s) (h2 : term317 A f x s u x') : False.
Proof. exact (or_elim (@lem3756038 A f x s u x' h2) (fun h0 : term344 A u s x' f x => @lem3756434 A u s x' f x h1 h0) (fun h0 : term341 A s u x' => @lem3756433 A f s u x' h1 h0)). Qed.
Lemma lem3756436 {A : Type'} (x : A -> Prop) (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term320 A f x s u) (h2 : term140 A f u s) : False.
Proof. exact (ex_elim (@lem3755927 A f x s u h1) (fun x' : A => fun h0 : term319 A f x s u x' => @lem3756435 A f x s u x' h2 h0)). Qed.
Lemma lem3756437 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term215 A f s u) (h2 : term140 A f u s) : False.
Proof. exact (ex_elim (@lem3755926 A f s u h1) (fun x : A -> Prop => fun h0 : term321 A f s u x => @lem3756436 A x f u s h0 h2)). Qed.
Lemma lem3756438 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term215 A f s u) (h2 : term140 A f u s) : (term215 A f s u) = False.
Proof. exact (prop_ext (fun h3 : term215 A f s u => @lem3756437 A f u s h1 h2) (fun h3 : False => @lem3755544 A f s u h1)). Qed.
Lemma lem3756439 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term215 A f s u) (h2 : term140 A f u s) : False.
Proof. exact (EQ_MP (@lem3756438 A f u s h1 h2) (@lem3755544 A f s u h1)). Qed.
Lemma lem3756440 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term214 A f s u.
Proof. exact (fun h0 : term215 A f s u => @lem3756439 A f u s h0 h1). Qed.
Lemma lem3756441 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term140 A f u s) : term192 A f s u.
Proof. exact (EQ_MP (@lem3755543 A f s u) (@lem3756440 A f u s h1)). Qed.
Lemma lem3756442 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term193 A f s u.
Proof. exact (fun h0 : term140 A f u s => @lem3756441 A f u s h0). Qed.
Lemma lem3756447 {A : Type'} (s : A -> Prop) (u : type1402 A) : term205 A s u.
Proof. exact (fun f : type686 A => @lem3756442 A f s u). Qed.
Lemma lem3756452 {A : Type'} (u : type1402 A) : term209 A u.
Proof. exact (fun s : A -> Prop => @lem3756447 A s u). Qed.
Lemma lem3756457 {A : Type'} : term213 A.
Proof. exact (fun u : type1402 A => @lem3756452 A u). Qed.
Lemma lem3756458 {A : Type'} : term212 A.
Proof. exact (EQ_MP (@lem3755538 A) (@lem3756457 A)). Qed.
Lemma lem3756459 {A : Type'} (u : type1402 A) : term388 A u.
Proof. exact (@lem3756458 A u). Qed.
Lemma lem3756460 {A : Type'} (u : type1402 A) : (term388 A u) = (term208 A u).
Proof. exact (eq_refl (term388 A u)). Qed.
Lemma lem3756461 {A : Type'} (u : type1402 A) : term208 A u.
Proof. exact (EQ_MP (@lem3756460 A u) (@lem3756459 A u)). Qed.
Lemma lem3756462 {A : Type'} (u : type1402 A) (s : A -> Prop) : term389 A u s.
Proof. exact (@lem3756461 A u s). Qed.
Lemma lem3756463 {A : Type'} (s : A -> Prop) (u : type1402 A) : (term389 A u s) = (term204 A s u).
Proof. exact (eq_refl (term389 A u s)). Qed.
Lemma lem3756464 {A : Type'} (s : A -> Prop) (u : type1402 A) : term204 A s u.
Proof. exact (EQ_MP (@lem3756463 A s u) (@lem3756462 A u s)). Qed.
Lemma lem3756465 {A : Type'} (s : A -> Prop) (u : type1402 A) (f : type686 A) : term390 A s u f.
Proof. exact (@lem3756464 A s u f). Qed.
Lemma lem3756466 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : (term390 A s u f) = (term195 A f s u).
Proof. exact (eq_refl (term390 A s u f)). Qed.
Lemma lem3756467 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term195 A f s u.
Proof. exact (EQ_MP (@lem3756466 A f s u) (@lem3756465 A s u f)). Qed.
Lemma lem3756469 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term195 A f s u.
Proof. exact (@lem3755273 A f s u (@lem3756467 A f s u)). Qed.
Lemma lem3756470 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term196 A f s u) : False.
Proof. exact (@lem3756469 A f s u (@lem3755257 A f s u h1)). Qed.
Lemma lem3756471 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term196 A f s u) : (term196 A f s u) = False.
Proof. exact (prop_ext (fun h2 : term196 A f s u => @lem3756470 A f s u h1) (fun h2 : False => @lem3755257 A f s u h1)). Qed.
Lemma lem3756472 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) (h1 : term196 A f s u) : False.
Proof. exact (EQ_MP (@lem3756471 A f s u h1) (@lem3755257 A f s u h1)). Qed.
Lemma lem3756473 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term195 A f s u.
Proof. exact (fun h0 : term196 A f s u => @lem3756472 A f s u h0). Qed.
Lemma lem3756474 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term193 A f s u.
Proof. exact (EQ_MP (@lem3755256 A f s u) (@lem3756473 A f s u)). Qed.
Lemma lem3756475 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term126 A f s u.
Proof. exact (EQ_MP (@lem3755252 A f s u) (@lem3756474 A f s u)). Qed.
Lemma lem3756476 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type1402 A) : term125 A f s u.
Proof. exact (EQ_MP (@lem3755071 A f s u) (@lem3756475 A f s u)). Qed.
Lemma lem3756477 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term71 A s f u) (h2 : @FINITE A s) : term114 A f s u.
Proof. exact (@lem3756476 A f s u (@lem3755017 A f u s h1 h2)). Qed.
Lemma lem3756478 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term71 A s f u) (h2 : @FINITE A s) : term115 A f u s.
Proof. exact (EQ_MP (@lem3755006 A f u s h2) (@lem3756477 A f u s h1 h2)). Qed.
Lemma lem3756479 {A : Type'} (f : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term71 A s f u) (h2 : @FINITE A s) : term49 A f s.
Proof. exact (ex_intro (term391 A f s) (@IMAGE A (A -> Prop) u s) (@lem3756478 A f u s h1 h2)). Qed.
Lemma lem3756480 {A : Type'} (u : type1402 A) (f : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : term90 A u f s.
Proof. exact (fun h0 : term71 A s f u => @lem3756479 A f u s h0 h1). Qed.
Lemma lem3756485 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : term93 A f s.
Proof. exact (fun u : type1402 A => @lem3756480 A u f s h1). Qed.
Lemma lem3756486 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : term51 A f s.
Proof. exact (EQ_MP (@lem3754880 A f s) (@lem3756485 A f s h1)). Qed.
Lemma lem3756487 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : @FINITE A s) : term50 A f s.
Proof. exact (EQ_MP (@lem3754776 A f s) (@lem3756486 A f s h1)). Qed.
Lemma lem3756488 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term23 A s f) : term49 A f s.
Proof. exact (@lem3756487 A f s h1 (@lem3754741 A s f h2)). Qed.
Lemma lem3756489 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term22 A s f) : term23 A s f.
Proof. exact (proj2 (@lem3754734 A s f h1)). Qed.
Lemma lem3756490 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term22 A s f) : @FINITE A s.
Proof. exact (proj1 (@lem3754734 A s f h1)). Qed.
Lemma lem3756491 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term23 A s f) : (term23 A s f) = (term49 A f s).
Proof. exact (prop_ext (fun h3 : term23 A s f => @lem3756488 A s f h1 h2) (fun h3 : term49 A f s => @lem3754735 A s f h2)). Qed.
Lemma lem3756492 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term23 A s f) : term49 A f s.
Proof. exact (EQ_MP (@lem3756491 A s f h1 h2) (@lem3754735 A s f h2)). Qed.
Lemma lem3756493 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term23 A s f) : (@FINITE A s) = (term49 A f s).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem3756492 A s f h1 h2) (fun h3 : term49 A f s => @lem3754736 A s h1)). Qed.
Lemma lem3756494 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term23 A s f) : term49 A f s.
Proof. exact (EQ_MP (@lem3756493 A s f h1 h2) (@lem3754736 A s h1)). Qed.
Lemma lem3756495 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : (term23 A s f) = (term49 A f s).
Proof. exact (prop_ext (fun h3 : term23 A s f => @lem3756494 A s f h1 h3) (fun h3 : term49 A f s => @lem3756489 A s f h2)). Qed.
Lemma lem3756496 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE A s) (h2 : term22 A s f) : term49 A f s.
Proof. exact (EQ_MP (@lem3756495 A s f h1 h2) (@lem3756489 A s f h2)). Qed.
Lemma lem3756497 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term22 A s f) : (@FINITE A s) = (term49 A f s).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem3756496 A s f h2 h1) (fun h2 : term49 A f s => @lem3756490 A s f h1)). Qed.
Lemma lem3756498 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term22 A s f) : term49 A f s.
Proof. exact (EQ_MP (@lem3756497 A s f h1) (@lem3756490 A s f h1)). Qed.
Lemma lem3756499 {A : Type'} (f : type686 A) (s : A -> Prop) : term392 A f s.
Proof. exact (fun h0 : term22 A s f => @lem3756498 A s f h0). Qed.
Lemma lem3756504 {A : Type'} (f : type686 A) : term393 A f.
Proof. exact (fun s : A -> Prop => @lem3756499 A f s). Qed.
Lemma lem3756509 {A : Type'} : term394 A.
Proof. exact (fun f : type686 A => @lem3756504 A f). Qed.
