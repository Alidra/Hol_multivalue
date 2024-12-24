Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPPORT_SUBSET_term_abbrevs.
Require Import IN_SUPPORT_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5719677 {_119826 _119829 : Type'} (op : type1400 _119826) : term0 _119826 _119829 op.
Proof. exact (@lem5718201 _119826 _119829 op). Qed.
Lemma lem5719678 {_119826 _119829 : Type'} (op : type1400 _119826) : (term0 _119826 _119829 op) = (term1 _119826 _119829 op).
Proof. exact (eq_refl (term0 _119826 _119829 op)). Qed.
Lemma lem5719679 {_119826 _119829 : Type'} (op : type1400 _119826) : term1 _119826 _119829 op.
Proof. exact (EQ_MP (@lem5719678 _119826 _119829 op) (@lem5719677 _119826 _119829 op)). Qed.
Lemma lem5719680 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : term2 _119826 _119829 op f.
Proof. exact (@lem5719679 _119826 _119829 op f). Qed.
Lemma lem5719681 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : (term2 _119826 _119829 op f) = (term3 _119826 _119829 f op).
Proof. exact (eq_refl (term2 _119826 _119829 op f)). Qed.
Lemma lem5719682 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : term3 _119826 _119829 f op.
Proof. exact (EQ_MP (@lem5719681 _119826 _119829 f op) (@lem5719680 _119826 _119829 op f)). Qed.
Lemma lem5719683 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) (x : _119829) : term4 _119826 _119829 f op x.
Proof. exact (@lem5719682 _119826 _119829 f op x). Qed.
Lemma lem5719684 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term4 _119826 _119829 f op x) = (term5 _119826 _119829 f x op).
Proof. exact (eq_refl (term4 _119826 _119829 f op x)). Qed.
Lemma lem5719685 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : term5 _119826 _119829 f x op.
Proof. exact (EQ_MP (@lem5719684 _119826 _119829 f x op) (@lem5719683 _119826 _119829 f op x)). Qed.
Lemma lem5719686 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) (s : _119829 -> Prop) : term6 _119826 _119829 f x op s.
Proof. exact (@lem5719685 _119826 _119829 f x op s). Qed.
Lemma lem5719687 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term6 _119826 _119829 f x op s) = ((term7 _119826 _119829 x op f s) = (term8 _119826 _119829 s f x op)).
Proof. exact (eq_refl (term6 _119826 _119829 f x op s)). Qed.
Lemma lem5719689 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5719690 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem5719691 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem5719690 A s) (@lem5719689 A s)). Qed.
Lemma lem5719692 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem5719691 A s t). Qed.
Lemma lem5719693 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = ((@SUBSET A s t) = (term12 A s t)).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem5719708 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term12 A s t).
Proof. exact (EQ_MP (@lem5719693 A s t) (@lem5719692 A s t)). Qed.
Lemma lem5719709 {_119922 : Type'} (s : _119922 -> Prop) (t : _119922 -> Prop) : (@SUBSET _119922 s t) = (term12 _119922 s t).
Proof. exact (@lem5719708 _119922 s t). Qed.
Lemma lem5719710 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (s : _119922 -> Prop) : (term13 _119921 _119922 op f s) = (term14 _119921 _119922 op f s).
Proof. exact (@lem5719709 _119922 (@support _119922 _119921 op f s) s). Qed.
Lemma lem5719718 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5719719 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem5719718 p q p' q'). Qed.
Lemma lem5719720 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem5719719 p q p'). Qed.
Lemma lem5719721 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (x : _119922) (s : _119922 -> Prop) : term18 _119921 _119922 op f x s.
Proof. exact (@lem5719720 (term7 _119921 _119922 x op f s) (@IN _119922 x s)). Qed.
Lemma lem5719722 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (x : _119922) (s : _119922 -> Prop) (p' : Prop) : term19 _119921 _119922 op f x s p'.
Proof. exact (@lem5719721 _119921 _119922 op f x s p'). Qed.
Lemma lem5719723 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (x : _119922) (s : _119922 -> Prop) (p' : Prop) : (term19 _119921 _119922 op f x s p') = (term20 _119921 _119922 op f x s p').
Proof. exact (eq_refl (term19 _119921 _119922 op f x s p')). Qed.
Lemma lem5719724 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (x : _119922) (s : _119922 -> Prop) (p' : Prop) : term20 _119921 _119922 op f x s p'.
Proof. exact (EQ_MP (@lem5719723 _119921 _119922 op f x s p') (@lem5719722 _119921 _119922 op f x s p')). Qed.
Lemma lem5719725 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (x : _119922) (s : _119922 -> Prop) (p' : Prop) (q' : Prop) : term21 _119921 _119922 op f x s p' q'.
Proof. exact (@lem5719724 _119921 _119922 op f x s p' q'). Qed.
Lemma lem5719726 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (x : _119922) (s : _119922 -> Prop) (p' : Prop) (q' : Prop) : (term21 _119921 _119922 op f x s p' q') = (term22 _119921 _119922 op f x s p' q').
Proof. exact (eq_refl (term21 _119921 _119922 op f x s p' q')). Qed.
Lemma lem5719727 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (x : _119922) (s : _119922 -> Prop) (p' : Prop) (q' : Prop) : term22 _119921 _119922 op f x s p' q'.
Proof. exact (EQ_MP (@lem5719726 _119921 _119922 op f x s p' q') (@lem5719725 _119921 _119922 op f x s p' q')). Qed.
Lemma lem5719729 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term7 _119826 _119829 x op f s) = (term8 _119826 _119829 s f x op).
Proof. exact (EQ_MP (@lem5719687 _119826 _119829 s f x op) (@lem5719686 _119826 _119829 f x op s)). Qed.
Lemma lem5719730 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) : (term7 _119921 _119922 x op f s) = (term8 _119921 _119922 s f x op).
Proof. exact (@lem5719729 _119921 _119922 s f x op). Qed.
Lemma lem5719735 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) (q' : Prop) : term23 _119921 _119922 s f x op q'.
Proof. exact (@lem5719727 _119921 _119922 op f x s (term8 _119921 _119922 s f x op) q'). Qed.
Lemma lem5719736 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) (q' : Prop) : term24 _119921 _119922 s f x op q'.
Proof. exact (@lem5719735 _119921 _119922 s f x op q' (@lem5719730 _119921 _119922 s f x op)). Qed.
Lemma lem5719737 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) (h1 : term8 _119921 _119922 s f x op) : term8 _119921 _119922 s f x op.
Proof. exact (h1). Qed.
Lemma lem5719752 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) (h1 : term8 _119921 _119922 s f x op) : @IN _119922 x s.
Proof. exact (proj1 (@lem5719737 _119921 _119922 s f x op h1)). Qed.
Lemma lem5719753 {_119922 : Type'} (x : _119922) (s : _119922 -> Prop) : (@IN _119922 x s) = ((@IN _119922 x s) = True).
Proof. exact (@lem7 (@IN _119922 x s)). Qed.
Lemma lem5719756 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) (h1 : term8 _119921 _119922 s f x op) : (@IN _119922 x s) = True.
Proof. exact (EQ_MP (@lem5719753 _119922 x s) (@lem5719752 _119921 _119922 s f x op h1)). Qed.
Lemma lem5719757 {_119921 _119922 : Type'} (f : _119922 -> _119921) (op : type1400 _119921) (x : _119922) (s : _119922 -> Prop) : term25 _119921 _119922 f op x s.
Proof. exact (fun h0 : term8 _119921 _119922 s f x op => @lem5719756 _119921 _119922 s f x op h0). Qed.
Lemma lem5719758 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) : term26 _119921 _119922 s f x op.
Proof. exact (@lem5719736 _119921 _119922 s f x op True). Qed.
Lemma lem5719759 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) : (term27 _119921 _119922 op f x s) = (term28 _119921 _119922 s f x op).
Proof. exact (@lem5719758 _119921 _119922 s f x op (@lem5719757 _119921 _119922 f op x s)). Qed.
Lemma lem5719761 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5719762 {_119921 _119922 : Type'} (s : _119922 -> Prop) (f : _119922 -> _119921) (x : _119922) (op : type1400 _119921) : (term28 _119921 _119922 s f x op) = True.
Proof. exact (@lem5719761 (term8 _119921 _119922 s f x op)). Qed.
Lemma lem5719763 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (x : _119922) (s : _119922 -> Prop) : (term27 _119921 _119922 op f x s) = True.
Proof. exact (TRANS (@lem5719759 _119921 _119922 s f x op) (@lem5719762 _119921 _119922 s f x op)). Qed.
Lemma lem5719764 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (s : _119922 -> Prop) : (term29 _119921 _119922 op f s) = (term30 _119922).
Proof. exact (fun_ext (fun x : _119922 => @lem5719763 _119921 _119922 op f x s)). Qed.
Lemma lem5719765 {_119922 : Type'} : (@all _119922) = (@all _119922).
Proof. exact (eq_refl (@all _119922)). Qed.
Lemma lem5719766 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (s : _119922 -> Prop) : (term14 _119921 _119922 op f s) = (term31 _119922).
Proof. exact (MK_COMB (@lem5719765 _119922) (@lem5719764 _119921 _119922 op f s)). Qed.
Lemma lem5719768 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5719769 {_119922 : Type'} (t : Prop) : (term32 _119922 t) = t.
Proof. exact (@lem5719768 _119922 t). Qed.
Lemma lem5719770 {_119922 : Type'} : (term31 _119922) = True.
Proof. exact (@lem5719769 _119922 True). Qed.
Lemma lem5719771 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (s : _119922 -> Prop) : (term14 _119921 _119922 op f s) = True.
Proof. exact (TRANS (@lem5719766 _119921 _119922 op f s) (@lem5719770 _119922)). Qed.
Lemma lem5719772 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) (s : _119922 -> Prop) : (term13 _119921 _119922 op f s) = True.
Proof. exact (TRANS (@lem5719710 _119921 _119922 op f s) (@lem5719771 _119921 _119922 op f s)). Qed.
Lemma lem5719773 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) : (term33 _119921 _119922 op f) = (term34 _119922).
Proof. exact (fun_ext (fun s : _119922 -> Prop => @lem5719772 _119921 _119922 op f s)). Qed.
Lemma lem5719774 {_119922 : Type'} : (@all (_119922 -> Prop)) = (@all (_119922 -> Prop)).
Proof. exact (eq_refl (@all (_119922 -> Prop))). Qed.
Lemma lem5719775 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) : (term35 _119921 _119922 op f) = (term36 _119922).
Proof. exact (MK_COMB (@lem5719774 _119922) (@lem5719773 _119921 _119922 op f)). Qed.
Lemma lem5719777 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5719778 {_119922 : Type'} (t : Prop) : (term37 _119922 t) = t.
Proof. exact (@lem5719777 (_119922 -> Prop) t). Qed.
Lemma lem5719779 {_119922 : Type'} : (term36 _119922) = True.
Proof. exact (@lem5719778 _119922 True). Qed.
Lemma lem5719780 {_119921 _119922 : Type'} (op : type1400 _119921) (f : _119922 -> _119921) : (term35 _119921 _119922 op f) = True.
Proof. exact (TRANS (@lem5719775 _119921 _119922 op f) (@lem5719779 _119922)). Qed.
Lemma lem5719781 {_119921 _119922 : Type'} (op : type1400 _119921) : (term38 _119921 _119922 op) = (term39 _119921 _119922).
Proof. exact (fun_ext (fun f : _119922 -> _119921 => @lem5719780 _119921 _119922 op f)). Qed.
Lemma lem5719782 {_119921 _119922 : Type'} : (@all (_119922 -> _119921)) = (@all (_119922 -> _119921)).
Proof. exact (eq_refl (@all (_119922 -> _119921))). Qed.
Lemma lem5719783 {_119921 _119922 : Type'} (op : type1400 _119921) : (term40 _119921 _119922 op) = (term41 _119921 _119922).
Proof. exact (MK_COMB (@lem5719782 _119921 _119922) (@lem5719781 _119921 _119922 op)). Qed.
Lemma lem5719785 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5719786 {_119921 _119922 : Type'} (t : Prop) : (term42 _119921 _119922 t) = t.
Proof. exact (@lem5719785 (_119922 -> _119921) t). Qed.
Lemma lem5719787 {_119921 _119922 : Type'} : (term41 _119921 _119922) = True.
Proof. exact (@lem5719786 _119921 _119922 True). Qed.
Lemma lem5719788 {_119921 _119922 : Type'} (op : type1400 _119921) : (term40 _119921 _119922 op) = True.
Proof. exact (TRANS (@lem5719783 _119921 _119922 op) (@lem5719787 _119921 _119922)). Qed.
Lemma lem5719789 {_119921 _119922 : Type'} : (term43 _119921 _119922) = (term44 _119921).
Proof. exact (fun_ext (fun op : type1400 _119921 => @lem5719788 _119921 _119922 op)). Qed.
Lemma lem5719790 {_119921 : Type'} : (@all (_119921 -> _119921 -> _119921)) = (@all (_119921 -> _119921 -> _119921)).
Proof. exact (eq_refl (@all (_119921 -> _119921 -> _119921))). Qed.
Lemma lem5719791 {_119921 _119922 : Type'} : (term45 _119921 _119922) = (term46 _119921).
Proof. exact (MK_COMB (@lem5719790 _119921) (@lem5719789 _119921 _119922)). Qed.
Lemma lem5719793 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5719794 {_119921 : Type'} (t : Prop) : (term47 _119921 t) = t.
Proof. exact (@lem5719793 (type1400 _119921) t). Qed.
Lemma lem5719795 {_119921 : Type'} : (term46 _119921) = True.
Proof. exact (@lem5719794 _119921 True). Qed.
Lemma lem5719796 {_119921 _119922 : Type'} : (term45 _119921 _119922) = True.
Proof. exact (TRANS (@lem5719791 _119921 _119922) (@lem5719795 _119921)). Qed.
Lemma lem5719797 {_119921 _119922 : Type'} : True = (term45 _119921 _119922).
Proof. exact (SYM (@lem5719796 _119921 _119922)). Qed.
Lemma lem5719798 {_119921 _119922 : Type'} : term45 _119921 _119922.
Proof. exact (EQ_MP (@lem5719797 _119921 _119922) (@lem0)). Qed.
