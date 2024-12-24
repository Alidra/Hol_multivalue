Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_SUPPORT_term_abbrevs.
Require Import SUPPORT_SUPPORT_spec.
Require Import iterate_spec.
Require Import thm0_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem5737645 {_119851 _119862 : Type'} (op : type1400 _119851) : term0 _119851 _119862 op.
Proof. exact (@lem5718586 _119851 _119862 op). Qed.
Lemma lem5737646 {_119851 _119862 : Type'} (op : type1400 _119851) : (term0 _119851 _119862 op) = (term1 _119851 _119862 op).
Proof. exact (eq_refl (term0 _119851 _119862 op)). Qed.
Lemma lem5737647 {_119851 _119862 : Type'} (op : type1400 _119851) : term1 _119851 _119862 op.
Proof. exact (EQ_MP (@lem5737646 _119851 _119862 op) (@lem5737645 _119851 _119862 op)). Qed.
Lemma lem5737648 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : term2 _119851 _119862 op f.
Proof. exact (@lem5737647 _119851 _119862 op f). Qed.
Lemma lem5737649 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : (term2 _119851 _119862 op f) = (term3 _119851 _119862 op f).
Proof. exact (eq_refl (term2 _119851 _119862 op f)). Qed.
Lemma lem5737650 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : term3 _119851 _119862 op f.
Proof. exact (EQ_MP (@lem5737649 _119851 _119862 op f) (@lem5737648 _119851 _119862 op f)). Qed.
Lemma lem5737651 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : term4 _119851 _119862 op f s.
Proof. exact (@lem5737650 _119851 _119862 op f s). Qed.
Lemma lem5737652 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term4 _119851 _119862 op f s) = ((term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s)).
Proof. exact (eq_refl (term4 _119851 _119862 op f s)). Qed.
Lemma lem5737654 {_119779 A : Type'} (f : A -> _119779) : term6 _119779 A f.
Proof. exact (@lem5718049 _119779 A f). Qed.
Lemma lem5737655 {_119779 A : Type'} (f : A -> _119779) : (term6 _119779 A f) = (term7 _119779 A f).
Proof. exact (eq_refl (term6 _119779 A f)). Qed.
Lemma lem5737656 {_119779 A : Type'} (f : A -> _119779) : term7 _119779 A f.
Proof. exact (EQ_MP (@lem5737655 _119779 A f) (@lem5737654 _119779 A f)). Qed.
Lemma lem5737657 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term8 _119779 A f s.
Proof. exact (@lem5737656 _119779 A f s). Qed.
Lemma lem5737658 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : (term8 _119779 A f s) = (term9 _119779 A f s).
Proof. exact (eq_refl (term8 _119779 A f s)). Qed.
Lemma lem5737659 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term9 _119779 A f s.
Proof. exact (EQ_MP (@lem5737658 _119779 A f s) (@lem5737657 _119779 A f s)). Qed.
Lemma lem5737660 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : term10 _119779 A f s op.
Proof. exact (@lem5737659 _119779 A f s op). Qed.
Lemma lem5737661 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (term10 _119779 A f s op) = ((@iterate _119779 A op s f) = (term11 _119779 A f s op)).
Proof. exact (eq_refl (term10 _119779 A f s op)). Qed.
Lemma lem5737678 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem5737661 _119779 A f s op) (@lem5737660 _119779 A f s op)). Qed.
Lemma lem5737679 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : (@iterate _120296 _120308 op s f) = (term11 _120296 _120308 f s op).
Proof. exact (@lem5737678 _120296 _120308 f s op). Qed.
Lemma lem5737680 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : (term12 _120296 _120308 op s f) = (term13 _120296 _120308 f s op).
Proof. exact (@lem5737679 _120296 _120308 f (@support _120308 _120296 op f s) op). Qed.
Lemma lem5737682 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term14 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5737683 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term15 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5737682 _2963 g t e g' t' e'). Qed.
Lemma lem5737684 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term16 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5737683 _2963 g t e g' t'). Qed.
Lemma lem5737685 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term17 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5737684 _2963 g t e g'). Qed.
Lemma lem5737686 {_120296 : Type'} (g : Prop) (t : _120296) (e : _120296) : term17 _120296 g t e.
Proof. exact (@lem5737685 _120296 g t e). Qed.
Lemma lem5737687 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : term18 _120296 _120308 f s op.
Proof. exact (@lem5737686 _120296 (term19 _120296 _120308 op f s) (term20 _120296 _120308 f s op) (@neutral _120296 op)). Qed.
Lemma lem5737688 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) : term21 _120296 _120308 f s op g'.
Proof. exact (@lem5737687 _120296 _120308 f s op g'). Qed.
Lemma lem5737689 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) : (term21 _120296 _120308 f s op g') = (term22 _120296 _120308 f s op g').
Proof. exact (eq_refl (term21 _120296 _120308 f s op g')). Qed.
Lemma lem5737690 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) : term22 _120296 _120308 f s op g'.
Proof. exact (EQ_MP (@lem5737689 _120296 _120308 f s op g') (@lem5737688 _120296 _120308 f s op g')). Qed.
Lemma lem5737691 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) (t' : _120296) : term23 _120296 _120308 f s op g' t'.
Proof. exact (@lem5737690 _120296 _120308 f s op g' t'). Qed.
Lemma lem5737692 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) (t' : _120296) : (term23 _120296 _120308 f s op g' t') = (term24 _120296 _120308 f s op g' t').
Proof. exact (eq_refl (term23 _120296 _120308 f s op g' t')). Qed.
Lemma lem5737693 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) (t' : _120296) : term24 _120296 _120308 f s op g' t'.
Proof. exact (EQ_MP (@lem5737692 _120296 _120308 f s op g' t') (@lem5737691 _120296 _120308 f s op g' t')). Qed.
Lemma lem5737694 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) (t' : _120296) (e' : _120296) : term25 _120296 _120308 f s op g' t' e'.
Proof. exact (@lem5737693 _120296 _120308 f s op g' t' e'). Qed.
Lemma lem5737695 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) (t' : _120296) (e' : _120296) : (term25 _120296 _120308 f s op g' t' e') = (term26 _120296 _120308 f s op g' t' e').
Proof. exact (eq_refl (term25 _120296 _120308 f s op g' t' e')). Qed.
Lemma lem5737696 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (g' : Prop) (t' : _120296) (e' : _120296) : term26 _120296 _120308 f s op g' t' e'.
Proof. exact (EQ_MP (@lem5737695 _120296 _120308 f s op g' t' e') (@lem5737694 _120296 _120308 f s op g' t' e')). Qed.
Lemma lem5737698 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s).
Proof. exact (EQ_MP (@lem5737652 _119851 _119862 op f s) (@lem5737651 _119851 _119862 op f s)). Qed.
Lemma lem5737699 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : (term5 _120296 _120308 op f s) = (@support _120308 _120296 op f s).
Proof. exact (@lem5737698 _120296 _120308 op f s). Qed.
Lemma lem5737700 {_120308 : Type'} : (@FINITE _120308) = (@FINITE _120308).
Proof. exact (eq_refl (@FINITE _120308)). Qed.
Lemma lem5737701 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : (term19 _120296 _120308 op f s) = (term27 _120296 _120308 op f s).
Proof. exact (MK_COMB (@lem5737700 _120308) (@lem5737699 _120296 _120308 op f s)). Qed.
Lemma lem5737702 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) (t' : _120296) (e' : _120296) : term28 _120296 _120308 op f s t' e'.
Proof. exact (@lem5737696 _120296 _120308 f s op (term27 _120296 _120308 op f s) t' e'). Qed.
Lemma lem5737703 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) (t' : _120296) (e' : _120296) : term29 _120296 _120308 op f s t' e'.
Proof. exact (@lem5737702 _120296 _120308 op f s t' e' (@lem5737701 _120296 _120308 op f s)). Qed.
Lemma lem5737708 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s).
Proof. exact (EQ_MP (@lem5737652 _119851 _119862 op f s) (@lem5737651 _119851 _119862 op f s)). Qed.
Lemma lem5737709 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : (term5 _120296 _120308 op f s) = (@support _120308 _120296 op f s).
Proof. exact (@lem5737708 _120296 _120308 op f s). Qed.
Lemma lem5737710 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term30 _120296 _120308 op f) = (term30 _120296 _120308 op f).
Proof. exact (eq_refl (term30 _120296 _120308 op f)). Qed.
Lemma lem5737711 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : (term31 _120296 _120308 op f s) = (term32 _120296 _120308 op f s).
Proof. exact (MK_COMB (@lem5737710 _120296 _120308 op f) (@lem5737709 _120296 _120308 op f s)). Qed.
Lemma lem5737712 {_120296 : Type'} (op : type1400 _120296) : (@neutral _120296 op) = (@neutral _120296 op).
Proof. exact (eq_refl (@neutral _120296 op)). Qed.
Lemma lem5737713 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : (term20 _120296 _120308 f s op) = (term33 _120296 _120308 f s op).
Proof. exact (MK_COMB (@lem5737711 _120296 _120308 op f s) (@lem5737712 _120296 op)). Qed.
Lemma lem5737714 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : term34 _120296 _120308 f s op.
Proof. exact (fun h0 : term27 _120296 _120308 op f s => @lem5737713 _120296 _120308 f s op). Qed.
Lemma lem5737715 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (e' : _120296) : term35 _120296 _120308 f s op e'.
Proof. exact (@lem5737703 _120296 _120308 op f s (term33 _120296 _120308 f s op) e'). Qed.
Lemma lem5737716 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) (e' : _120296) : term36 _120296 _120308 f s op e'.
Proof. exact (@lem5737715 _120296 _120308 f s op e' (@lem5737714 _120296 _120308 f s op)). Qed.
Lemma lem5737720 {_120296 : Type'} (op : type1400 _120296) : (@neutral _120296 op) = (@neutral _120296 op).
Proof. exact (eq_refl (@neutral _120296 op)). Qed.
Lemma lem5737721 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : term37 _120296 _120308 f s op.
Proof. exact (fun h0 : term38 _120296 _120308 op f s => @lem5737720 _120296 op). Qed.
Lemma lem5737722 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : term39 _120296 _120308 f s op.
Proof. exact (@lem5737716 _120296 _120308 f s op (@neutral _120296 op)). Qed.
Lemma lem5737723 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : (term13 _120296 _120308 f s op) = (term11 _120296 _120308 f s op).
Proof. exact (@lem5737722 _120296 _120308 f s op (@lem5737721 _120296 _120308 f s op)). Qed.
Lemma lem5737757 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : (term12 _120296 _120308 op s f) = (term11 _120296 _120308 f s op).
Proof. exact (TRANS (@lem5737680 _120296 _120308 f s op) (@lem5737723 _120296 _120308 f s op)). Qed.
Lemma lem5737758 {_120296 : Type'} : (@eq _120296) = (@eq _120296).
Proof. exact (eq_refl (@eq _120296)). Qed.
Lemma lem5737759 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : (term40 _120296 _120308 op s f) = (term41 _120296 _120308 f s op).
Proof. exact (MK_COMB (@lem5737758 _120296) (@lem5737757 _120296 _120308 f s op)). Qed.
Lemma lem5737794 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem5737661 _119779 A f s op) (@lem5737660 _119779 A f s op)). Qed.
Lemma lem5737795 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : (@iterate _120296 _120308 op s f) = (term11 _120296 _120308 f s op).
Proof. exact (@lem5737794 _120296 _120308 f s op). Qed.
Lemma lem5737829 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : ((term12 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((term11 _120296 _120308 f s op) = (term11 _120296 _120308 f s op)).
Proof. exact (MK_COMB (@lem5737759 _120296 _120308 f s op) (@lem5737795 _120296 _120308 f s op)). Qed.
Lemma lem5737831 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5737832 {_120296 : Type'} (x : _120296) : (x = x) = True.
Proof. exact (@lem5737831 _120296 x). Qed.
Lemma lem5737833 {_120296 _120308 : Type'} (f : _120308 -> _120296) (s : _120308 -> Prop) (op : type1400 _120296) : ((term11 _120296 _120308 f s op) = (term11 _120296 _120308 f s op)) = True.
Proof. exact (@lem5737832 _120296 (term11 _120296 _120308 f s op)). Qed.
Lemma lem5737834 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term12 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = True.
Proof. exact (TRANS (@lem5737829 _120296 _120308 f s op) (@lem5737833 _120296 _120308 f s op)). Qed.
Lemma lem5737835 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term42 _120296 _120308 op f) = (term43 _120308).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem5737834 _120296 _120308 op s f)). Qed.
Lemma lem5737836 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem5737837 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term44 _120296 _120308 op f) = (term45 _120308).
Proof. exact (MK_COMB (@lem5737836 _120308) (@lem5737835 _120296 _120308 op f)). Qed.
Lemma lem5737839 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5737840 {_120308 : Type'} (t : Prop) : (term47 _120308 t) = t.
Proof. exact (@lem5737839 (_120308 -> Prop) t). Qed.
Lemma lem5737841 {_120308 : Type'} : (term45 _120308) = True.
Proof. exact (@lem5737840 _120308 True). Qed.
Lemma lem5737842 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term44 _120296 _120308 op f) = True.
Proof. exact (TRANS (@lem5737837 _120296 _120308 op f) (@lem5737841 _120308)). Qed.
Lemma lem5737843 {_120296 _120308 : Type'} (op : type1400 _120296) : (term48 _120296 _120308 op) = (term49 _120296 _120308).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem5737842 _120296 _120308 op f)). Qed.
Lemma lem5737844 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem5737845 {_120296 _120308 : Type'} (op : type1400 _120296) : (term50 _120296 _120308 op) = (term51 _120296 _120308).
Proof. exact (MK_COMB (@lem5737844 _120296 _120308) (@lem5737843 _120296 _120308 op)). Qed.
Lemma lem5737847 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5737848 {_120296 _120308 : Type'} (t : Prop) : (term52 _120296 _120308 t) = t.
Proof. exact (@lem5737847 (_120308 -> _120296) t). Qed.
Lemma lem5737849 {_120296 _120308 : Type'} : (term51 _120296 _120308) = True.
Proof. exact (@lem5737848 _120296 _120308 True). Qed.
Lemma lem5737850 {_120296 _120308 : Type'} (op : type1400 _120296) : (term50 _120296 _120308 op) = True.
Proof. exact (TRANS (@lem5737845 _120296 _120308 op) (@lem5737849 _120296 _120308)). Qed.
Lemma lem5737851 {_120296 _120308 : Type'} : (term53 _120296 _120308) = (term54 _120296).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem5737850 _120296 _120308 op)). Qed.
Lemma lem5737852 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem5737853 {_120296 _120308 : Type'} : (term55 _120296 _120308) = (term56 _120296).
Proof. exact (MK_COMB (@lem5737852 _120296) (@lem5737851 _120296 _120308)). Qed.
Lemma lem5737855 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5737856 {_120296 : Type'} (t : Prop) : (term57 _120296 t) = t.
Proof. exact (@lem5737855 (type1400 _120296) t). Qed.
Lemma lem5737857 {_120296 : Type'} : (term56 _120296) = True.
Proof. exact (@lem5737856 _120296 True). Qed.
Lemma lem5737858 {_120296 _120308 : Type'} : (term55 _120296 _120308) = True.
Proof. exact (TRANS (@lem5737853 _120296 _120308) (@lem5737857 _120296)). Qed.
Lemma lem5737859 {_120296 _120308 : Type'} : True = (term55 _120296 _120308).
Proof. exact (SYM (@lem5737858 _120296 _120308)). Qed.
Lemma lem5737860 {_120296 _120308 : Type'} : term55 _120296 _120308.
Proof. exact (EQ_MP (@lem5737859 _120296 _120308) (@lem0)). Qed.
