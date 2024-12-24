Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PSUBSET_UNIONS_PAIRWISE_DISJOINT_term_abbrevs.
Require Import DIFF_UNIONS_PAIRWISE_DISJOINT_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EMPTY_UNIONS_spec.
Require Import IN_DELETE_spec.
Require Import IN_DIFF_spec.
Require Import PSUBSET_ALT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
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
Require Import thm19490_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem4833714 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4833715 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4833716 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4833715 t1) (@lem4833714 t1)). Qed.
Lemma lem4833717 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4833716 t1 t2). Qed.
Lemma lem4833718 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4833719 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4833718 t1 t2) (@lem4833717 t1 t2)). Qed.
Lemma lem4833720 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4833719 t1 t2 t3). Qed.
Lemma lem4833721 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4833722 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4833721 t1 t2 t3) (@lem4833720 t1 t2 t3)). Qed.
Lemma lem4833723 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4833722 t1 t2 t3)). Qed.
Lemma lem4833724 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem4833725 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem4833726 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem4833725 A s) (@lem4833724 A s)). Qed.
Lemma lem4833727 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem4833726 A s t). Qed.
Lemma lem4833728 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term10 A s t).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem4833729 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (EQ_MP (@lem4833728 A s t) (@lem4833727 A s t)). Qed.
Lemma lem4833730 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term11 A s t x.
Proof. exact (@lem4833729 A s t x). Qed.
Lemma lem4833731 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s t x) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl (term11 A s t x)). Qed.
Lemma lem4833733 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem4833734 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem4833735 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem4833734 A s) (@lem4833733 A s)). Qed.
Lemma lem4833736 {A : Type'} (s : A -> Prop) (x : A) : term16 A s x.
Proof. exact (@lem4833735 A s x). Qed.
Lemma lem4833737 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term17 A s x).
Proof. exact (eq_refl (term16 A s x)). Qed.
Lemma lem4833738 {A : Type'} (s : A -> Prop) (x : A) : term17 A s x.
Proof. exact (EQ_MP (@lem4833737 A s x) (@lem4833736 A s x)). Qed.
Lemma lem4833739 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term18 A s x y.
Proof. exact (@lem4833738 A s x y). Qed.
Lemma lem4833740 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term18 A s x y) = ((term19 A x s y) = (term20 A s x y)).
Proof. exact (eq_refl (term18 A s x y)). Qed.
Lemma lem4833742 {A : Type'} (s : A -> Prop) : term21 A s.
Proof. exact (@lem3231915 A s). Qed.
Lemma lem4833743 {A : Type'} (s : A -> Prop) : (term21 A s) = (term22 A s).
Proof. exact (eq_refl (term21 A s)). Qed.
Lemma lem4833744 {A : Type'} (s : A -> Prop) : term22 A s.
Proof. exact (EQ_MP (@lem4833743 A s) (@lem4833742 A s)). Qed.
Lemma lem4833745 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term23 A s t.
Proof. exact (@lem4833744 A s t). Qed.
Lemma lem4833746 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term23 A s t) = ((@PSUBSET A s t) = (term24 A t s)).
Proof. exact (eq_refl (term23 A s t)). Qed.
Lemma lem4833748 {_86951 : Type'} (s : type686 _86951) : term25 _86951 s.
Proof. exact (@lem3329633 _86951 s). Qed.
Lemma lem4833749 {_86951 : Type'} (s : type686 _86951) : (term25 _86951 s) = (((@UNIONS _86951 s) = (@EMPTY _86951)) = (term26 _86951 s)).
Proof. exact (eq_refl (term25 _86951 s)). Qed.
Lemma lem4833751 {A : Type'} (s : type686 A) : term27 A s.
Proof. exact (@lem4829792 A s). Qed.
Lemma lem4833752 {A : Type'} (s : type686 A) : (term27 A s) = (term28 A s).
Proof. exact (eq_refl (term27 A s)). Qed.
Lemma lem4833753 {A : Type'} (s : type686 A) : term28 A s.
Proof. exact (EQ_MP (@lem4833752 A s) (@lem4833751 A s)). Qed.
Lemma lem4833754 {A : Type'} (s : type686 A) (t : type686 A) : term29 A s t.
Proof. exact (@lem4833753 A s t). Qed.
Lemma lem4833755 {A : Type'} (s : type686 A) (t : type686 A) : (term29 A s t) = (term30 A s t).
Proof. exact (eq_refl (term29 A s t)). Qed.
Lemma lem4833772 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4833773 {_111029 : Type'} (s : _111029 -> Prop) (t : _111029 -> Prop) : (@SUBSET _111029 s t) = (term31 _111029 s t).
Proof. exact (@lem4833772 _111029 s t). Qed.
Lemma lem4833774 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (@SUBSET _111029 u v) = (term31 _111029 u v).
Proof. exact (@lem4833773 _111029 u v). Qed.
Lemma lem4833781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833782 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term32 _111029 u v) = (term33 _111029 u v).
Proof. exact (MK_COMB (@lem4833781) (@lem4833774 _111029 u v)). Qed.
Lemma lem4833786 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term34 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4833787 {_111029 : Type'} (s : _111029 -> Prop) (t : _111029 -> Prop) : (s = t) = (term34 _111029 s t).
Proof. exact (@lem4833786 _111029 s t). Qed.
Lemma lem4833788 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : ((@DIFF _111029 v u) = (@EMPTY _111029)) = (term35 _111029 v u).
Proof. exact (@lem4833787 _111029 (@DIFF _111029 v u) (@EMPTY _111029)). Qed.
Lemma lem4833797 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833798 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term36 _111029 v u) = (term37 _111029 v u).
Proof. exact (MK_COMB (@lem4833797) (@lem4833788 _111029 v u)). Qed.
Lemma lem4833799 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term38 _111029 v u) = (term39 _111029 v u).
Proof. exact (MK_COMB (@lem4833782 _111029 u v) (@lem4833798 _111029 v u)). Qed.
Lemma lem4833802 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4833803 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term40 _111029 v u) = (term41 _111029 v u).
Proof. exact (MK_COMB (@lem4833802) (@lem4833799 _111029 v u)). Qed.
Lemma lem4833805 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term42 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem4833806 {_111029 : Type'} (s : _111029 -> Prop) (t : _111029 -> Prop) : (@PSUBSET _111029 s t) = (term42 _111029 s t).
Proof. exact (@lem4833805 _111029 s t). Qed.
Lemma lem4833807 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (@PSUBSET _111029 u v) = (term42 _111029 u v).
Proof. exact (@lem4833806 _111029 u v). Qed.
Lemma lem4833811 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4833812 {_111029 : Type'} (s : _111029 -> Prop) (t : _111029 -> Prop) : (@SUBSET _111029 s t) = (term31 _111029 s t).
Proof. exact (@lem4833811 _111029 s t). Qed.
Lemma lem4833813 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (@SUBSET _111029 u v) = (term31 _111029 u v).
Proof. exact (@lem4833812 _111029 u v). Qed.
Lemma lem4833820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833821 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term32 _111029 u v) = (term33 _111029 u v).
Proof. exact (MK_COMB (@lem4833820) (@lem4833813 _111029 u v)). Qed.
Lemma lem4833825 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term34 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4833826 {_111029 : Type'} (s : _111029 -> Prop) (t : _111029 -> Prop) : (s = t) = (term34 _111029 s t).
Proof. exact (@lem4833825 _111029 s t). Qed.
Lemma lem4833827 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (u = v) = (term34 _111029 u v).
Proof. exact (@lem4833826 _111029 u v). Qed.
Lemma lem4833836 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833837 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term43 _111029 u v) = (term44 _111029 u v).
Proof. exact (MK_COMB (@lem4833836) (@lem4833827 _111029 u v)). Qed.
Lemma lem4833838 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term42 _111029 u v) = (term45 _111029 u v).
Proof. exact (MK_COMB (@lem4833821 _111029 u v) (@lem4833837 _111029 u v)). Qed.
Lemma lem4833841 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (@PSUBSET _111029 u v) = (term45 _111029 u v).
Proof. exact (TRANS (@lem4833807 _111029 u v) (@lem4833838 _111029 u v)). Qed.
Lemma lem4833842 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term46 _111029 u v) = (term47 _111029 u v).
Proof. exact (MK_COMB (@lem4833803 _111029 v u) (@lem4833841 _111029 u v)). Qed.
Lemma lem4833845 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term47 _111029 u v) = (term46 _111029 u v).
Proof. exact (SYM (@lem4833842 _111029 u v)). Qed.
Lemma lem4833857 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4833858 {_111029 : Type'} (P : _111029 -> Prop) (x : _111029) : (@IN _111029 x P) = (P x).
Proof. exact (@lem4833857 _111029 P x). Qed.
Lemma lem4833859 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (@IN _111029 x u) = (u x).
Proof. exact (@lem4833858 _111029 u x). Qed.
Lemma lem4833860 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4833861 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (term48 _111029 x u) = (term49 _111029 u x).
Proof. exact (MK_COMB (@lem4833860) (@lem4833859 _111029 u x)). Qed.
Lemma lem4833863 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4833864 {_111029 : Type'} (P : _111029 -> Prop) (x : _111029) : (@IN _111029 x P) = (P x).
Proof. exact (@lem4833863 _111029 P x). Qed.
Lemma lem4833865 {_111029 : Type'} (v : _111029 -> Prop) (x : _111029) : (@IN _111029 x v) = (v x).
Proof. exact (@lem4833864 _111029 v x). Qed.
Lemma lem4833866 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term50 _111029 u x v) = (term51 _111029 u v x).
Proof. exact (MK_COMB (@lem4833861 _111029 u x) (@lem4833865 _111029 v x)). Qed.
Lemma lem4833869 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term52 _111029 u v) = (term53 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4833866 _111029 u v x)). Qed.
Lemma lem4833870 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4833871 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term31 _111029 u v) = (term54 _111029 u v).
Proof. exact (MK_COMB (@lem4833870 _111029) (@lem4833869 _111029 u v)). Qed.
Lemma lem4833876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833877 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term33 _111029 u v) = (term55 _111029 u v).
Proof. exact (MK_COMB (@lem4833876) (@lem4833871 _111029 u v)). Qed.
Lemma lem4833885 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4833886 {_111029 : Type'} (s : _111029 -> Prop) (x : _111029) (t : _111029 -> Prop) : (term12 _111029 x s t) = (term13 _111029 s x t).
Proof. exact (@lem4833885 _111029 s x t). Qed.
Lemma lem4833887 {_111029 : Type'} (v : _111029 -> Prop) (x : _111029) (u : _111029 -> Prop) : (term12 _111029 x v u) = (term13 _111029 v x u).
Proof. exact (@lem4833886 _111029 v x u). Qed.
Lemma lem4833891 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4833892 {_111029 : Type'} (P : _111029 -> Prop) (x : _111029) : (@IN _111029 x P) = (P x).
Proof. exact (@lem4833891 _111029 P x). Qed.
Lemma lem4833893 {_111029 : Type'} (v : _111029 -> Prop) (x : _111029) : (@IN _111029 x v) = (v x).
Proof. exact (@lem4833892 _111029 v x). Qed.
Lemma lem4833894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833895 {_111029 : Type'} (v : _111029 -> Prop) (x : _111029) : (term56 _111029 x v) = (term57 _111029 v x).
Proof. exact (MK_COMB (@lem4833894) (@lem4833893 _111029 v x)). Qed.
Lemma lem4833897 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4833898 {_111029 : Type'} (P : _111029 -> Prop) (x : _111029) : (@IN _111029 x P) = (P x).
Proof. exact (@lem4833897 _111029 P x). Qed.
Lemma lem4833899 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (@IN _111029 x u) = (u x).
Proof. exact (@lem4833898 _111029 u x). Qed.
Lemma lem4833900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833901 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (term58 _111029 x u) = (term59 _111029 u x).
Proof. exact (MK_COMB (@lem4833900) (@lem4833899 _111029 u x)). Qed.
Lemma lem4833902 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term13 _111029 v x u) = (term60 _111029 v u x).
Proof. exact (MK_COMB (@lem4833895 _111029 v x) (@lem4833901 _111029 u x)). Qed.
Lemma lem4833905 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term12 _111029 x v u) = (term60 _111029 v u x).
Proof. exact (TRANS (@lem4833887 _111029 v x u) (@lem4833902 _111029 v u x)). Qed.
Lemma lem4833906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4833907 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term61 _111029 x v u) = (term62 _111029 v u x).
Proof. exact (MK_COMB (@lem4833906) (@lem4833905 _111029 v u x)). Qed.
Lemma lem4833909 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4833910 {_111029 : Type'} (x : _111029) : (@IN _111029 x (@EMPTY _111029)) = False.
Proof. exact (@lem4833909 _111029 x). Qed.
Lemma lem4833911 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : ((term12 _111029 x v u) = (@IN _111029 x (@EMPTY _111029))) = ((term60 _111029 v u x) = False).
Proof. exact (MK_COMB (@lem4833907 _111029 v u x) (@lem4833910 _111029 x)). Qed.
Lemma lem4833913 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4833914 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : ((term60 _111029 v u x) = False) = (term63 _111029 v u x).
Proof. exact (@lem4833913 (term60 _111029 v u x)). Qed.
Lemma lem4833917 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : ((term12 _111029 x v u) = (@IN _111029 x (@EMPTY _111029))) = (term63 _111029 v u x).
Proof. exact (TRANS (@lem4833911 _111029 v u x) (@lem4833914 _111029 v u x)). Qed.
Lemma lem4833918 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term64 _111029 v u) = (term65 _111029 v u).
Proof. exact (fun_ext (fun x : _111029 => @lem4833917 _111029 v u x)). Qed.
Lemma lem4833919 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4833920 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term35 _111029 v u) = (term66 _111029 v u).
Proof. exact (MK_COMB (@lem4833919 _111029) (@lem4833918 _111029 v u)). Qed.
Lemma lem4833925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833926 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term37 _111029 v u) = (term67 _111029 v u).
Proof. exact (MK_COMB (@lem4833925) (@lem4833920 _111029 v u)). Qed.
Lemma lem4833927 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term39 _111029 v u) = (term68 _111029 v u).
Proof. exact (MK_COMB (@lem4833877 _111029 u v) (@lem4833926 _111029 v u)). Qed.
Lemma lem4833930 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4833931 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term41 _111029 v u) = (term69 _111029 v u).
Proof. exact (MK_COMB (@lem4833930) (@lem4833927 _111029 v u)). Qed.
Lemma lem4833941 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4833942 {_111029 : Type'} (P : _111029 -> Prop) (x : _111029) : (@IN _111029 x P) = (P x).
Proof. exact (@lem4833941 _111029 P x). Qed.
Lemma lem4833943 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (@IN _111029 x u) = (u x).
Proof. exact (@lem4833942 _111029 u x). Qed.
Lemma lem4833944 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4833945 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (term48 _111029 x u) = (term49 _111029 u x).
Proof. exact (MK_COMB (@lem4833944) (@lem4833943 _111029 u x)). Qed.
Lemma lem4833947 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4833948 {_111029 : Type'} (P : _111029 -> Prop) (x : _111029) : (@IN _111029 x P) = (P x).
Proof. exact (@lem4833947 _111029 P x). Qed.
Lemma lem4833949 {_111029 : Type'} (v : _111029 -> Prop) (x : _111029) : (@IN _111029 x v) = (v x).
Proof. exact (@lem4833948 _111029 v x). Qed.
Lemma lem4833950 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term50 _111029 u x v) = (term51 _111029 u v x).
Proof. exact (MK_COMB (@lem4833945 _111029 u x) (@lem4833949 _111029 v x)). Qed.
Lemma lem4833953 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term52 _111029 u v) = (term53 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4833950 _111029 u v x)). Qed.
Lemma lem4833954 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4833955 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term31 _111029 u v) = (term54 _111029 u v).
Proof. exact (MK_COMB (@lem4833954 _111029) (@lem4833953 _111029 u v)). Qed.
Lemma lem4833960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4833961 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term33 _111029 u v) = (term55 _111029 u v).
Proof. exact (MK_COMB (@lem4833960) (@lem4833955 _111029 u v)). Qed.
Lemma lem4833969 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4833970 {_111029 : Type'} (P : _111029 -> Prop) (x : _111029) : (@IN _111029 x P) = (P x).
Proof. exact (@lem4833969 _111029 P x). Qed.
Lemma lem4833971 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (@IN _111029 x u) = (u x).
Proof. exact (@lem4833970 _111029 u x). Qed.
Lemma lem4833972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4833973 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (term70 _111029 x u) = (term71 _111029 u x).
Proof. exact (MK_COMB (@lem4833972) (@lem4833971 _111029 u x)). Qed.
Lemma lem4833975 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4833976 {_111029 : Type'} (P : _111029 -> Prop) (x : _111029) : (@IN _111029 x P) = (P x).
Proof. exact (@lem4833975 _111029 P x). Qed.
Lemma lem4833977 {_111029 : Type'} (v : _111029 -> Prop) (x : _111029) : (@IN _111029 x v) = (v x).
Proof. exact (@lem4833976 _111029 v x). Qed.
Lemma lem4833978 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : ((@IN _111029 x u) = (@IN _111029 x v)) = ((u x) = (v x)).
Proof. exact (MK_COMB (@lem4833973 _111029 u x) (@lem4833977 _111029 v x)). Qed.
Lemma lem4833981 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term72 _111029 u v) = (term73 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4833978 _111029 u v x)). Qed.
Lemma lem4833982 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4833983 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term34 _111029 u v) = (term74 _111029 u v).
Proof. exact (MK_COMB (@lem4833982 _111029) (@lem4833981 _111029 u v)). Qed.
Lemma lem4833988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4833989 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term44 _111029 u v) = (term75 _111029 u v).
Proof. exact (MK_COMB (@lem4833988) (@lem4833983 _111029 u v)). Qed.
Lemma lem4833990 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term45 _111029 u v) = (term76 _111029 u v).
Proof. exact (MK_COMB (@lem4833961 _111029 u v) (@lem4833989 _111029 u v)). Qed.
Lemma lem4833993 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term47 _111029 u v) = (term77 _111029 u v).
Proof. exact (MK_COMB (@lem4833931 _111029 v u) (@lem4833990 _111029 u v)). Qed.
Lemma lem4833996 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term77 _111029 u v) = (term47 _111029 u v).
Proof. exact (SYM (@lem4833993 _111029 u v)). Qed.
Lemma lem4833998 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4833999 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term77 _111029 u v) = (term79 _111029 u v).
Proof. exact (@lem4833998 (term77 _111029 u v)). Qed.
Lemma lem4834000 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term79 _111029 u v) = (term77 _111029 u v).
Proof. exact (SYM (@lem4833999 _111029 u v)). Qed.
Lemma lem4834001 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term80 _111029 u v) : term80 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834004 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term79 _111029 u v) : term79 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834005 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term81 _111029 u v.
Proof. exact (fun h0 : term79 _111029 u v => @lem4834004 _111029 u v h0). Qed.
Lemma lem4834006 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term81 _111029 u v) : term81 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834007 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term79 _111029 u v) : term79 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834008 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term79 _111029 u v) (h2 : term81 _111029 u v) : term79 _111029 u v.
Proof. exact (@lem4834006 _111029 u v h2 (@lem4834007 _111029 u v h1)). Qed.
Lemma lem4834009 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term79 _111029 u v) : term82 _111029 u v.
Proof. exact (fun h0 : term81 _111029 u v => @lem4834008 _111029 u v h1 h0). Qed.
Lemma lem4834010 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term81 _111029 u v) : term81 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834011 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term79 _111029 u v) (h2 : term81 _111029 u v) : term79 _111029 u v.
Proof. exact (@lem4834009 _111029 u v h1 (@lem4834010 _111029 u v h2)). Qed.
Lemma lem4834012 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term81 _111029 u v) : term81 _111029 u v.
Proof. exact (fun h0 : term79 _111029 u v => @lem4834011 _111029 u v h0 h1). Qed.
Lemma lem4834013 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term83 _111029 u v.
Proof. exact (fun h0 : term81 _111029 u v => @lem4834012 _111029 u v h0). Qed.
Lemma lem4834016 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term81 _111029 u v.
Proof. exact (@lem4834013 _111029 u v (@lem4834005 _111029 u v)). Qed.
Lemma lem4834017 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term81 _111029 u v.
Proof. exact (@lem4834016 _111029 u v). Qed.
Lemma lem4834027 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4834028 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term79 _111029 u v) = (term84 _111029 u v).
Proof. exact (@lem4834027 (term80 _111029 u v)). Qed.
Lemma lem4834030 (t : Prop) : (term85 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4834031 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term84 _111029 u v) = (term77 _111029 u v).
Proof. exact (@lem4834030 (term77 _111029 u v)). Qed.
Lemma lem4834034 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term79 _111029 u v) = (term77 _111029 u v).
Proof. exact (TRANS (@lem4834028 _111029 u v) (@lem4834031 _111029 u v)). Qed.
Lemma lem4834061 {_111029 : Type'} (v : _111029 -> Prop) : (term86 _111029 v) = (term87 _111029 v).
Proof. exact (fun_ext (fun u : _111029 -> Prop => @lem4834034 _111029 u v)). Qed.
Lemma lem4834062 {_111029 : Type'} : (@all (_111029 -> Prop)) = (@all (_111029 -> Prop)).
Proof. exact (eq_refl (@all (_111029 -> Prop))). Qed.
Lemma lem4834063 {_111029 : Type'} (v : _111029 -> Prop) : (term88 _111029 v) = (term89 _111029 v).
Proof. exact (MK_COMB (@lem4834062 _111029) (@lem4834061 _111029 v)). Qed.
Lemma lem4834068 {_111029 : Type'} : (term90 _111029) = (term91 _111029).
Proof. exact (fun_ext (fun v : _111029 -> Prop => @lem4834063 _111029 v)). Qed.
Lemma lem4834069 {_111029 : Type'} : (@all (_111029 -> Prop)) = (@all (_111029 -> Prop)).
Proof. exact (eq_refl (@all (_111029 -> Prop))). Qed.
Lemma lem4834078 {_111029 : Type'} : (term92 _111029) = (term93 _111029).
Proof. exact (MK_COMB (@lem4834069 _111029) (@lem4834068 _111029)). Qed.
Lemma lem4834083 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : ((u x) = (v x)) = ((u x) = (v x)).
Proof. exact (eq_refl ((u x) = (v x))). Qed.
Lemma lem4834084 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term73 _111029 u v) = (term73 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834083 _111029 u v x)). Qed.
Lemma lem4834085 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834086 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term74 _111029 u v) = (term74 _111029 u v).
Proof. exact (MK_COMB (@lem4834085 _111029) (@lem4834084 _111029 u v)). Qed.
Lemma lem4834087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4834088 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term75 _111029 u v) = (term75 _111029 u v).
Proof. exact (MK_COMB (@lem4834087) (@lem4834086 _111029 u v)). Qed.
Lemma lem4834093 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term51 _111029 u v x) = (term51 _111029 u v x).
Proof. exact (eq_refl (term51 _111029 u v x)). Qed.
Lemma lem4834094 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term53 _111029 u v) = (term53 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834093 _111029 u v x)). Qed.
Lemma lem4834095 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834096 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term54 _111029 u v) = (term54 _111029 u v).
Proof. exact (MK_COMB (@lem4834095 _111029) (@lem4834094 _111029 u v)). Qed.
Lemma lem4834097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834098 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term55 _111029 u v) = (term55 _111029 u v).
Proof. exact (MK_COMB (@lem4834097) (@lem4834096 _111029 u v)). Qed.
Lemma lem4834099 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term76 _111029 u v) = (term76 _111029 u v).
Proof. exact (MK_COMB (@lem4834098 _111029 u v) (@lem4834088 _111029 u v)). Qed.
Lemma lem4834108 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term63 _111029 v u x) = (term63 _111029 v u x).
Proof. exact (eq_refl (term63 _111029 v u x)). Qed.
Lemma lem4834109 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term65 _111029 v u) = (term65 _111029 v u).
Proof. exact (fun_ext (fun x : _111029 => @lem4834108 _111029 v u x)). Qed.
Lemma lem4834110 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834111 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term66 _111029 v u) = (term66 _111029 v u).
Proof. exact (MK_COMB (@lem4834110 _111029) (@lem4834109 _111029 v u)). Qed.
Lemma lem4834112 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4834113 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term67 _111029 v u) = (term67 _111029 v u).
Proof. exact (MK_COMB (@lem4834112) (@lem4834111 _111029 v u)). Qed.
Lemma lem4834118 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term51 _111029 u v x) = (term51 _111029 u v x).
Proof. exact (eq_refl (term51 _111029 u v x)). Qed.
Lemma lem4834119 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term53 _111029 u v) = (term53 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834118 _111029 u v x)). Qed.
Lemma lem4834120 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834121 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term54 _111029 u v) = (term54 _111029 u v).
Proof. exact (MK_COMB (@lem4834120 _111029) (@lem4834119 _111029 u v)). Qed.
Lemma lem4834122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834123 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term55 _111029 u v) = (term55 _111029 u v).
Proof. exact (MK_COMB (@lem4834122) (@lem4834121 _111029 u v)). Qed.
Lemma lem4834124 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term68 _111029 v u) = (term68 _111029 v u).
Proof. exact (MK_COMB (@lem4834123 _111029 u v) (@lem4834113 _111029 v u)). Qed.
Lemma lem4834125 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4834126 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term69 _111029 v u) = (term69 _111029 v u).
Proof. exact (MK_COMB (@lem4834125) (@lem4834124 _111029 v u)). Qed.
Lemma lem4834127 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term77 _111029 u v) = (term77 _111029 u v).
Proof. exact (MK_COMB (@lem4834126 _111029 v u) (@lem4834099 _111029 u v)). Qed.
Lemma lem4834128 {_111029 : Type'} (v : _111029 -> Prop) : (term87 _111029 v) = (term87 _111029 v).
Proof. exact (fun_ext (fun u : _111029 -> Prop => @lem4834127 _111029 u v)). Qed.
Lemma lem4834129 {_111029 : Type'} : (@all (_111029 -> Prop)) = (@all (_111029 -> Prop)).
Proof. exact (eq_refl (@all (_111029 -> Prop))). Qed.
Lemma lem4834130 {_111029 : Type'} (v : _111029 -> Prop) : (term89 _111029 v) = (term89 _111029 v).
Proof. exact (MK_COMB (@lem4834129 _111029) (@lem4834128 _111029 v)). Qed.
Lemma lem4834131 {_111029 : Type'} : (term91 _111029) = (term91 _111029).
Proof. exact (fun_ext (fun v : _111029 -> Prop => @lem4834130 _111029 v)). Qed.
Lemma lem4834132 {_111029 : Type'} : (@all (_111029 -> Prop)) = (@all (_111029 -> Prop)).
Proof. exact (eq_refl (@all (_111029 -> Prop))). Qed.
Lemma lem4834133 {_111029 : Type'} : (term93 _111029) = (term93 _111029).
Proof. exact (MK_COMB (@lem4834132 _111029) (@lem4834131 _111029)). Qed.
Lemma lem4834184 {_111029 : Type'} : (term92 _111029) = (term93 _111029).
Proof. exact (TRANS (@lem4834078 _111029) (@lem4834133 _111029)). Qed.
Lemma lem4834185 {_111029 : Type'} : (term93 _111029) = (term92 _111029).
Proof. exact (SYM (@lem4834184 _111029)). Qed.
Lemma lem4834186 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term68 _111029 v u) : term68 _111029 v u.
Proof. exact (h1). Qed.
Lemma lem4834188 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4834189 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term76 _111029 u v) = (term94 _111029 u v).
Proof. exact (@lem4834188 (term76 _111029 u v)). Qed.
Lemma lem4834190 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term94 _111029 u v) = (term76 _111029 u v).
Proof. exact (SYM (@lem4834189 _111029 u v)). Qed.
Lemma lem4834191 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term95 _111029 u v) : term95 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834198 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term51 _111029 u v x) = (term96 _111029 u v x).
Proof. exact (@lem17265 (u x) (v x)). Qed.
Lemma lem4834199 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term53 _111029 u v) = (term97 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834198 _111029 u v x)). Qed.
Lemma lem4834200 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834201 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term54 _111029 u v) = (term98 _111029 u v).
Proof. exact (MK_COMB (@lem4834200 _111029) (@lem4834199 _111029 u v)). Qed.
Lemma lem4834208 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term99 _111029 v u x) = (term60 _111029 v u x).
Proof. exact (@lem16933 (term60 _111029 v u x)). Qed.
Lemma lem4834209 {_111029 : Type'} (P : _111029 -> Prop) : (term100 _111029 P) = (term101 _111029 P).
Proof. exact (@lem18392 _111029 P). Qed.
Lemma lem4834210 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term67 _111029 v u) = (term102 _111029 v u).
Proof. exact (@lem4834209 _111029 (term65 _111029 v u)). Qed.
Lemma lem4834211 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term103 _111029 v u x) = (term63 _111029 v u x).
Proof. exact (eq_refl (term103 _111029 v u x)). Qed.
Lemma lem4834212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4834213 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term104 _111029 v u x) = (term99 _111029 v u x).
Proof. exact (MK_COMB (@lem4834212) (@lem4834211 _111029 v u x)). Qed.
Lemma lem4834214 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term104 _111029 v u x) = (term60 _111029 v u x).
Proof. exact (TRANS (@lem4834213 _111029 v u x) (@lem4834208 _111029 v u x)). Qed.
Lemma lem4834215 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term105 _111029 v u) = (term106 _111029 v u).
Proof. exact (fun_ext (fun x : _111029 => @lem4834214 _111029 v u x)). Qed.
Lemma lem4834216 {_111029 : Type'} : (@ex _111029) = (@ex _111029).
Proof. exact (eq_refl (@ex _111029)). Qed.
Lemma lem4834217 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term102 _111029 v u) = (term107 _111029 v u).
Proof. exact (MK_COMB (@lem4834216 _111029) (@lem4834215 _111029 v u)). Qed.
Lemma lem4834218 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term67 _111029 v u) = (term107 _111029 v u).
Proof. exact (TRANS (@lem4834210 _111029 v u) (@lem4834217 _111029 v u)). Qed.
Lemma lem4834219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834220 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term55 _111029 u v) = (term108 _111029 u v).
Proof. exact (MK_COMB (@lem4834219) (@lem4834201 _111029 u v)). Qed.
Lemma lem4834221 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term68 _111029 v u) = (term109 _111029 v u).
Proof. exact (MK_COMB (@lem4834220 _111029 u v) (@lem4834218 _111029 v u)). Qed.
Lemma lem4834284 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4834285 {_111029 : Type'} (P : Prop) (Q : _111029 -> Prop) : (term110 _111029 P Q) = (term111 _111029 P Q).
Proof. exact (@lem4834284 _111029 P Q). Qed.
Lemma lem4834286 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term112 _111029 v u) = (term113 _111029 v u).
Proof. exact (@lem4834285 _111029 (term98 _111029 u v) (term106 _111029 v u)). Qed.
Lemma lem4834287 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term114 _111029 v u x) = (term60 _111029 v u x).
Proof. exact (eq_refl (term114 _111029 v u x)). Qed.
Lemma lem4834288 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term115 _111029 v u) = (term106 _111029 v u).
Proof. exact (fun_ext (fun x : _111029 => @lem4834287 _111029 v u x)). Qed.
Lemma lem4834289 {_111029 : Type'} : (@ex _111029) = (@ex _111029).
Proof. exact (eq_refl (@ex _111029)). Qed.
Lemma lem4834290 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term116 _111029 v u) = (term107 _111029 v u).
Proof. exact (MK_COMB (@lem4834289 _111029) (@lem4834288 _111029 v u)). Qed.
Lemma lem4834291 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term108 _111029 u v) = (term108 _111029 u v).
Proof. exact (eq_refl (term108 _111029 u v)). Qed.
Lemma lem4834292 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term112 _111029 v u) = (term109 _111029 v u).
Proof. exact (MK_COMB (@lem4834291 _111029 u v) (@lem4834290 _111029 v u)). Qed.
Lemma lem4834293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4834294 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term117 _111029 v u) = (term118 _111029 v u).
Proof. exact (MK_COMB (@lem4834293) (@lem4834292 _111029 v u)). Qed.
Lemma lem4834295 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term114 _111029 v u x) = (term60 _111029 v u x).
Proof. exact (eq_refl (term114 _111029 v u x)). Qed.
Lemma lem4834296 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term108 _111029 u v) = (term108 _111029 u v).
Proof. exact (eq_refl (term108 _111029 u v)). Qed.
Lemma lem4834297 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x : _111029) : (term119 _111029 v u x) = (term120 _111029 v u x).
Proof. exact (MK_COMB (@lem4834296 _111029 u v) (@lem4834295 _111029 v u x)). Qed.
Lemma lem4834298 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term121 _111029 v u) = (term122 _111029 v u).
Proof. exact (fun_ext (fun x : _111029 => @lem4834297 _111029 v u x)). Qed.
Lemma lem4834299 {_111029 : Type'} : (@ex _111029) = (@ex _111029).
Proof. exact (eq_refl (@ex _111029)). Qed.
Lemma lem4834300 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term113 _111029 v u) = (term123 _111029 v u).
Proof. exact (MK_COMB (@lem4834299 _111029) (@lem4834298 _111029 v u)). Qed.
Lemma lem4834301 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : ((term112 _111029 v u) = (term113 _111029 v u)) = ((term109 _111029 v u) = (term123 _111029 v u)).
Proof. exact (MK_COMB (@lem4834294 _111029 v u) (@lem4834300 _111029 v u)). Qed.
Lemma lem4834303 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term109 _111029 v u) = (term123 _111029 v u).
Proof. exact (EQ_MP (@lem4834301 _111029 v u) (@lem4834286 _111029 v u)). Qed.
Lemma lem4834304 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : (term68 _111029 v u) = (term123 _111029 v u).
Proof. exact (TRANS (@lem4834221 _111029 v u) (@lem4834303 _111029 v u)). Qed.
Lemma lem4834305 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term68 _111029 v u) : term123 _111029 v u.
Proof. exact (EQ_MP (@lem4834304 _111029 v u) (@lem4834186 _111029 v u h1)). Qed.
Lemma lem4834312 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term124 _111029 u v x) = (term60 _111029 u v x).
Proof. exact (@lem17362 (u x) (v x)). Qed.
Lemma lem4834313 {_111029 : Type'} (P : _111029 -> Prop) : (term100 _111029 P) = (term101 _111029 P).
Proof. exact (@lem18392 _111029 P). Qed.
Lemma lem4834314 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term125 _111029 u v) = (term126 _111029 u v).
Proof. exact (@lem4834313 _111029 (term53 _111029 u v)). Qed.
Lemma lem4834315 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term127 _111029 u v x) = (term51 _111029 u v x).
Proof. exact (eq_refl (term127 _111029 u v x)). Qed.
Lemma lem4834316 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4834317 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term128 _111029 u v x) = (term124 _111029 u v x).
Proof. exact (MK_COMB (@lem4834316) (@lem4834315 _111029 u v x)). Qed.
Lemma lem4834318 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term128 _111029 u v x) = (term60 _111029 u v x).
Proof. exact (TRANS (@lem4834317 _111029 u v x) (@lem4834312 _111029 u v x)). Qed.
Lemma lem4834319 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term129 _111029 u v) = (term106 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834318 _111029 u v x)). Qed.
Lemma lem4834320 {_111029 : Type'} : (@ex _111029) = (@ex _111029).
Proof. exact (eq_refl (@ex _111029)). Qed.
Lemma lem4834321 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term126 _111029 u v) = (term107 _111029 u v).
Proof. exact (MK_COMB (@lem4834320 _111029) (@lem4834319 _111029 u v)). Qed.
Lemma lem4834322 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term125 _111029 u v) = (term107 _111029 u v).
Proof. exact (TRANS (@lem4834314 _111029 u v) (@lem4834321 _111029 u v)). Qed.
Lemma lem4834337 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : ((u x) = (v x)) = (term130 _111029 u v x).
Proof. exact (@lem17784 (u x) (v x)). Qed.
Lemma lem4834338 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term73 _111029 u v) = (term131 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834337 _111029 u v x)). Qed.
Lemma lem4834339 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834340 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term74 _111029 u v) = (term132 _111029 u v).
Proof. exact (MK_COMB (@lem4834339 _111029) (@lem4834338 _111029 u v)). Qed.
Lemma lem4834341 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term133 _111029 u v) = (term74 _111029 u v).
Proof. exact (@lem16933 (term74 _111029 u v)). Qed.
Lemma lem4834342 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term133 _111029 u v) = (term132 _111029 u v).
Proof. exact (TRANS (@lem4834341 _111029 u v) (@lem4834340 _111029 u v)). Qed.
Lemma lem4834343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4834344 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term134 _111029 u v) = (term135 _111029 u v).
Proof. exact (MK_COMB (@lem4834343) (@lem4834322 _111029 u v)). Qed.
Lemma lem4834345 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term136 _111029 u v) = (term137 _111029 u v).
Proof. exact (MK_COMB (@lem4834344 _111029 u v) (@lem4834342 _111029 u v)). Qed.
Lemma lem4834346 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term95 _111029 u v) = (term136 _111029 u v).
Proof. exact (@lem17045 (term54 _111029 u v) (term75 _111029 u v)). Qed.
Lemma lem4834347 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term95 _111029 u v) = (term137 _111029 u v).
Proof. exact (TRANS (@lem4834346 _111029 u v) (@lem4834345 _111029 u v)). Qed.
Lemma lem4834377 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4834378 {_111029 : Type'} (P : _111029 -> Prop) (Q : _111029 -> Prop) : (term138 _111029 P Q) = (term139 _111029 P Q).
Proof. exact (@lem4834377 _111029 P Q). Qed.
Lemma lem4834379 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term140 _111029 u v) = (term141 _111029 u v).
Proof. exact (@lem4834378 _111029 (term142 _111029 u v) (term97 _111029 u v)). Qed.
Lemma lem4834380 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term143 _111029 u v x) = (term144 _111029 u v x).
Proof. exact (eq_refl (term143 _111029 u v x)). Qed.
Lemma lem4834381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834382 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term145 _111029 u v x) = (term146 _111029 u v x).
Proof. exact (MK_COMB (@lem4834381) (@lem4834380 _111029 u v x)). Qed.
Lemma lem4834383 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term147 _111029 u v x) = (term96 _111029 u v x).
Proof. exact (eq_refl (term147 _111029 u v x)). Qed.
Lemma lem4834384 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term148 _111029 u v x) = (term130 _111029 u v x).
Proof. exact (MK_COMB (@lem4834382 _111029 u v x) (@lem4834383 _111029 u v x)). Qed.
Lemma lem4834385 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term149 _111029 u v) = (term131 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834384 _111029 u v x)). Qed.
Lemma lem4834386 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834387 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term140 _111029 u v) = (term132 _111029 u v).
Proof. exact (MK_COMB (@lem4834386 _111029) (@lem4834385 _111029 u v)). Qed.
Lemma lem4834388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4834389 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term150 _111029 u v) = (term151 _111029 u v).
Proof. exact (MK_COMB (@lem4834388) (@lem4834387 _111029 u v)). Qed.
Lemma lem4834390 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term143 _111029 u v x) = (term144 _111029 u v x).
Proof. exact (eq_refl (term143 _111029 u v x)). Qed.
Lemma lem4834391 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term152 _111029 u v) = (term142 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834390 _111029 u v x)). Qed.
Lemma lem4834392 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834393 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term153 _111029 u v) = (term154 _111029 u v).
Proof. exact (MK_COMB (@lem4834392 _111029) (@lem4834391 _111029 u v)). Qed.
Lemma lem4834394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834395 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term155 _111029 u v) = (term156 _111029 u v).
Proof. exact (MK_COMB (@lem4834394) (@lem4834393 _111029 u v)). Qed.
Lemma lem4834396 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term147 _111029 u v x) = (term96 _111029 u v x).
Proof. exact (eq_refl (term147 _111029 u v x)). Qed.
Lemma lem4834397 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term157 _111029 u v) = (term97 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834396 _111029 u v x)). Qed.
Lemma lem4834398 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834399 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term158 _111029 u v) = (term98 _111029 u v).
Proof. exact (MK_COMB (@lem4834398 _111029) (@lem4834397 _111029 u v)). Qed.
Lemma lem4834400 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term141 _111029 u v) = (term159 _111029 u v).
Proof. exact (MK_COMB (@lem4834395 _111029 u v) (@lem4834399 _111029 u v)). Qed.
Lemma lem4834401 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : ((term140 _111029 u v) = (term141 _111029 u v)) = ((term132 _111029 u v) = (term159 _111029 u v)).
Proof. exact (MK_COMB (@lem4834389 _111029 u v) (@lem4834400 _111029 u v)). Qed.
Lemma lem4834402 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term132 _111029 u v) = (term159 _111029 u v).
Proof. exact (EQ_MP (@lem4834401 _111029 u v) (@lem4834379 _111029 u v)). Qed.
Lemma lem4834463 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term135 _111029 u v) = (term135 _111029 u v).
Proof. exact (eq_refl (term135 _111029 u v)). Qed.
Lemma lem4834464 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term137 _111029 u v) = (term160 _111029 u v).
Proof. exact (MK_COMB (@lem4834463 _111029 u v) (@lem4834402 _111029 u v)). Qed.
Lemma lem4834466 {A : Type'} (P : A -> Prop) (Q : Prop) : (term161 A P Q) = (term162 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4834467 {_111029 : Type'} (P : _111029 -> Prop) (Q : Prop) : (term161 _111029 P Q) = (term162 _111029 P Q).
Proof. exact (@lem4834466 _111029 P Q). Qed.
Lemma lem4834468 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term163 _111029 u v) = (term164 _111029 u v).
Proof. exact (@lem4834467 _111029 (term106 _111029 u v) (term159 _111029 u v)). Qed.
Lemma lem4834469 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term114 _111029 u v x) = (term60 _111029 u v x).
Proof. exact (eq_refl (term114 _111029 u v x)). Qed.
Lemma lem4834470 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term115 _111029 u v) = (term106 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834469 _111029 u v x)). Qed.
Lemma lem4834471 {_111029 : Type'} : (@ex _111029) = (@ex _111029).
Proof. exact (eq_refl (@ex _111029)). Qed.
Lemma lem4834472 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term116 _111029 u v) = (term107 _111029 u v).
Proof. exact (MK_COMB (@lem4834471 _111029) (@lem4834470 _111029 u v)). Qed.
Lemma lem4834473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4834474 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term165 _111029 u v) = (term135 _111029 u v).
Proof. exact (MK_COMB (@lem4834473) (@lem4834472 _111029 u v)). Qed.
Lemma lem4834475 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term159 _111029 u v) = (term159 _111029 u v).
Proof. exact (eq_refl (term159 _111029 u v)). Qed.
Lemma lem4834476 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term163 _111029 u v) = (term160 _111029 u v).
Proof. exact (MK_COMB (@lem4834474 _111029 u v) (@lem4834475 _111029 u v)). Qed.
Lemma lem4834477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4834478 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term166 _111029 u v) = (term167 _111029 u v).
Proof. exact (MK_COMB (@lem4834477) (@lem4834476 _111029 u v)). Qed.
Lemma lem4834479 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term114 _111029 u v x) = (term60 _111029 u v x).
Proof. exact (eq_refl (term114 _111029 u v x)). Qed.
Lemma lem4834480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4834481 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term168 _111029 u v x) = (term169 _111029 u v x).
Proof. exact (MK_COMB (@lem4834480) (@lem4834479 _111029 u v x)). Qed.
Lemma lem4834482 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term159 _111029 u v) = (term159 _111029 u v).
Proof. exact (eq_refl (term159 _111029 u v)). Qed.
Lemma lem4834483 {_111029 : Type'} (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) : (term170 _111029 x u v) = (term171 _111029 x u v).
Proof. exact (MK_COMB (@lem4834481 _111029 u v x) (@lem4834482 _111029 u v)). Qed.
Lemma lem4834484 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term172 _111029 u v) = (term173 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834483 _111029 x u v)). Qed.
Lemma lem4834485 {_111029 : Type'} : (@ex _111029) = (@ex _111029).
Proof. exact (eq_refl (@ex _111029)). Qed.
Lemma lem4834486 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term164 _111029 u v) = (term174 _111029 u v).
Proof. exact (MK_COMB (@lem4834485 _111029) (@lem4834484 _111029 u v)). Qed.
Lemma lem4834487 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : ((term163 _111029 u v) = (term164 _111029 u v)) = ((term160 _111029 u v) = (term174 _111029 u v)).
Proof. exact (MK_COMB (@lem4834478 _111029 u v) (@lem4834486 _111029 u v)). Qed.
Lemma lem4834488 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term160 _111029 u v) = (term174 _111029 u v).
Proof. exact (EQ_MP (@lem4834487 _111029 u v) (@lem4834468 _111029 u v)). Qed.
Lemma lem4834489 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term137 _111029 u v) = (term174 _111029 u v).
Proof. exact (TRANS (@lem4834464 _111029 u v) (@lem4834488 _111029 u v)). Qed.
Lemma lem4834490 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term95 _111029 u v) = (term174 _111029 u v).
Proof. exact (TRANS (@lem4834347 _111029 u v) (@lem4834489 _111029 u v)). Qed.
Lemma lem4834491 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term95 _111029 u v) : term174 _111029 u v.
Proof. exact (EQ_MP (@lem4834490 _111029 u v) (@lem4834191 _111029 u v h1)). Qed.
Lemma lem4834492 {_111029 : Type'} (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term171 _111029 x u v) : term171 _111029 x u v.
Proof. exact (h1). Qed.
Lemma lem4834493 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term120 _111029 v u x'.
Proof. exact (h1). Qed.
Lemma lem4834504 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term96 _111029 u v x) = (term96 _111029 u v x).
Proof. exact (eq_refl (term96 _111029 u v x)). Qed.
Lemma lem4834505 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term97 _111029 u v) = (term97 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834504 _111029 u v x)). Qed.
Lemma lem4834506 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834507 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term98 _111029 u v) = (term98 _111029 u v).
Proof. exact (MK_COMB (@lem4834506 _111029) (@lem4834505 _111029 u v)). Qed.
Lemma lem4834518 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term144 _111029 u v x) = (term144 _111029 u v x).
Proof. exact (eq_refl (term144 _111029 u v x)). Qed.
Lemma lem4834519 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term142 _111029 u v) = (term142 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834518 _111029 u v x)). Qed.
Lemma lem4834520 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834521 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term154 _111029 u v) = (term154 _111029 u v).
Proof. exact (MK_COMB (@lem4834520 _111029) (@lem4834519 _111029 u v)). Qed.
Lemma lem4834522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834523 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term156 _111029 u v) = (term156 _111029 u v).
Proof. exact (MK_COMB (@lem4834522) (@lem4834521 _111029 u v)). Qed.
Lemma lem4834524 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term159 _111029 u v) = (term159 _111029 u v).
Proof. exact (MK_COMB (@lem4834523 _111029 u v) (@lem4834507 _111029 u v)). Qed.
Lemma lem4834537 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term169 _111029 u v x) = (term169 _111029 u v x).
Proof. exact (eq_refl (term169 _111029 u v x)). Qed.
Lemma lem4834538 {_111029 : Type'} (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) : (term171 _111029 x u v) = (term171 _111029 x u v).
Proof. exact (MK_COMB (@lem4834537 _111029 u v x) (@lem4834524 _111029 u v)). Qed.
Lemma lem4834539 {_111029 : Type'} (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term171 _111029 x u v) : term171 _111029 x u v.
Proof. exact (EQ_MP (@lem4834538 _111029 x u v) (@lem4834492 _111029 x u v h1)). Qed.
Lemma lem4834550 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) : (term60 _111029 v u x') = (term60 _111029 v u x').
Proof. exact (eq_refl (term60 _111029 v u x')). Qed.
Lemma lem4834561 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term96 _111029 u v x) = (term96 _111029 u v x).
Proof. exact (eq_refl (term96 _111029 u v x)). Qed.
Lemma lem4834562 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term97 _111029 u v) = (term97 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834561 _111029 u v x)). Qed.
Lemma lem4834563 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834564 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term98 _111029 u v) = (term98 _111029 u v).
Proof. exact (MK_COMB (@lem4834563 _111029) (@lem4834562 _111029 u v)). Qed.
Lemma lem4834565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834566 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term108 _111029 u v) = (term108 _111029 u v).
Proof. exact (MK_COMB (@lem4834565) (@lem4834564 _111029 u v)). Qed.
Lemma lem4834567 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) : (term120 _111029 v u x') = (term120 _111029 v u x').
Proof. exact (MK_COMB (@lem4834566 _111029 u v) (@lem4834550 _111029 v u x')). Qed.
Lemma lem4834568 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term120 _111029 v u x'.
Proof. exact (EQ_MP (@lem4834567 _111029 v u x') (@lem4834493 _111029 v u x' h1)). Qed.
Lemma lem4834569 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term60 _111029 v u x'.
Proof. exact (proj2 (@lem4834568 _111029 v u x' h1)). Qed.
Lemma lem4834570 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term98 _111029 u v.
Proof. exact (proj1 (@lem4834568 _111029 v u x' h1)). Qed.
Lemma lem4834573 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term60 _111029 u v x) : term60 _111029 u v x.
Proof. exact (h1). Qed.
Lemma lem4834574 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term159 _111029 u v) : term159 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834578 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term159 _111029 u v) : term154 _111029 u v.
Proof. exact (proj1 (@lem4834574 _111029 u v h1)). Qed.
Lemma lem4834586 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term96 _111029 u v x) = (term96 _111029 u v x).
Proof. exact (eq_refl (term96 _111029 u v x)). Qed.
Lemma lem4834587 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term97 _111029 u v) = (term97 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834586 _111029 u v x)). Qed.
Lemma lem4834588 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834590 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term98 _111029 u v) = (term98 _111029 u v).
Proof. exact (MK_COMB (@lem4834588 _111029) (@lem4834587 _111029 u v)). Qed.
Lemma lem4834591 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term98 _111029 u v.
Proof. exact (EQ_MP (@lem4834590 _111029 u v) (@lem4834570 _111029 v u x' h1)). Qed.
Lemma lem4834636 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) : (term144 _111029 u v x) = (term144 _111029 u v x).
Proof. exact (eq_refl (term144 _111029 u v x)). Qed.
Lemma lem4834637 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term142 _111029 u v) = (term142 _111029 u v).
Proof. exact (fun_ext (fun x : _111029 => @lem4834636 _111029 u v x)). Qed.
Lemma lem4834638 {_111029 : Type'} : (@all _111029) = (@all _111029).
Proof. exact (eq_refl (@all _111029)). Qed.
Lemma lem4834640 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term154 _111029 u v) = (term154 _111029 u v).
Proof. exact (MK_COMB (@lem4834638 _111029) (@lem4834637 _111029 u v)). Qed.
Lemma lem4834641 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term159 _111029 u v) : term154 _111029 u v.
Proof. exact (EQ_MP (@lem4834640 _111029 u v) (@lem4834578 _111029 u v h1)). Qed.
Lemma lem4834655 {_111029 : Type'} (_59859 : _111029) (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term147 _111029 u v _59859.
Proof. exact (@lem4834591 _111029 v u x' h1 _59859). Qed.
Lemma lem4834656 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (_59859 : _111029) : (term147 _111029 u v _59859) = (term96 _111029 u v _59859).
Proof. exact (eq_refl (term147 _111029 u v _59859)). Qed.
Lemma lem4834661 {_111029 : Type'} (_59861 : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term159 _111029 u v) : term143 _111029 u v _59861.
Proof. exact (@lem4834641 _111029 u v h1 _59861). Qed.
Lemma lem4834662 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (_59861 : _111029) : (term143 _111029 u v _59861) = (term144 _111029 u v _59861).
Proof. exact (eq_refl (term143 _111029 u v _59861)). Qed.
Lemma lem4834672 {_111029 : Type'} (_59859 : _111029) (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term96 _111029 u v _59859.
Proof. exact (EQ_MP (@lem4834656 _111029 u v _59859) (@lem4834655 _111029 _59859 v u x' h1)). Qed.
Lemma lem4834680 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term60 _111029 u v x) : term59 _111029 v x.
Proof. exact (proj2 (@lem4834573 _111029 u v x h1)). Qed.
Lemma lem4834690 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term59 _111029 u x'.
Proof. exact (proj2 (@lem4834569 _111029 v u x' h1)). Qed.
Lemma lem4834696 {_111029 : Type'} (_59861 : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term159 _111029 u v) : term144 _111029 u v _59861.
Proof. exact (EQ_MP (@lem4834662 _111029 u v _59861) (@lem4834661 _111029 _59861 u v h1)). Qed.
Lemma lem4834704 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term60 _111029 u v x) : u x.
Proof. exact (proj1 (@lem4834573 _111029 u v x h1)). Qed.
Lemma lem4834705 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term60 _111029 u v x) : term175 _111029 u x.
Proof. exact (fun h0 : term59 _111029 u x => @lem4834704 _111029 u v x h1). Qed.
Lemma lem4834707 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4834708 {_111029 : Type'} (u : _111029 -> Prop) (x : _111029) : (term175 _111029 u x) = (u x).
Proof. exact (@lem4834707 (u x)). Qed.
Lemma lem4834709 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term60 _111029 u v x) : u x.
Proof. exact (EQ_MP (@lem4834708 _111029 u x) (@lem4834705 _111029 u v x h1)). Qed.
Lemma lem4834715 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4834716 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59859 : _111029) : (term96 _111029 u v _59859) = (term144 _111029 v u _59859).
Proof. exact (@lem4834715 (v _59859) (term59 _111029 u _59859)). Qed.
Lemma lem4834722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4834723 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59859 : _111029) : (term177 _111029 u v _59859) = (term178 _111029 v u _59859).
Proof. exact (MK_COMB (@lem4834722) (@lem4834716 _111029 v u _59859)). Qed.
Lemma lem4834729 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59859 : _111029) : (term144 _111029 v u _59859) = (term144 _111029 v u _59859).
Proof. exact (eq_refl (term144 _111029 v u _59859)). Qed.
Lemma lem4834730 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59859 : _111029) : ((term96 _111029 u v _59859) = (term144 _111029 v u _59859)) = ((term144 _111029 v u _59859) = (term144 _111029 v u _59859)).
Proof. exact (MK_COMB (@lem4834723 _111029 v u _59859) (@lem4834729 _111029 v u _59859)). Qed.
Lemma lem4834732 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4834733 (x : Prop) : (x = x) = True.
Proof. exact (@lem4834732 Prop x). Qed.
Lemma lem4834734 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59859 : _111029) : ((term144 _111029 v u _59859) = (term144 _111029 v u _59859)) = True.
Proof. exact (@lem4834733 (term144 _111029 v u _59859)). Qed.
Lemma lem4834735 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59859 : _111029) : ((term96 _111029 u v _59859) = (term144 _111029 v u _59859)) = True.
Proof. exact (TRANS (@lem4834730 _111029 v u _59859) (@lem4834734 _111029 v u _59859)). Qed.
Lemma lem4834736 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59859 : _111029) : True = ((term96 _111029 u v _59859) = (term144 _111029 v u _59859)).
Proof. exact (SYM (@lem4834735 _111029 v u _59859)). Qed.
Lemma lem4834737 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59859 : _111029) : (term96 _111029 u v _59859) = (term144 _111029 v u _59859).
Proof. exact (EQ_MP (@lem4834736 _111029 v u _59859) (@lem0)). Qed.
Lemma lem4834738 {_111029 : Type'} (_59859 : _111029) (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term144 _111029 v u _59859.
Proof. exact (EQ_MP (@lem4834737 _111029 v u _59859) (@lem4834672 _111029 _59859 v u x' h1)). Qed.
Lemma lem4834740 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4834741 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (_59859 : _111029) : (term144 _111029 v u _59859) = (term180 _111029 u v _59859).
Proof. exact (@lem4834740 (term59 _111029 u _59859) (v _59859)). Qed.
Lemma lem4834743 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4834744 {_111029 : Type'} (u : _111029 -> Prop) (_59859 : _111029) : (term181 _111029 u _59859) = (u _59859).
Proof. exact (@lem4834743 (u _59859)). Qed.
Lemma lem4834745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4834746 {_111029 : Type'} (u : _111029 -> Prop) (_59859 : _111029) : (term182 _111029 u _59859) = (term49 _111029 u _59859).
Proof. exact (MK_COMB (@lem4834745) (@lem4834744 _111029 u _59859)). Qed.
Lemma lem4834747 {_111029 : Type'} (v : _111029 -> Prop) (_59859 : _111029) : (v _59859) = (v _59859).
Proof. exact (eq_refl (v _59859)). Qed.
Lemma lem4834748 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (_59859 : _111029) : (term180 _111029 u v _59859) = (term51 _111029 u v _59859).
Proof. exact (MK_COMB (@lem4834746 _111029 u _59859) (@lem4834747 _111029 v _59859)). Qed.
Lemma lem4834749 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (_59859 : _111029) : (term144 _111029 v u _59859) = (term51 _111029 u v _59859).
Proof. exact (TRANS (@lem4834741 _111029 u v _59859) (@lem4834748 _111029 u v _59859)). Qed.
Lemma lem4834752 {_111029 : Type'} (_59859 : _111029) (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term51 _111029 u v _59859.
Proof. exact (EQ_MP (@lem4834749 _111029 u v _59859) (@lem4834738 _111029 _59859 v u x' h1)). Qed.
Lemma lem4834753 {_111029 : Type'} (_59859 : _111029) (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term51 _111029 u v _59859.
Proof. exact (@lem4834752 _111029 _59859 v u x' h1). Qed.
Lemma lem4834754 {_111029 : Type'} (x : _111029) (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term51 _111029 u v x.
Proof. exact (@lem4834753 _111029 x v u x' h1). Qed.
Lemma lem4834757 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term120 _111029 v u x') (h2 : term60 _111029 u v x) : v x.
Proof. exact (@lem4834754 _111029 x v u x' h1 (@lem4834709 _111029 u v x h2)). Qed.
Lemma lem4834758 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term120 _111029 v u x') (h2 : term60 _111029 u v x) : term175 _111029 v x.
Proof. exact (fun h0 : term59 _111029 v x => @lem4834757 _111029 x' u v x h1 h2). Qed.
Lemma lem4834760 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4834761 {_111029 : Type'} (v : _111029 -> Prop) (x : _111029) : (term175 _111029 v x) = (v x).
Proof. exact (@lem4834760 (v x)). Qed.
Lemma lem4834762 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term120 _111029 v u x') (h2 : term60 _111029 u v x) : v x.
Proof. exact (EQ_MP (@lem4834761 _111029 v x) (@lem4834758 _111029 x' u v x h1 h2)). Qed.
Lemma lem4834765 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4834767 {_111029 : Type'} (v : _111029 -> Prop) (x : _111029) : (term59 _111029 v x) = (term183 _111029 v x).
Proof. exact (@lem4834765 (v x)). Qed.
Lemma lem4834770 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term60 _111029 u v x) : term183 _111029 v x.
Proof. exact (EQ_MP (@lem4834767 _111029 v x) (@lem4834680 _111029 u v x h1)). Qed.
Lemma lem4834773 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term120 _111029 v u x') (h2 : term60 _111029 u v x) : False.
Proof. exact (@lem4834770 _111029 u v x h2 (@lem4834762 _111029 x' u v x h1 h2)). Qed.
Lemma lem4834774 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term120 _111029 v u x') (h2 : term60 _111029 u v x) : term184.
Proof. exact (fun h0 : ~ False => @lem4834773 _111029 x' u v x h1 h2). Qed.
Lemma lem4834776 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4834777 : term184 = False.
Proof. exact (@lem4834776 False). Qed.
Lemma lem4834778 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (x : _111029) (h1 : term120 _111029 v u x') (h2 : term60 _111029 u v x) : False.
Proof. exact (EQ_MP (@lem4834777) (@lem4834774 _111029 x' u v x h1 h2)). Qed.
Lemma lem4834780 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : v x'.
Proof. exact (proj1 (@lem4834569 _111029 v u x' h1)). Qed.
Lemma lem4834781 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term175 _111029 v x'.
Proof. exact (fun h0 : term59 _111029 v x' => @lem4834780 _111029 v u x' h1). Qed.
Lemma lem4834783 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4834784 {_111029 : Type'} (v : _111029 -> Prop) (x' : _111029) : (term175 _111029 v x') = (v x').
Proof. exact (@lem4834783 (v x')). Qed.
Lemma lem4834785 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : v x'.
Proof. exact (EQ_MP (@lem4834784 _111029 v x') (@lem4834781 _111029 v u x' h1)). Qed.
Lemma lem4834787 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4834788 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59861 : _111029) : (term144 _111029 u v _59861) = (term180 _111029 v u _59861).
Proof. exact (@lem4834787 (term59 _111029 v _59861) (u _59861)). Qed.
Lemma lem4834790 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4834791 {_111029 : Type'} (v : _111029 -> Prop) (_59861 : _111029) : (term181 _111029 v _59861) = (v _59861).
Proof. exact (@lem4834790 (v _59861)). Qed.
Lemma lem4834792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4834793 {_111029 : Type'} (v : _111029 -> Prop) (_59861 : _111029) : (term182 _111029 v _59861) = (term49 _111029 v _59861).
Proof. exact (MK_COMB (@lem4834792) (@lem4834791 _111029 v _59861)). Qed.
Lemma lem4834794 {_111029 : Type'} (u : _111029 -> Prop) (_59861 : _111029) : (u _59861) = (u _59861).
Proof. exact (eq_refl (u _59861)). Qed.
Lemma lem4834795 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59861 : _111029) : (term180 _111029 v u _59861) = (term51 _111029 v u _59861).
Proof. exact (MK_COMB (@lem4834793 _111029 v _59861) (@lem4834794 _111029 u _59861)). Qed.
Lemma lem4834796 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (_59861 : _111029) : (term144 _111029 u v _59861) = (term51 _111029 v u _59861).
Proof. exact (TRANS (@lem4834788 _111029 v u _59861) (@lem4834795 _111029 v u _59861)). Qed.
Lemma lem4834799 {_111029 : Type'} (_59861 : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term159 _111029 u v) : term51 _111029 v u _59861.
Proof. exact (EQ_MP (@lem4834796 _111029 v u _59861) (@lem4834696 _111029 _59861 u v h1)). Qed.
Lemma lem4834800 {_111029 : Type'} (_59861 : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term159 _111029 u v) : term51 _111029 v u _59861.
Proof. exact (@lem4834799 _111029 _59861 u v h1). Qed.
Lemma lem4834801 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term159 _111029 u v) : term51 _111029 v u x'.
Proof. exact (@lem4834800 _111029 x' u v h1). Qed.
Lemma lem4834804 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term159 _111029 u v) : u x'.
Proof. exact (@lem4834801 _111029 x' u v h2 (@lem4834785 _111029 v u x' h1)). Qed.
Lemma lem4834805 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term159 _111029 u v) : term175 _111029 u x'.
Proof. exact (fun h0 : term59 _111029 u x' => @lem4834804 _111029 x' u v h1 h2). Qed.
Lemma lem4834807 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4834808 {_111029 : Type'} (u : _111029 -> Prop) (x' : _111029) : (term175 _111029 u x') = (u x').
Proof. exact (@lem4834807 (u x')). Qed.
Lemma lem4834809 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term159 _111029 u v) : u x'.
Proof. exact (EQ_MP (@lem4834808 _111029 u x') (@lem4834805 _111029 x' u v h1 h2)). Qed.
Lemma lem4834812 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4834814 {_111029 : Type'} (u : _111029 -> Prop) (x' : _111029) : (term59 _111029 u x') = (term183 _111029 u x').
Proof. exact (@lem4834812 (u x')). Qed.
Lemma lem4834817 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (x' : _111029) (h1 : term120 _111029 v u x') : term183 _111029 u x'.
Proof. exact (EQ_MP (@lem4834814 _111029 u x') (@lem4834690 _111029 v u x' h1)). Qed.
Lemma lem4834820 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term159 _111029 u v) : False.
Proof. exact (@lem4834817 _111029 v u x' h1 (@lem4834809 _111029 x' u v h1 h2)). Qed.
Lemma lem4834821 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term159 _111029 u v) : term184.
Proof. exact (fun h0 : ~ False => @lem4834820 _111029 x' u v h1 h2). Qed.
Lemma lem4834823 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4834824 : term184 = False.
Proof. exact (@lem4834823 False). Qed.
Lemma lem4834825 {_111029 : Type'} (x' : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term159 _111029 u v) : False.
Proof. exact (EQ_MP (@lem4834824) (@lem4834821 _111029 x' u v h1 h2)). Qed.
Lemma lem4834826 {_111029 : Type'} (x' : _111029) (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term171 _111029 x u v) : False.
Proof. exact (or_elim (@lem4834539 _111029 x u v h2) (fun h0 : term60 _111029 u v x => @lem4834778 _111029 x' u v x h1 h0) (fun h0 : term159 _111029 u v => @lem4834825 _111029 x' u v h1 h0)). Qed.
Lemma lem4834827 {_111029 : Type'} (x' : _111029) (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term171 _111029 x u v) : (term120 _111029 v u x') = False.
Proof. exact (prop_ext (fun h3 : term120 _111029 v u x' => @lem4834826 _111029 x' x u v h1 h2) (fun h3 : False => @lem4834568 _111029 v u x' h1)). Qed.
Lemma lem4834828 {_111029 : Type'} (x' : _111029) (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term171 _111029 x u v) : False.
Proof. exact (EQ_MP (@lem4834827 _111029 x' x u v h1 h2) (@lem4834568 _111029 v u x' h1)). Qed.
Lemma lem4834829 {_111029 : Type'} (x' : _111029) (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term171 _111029 x u v) : (term171 _111029 x u v) = False.
Proof. exact (prop_ext (fun h3 : term171 _111029 x u v => @lem4834828 _111029 x' x u v h1 h2) (fun h3 : False => @lem4834539 _111029 x u v h2)). Qed.
Lemma lem4834830 {_111029 : Type'} (x' : _111029) (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term120 _111029 v u x') (h2 : term171 _111029 x u v) : False.
Proof. exact (EQ_MP (@lem4834829 _111029 x' x u v h1 h2) (@lem4834539 _111029 x u v h2)). Qed.
Lemma lem4834831 {_111029 : Type'} (x : _111029) (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term68 _111029 v u) (h2 : term171 _111029 x u v) : False.
Proof. exact (ex_elim (@lem4834305 _111029 v u h1) (fun x' : _111029 => fun h0 : term122 _111029 v u x' => @lem4834830 _111029 x' x u v h0 h2)). Qed.
Lemma lem4834832 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term95 _111029 u v) (h2 : term68 _111029 v u) : False.
Proof. exact (ex_elim (@lem4834491 _111029 u v h1) (fun x : _111029 => fun h0 : term173 _111029 u v x => @lem4834831 _111029 x u v h2 h0)). Qed.
Lemma lem4834833 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term95 _111029 u v) (h2 : term68 _111029 v u) : (term95 _111029 u v) = False.
Proof. exact (prop_ext (fun h3 : term95 _111029 u v => @lem4834832 _111029 v u h1 h2) (fun h3 : False => @lem4834191 _111029 u v h1)). Qed.
Lemma lem4834834 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term95 _111029 u v) (h2 : term68 _111029 v u) : False.
Proof. exact (EQ_MP (@lem4834833 _111029 v u h1 h2) (@lem4834191 _111029 u v h1)). Qed.
Lemma lem4834835 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term68 _111029 v u) : term94 _111029 u v.
Proof. exact (fun h0 : term95 _111029 u v => @lem4834834 _111029 v u h0 h1). Qed.
Lemma lem4834836 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term68 _111029 v u) : term76 _111029 u v.
Proof. exact (EQ_MP (@lem4834190 _111029 u v) (@lem4834835 _111029 v u h1)). Qed.
Lemma lem4834837 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term77 _111029 u v.
Proof. exact (fun h0 : term68 _111029 v u => @lem4834836 _111029 v u h0). Qed.
Lemma lem4834842 {_111029 : Type'} (v : _111029 -> Prop) : term89 _111029 v.
Proof. exact (fun u : _111029 -> Prop => @lem4834837 _111029 u v). Qed.
Lemma lem4834847 {_111029 : Type'} : term93 _111029.
Proof. exact (fun v : _111029 -> Prop => @lem4834842 _111029 v). Qed.
Lemma lem4834848 {_111029 : Type'} : term92 _111029.
Proof. exact (EQ_MP (@lem4834185 _111029) (@lem4834847 _111029)). Qed.
Lemma lem4834849 {_111029 : Type'} (v : _111029 -> Prop) : term185 _111029 v.
Proof. exact (@lem4834848 _111029 v). Qed.
Lemma lem4834850 {_111029 : Type'} (v : _111029 -> Prop) : (term185 _111029 v) = (term88 _111029 v).
Proof. exact (eq_refl (term185 _111029 v)). Qed.
Lemma lem4834851 {_111029 : Type'} (v : _111029 -> Prop) : term88 _111029 v.
Proof. exact (EQ_MP (@lem4834850 _111029 v) (@lem4834849 _111029 v)). Qed.
Lemma lem4834852 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) : term186 _111029 v u.
Proof. exact (@lem4834851 _111029 v u). Qed.
Lemma lem4834853 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : (term186 _111029 v u) = (term79 _111029 u v).
Proof. exact (eq_refl (term186 _111029 v u)). Qed.
Lemma lem4834854 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term79 _111029 u v.
Proof. exact (EQ_MP (@lem4834853 _111029 u v) (@lem4834852 _111029 v u)). Qed.
Lemma lem4834856 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term79 _111029 u v.
Proof. exact (@lem4834017 _111029 u v (@lem4834854 _111029 u v)). Qed.
Lemma lem4834857 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term80 _111029 u v) : False.
Proof. exact (@lem4834856 _111029 u v (@lem4834001 _111029 u v h1)). Qed.
Lemma lem4834858 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term80 _111029 u v) : (term80 _111029 u v) = False.
Proof. exact (prop_ext (fun h2 : term80 _111029 u v => @lem4834857 _111029 u v h1) (fun h2 : False => @lem4834001 _111029 u v h1)). Qed.
Lemma lem4834859 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term80 _111029 u v) : False.
Proof. exact (EQ_MP (@lem4834858 _111029 u v h1) (@lem4834001 _111029 u v h1)). Qed.
Lemma lem4834860 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term79 _111029 u v.
Proof. exact (fun h0 : term80 _111029 u v => @lem4834859 _111029 u v h0). Qed.
Lemma lem4834861 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term77 _111029 u v.
Proof. exact (EQ_MP (@lem4834000 _111029 u v) (@lem4834860 _111029 u v)). Qed.
Lemma lem4834862 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term47 _111029 u v.
Proof. exact (EQ_MP (@lem4833996 _111029 u v) (@lem4834861 _111029 u v)). Qed.
Lemma lem4834863 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term46 _111029 u v.
Proof. exact (EQ_MP (@lem4833845 _111029 u v) (@lem4834862 _111029 u v)). Qed.
Lemma lem4834864 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term46 _111029 u v) : term46 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834865 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term38 _111029 v u) : term38 _111029 v u.
Proof. exact (h1). Qed.
Lemma lem4834866 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term38 _111029 v u) (h2 : term46 _111029 u v) : @PSUBSET _111029 u v.
Proof. exact (@lem4834864 _111029 u v h2 (@lem4834865 _111029 v u h1)). Qed.
Lemma lem4834867 {_111029 : Type'} (v : _111029 -> Prop) (u : _111029 -> Prop) (h1 : term38 _111029 v u) : term187 _111029 u v.
Proof. exact (fun h0 : term46 _111029 u v => @lem4834866 _111029 u v h1 h0). Qed.
Lemma lem4834868 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term46 _111029 u v) : term46 _111029 u v.
Proof. exact (h1). Qed.
Lemma lem4834869 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term38 _111029 v u) (h2 : term46 _111029 u v) : @PSUBSET _111029 u v.
Proof. exact (@lem4834867 _111029 v u h1 (@lem4834868 _111029 u v h2)). Qed.
Lemma lem4834870 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) (h1 : term46 _111029 u v) : term46 _111029 u v.
Proof. exact (fun h0 : term38 _111029 v u => @lem4834869 _111029 u v h0 h1). Qed.
Lemma lem4834871 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term188 _111029 u v.
Proof. exact (fun h0 : term46 _111029 u v => @lem4834870 _111029 u v h0). Qed.
Lemma lem4834873 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term189 A u v) : term189 A u v.
Proof. exact (h1). Qed.
Lemma lem4834874 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) : term190 A u v.
Proof. exact (h1). Qed.
Lemma lem4834875 {A : Type'} (v : type686 A) (h1 : @pairwise (A -> Prop) (@DISJOINT A) v) : @pairwise (A -> Prop) (@DISJOINT A) v.
Proof. exact (h1). Qed.
Lemma lem4834877 {_111029 : Type'} (u : _111029 -> Prop) (v : _111029 -> Prop) : term46 _111029 u v.
Proof. exact (@lem4834871 _111029 u v (@lem4834863 _111029 u v)). Qed.
Lemma lem4834878 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term46 A u v.
Proof. exact (@lem4834877 A u v). Qed.
Lemma lem4834879 {A : Type'} (u : type686 A) (v : type686 A) : term191 A u v.
Proof. exact (@lem4834878 A (@UNIONS A u) (@UNIONS A v)). Qed.
Lemma lem4834890 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term192 A u v.
Proof. exact (conj (@lem4834874 A u v h1) (@lem4834875 A v h2)). Qed.
Lemma lem4834896 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term42 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem4834897 {A : Type'} (s : type686 A) (t : type686 A) : (@PSUBSET (A -> Prop) s t) = (term193 A s t).
Proof. exact (@lem4834896 (A -> Prop) s t). Qed.
Lemma lem4834898 {A : Type'} (u : type686 A) (v : type686 A) : (term190 A u v) = (term194 A u v).
Proof. exact (@lem4834897 A u (@DELETE (A -> Prop) v (@EMPTY A))). Qed.
Lemma lem4834902 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4834903 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term195 A s t).
Proof. exact (@lem4834902 (A -> Prop) s t). Qed.
Lemma lem4834904 {A : Type'} (u : type686 A) (v : type686 A) : (term196 A u v) = (term197 A u v).
Proof. exact (@lem4834903 A u (@DELETE (A -> Prop) v (@EMPTY A))). Qed.
Lemma lem4834911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834912 {A : Type'} (u : type686 A) (v : type686 A) : (term198 A u v) = (term199 A u v).
Proof. exact (MK_COMB (@lem4834911) (@lem4834904 A u v)). Qed.
Lemma lem4834916 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term34 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4834917 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term200 A s t).
Proof. exact (@lem4834916 (A -> Prop) s t). Qed.
Lemma lem4834918 {A : Type'} (u : type686 A) (v : type686 A) : (u = (@DELETE (A -> Prop) v (@EMPTY A))) = (term201 A u v).
Proof. exact (@lem4834917 A u (@DELETE (A -> Prop) v (@EMPTY A))). Qed.
Lemma lem4834927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4834928 {A : Type'} (u : type686 A) (v : type686 A) : (term202 A u v) = (term203 A u v).
Proof. exact (MK_COMB (@lem4834927) (@lem4834918 A u v)). Qed.
Lemma lem4834929 {A : Type'} (u : type686 A) (v : type686 A) : (term194 A u v) = (term204 A u v).
Proof. exact (MK_COMB (@lem4834912 A u v) (@lem4834928 A u v)). Qed.
Lemma lem4834932 {A : Type'} (u : type686 A) (v : type686 A) : (term190 A u v) = (term204 A u v).
Proof. exact (TRANS (@lem4834898 A u v) (@lem4834929 A u v)). Qed.
Lemma lem4834933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834934 {A : Type'} (u : type686 A) (v : type686 A) : (term205 A u v) = (term206 A u v).
Proof. exact (MK_COMB (@lem4834933) (@lem4834932 A u v)). Qed.
Lemma lem4834935 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4834936 {A : Type'} (u : type686 A) (v : type686 A) : (term192 A u v) = (term207 A u v).
Proof. exact (MK_COMB (@lem4834934 A u v) (@lem4834935 A v)). Qed.
Lemma lem4834939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4834940 {A : Type'} (u : type686 A) (v : type686 A) : (term208 A u v) = (term209 A u v).
Proof. exact (MK_COMB (@lem4834939) (@lem4834936 A u v)). Qed.
Lemma lem4834942 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4834943 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term31 A s t).
Proof. exact (@lem4834942 A s t). Qed.
Lemma lem4834944 {A : Type'} (u : type686 A) (v : type686 A) : (term210 A u v) = (term211 A u v).
Proof. exact (@lem4834943 A (@UNIONS A u) (@UNIONS A v)). Qed.
Lemma lem4834951 {A : Type'} (u : type686 A) (v : type686 A) : (term212 A u v) = (term213 A u v).
Proof. exact (MK_COMB (@lem4834940 A u v) (@lem4834944 A u v)). Qed.
Lemma lem4834954 {A : Type'} (u : type686 A) (v : type686 A) : (term213 A u v) = (term212 A u v).
Proof. exact (SYM (@lem4834951 A u v)). Qed.
Lemma lem4834968 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4834969 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4834968 (A -> Prop) P x). Qed.
Lemma lem4834970 {A : Type'} (u : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x u) = (u x).
Proof. exact (@lem4834969 A u x). Qed.
Lemma lem4834971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4834972 {A : Type'} (u : type686 A) (x : A -> Prop) : (term214 A x u) = (term215 A u x).
Proof. exact (MK_COMB (@lem4834971) (@lem4834970 A u x)). Qed.
Lemma lem4834974 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term19 A x s y) = (term20 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4834975 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term216 A x s y) = (term217 A s x y).
Proof. exact (@lem4834974 (A -> Prop) s x y). Qed.
Lemma lem4834976 {A : Type'} (v : type686 A) (x : A -> Prop) : (term218 A x v) = (term219 A v x).
Proof. exact (@lem4834975 A v x (@EMPTY A)). Qed.
Lemma lem4834980 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4834981 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4834980 (A -> Prop) P x). Qed.
Lemma lem4834982 {A : Type'} (v : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x v) = (v x).
Proof. exact (@lem4834981 A v x). Qed.
Lemma lem4834983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4834984 {A : Type'} (v : type686 A) (x : A -> Prop) : (term220 A x v) = (term221 A v x).
Proof. exact (MK_COMB (@lem4834983) (@lem4834982 A v x)). Qed.
Lemma lem4834987 {A : Type'} (x : A -> Prop) : (term222 A x) = (term222 A x).
Proof. exact (eq_refl (term222 A x)). Qed.
Lemma lem4834988 {A : Type'} (v : type686 A) (x : A -> Prop) : (term219 A v x) = (term223 A v x).
Proof. exact (MK_COMB (@lem4834984 A v x) (@lem4834987 A x)). Qed.
Lemma lem4834991 {A : Type'} (v : type686 A) (x : A -> Prop) : (term218 A x v) = (term223 A v x).
Proof. exact (TRANS (@lem4834976 A v x) (@lem4834988 A v x)). Qed.
Lemma lem4834992 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term224 A u x v) = (term225 A u v x).
Proof. exact (MK_COMB (@lem4834972 A u x) (@lem4834991 A v x)). Qed.
Lemma lem4834995 {A : Type'} (u : type686 A) (v : type686 A) : (term226 A u v) = (term227 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4834992 A u v x)). Qed.
Lemma lem4834996 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4834997 {A : Type'} (u : type686 A) (v : type686 A) : (term197 A u v) = (term228 A u v).
Proof. exact (MK_COMB (@lem4834996 A) (@lem4834995 A u v)). Qed.
Lemma lem4835002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835003 {A : Type'} (u : type686 A) (v : type686 A) : (term199 A u v) = (term229 A u v).
Proof. exact (MK_COMB (@lem4835002) (@lem4834997 A u v)). Qed.
Lemma lem4835011 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4835012 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4835011 (A -> Prop) P x). Qed.
Lemma lem4835013 {A : Type'} (u : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x u) = (u x).
Proof. exact (@lem4835012 A u x). Qed.
Lemma lem4835014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4835015 {A : Type'} (u : type686 A) (x : A -> Prop) : (term230 A x u) = (term231 A u x).
Proof. exact (MK_COMB (@lem4835014) (@lem4835013 A u x)). Qed.
Lemma lem4835017 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term19 A x s y) = (term20 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4835018 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term216 A x s y) = (term217 A s x y).
Proof. exact (@lem4835017 (A -> Prop) s x y). Qed.
Lemma lem4835019 {A : Type'} (v : type686 A) (x : A -> Prop) : (term218 A x v) = (term219 A v x).
Proof. exact (@lem4835018 A v x (@EMPTY A)). Qed.
Lemma lem4835023 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4835024 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4835023 (A -> Prop) P x). Qed.
Lemma lem4835025 {A : Type'} (v : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x v) = (v x).
Proof. exact (@lem4835024 A v x). Qed.
Lemma lem4835026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835027 {A : Type'} (v : type686 A) (x : A -> Prop) : (term220 A x v) = (term221 A v x).
Proof. exact (MK_COMB (@lem4835026) (@lem4835025 A v x)). Qed.
Lemma lem4835030 {A : Type'} (x : A -> Prop) : (term222 A x) = (term222 A x).
Proof. exact (eq_refl (term222 A x)). Qed.
Lemma lem4835031 {A : Type'} (v : type686 A) (x : A -> Prop) : (term219 A v x) = (term223 A v x).
Proof. exact (MK_COMB (@lem4835027 A v x) (@lem4835030 A x)). Qed.
Lemma lem4835034 {A : Type'} (v : type686 A) (x : A -> Prop) : (term218 A x v) = (term223 A v x).
Proof. exact (TRANS (@lem4835019 A v x) (@lem4835031 A v x)). Qed.
Lemma lem4835035 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x u) = (term218 A x v)) = ((u x) = (term223 A v x)).
Proof. exact (MK_COMB (@lem4835015 A u x) (@lem4835034 A v x)). Qed.
Lemma lem4835038 {A : Type'} (u : type686 A) (v : type686 A) : (term232 A u v) = (term233 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835035 A u v x)). Qed.
Lemma lem4835039 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4835040 {A : Type'} (u : type686 A) (v : type686 A) : (term201 A u v) = (term234 A u v).
Proof. exact (MK_COMB (@lem4835039 A) (@lem4835038 A u v)). Qed.
Lemma lem4835045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835046 {A : Type'} (u : type686 A) (v : type686 A) : (term203 A u v) = (term235 A u v).
Proof. exact (MK_COMB (@lem4835045) (@lem4835040 A u v)). Qed.
Lemma lem4835047 {A : Type'} (u : type686 A) (v : type686 A) : (term204 A u v) = (term236 A u v).
Proof. exact (MK_COMB (@lem4835003 A u v) (@lem4835046 A u v)). Qed.
Lemma lem4835050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835051 {A : Type'} (u : type686 A) (v : type686 A) : (term206 A u v) = (term237 A u v).
Proof. exact (MK_COMB (@lem4835050) (@lem4835047 A u v)). Qed.
Lemma lem4835052 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4835053 {A : Type'} (u : type686 A) (v : type686 A) : (term207 A u v) = (term238 A u v).
Proof. exact (MK_COMB (@lem4835051 A u v) (@lem4835052 A v)). Qed.
Lemma lem4835056 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4835057 {A : Type'} (u : type686 A) (v : type686 A) : (term209 A u v) = (term239 A u v).
Proof. exact (MK_COMB (@lem4835056) (@lem4835053 A u v)). Qed.
Lemma lem4835065 {A : Type'} (s : type686 A) (x : A) : (term240 A x s) = (term241 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4835066 {A : Type'} (s : type686 A) (x : A) : (term240 A x s) = (term241 A s x).
Proof. exact (@lem4835065 A s x). Qed.
Lemma lem4835067 {A : Type'} (u : type686 A) (x : A) : (term240 A x u) = (term241 A u x).
Proof. exact (@lem4835066 A u x). Qed.
Lemma lem4835075 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4835076 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4835075 (A -> Prop) P x). Qed.
Lemma lem4835077 {A : Type'} (u : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t u) = (u t).
Proof. exact (@lem4835076 A u t). Qed.
Lemma lem4835078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835079 {A : Type'} (u : type686 A) (t : A -> Prop) : (term220 A t u) = (term221 A u t).
Proof. exact (MK_COMB (@lem4835078) (@lem4835077 A u t)). Qed.
Lemma lem4835081 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4835082 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4835081 A P x). Qed.
Lemma lem4835083 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4835082 A t x). Qed.
Lemma lem4835084 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term242 A u x t) = (term243 A u t x).
Proof. exact (MK_COMB (@lem4835079 A u t) (@lem4835083 A t x)). Qed.
Lemma lem4835087 {A : Type'} (u : type686 A) (x : A) : (term244 A u x) = (term245 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4835084 A u t x)). Qed.
Lemma lem4835088 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835089 {A : Type'} (u : type686 A) (x : A) : (term241 A u x) = (term246 A u x).
Proof. exact (MK_COMB (@lem4835088 A) (@lem4835087 A u x)). Qed.
Lemma lem4835094 {A : Type'} (u : type686 A) (x : A) : (term240 A x u) = (term246 A u x).
Proof. exact (TRANS (@lem4835067 A u x) (@lem4835089 A u x)). Qed.
Lemma lem4835095 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4835096 {A : Type'} (u : type686 A) (x : A) : (term247 A x u) = (term248 A u x).
Proof. exact (MK_COMB (@lem4835095) (@lem4835094 A u x)). Qed.
Lemma lem4835098 {A : Type'} (s : type686 A) (x : A) : (term240 A x s) = (term241 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4835099 {A : Type'} (s : type686 A) (x : A) : (term240 A x s) = (term241 A s x).
Proof. exact (@lem4835098 A s x). Qed.
Lemma lem4835100 {A : Type'} (v : type686 A) (x : A) : (term240 A x v) = (term241 A v x).
Proof. exact (@lem4835099 A v x). Qed.
Lemma lem4835108 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4835109 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4835108 (A -> Prop) P x). Qed.
Lemma lem4835110 {A : Type'} (v : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t v) = (v t).
Proof. exact (@lem4835109 A v t). Qed.
Lemma lem4835111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835112 {A : Type'} (v : type686 A) (t : A -> Prop) : (term220 A t v) = (term221 A v t).
Proof. exact (MK_COMB (@lem4835111) (@lem4835110 A v t)). Qed.
Lemma lem4835114 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4835115 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4835114 A P x). Qed.
Lemma lem4835116 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4835115 A t x). Qed.
Lemma lem4835117 {A : Type'} (v : type686 A) (t : A -> Prop) (x : A) : (term242 A v x t) = (term243 A v t x).
Proof. exact (MK_COMB (@lem4835112 A v t) (@lem4835116 A t x)). Qed.
Lemma lem4835120 {A : Type'} (v : type686 A) (x : A) : (term244 A v x) = (term245 A v x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4835117 A v t x)). Qed.
Lemma lem4835121 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835122 {A : Type'} (v : type686 A) (x : A) : (term241 A v x) = (term246 A v x).
Proof. exact (MK_COMB (@lem4835121 A) (@lem4835120 A v x)). Qed.
Lemma lem4835127 {A : Type'} (v : type686 A) (x : A) : (term240 A x v) = (term246 A v x).
Proof. exact (TRANS (@lem4835100 A v x) (@lem4835122 A v x)). Qed.
Lemma lem4835128 {A : Type'} (u : type686 A) (v : type686 A) (x : A) : (term249 A u x v) = (term250 A u v x).
Proof. exact (MK_COMB (@lem4835096 A u x) (@lem4835127 A v x)). Qed.
Lemma lem4835131 {A : Type'} (u : type686 A) (v : type686 A) : (term251 A u v) = (term252 A u v).
Proof. exact (fun_ext (fun x : A => @lem4835128 A u v x)). Qed.
Lemma lem4835132 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4835133 {A : Type'} (u : type686 A) (v : type686 A) : (term211 A u v) = (term253 A u v).
Proof. exact (MK_COMB (@lem4835132 A) (@lem4835131 A u v)). Qed.
Lemma lem4835138 {A : Type'} (u : type686 A) (v : type686 A) : (term213 A u v) = (term254 A u v).
Proof. exact (MK_COMB (@lem4835057 A u v) (@lem4835133 A u v)). Qed.
Lemma lem4835141 {A : Type'} (u : type686 A) (v : type686 A) : (term254 A u v) = (term213 A u v).
Proof. exact (SYM (@lem4835138 A u v)). Qed.
Lemma lem4835143 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4835144 {A : Type'} (u : type686 A) (v : type686 A) : (term254 A u v) = (term255 A u v).
Proof. exact (@lem4835143 (term254 A u v)). Qed.
Lemma lem4835145 {A : Type'} (u : type686 A) (v : type686 A) : (term255 A u v) = (term254 A u v).
Proof. exact (SYM (@lem4835144 A u v)). Qed.
Lemma lem4835146 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term256 A u v) : term256 A u v.
Proof. exact (h1). Qed.
Lemma lem4835149 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term255 A u v) : term255 A u v.
Proof. exact (h1). Qed.
Lemma lem4835150 {A : Type'} (u : type686 A) (v : type686 A) : term257 A u v.
Proof. exact (fun h0 : term255 A u v => @lem4835149 A u v h0). Qed.
Lemma lem4835151 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term257 A u v) : term257 A u v.
Proof. exact (h1). Qed.
Lemma lem4835152 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term255 A u v) : term255 A u v.
Proof. exact (h1). Qed.
Lemma lem4835153 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term255 A u v) (h2 : term257 A u v) : term255 A u v.
Proof. exact (@lem4835151 A u v h2 (@lem4835152 A u v h1)). Qed.
Lemma lem4835154 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term255 A u v) : term258 A u v.
Proof. exact (fun h0 : term257 A u v => @lem4835153 A u v h1 h0). Qed.
Lemma lem4835155 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term257 A u v) : term257 A u v.
Proof. exact (h1). Qed.
Lemma lem4835156 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term255 A u v) (h2 : term257 A u v) : term255 A u v.
Proof. exact (@lem4835154 A u v h1 (@lem4835155 A u v h2)). Qed.
Lemma lem4835157 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term257 A u v) : term257 A u v.
Proof. exact (fun h0 : term255 A u v => @lem4835156 A u v h0 h1). Qed.
Lemma lem4835158 {A : Type'} (u : type686 A) (v : type686 A) : term259 A u v.
Proof. exact (fun h0 : term257 A u v => @lem4835157 A u v h0). Qed.
Lemma lem4835161 {A : Type'} (u : type686 A) (v : type686 A) : term257 A u v.
Proof. exact (@lem4835158 A u v (@lem4835150 A u v)). Qed.
Lemma lem4835162 {A : Type'} (u : type686 A) (v : type686 A) : term257 A u v.
Proof. exact (@lem4835161 A u v). Qed.
Lemma lem4835172 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4835173 {A : Type'} (u : type686 A) (v : type686 A) : (term255 A u v) = (term260 A u v).
Proof. exact (@lem4835172 (term256 A u v)). Qed.
Lemma lem4835175 (t : Prop) : (term85 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4835176 {A : Type'} (u : type686 A) (v : type686 A) : (term260 A u v) = (term254 A u v).
Proof. exact (@lem4835175 (term254 A u v)). Qed.
Lemma lem4835179 {A : Type'} (u : type686 A) (v : type686 A) : (term255 A u v) = (term254 A u v).
Proof. exact (TRANS (@lem4835173 A u v) (@lem4835176 A u v)). Qed.
Lemma lem4835264 {A : Type'} (v : type686 A) : (term261 A v) = (term262 A v).
Proof. exact (fun_ext (fun u : type686 A => @lem4835179 A u v)). Qed.
Lemma lem4835265 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4835266 {A : Type'} (v : type686 A) : (term263 A v) = (term264 A v).
Proof. exact (MK_COMB (@lem4835265 A) (@lem4835264 A v)). Qed.
Lemma lem4835271 {A : Type'} : (term265 A) = (term266 A).
Proof. exact (fun_ext (fun v : type686 A => @lem4835266 A v)). Qed.
Lemma lem4835272 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4835281 {A : Type'} : (term267 A) = (term268 A).
Proof. exact (MK_COMB (@lem4835272 A) (@lem4835271 A)). Qed.
Lemma lem4835286 {A : Type'} (v : type686 A) (t : A -> Prop) (x : A) : (term243 A v t x) = (term243 A v t x).
Proof. exact (eq_refl (term243 A v t x)). Qed.
Lemma lem4835287 {A : Type'} (v : type686 A) (x : A) : (term245 A v x) = (term245 A v x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4835286 A v t x)). Qed.
Lemma lem4835288 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835289 {A : Type'} (v : type686 A) (x : A) : (term246 A v x) = (term246 A v x).
Proof. exact (MK_COMB (@lem4835288 A) (@lem4835287 A v x)). Qed.
Lemma lem4835294 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term243 A u t x) = (term243 A u t x).
Proof. exact (eq_refl (term243 A u t x)). Qed.
Lemma lem4835295 {A : Type'} (u : type686 A) (x : A) : (term245 A u x) = (term245 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4835294 A u t x)). Qed.
Lemma lem4835296 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835297 {A : Type'} (u : type686 A) (x : A) : (term246 A u x) = (term246 A u x).
Proof. exact (MK_COMB (@lem4835296 A) (@lem4835295 A u x)). Qed.
Lemma lem4835298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4835299 {A : Type'} (u : type686 A) (x : A) : (term248 A u x) = (term248 A u x).
Proof. exact (MK_COMB (@lem4835298) (@lem4835297 A u x)). Qed.
Lemma lem4835300 {A : Type'} (u : type686 A) (v : type686 A) (x : A) : (term250 A u v x) = (term250 A u v x).
Proof. exact (MK_COMB (@lem4835299 A u x) (@lem4835289 A v x)). Qed.
Lemma lem4835301 {A : Type'} (u : type686 A) (v : type686 A) : (term252 A u v) = (term252 A u v).
Proof. exact (fun_ext (fun x : A => @lem4835300 A u v x)). Qed.
Lemma lem4835302 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4835303 {A : Type'} (u : type686 A) (v : type686 A) : (term253 A u v) = (term253 A u v).
Proof. exact (MK_COMB (@lem4835302 A) (@lem4835301 A u v)). Qed.
Lemma lem4835304 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4835315 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : ((u x) = (term223 A v x)) = ((u x) = (term223 A v x)).
Proof. exact (eq_refl ((u x) = (term223 A v x))). Qed.
Lemma lem4835316 {A : Type'} (u : type686 A) (v : type686 A) : (term233 A u v) = (term233 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835315 A u v x)). Qed.
Lemma lem4835317 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4835318 {A : Type'} (u : type686 A) (v : type686 A) : (term234 A u v) = (term234 A u v).
Proof. exact (MK_COMB (@lem4835317 A) (@lem4835316 A u v)). Qed.
Lemma lem4835319 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835320 {A : Type'} (u : type686 A) (v : type686 A) : (term235 A u v) = (term235 A u v).
Proof. exact (MK_COMB (@lem4835319) (@lem4835318 A u v)). Qed.
Lemma lem4835331 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term225 A u v x) = (term225 A u v x).
Proof. exact (eq_refl (term225 A u v x)). Qed.
Lemma lem4835332 {A : Type'} (u : type686 A) (v : type686 A) : (term227 A u v) = (term227 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835331 A u v x)). Qed.
Lemma lem4835333 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4835334 {A : Type'} (u : type686 A) (v : type686 A) : (term228 A u v) = (term228 A u v).
Proof. exact (MK_COMB (@lem4835333 A) (@lem4835332 A u v)). Qed.
Lemma lem4835335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835336 {A : Type'} (u : type686 A) (v : type686 A) : (term229 A u v) = (term229 A u v).
Proof. exact (MK_COMB (@lem4835335) (@lem4835334 A u v)). Qed.
Lemma lem4835337 {A : Type'} (u : type686 A) (v : type686 A) : (term236 A u v) = (term236 A u v).
Proof. exact (MK_COMB (@lem4835336 A u v) (@lem4835320 A u v)). Qed.
Lemma lem4835338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835339 {A : Type'} (u : type686 A) (v : type686 A) : (term237 A u v) = (term237 A u v).
Proof. exact (MK_COMB (@lem4835338) (@lem4835337 A u v)). Qed.
Lemma lem4835340 {A : Type'} (u : type686 A) (v : type686 A) : (term238 A u v) = (term238 A u v).
Proof. exact (MK_COMB (@lem4835339 A u v) (@lem4835304 A v)). Qed.
Lemma lem4835341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4835342 {A : Type'} (u : type686 A) (v : type686 A) : (term239 A u v) = (term239 A u v).
Proof. exact (MK_COMB (@lem4835341) (@lem4835340 A u v)). Qed.
Lemma lem4835343 {A : Type'} (u : type686 A) (v : type686 A) : (term254 A u v) = (term254 A u v).
Proof. exact (MK_COMB (@lem4835342 A u v) (@lem4835303 A u v)). Qed.
Lemma lem4835344 {A : Type'} (v : type686 A) : (term262 A v) = (term262 A v).
Proof. exact (fun_ext (fun u : type686 A => @lem4835343 A u v)). Qed.
Lemma lem4835345 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4835346 {A : Type'} (v : type686 A) : (term264 A v) = (term264 A v).
Proof. exact (MK_COMB (@lem4835345 A) (@lem4835344 A v)). Qed.
Lemma lem4835347 {A : Type'} : (term266 A) = (term266 A).
Proof. exact (fun_ext (fun v : type686 A => @lem4835346 A v)). Qed.
Lemma lem4835348 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4835349 {A : Type'} : (term268 A) = (term268 A).
Proof. exact (MK_COMB (@lem4835348 A) (@lem4835347 A)). Qed.
Lemma lem4835412 {A : Type'} : (term267 A) = (term268 A).
Proof. exact (TRANS (@lem4835281 A) (@lem4835349 A)). Qed.
Lemma lem4835413 {A : Type'} : (term268 A) = (term267 A).
Proof. exact (SYM (@lem4835412 A)). Qed.
Lemma lem4835414 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term238 A u v) : term238 A u v.
Proof. exact (h1). Qed.
Lemma lem4835415 {A : Type'} (u : type686 A) (x : A) (h1 : term246 A u x) : term246 A u x.
Proof. exact (h1). Qed.
Lemma lem4835417 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4835418 {A : Type'} (v : type686 A) (x : A) : (term246 A v x) = (term269 A v x).
Proof. exact (@lem4835417 (term246 A v x)). Qed.
Lemma lem4835419 {A : Type'} (v : type686 A) (x : A) : (term269 A v x) = (term246 A v x).
Proof. exact (SYM (@lem4835418 A v x)). Qed.
Lemma lem4835420 {A : Type'} (v : type686 A) (x : A) (h1 : term270 A v x) : term270 A v x.
Proof. exact (h1). Qed.
Lemma lem4835431 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term225 A u v x) = (term271 A u v x).
Proof. exact (@lem17265 (u x) (term223 A v x)). Qed.
Lemma lem4835432 {A : Type'} (u : type686 A) (v : type686 A) : (term227 A u v) = (term272 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835431 A u v x)). Qed.
Lemma lem4835433 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4835434 {A : Type'} (u : type686 A) (v : type686 A) : (term228 A u v) = (term273 A u v).
Proof. exact (MK_COMB (@lem4835433 A) (@lem4835432 A u v)). Qed.
Lemma lem4835442 {A : Type'} (x : A -> Prop) : (term274 A x) = (x = (@EMPTY A)).
Proof. exact (@lem16933 (x = (@EMPTY A))). Qed.
Lemma lem4835444 {A : Type'} (v : type686 A) (x : A -> Prop) : (term275 A v x) = (term275 A v x).
Proof. exact (eq_refl (term275 A v x)). Qed.
Lemma lem4835445 {A : Type'} (v : type686 A) (x : A -> Prop) : (term276 A v x) = (term277 A v x).
Proof. exact (MK_COMB (@lem4835444 A v x) (@lem4835442 A x)). Qed.
Lemma lem4835446 {A : Type'} (v : type686 A) (x : A -> Prop) : (term278 A v x) = (term276 A v x).
Proof. exact (@lem17045 (v x) (term222 A x)). Qed.
Lemma lem4835447 {A : Type'} (v : type686 A) (x : A -> Prop) : (term278 A v x) = (term277 A v x).
Proof. exact (TRANS (@lem4835446 A v x) (@lem4835445 A v x)). Qed.
Lemma lem4835453 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term279 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term279 A u v x)). Qed.
Lemma lem4835455 {A : Type'} (u : type686 A) (x : A -> Prop) : (term221 A u x) = (term221 A u x).
Proof. exact (eq_refl (term221 A u x)). Qed.
Lemma lem4835456 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term280 A u v x) = (term281 A u v x).
Proof. exact (MK_COMB (@lem4835455 A u x) (@lem4835447 A v x)). Qed.
Lemma lem4835457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835458 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term282 A u v x) = (term283 A u v x).
Proof. exact (MK_COMB (@lem4835457) (@lem4835456 A u v x)). Qed.
Lemma lem4835459 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term284 A u v x) = (term285 A u v x).
Proof. exact (MK_COMB (@lem4835458 A u v x) (@lem4835453 A u v x)). Qed.
Lemma lem4835460 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term286 A u v x) = (term284 A u v x).
Proof. exact (@lem17646 (u x) (term223 A v x)). Qed.
Lemma lem4835461 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term286 A u v x) = (term285 A u v x).
Proof. exact (TRANS (@lem4835460 A u v x) (@lem4835459 A u v x)). Qed.
Lemma lem4835462 {A : Type'} (P : type686 A) : (term287 A P) = (term288 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4835463 {A : Type'} (u : type686 A) (v : type686 A) : (term235 A u v) = (term289 A u v).
Proof. exact (@lem4835462 A (term233 A u v)). Qed.
Lemma lem4835464 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term290 A u v x) = ((u x) = (term223 A v x)).
Proof. exact (eq_refl (term290 A u v x)). Qed.
Lemma lem4835465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835466 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term291 A u v x) = (term286 A u v x).
Proof. exact (MK_COMB (@lem4835465) (@lem4835464 A u v x)). Qed.
Lemma lem4835467 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term291 A u v x) = (term285 A u v x).
Proof. exact (TRANS (@lem4835466 A u v x) (@lem4835461 A u v x)). Qed.
Lemma lem4835468 {A : Type'} (u : type686 A) (v : type686 A) : (term292 A u v) = (term293 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835467 A u v x)). Qed.
Lemma lem4835469 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835470 {A : Type'} (u : type686 A) (v : type686 A) : (term289 A u v) = (term294 A u v).
Proof. exact (MK_COMB (@lem4835469 A) (@lem4835468 A u v)). Qed.
Lemma lem4835471 {A : Type'} (u : type686 A) (v : type686 A) : (term235 A u v) = (term294 A u v).
Proof. exact (TRANS (@lem4835463 A u v) (@lem4835470 A u v)). Qed.
Lemma lem4835472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835473 {A : Type'} (u : type686 A) (v : type686 A) : (term229 A u v) = (term295 A u v).
Proof. exact (MK_COMB (@lem4835472) (@lem4835434 A u v)). Qed.
Lemma lem4835474 {A : Type'} (u : type686 A) (v : type686 A) : (term236 A u v) = (term296 A u v).
Proof. exact (MK_COMB (@lem4835473 A u v) (@lem4835471 A u v)). Qed.
Lemma lem4835475 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4835476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835477 {A : Type'} (u : type686 A) (v : type686 A) : (term237 A u v) = (term297 A u v).
Proof. exact (MK_COMB (@lem4835476) (@lem4835474 A u v)). Qed.
Lemma lem4835478 {A : Type'} (u : type686 A) (v : type686 A) : (term238 A u v) = (term298 A u v).
Proof. exact (MK_COMB (@lem4835477 A u v) (@lem4835475 A v)). Qed.
Lemma lem4835528 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term299 A P Q) = (term300 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4835529 {A : Type'} (P : type686 A) (Q : type686 A) : (term301 A P Q) = (term302 A P Q).
Proof. exact (@lem4835528 (A -> Prop) P Q). Qed.
Lemma lem4835530 {A : Type'} (u : type686 A) (v : type686 A) : (term303 A u v) = (term304 A u v).
Proof. exact (@lem4835529 A (term305 A u v) (term306 A u v)). Qed.
Lemma lem4835531 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term307 A u v x) = (term281 A u v x).
Proof. exact (eq_refl (term307 A u v x)). Qed.
Lemma lem4835532 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835533 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term308 A u v x) = (term283 A u v x).
Proof. exact (MK_COMB (@lem4835532) (@lem4835531 A u v x)). Qed.
Lemma lem4835534 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term309 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term309 A u v x)). Qed.
Lemma lem4835535 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term310 A u v x) = (term285 A u v x).
Proof. exact (MK_COMB (@lem4835533 A u v x) (@lem4835534 A u v x)). Qed.
Lemma lem4835536 {A : Type'} (u : type686 A) (v : type686 A) : (term311 A u v) = (term293 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835535 A u v x)). Qed.
Lemma lem4835537 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835538 {A : Type'} (u : type686 A) (v : type686 A) : (term303 A u v) = (term294 A u v).
Proof. exact (MK_COMB (@lem4835537 A) (@lem4835536 A u v)). Qed.
Lemma lem4835539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4835540 {A : Type'} (u : type686 A) (v : type686 A) : (term312 A u v) = (term313 A u v).
Proof. exact (MK_COMB (@lem4835539) (@lem4835538 A u v)). Qed.
Lemma lem4835541 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term307 A u v x) = (term281 A u v x).
Proof. exact (eq_refl (term307 A u v x)). Qed.
Lemma lem4835542 {A : Type'} (u : type686 A) (v : type686 A) : (term314 A u v) = (term305 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835541 A u v x)). Qed.
Lemma lem4835543 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835544 {A : Type'} (u : type686 A) (v : type686 A) : (term315 A u v) = (term316 A u v).
Proof. exact (MK_COMB (@lem4835543 A) (@lem4835542 A u v)). Qed.
Lemma lem4835545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835546 {A : Type'} (u : type686 A) (v : type686 A) : (term317 A u v) = (term318 A u v).
Proof. exact (MK_COMB (@lem4835545) (@lem4835544 A u v)). Qed.
Lemma lem4835547 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term309 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term309 A u v x)). Qed.
Lemma lem4835548 {A : Type'} (u : type686 A) (v : type686 A) : (term319 A u v) = (term306 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835547 A u v x)). Qed.
Lemma lem4835549 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835550 {A : Type'} (u : type686 A) (v : type686 A) : (term320 A u v) = (term321 A u v).
Proof. exact (MK_COMB (@lem4835549 A) (@lem4835548 A u v)). Qed.
Lemma lem4835551 {A : Type'} (u : type686 A) (v : type686 A) : (term304 A u v) = (term322 A u v).
Proof. exact (MK_COMB (@lem4835546 A u v) (@lem4835550 A u v)). Qed.
Lemma lem4835552 {A : Type'} (u : type686 A) (v : type686 A) : ((term303 A u v) = (term304 A u v)) = ((term294 A u v) = (term322 A u v)).
Proof. exact (MK_COMB (@lem4835540 A u v) (@lem4835551 A u v)). Qed.
Lemma lem4835553 {A : Type'} (u : type686 A) (v : type686 A) : (term294 A u v) = (term322 A u v).
Proof. exact (EQ_MP (@lem4835552 A u v) (@lem4835530 A u v)). Qed.
Lemma lem4835630 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term295 A u v).
Proof. exact (eq_refl (term295 A u v)). Qed.
Lemma lem4835631 {A : Type'} (u : type686 A) (v : type686 A) : (term296 A u v) = (term323 A u v).
Proof. exact (MK_COMB (@lem4835630 A u v) (@lem4835553 A u v)). Qed.
Lemma lem4835632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835633 {A : Type'} (u : type686 A) (v : type686 A) : (term297 A u v) = (term324 A u v).
Proof. exact (MK_COMB (@lem4835632) (@lem4835631 A u v)). Qed.
Lemma lem4835634 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4835635 {A : Type'} (u : type686 A) (v : type686 A) : (term298 A u v) = (term325 A u v).
Proof. exact (MK_COMB (@lem4835633 A u v) (@lem4835634 A v)). Qed.
Lemma lem4835637 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term300 A P Q) = (term299 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4835638 {A : Type'} (P : type686 A) (Q : type686 A) : (term302 A P Q) = (term301 A P Q).
Proof. exact (@lem4835637 (A -> Prop) P Q). Qed.
Lemma lem4835639 {A : Type'} (u : type686 A) (v : type686 A) : (term304 A u v) = (term303 A u v).
Proof. exact (@lem4835638 A (term305 A u v) (term306 A u v)). Qed.
Lemma lem4835640 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term307 A u v x) = (term281 A u v x).
Proof. exact (eq_refl (term307 A u v x)). Qed.
Lemma lem4835641 {A : Type'} (u : type686 A) (v : type686 A) : (term314 A u v) = (term305 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835640 A u v x)). Qed.
Lemma lem4835642 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835643 {A : Type'} (u : type686 A) (v : type686 A) : (term315 A u v) = (term316 A u v).
Proof. exact (MK_COMB (@lem4835642 A) (@lem4835641 A u v)). Qed.
Lemma lem4835644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835645 {A : Type'} (u : type686 A) (v : type686 A) : (term317 A u v) = (term318 A u v).
Proof. exact (MK_COMB (@lem4835644) (@lem4835643 A u v)). Qed.
Lemma lem4835646 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term309 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term309 A u v x)). Qed.
Lemma lem4835647 {A : Type'} (u : type686 A) (v : type686 A) : (term319 A u v) = (term306 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835646 A u v x)). Qed.
Lemma lem4835648 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835649 {A : Type'} (u : type686 A) (v : type686 A) : (term320 A u v) = (term321 A u v).
Proof. exact (MK_COMB (@lem4835648 A) (@lem4835647 A u v)). Qed.
Lemma lem4835650 {A : Type'} (u : type686 A) (v : type686 A) : (term304 A u v) = (term322 A u v).
Proof. exact (MK_COMB (@lem4835645 A u v) (@lem4835649 A u v)). Qed.
Lemma lem4835651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4835652 {A : Type'} (u : type686 A) (v : type686 A) : (term326 A u v) = (term327 A u v).
Proof. exact (MK_COMB (@lem4835651) (@lem4835650 A u v)). Qed.
Lemma lem4835653 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term307 A u v x) = (term281 A u v x).
Proof. exact (eq_refl (term307 A u v x)). Qed.
Lemma lem4835654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835655 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term308 A u v x) = (term283 A u v x).
Proof. exact (MK_COMB (@lem4835654) (@lem4835653 A u v x)). Qed.
Lemma lem4835656 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term309 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term309 A u v x)). Qed.
Lemma lem4835657 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term310 A u v x) = (term285 A u v x).
Proof. exact (MK_COMB (@lem4835655 A u v x) (@lem4835656 A u v x)). Qed.
Lemma lem4835658 {A : Type'} (u : type686 A) (v : type686 A) : (term311 A u v) = (term293 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835657 A u v x)). Qed.
Lemma lem4835659 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835660 {A : Type'} (u : type686 A) (v : type686 A) : (term303 A u v) = (term294 A u v).
Proof. exact (MK_COMB (@lem4835659 A) (@lem4835658 A u v)). Qed.
Lemma lem4835661 {A : Type'} (u : type686 A) (v : type686 A) : ((term304 A u v) = (term303 A u v)) = ((term322 A u v) = (term294 A u v)).
Proof. exact (MK_COMB (@lem4835652 A u v) (@lem4835660 A u v)). Qed.
Lemma lem4835662 {A : Type'} (u : type686 A) (v : type686 A) : (term322 A u v) = (term294 A u v).
Proof. exact (EQ_MP (@lem4835661 A u v) (@lem4835639 A u v)). Qed.
Lemma lem4835663 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term295 A u v).
Proof. exact (eq_refl (term295 A u v)). Qed.
Lemma lem4835664 {A : Type'} (u : type686 A) (v : type686 A) : (term323 A u v) = (term296 A u v).
Proof. exact (MK_COMB (@lem4835663 A u v) (@lem4835662 A u v)). Qed.
Lemma lem4835666 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4835667 {A : Type'} (P : Prop) (Q : type686 A) : (term328 A P Q) = (term329 A P Q).
Proof. exact (@lem4835666 (A -> Prop) P Q). Qed.
Lemma lem4835668 {A : Type'} (u : type686 A) (v : type686 A) : (term330 A u v) = (term331 A u v).
Proof. exact (@lem4835667 A (term273 A u v) (term293 A u v)). Qed.
Lemma lem4835669 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term332 A u v x) = (term285 A u v x).
Proof. exact (eq_refl (term332 A u v x)). Qed.
Lemma lem4835670 {A : Type'} (u : type686 A) (v : type686 A) : (term333 A u v) = (term293 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835669 A u v x)). Qed.
Lemma lem4835671 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835672 {A : Type'} (u : type686 A) (v : type686 A) : (term334 A u v) = (term294 A u v).
Proof. exact (MK_COMB (@lem4835671 A) (@lem4835670 A u v)). Qed.
Lemma lem4835673 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term295 A u v).
Proof. exact (eq_refl (term295 A u v)). Qed.
Lemma lem4835674 {A : Type'} (u : type686 A) (v : type686 A) : (term330 A u v) = (term296 A u v).
Proof. exact (MK_COMB (@lem4835673 A u v) (@lem4835672 A u v)). Qed.
Lemma lem4835675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4835676 {A : Type'} (u : type686 A) (v : type686 A) : (term335 A u v) = (term336 A u v).
Proof. exact (MK_COMB (@lem4835675) (@lem4835674 A u v)). Qed.
Lemma lem4835677 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term332 A u v x) = (term285 A u v x).
Proof. exact (eq_refl (term332 A u v x)). Qed.
Lemma lem4835678 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term295 A u v).
Proof. exact (eq_refl (term295 A u v)). Qed.
Lemma lem4835679 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term337 A u v x) = (term338 A u v x).
Proof. exact (MK_COMB (@lem4835678 A u v) (@lem4835677 A u v x)). Qed.
Lemma lem4835680 {A : Type'} (u : type686 A) (v : type686 A) : (term339 A u v) = (term340 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835679 A u v x)). Qed.
Lemma lem4835681 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835682 {A : Type'} (u : type686 A) (v : type686 A) : (term331 A u v) = (term341 A u v).
Proof. exact (MK_COMB (@lem4835681 A) (@lem4835680 A u v)). Qed.
Lemma lem4835683 {A : Type'} (u : type686 A) (v : type686 A) : ((term330 A u v) = (term331 A u v)) = ((term296 A u v) = (term341 A u v)).
Proof. exact (MK_COMB (@lem4835676 A u v) (@lem4835682 A u v)). Qed.
Lemma lem4835684 {A : Type'} (u : type686 A) (v : type686 A) : (term296 A u v) = (term341 A u v).
Proof. exact (EQ_MP (@lem4835683 A u v) (@lem4835668 A u v)). Qed.
Lemma lem4835685 {A : Type'} (u : type686 A) (v : type686 A) : (term323 A u v) = (term341 A u v).
Proof. exact (TRANS (@lem4835664 A u v) (@lem4835684 A u v)). Qed.
Lemma lem4835686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835687 {A : Type'} (u : type686 A) (v : type686 A) : (term324 A u v) = (term342 A u v).
Proof. exact (MK_COMB (@lem4835686) (@lem4835685 A u v)). Qed.
Lemma lem4835688 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4835689 {A : Type'} (u : type686 A) (v : type686 A) : (term325 A u v) = (term343 A u v).
Proof. exact (MK_COMB (@lem4835687 A u v) (@lem4835688 A v)). Qed.
Lemma lem4835691 {A : Type'} (P : A -> Prop) (Q : Prop) : (term344 A P Q) = (term345 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4835692 {A : Type'} (P : type686 A) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem4835691 (A -> Prop) P Q). Qed.
Lemma lem4835693 {A : Type'} (u : type686 A) (v : type686 A) : (term348 A u v) = (term349 A u v).
Proof. exact (@lem4835692 A (term340 A u v) (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4835694 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term350 A u v x) = (term338 A u v x).
Proof. exact (eq_refl (term350 A u v x)). Qed.
Lemma lem4835695 {A : Type'} (u : type686 A) (v : type686 A) : (term351 A u v) = (term340 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835694 A u v x)). Qed.
Lemma lem4835696 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835697 {A : Type'} (u : type686 A) (v : type686 A) : (term352 A u v) = (term341 A u v).
Proof. exact (MK_COMB (@lem4835696 A) (@lem4835695 A u v)). Qed.
Lemma lem4835698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835699 {A : Type'} (u : type686 A) (v : type686 A) : (term353 A u v) = (term342 A u v).
Proof. exact (MK_COMB (@lem4835698) (@lem4835697 A u v)). Qed.
Lemma lem4835700 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4835701 {A : Type'} (u : type686 A) (v : type686 A) : (term348 A u v) = (term343 A u v).
Proof. exact (MK_COMB (@lem4835699 A u v) (@lem4835700 A v)). Qed.
Lemma lem4835702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4835703 {A : Type'} (u : type686 A) (v : type686 A) : (term354 A u v) = (term355 A u v).
Proof. exact (MK_COMB (@lem4835702) (@lem4835701 A u v)). Qed.
Lemma lem4835704 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term350 A u v x) = (term338 A u v x).
Proof. exact (eq_refl (term350 A u v x)). Qed.
Lemma lem4835705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835706 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term356 A u v x) = (term357 A u v x).
Proof. exact (MK_COMB (@lem4835705) (@lem4835704 A u v x)). Qed.
Lemma lem4835707 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4835708 {A : Type'} (u : type686 A) (x : A -> Prop) (v : type686 A) : (term358 A u x v) = (term359 A u x v).
Proof. exact (MK_COMB (@lem4835706 A u v x) (@lem4835707 A v)). Qed.
Lemma lem4835709 {A : Type'} (u : type686 A) (v : type686 A) : (term360 A u v) = (term361 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835708 A u x v)). Qed.
Lemma lem4835710 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835711 {A : Type'} (u : type686 A) (v : type686 A) : (term349 A u v) = (term362 A u v).
Proof. exact (MK_COMB (@lem4835710 A) (@lem4835709 A u v)). Qed.
Lemma lem4835712 {A : Type'} (u : type686 A) (v : type686 A) : ((term348 A u v) = (term349 A u v)) = ((term343 A u v) = (term362 A u v)).
Proof. exact (MK_COMB (@lem4835703 A u v) (@lem4835711 A u v)). Qed.
Lemma lem4835713 {A : Type'} (u : type686 A) (v : type686 A) : (term343 A u v) = (term362 A u v).
Proof. exact (EQ_MP (@lem4835712 A u v) (@lem4835693 A u v)). Qed.
Lemma lem4835714 {A : Type'} (u : type686 A) (v : type686 A) : (term325 A u v) = (term362 A u v).
Proof. exact (TRANS (@lem4835689 A u v) (@lem4835713 A u v)). Qed.
Lemma lem4835715 {A : Type'} (u : type686 A) (v : type686 A) : (term298 A u v) = (term362 A u v).
Proof. exact (TRANS (@lem4835635 A u v) (@lem4835714 A u v)). Qed.
Lemma lem4835716 {A : Type'} (u : type686 A) (v : type686 A) : (term238 A u v) = (term362 A u v).
Proof. exact (TRANS (@lem4835478 A u v) (@lem4835715 A u v)). Qed.
Lemma lem4835717 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term238 A u v) : term362 A u v.
Proof. exact (EQ_MP (@lem4835716 A u v) (@lem4835414 A u v h1)). Qed.
Lemma lem4835722 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term243 A u t x) = (term243 A u t x).
Proof. exact (eq_refl (term243 A u t x)). Qed.
Lemma lem4835723 {A : Type'} (u : type686 A) (x : A) : (term245 A u x) = (term245 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4835722 A u t x)). Qed.
Lemma lem4835724 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4835757 {A : Type'} (u : type686 A) (x : A) : (term246 A u x) = (term246 A u x).
Proof. exact (MK_COMB (@lem4835724 A) (@lem4835723 A u x)). Qed.
Lemma lem4835758 {A : Type'} (u : type686 A) (x : A) (h1 : term246 A u x) : term246 A u x.
Proof. exact (EQ_MP (@lem4835757 A u x) (@lem4835415 A u x h1)). Qed.
Lemma lem4835765 {A : Type'} (v : type686 A) (t : A -> Prop) (x : A) : (term363 A v t x) = (term364 A v t x).
Proof. exact (@lem17045 (v t) (t x)). Qed.
Lemma lem4835766 {A : Type'} (P : type686 A) : (term365 A P) = (term366 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4835767 {A : Type'} (v : type686 A) (x : A) : (term270 A v x) = (term367 A v x).
Proof. exact (@lem4835766 A (term245 A v x)). Qed.
Lemma lem4835768 {A : Type'} (v : type686 A) (t : A -> Prop) (x : A) : (term368 A v x t) = (term243 A v t x).
Proof. exact (eq_refl (term368 A v x t)). Qed.
Lemma lem4835769 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835770 {A : Type'} (v : type686 A) (t : A -> Prop) (x : A) : (term369 A v x t) = (term363 A v t x).
Proof. exact (MK_COMB (@lem4835769) (@lem4835768 A v t x)). Qed.
Lemma lem4835771 {A : Type'} (v : type686 A) (t : A -> Prop) (x : A) : (term369 A v x t) = (term364 A v t x).
Proof. exact (TRANS (@lem4835770 A v t x) (@lem4835765 A v t x)). Qed.
Lemma lem4835772 {A : Type'} (v : type686 A) (x : A) : (term370 A v x) = (term371 A v x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4835771 A v t x)). Qed.
Lemma lem4835773 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4835774 {A : Type'} (v : type686 A) (x : A) : (term367 A v x) = (term372 A v x).
Proof. exact (MK_COMB (@lem4835773 A) (@lem4835772 A v x)). Qed.
Lemma lem4835827 {A : Type'} (v : type686 A) (x : A) : (term270 A v x) = (term372 A v x).
Proof. exact (TRANS (@lem4835767 A v x) (@lem4835774 A v x)). Qed.
Lemma lem4835828 {A : Type'} (v : type686 A) (x : A) (h1 : term270 A v x) : term372 A v x.
Proof. exact (EQ_MP (@lem4835827 A v x) (@lem4835420 A v x h1)). Qed.
Lemma lem4835829 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) (h1 : term243 A u t x) : term243 A u t x.
Proof. exact (h1). Qed.
Lemma lem4835830 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term359 A u x' v.
Proof. exact (h1). Qed.
Lemma lem4835831 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835836 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835837 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4835836 A Prop f x). Qed.
Lemma lem4835839 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4835837 A t x). Qed.
Lemma lem4835840 {A : Type'} (t : A -> Prop) (x : A) : (term59 A t x) = (term373 A t x).
Proof. exact (MK_COMB (@lem4835831) (@lem4835839 A t x)). Qed.
Lemma lem4835841 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835846 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835847 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4835846 (A -> Prop) Prop f x). Qed.
Lemma lem4835849 {A : Type'} (v : type686 A) (t : A -> Prop) : (v t) = (@I ((A -> Prop) -> Prop) v t).
Proof. exact (@lem4835847 A v t). Qed.
Lemma lem4835850 {A : Type'} (v : type686 A) (t : A -> Prop) : (term374 A v t) = (term375 A v t).
Proof. exact (MK_COMB (@lem4835841) (@lem4835849 A v t)). Qed.
Lemma lem4835851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835852 {A : Type'} (v : type686 A) (t : A -> Prop) : (term275 A v t) = (term376 A v t).
Proof. exact (MK_COMB (@lem4835851) (@lem4835850 A v t)). Qed.
Lemma lem4835853 {A : Type'} (v : type686 A) (t : A -> Prop) (x : A) : (term364 A v t x) = (term377 A v t x).
Proof. exact (MK_COMB (@lem4835852 A v t) (@lem4835840 A t x)). Qed.
Lemma lem4835854 {A : Type'} (v : type686 A) (x : A) : (term371 A v x) = (term378 A v x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4835853 A v t x)). Qed.
Lemma lem4835855 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4835856 {A : Type'} (v : type686 A) (x : A) : (term372 A v x) = (term379 A v x).
Proof. exact (MK_COMB (@lem4835855 A) (@lem4835854 A v x)). Qed.
Lemma lem4835857 {A : Type'} (v : type686 A) (x : A) (h1 : term270 A v x) : term379 A v x.
Proof. exact (EQ_MP (@lem4835856 A v x) (@lem4835828 A v x h1)). Qed.
Lemma lem4835862 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835863 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4835862 A Prop f x). Qed.
Lemma lem4835865 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4835863 A t x). Qed.
Lemma lem4835870 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835871 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4835870 (A -> Prop) Prop f x). Qed.
Lemma lem4835873 {A : Type'} (u : type686 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem4835871 A u t). Qed.
Lemma lem4835874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835875 {A : Type'} (u : type686 A) (t : A -> Prop) : (term221 A u t) = (term380 A u t).
Proof. exact (MK_COMB (@lem4835874) (@lem4835873 A u t)). Qed.
Lemma lem4835876 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term243 A u t x) = (term381 A u t x).
Proof. exact (MK_COMB (@lem4835875 A u t) (@lem4835865 A t x)). Qed.
Lemma lem4835877 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) (h1 : term243 A u t x) : term381 A u t x.
Proof. exact (EQ_MP (@lem4835876 A u t x) (@lem4835829 A u t x h1)). Qed.
Lemma lem4835884 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835885 {A : Type'} (f : type140 A) (x : type639 A) : (f x) = (@I (((A -> Prop) -> (A -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4835884 (type639 A) (type180 A) f x). Qed.
Lemma lem4835886 {A : Type'} : (@pairwise (A -> Prop) (@DISJOINT A)) = (@I (((A -> Prop) -> (A -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> Prop) (@pairwise (A -> Prop)) (@DISJOINT A)).
Proof. exact (@lem4835885 A (@pairwise (A -> Prop)) (@DISJOINT A)). Qed.
Lemma lem4835887 {A : Type'} (v : type686 A) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem4835888 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@I (((A -> Prop) -> (A -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> Prop) (@pairwise (A -> Prop)) (@DISJOINT A) v).
Proof. exact (MK_COMB (@lem4835886 A) (@lem4835887 A v)). Qed.
Lemma lem4835890 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835891 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4835890 (type686 A) Prop f x). Qed.
Lemma lem4835892 {A : Type'} (v : type686 A) : (@I (((A -> Prop) -> (A -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> Prop) (@pairwise (A -> Prop)) (@DISJOINT A) v) = (term382 A v).
Proof. exact (@lem4835891 A (@I (((A -> Prop) -> (A -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> Prop) (@pairwise (A -> Prop)) (@DISJOINT A)) v). Qed.
Lemma lem4835894 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (term382 A v).
Proof. exact (TRANS (@lem4835888 A v) (@lem4835892 A v)). Qed.
Lemma lem4835901 {A : Type'} (x' : A -> Prop) : (term222 A x') = (term222 A x').
Proof. exact (eq_refl (term222 A x')). Qed.
Lemma lem4835906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835907 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4835906 (A -> Prop) Prop f x). Qed.
Lemma lem4835909 {A : Type'} (v : type686 A) (x' : A -> Prop) : (v x') = (@I ((A -> Prop) -> Prop) v x').
Proof. exact (@lem4835907 A v x'). Qed.
Lemma lem4835910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835911 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term221 A v x') = (term380 A v x').
Proof. exact (MK_COMB (@lem4835910) (@lem4835909 A v x')). Qed.
Lemma lem4835912 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term223 A v x') = (term383 A v x').
Proof. exact (MK_COMB (@lem4835911 A v x') (@lem4835901 A x')). Qed.
Lemma lem4835913 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835919 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4835918 (A -> Prop) Prop f x). Qed.
Lemma lem4835921 {A : Type'} (u : type686 A) (x' : A -> Prop) : (u x') = (@I ((A -> Prop) -> Prop) u x').
Proof. exact (@lem4835919 A u x'). Qed.
Lemma lem4835922 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term374 A u x') = (term375 A u x').
Proof. exact (MK_COMB (@lem4835913) (@lem4835921 A u x')). Qed.
Lemma lem4835923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835924 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term384 A u x') = (term385 A u x').
Proof. exact (MK_COMB (@lem4835923) (@lem4835922 A u x')). Qed.
Lemma lem4835925 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term279 A u v x') = (term386 A u v x').
Proof. exact (MK_COMB (@lem4835924 A u x') (@lem4835912 A v x')). Qed.
Lemma lem4835930 {A : Type'} (x' : A -> Prop) : (x' = (@EMPTY A)) = (x' = (@EMPTY A)).
Proof. exact (eq_refl (x' = (@EMPTY A))). Qed.
Lemma lem4835931 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835937 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4835936 (A -> Prop) Prop f x). Qed.
Lemma lem4835939 {A : Type'} (v : type686 A) (x' : A -> Prop) : (v x') = (@I ((A -> Prop) -> Prop) v x').
Proof. exact (@lem4835937 A v x'). Qed.
Lemma lem4835940 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term374 A v x') = (term375 A v x').
Proof. exact (MK_COMB (@lem4835931) (@lem4835939 A v x')). Qed.
Lemma lem4835941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835942 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term275 A v x') = (term376 A v x').
Proof. exact (MK_COMB (@lem4835941) (@lem4835940 A v x')). Qed.
Lemma lem4835943 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term277 A v x') = (term387 A v x').
Proof. exact (MK_COMB (@lem4835942 A v x') (@lem4835930 A x')). Qed.
Lemma lem4835948 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835949 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4835948 (A -> Prop) Prop f x). Qed.
Lemma lem4835951 {A : Type'} (u : type686 A) (x' : A -> Prop) : (u x') = (@I ((A -> Prop) -> Prop) u x').
Proof. exact (@lem4835949 A u x'). Qed.
Lemma lem4835952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835953 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term221 A u x') = (term380 A u x').
Proof. exact (MK_COMB (@lem4835952) (@lem4835951 A u x')). Qed.
Lemma lem4835954 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term281 A u v x') = (term388 A u v x').
Proof. exact (MK_COMB (@lem4835953 A u x') (@lem4835943 A v x')). Qed.
Lemma lem4835955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835956 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term283 A u v x') = (term389 A u v x').
Proof. exact (MK_COMB (@lem4835955) (@lem4835954 A u v x')). Qed.
Lemma lem4835957 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term285 A u v x') = (term390 A u v x').
Proof. exact (MK_COMB (@lem4835956 A u v x') (@lem4835925 A u v x')). Qed.
Lemma lem4835964 {A : Type'} (x : A -> Prop) : (term222 A x) = (term222 A x).
Proof. exact (eq_refl (term222 A x)). Qed.
Lemma lem4835969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835970 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4835969 (A -> Prop) Prop f x). Qed.
Lemma lem4835972 {A : Type'} (v : type686 A) (x : A -> Prop) : (v x) = (@I ((A -> Prop) -> Prop) v x).
Proof. exact (@lem4835970 A v x). Qed.
Lemma lem4835973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835974 {A : Type'} (v : type686 A) (x : A -> Prop) : (term221 A v x) = (term380 A v x).
Proof. exact (MK_COMB (@lem4835973) (@lem4835972 A v x)). Qed.
Lemma lem4835975 {A : Type'} (v : type686 A) (x : A -> Prop) : (term223 A v x) = (term383 A v x).
Proof. exact (MK_COMB (@lem4835974 A v x) (@lem4835964 A x)). Qed.
Lemma lem4835976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4835981 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4835982 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4835981 (A -> Prop) Prop f x). Qed.
Lemma lem4835984 {A : Type'} (u : type686 A) (x : A -> Prop) : (u x) = (@I ((A -> Prop) -> Prop) u x).
Proof. exact (@lem4835982 A u x). Qed.
Lemma lem4835985 {A : Type'} (u : type686 A) (x : A -> Prop) : (term374 A u x) = (term375 A u x).
Proof. exact (MK_COMB (@lem4835976) (@lem4835984 A u x)). Qed.
Lemma lem4835986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4835987 {A : Type'} (u : type686 A) (x : A -> Prop) : (term275 A u x) = (term376 A u x).
Proof. exact (MK_COMB (@lem4835986) (@lem4835985 A u x)). Qed.
Lemma lem4835988 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term271 A u v x) = (term391 A u v x).
Proof. exact (MK_COMB (@lem4835987 A u x) (@lem4835975 A v x)). Qed.
Lemma lem4835989 {A : Type'} (u : type686 A) (v : type686 A) : (term272 A u v) = (term392 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4835988 A u v x)). Qed.
Lemma lem4835990 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4835991 {A : Type'} (u : type686 A) (v : type686 A) : (term273 A u v) = (term393 A u v).
Proof. exact (MK_COMB (@lem4835990 A) (@lem4835989 A u v)). Qed.
Lemma lem4835992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835993 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term394 A u v).
Proof. exact (MK_COMB (@lem4835992) (@lem4835991 A u v)). Qed.
Lemma lem4835994 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term338 A u v x') = (term395 A u v x').
Proof. exact (MK_COMB (@lem4835993 A u v) (@lem4835957 A u v x')). Qed.
Lemma lem4835995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4835996 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term357 A u v x') = (term396 A u v x').
Proof. exact (MK_COMB (@lem4835995) (@lem4835994 A u v x')). Qed.
Lemma lem4835997 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) : (term359 A u x' v) = (term397 A u x' v).
Proof. exact (MK_COMB (@lem4835996 A u v x') (@lem4835894 A v)). Qed.
Lemma lem4835998 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term397 A u x' v.
Proof. exact (EQ_MP (@lem4835997 A u x' v) (@lem4835830 A u x' v h1)). Qed.
Lemma lem4836000 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term395 A u v x'.
Proof. exact (proj1 (@lem4835998 A u x' v h1)). Qed.
Lemma lem4836001 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term390 A u v x'.
Proof. exact (proj2 (@lem4836000 A u x' v h1)). Qed.
Lemma lem4836002 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term393 A u v.
Proof. exact (proj1 (@lem4836000 A u x' v h1)). Qed.
Lemma lem4836005 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') : term388 A u v x'.
Proof. exact (h1). Qed.
Lemma lem4836007 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') : term387 A v x'.
Proof. exact (proj2 (@lem4836005 A u v x' h1)). Qed.
Lemma lem4836049 {A : Type'} (v : type686 A) (u : type686 A) (x : A -> Prop) : (term391 A u v x) = (term398 A v u x).
Proof. exact (@lem19490 (@I ((A -> Prop) -> Prop) v x) (term375 A u x) (term222 A x)). Qed.
Lemma lem4836050 {A : Type'} (v : type686 A) (u : type686 A) : (term392 A u v) = (term399 A v u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4836049 A v u x)). Qed.
Lemma lem4836051 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4836053 {A : Type'} (v : type686 A) (u : type686 A) : (term393 A u v) = (term400 A v u).
Proof. exact (MK_COMB (@lem4836051 A) (@lem4836050 A v u)). Qed.
Lemma lem4836054 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term400 A v u.
Proof. exact (EQ_MP (@lem4836053 A v u) (@lem4836002 A u x' v h1)). Qed.
Lemma lem4836070 {A : Type'} (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') : term375 A v x'.
Proof. exact (h1). Qed.
Lemma lem4836105 {A : Type'} (v : type686 A) (u : type686 A) (x : A -> Prop) : (term391 A u v x) = (term398 A v u x).
Proof. exact (@lem19490 (@I ((A -> Prop) -> Prop) v x) (term375 A u x) (term222 A x)). Qed.
Lemma lem4836106 {A : Type'} (v : type686 A) (u : type686 A) : (term392 A u v) = (term399 A v u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4836105 A v u x)). Qed.
Lemma lem4836107 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4836109 {A : Type'} (v : type686 A) (u : type686 A) : (term393 A u v) = (term400 A v u).
Proof. exact (MK_COMB (@lem4836107 A) (@lem4836106 A v u)). Qed.
Lemma lem4836110 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term400 A v u.
Proof. exact (EQ_MP (@lem4836109 A v u) (@lem4836002 A u x' v h1)). Qed.
Lemma lem4836126 {A : Type'} (x' : A -> Prop) (h1 : x' = (@EMPTY A)) : x' = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4836134 {A : Type'} (v : type686 A) (t : A -> Prop) (x : A) : (term377 A v t x) = (term377 A v t x).
Proof. exact (eq_refl (term377 A v t x)). Qed.
Lemma lem4836135 {A : Type'} (v : type686 A) (x : A) : (term378 A v x) = (term378 A v x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4836134 A v t x)). Qed.
Lemma lem4836136 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4836138 {A : Type'} (v : type686 A) (x : A) : (term379 A v x) = (term379 A v x).
Proof. exact (MK_COMB (@lem4836136 A) (@lem4836135 A v x)). Qed.
Lemma lem4836139 {A : Type'} (v : type686 A) (x : A) (h1 : term270 A v x) : term379 A v x.
Proof. exact (EQ_MP (@lem4836138 A v x) (@lem4835857 A v x h1)). Qed.
Lemma lem4836161 {A : Type'} (v : type686 A) (u : type686 A) (x : A -> Prop) : (term391 A u v x) = (term398 A v u x).
Proof. exact (@lem19490 (@I ((A -> Prop) -> Prop) v x) (term375 A u x) (term222 A x)). Qed.
Lemma lem4836162 {A : Type'} (v : type686 A) (u : type686 A) : (term392 A u v) = (term399 A v u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4836161 A v u x)). Qed.
Lemma lem4836163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4836165 {A : Type'} (v : type686 A) (u : type686 A) : (term393 A u v) = (term400 A v u).
Proof. exact (MK_COMB (@lem4836163 A) (@lem4836162 A v u)). Qed.
Lemma lem4836166 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term400 A v u.
Proof. exact (EQ_MP (@lem4836165 A v u) (@lem4836002 A u x' v h1)). Qed.
Lemma lem4836190 {A : Type'} (_59864 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term401 A v u _59864.
Proof. exact (@lem4836054 A u x' v h1 _59864). Qed.
Lemma lem4836191 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : (term401 A v u _59864) = (term398 A v u _59864).
Proof. exact (eq_refl (term401 A v u _59864)). Qed.
Lemma lem4836192 {A : Type'} (_59864 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term398 A v u _59864.
Proof. exact (EQ_MP (@lem4836191 A v u _59864) (@lem4836190 A _59864 u x' v h1)). Qed.
Lemma lem4836196 {A : Type'} (_59866 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term401 A v u _59866.
Proof. exact (@lem4836110 A u x' v h1 _59866). Qed.
Lemma lem4836197 {A : Type'} (v : type686 A) (u : type686 A) (_59866 : A -> Prop) : (term401 A v u _59866) = (term398 A v u _59866).
Proof. exact (eq_refl (term401 A v u _59866)). Qed.
Lemma lem4836198 {A : Type'} (_59866 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term398 A v u _59866.
Proof. exact (EQ_MP (@lem4836197 A v u _59866) (@lem4836196 A _59866 u x' v h1)). Qed.
Lemma lem4836199 {A : Type'} (_59867 : A -> Prop) (v : type686 A) (x : A) (h1 : term270 A v x) : term402 A v x _59867.
Proof. exact (@lem4836139 A v x h1 _59867). Qed.
Lemma lem4836200 {A : Type'} (v : type686 A) (_59867 : A -> Prop) (x : A) : (term402 A v x _59867) = (term377 A v _59867 x).
Proof. exact (eq_refl (term402 A v x _59867)). Qed.
Lemma lem4836202 {A : Type'} (_59868 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term401 A v u _59868.
Proof. exact (@lem4836166 A u x' v h1 _59868). Qed.
Lemma lem4836203 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : (term401 A v u _59868) = (term398 A v u _59868).
Proof. exact (eq_refl (term401 A v u _59868)). Qed.
Lemma lem4836204 {A : Type'} (_59868 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term398 A v u _59868.
Proof. exact (EQ_MP (@lem4836203 A v u _59868) (@lem4836202 A _59868 u x' v h1)). Qed.
Lemma lem4836226 {A : Type'} (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') : term375 A v x'.
Proof. exact (h1). Qed.
Lemma lem4836232 {A : Type'} (_59864 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term403 A u v _59864.
Proof. exact (proj1 (@lem4836192 A _59864 u x' v h1)). Qed.
Lemma lem4836252 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') : @I ((A -> Prop) -> Prop) u x'.
Proof. exact (proj1 (@lem4836005 A u v x' h1)). Qed.
Lemma lem4836254 {A : Type'} (x' : A -> Prop) (h1 : x' = (@EMPTY A)) : x' = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem4836272 {A : Type'} (_59867 : A -> Prop) (v : type686 A) (x : A) (h1 : term270 A v x) : term377 A v _59867 x.
Proof. exact (EQ_MP (@lem4836200 A v _59867 x) (@lem4836199 A _59867 v x h1)). Qed.
Lemma lem4836290 {A : Type'} (_59868 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term403 A u v _59868.
Proof. exact (proj1 (@lem4836204 A _59868 u x' v h1)). Qed.
Lemma lem4836367 {A : Type'} (u : type686 A) : (term404 A u) = (term404 A u).
Proof. exact (eq_refl (term404 A u)). Qed.
Lemma lem4836368 {A : Type'} (u : type686 A) (x' : A -> Prop) (h1 : x' = (@EMPTY A)) : (term405 A u x') = (term406 A u).
Proof. exact (MK_COMB (@lem4836367 A u) (@lem4836254 A x' h1)). Qed.
Lemma lem4836369 {A : Type'} (u : type686 A) : (term406 A u) = (@I ((A -> Prop) -> Prop) u (@EMPTY A)).
Proof. exact (eq_refl (term406 A u)). Qed.
Lemma lem4836370 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term407 A u x') = (term407 A u x').
Proof. exact (eq_refl (term407 A u x')). Qed.
Lemma lem4836371 {A : Type'} (x' : A -> Prop) (u : type686 A) : ((term405 A u x') = (term406 A u)) = ((term405 A u x') = (@I ((A -> Prop) -> Prop) u (@EMPTY A))).
Proof. exact (MK_COMB (@lem4836370 A u x') (@lem4836369 A u)). Qed.
Lemma lem4836372 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term405 A u x') = (@I ((A -> Prop) -> Prop) u x').
Proof. exact (eq_refl (term405 A u x')). Qed.
Lemma lem4836373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4836374 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term407 A u x') = (term408 A u x').
Proof. exact (MK_COMB (@lem4836373) (@lem4836372 A u x')). Qed.
Lemma lem4836375 {A : Type'} (u : type686 A) : (@I ((A -> Prop) -> Prop) u (@EMPTY A)) = (@I ((A -> Prop) -> Prop) u (@EMPTY A)).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) u (@EMPTY A))). Qed.
Lemma lem4836376 {A : Type'} (x' : A -> Prop) (u : type686 A) : ((term405 A u x') = (@I ((A -> Prop) -> Prop) u (@EMPTY A))) = ((@I ((A -> Prop) -> Prop) u x') = (@I ((A -> Prop) -> Prop) u (@EMPTY A))).
Proof. exact (MK_COMB (@lem4836374 A u x') (@lem4836375 A u)). Qed.
Lemma lem4836377 {A : Type'} (x' : A -> Prop) (u : type686 A) : ((term405 A u x') = (term406 A u)) = ((@I ((A -> Prop) -> Prop) u x') = (@I ((A -> Prop) -> Prop) u (@EMPTY A))).
Proof. exact (TRANS (@lem4836371 A x' u) (@lem4836376 A x' u)). Qed.
Lemma lem4836378 {A : Type'} (u : type686 A) (x' : A -> Prop) (h1 : x' = (@EMPTY A)) : (@I ((A -> Prop) -> Prop) u x') = (@I ((A -> Prop) -> Prop) u (@EMPTY A)).
Proof. exact (EQ_MP (@lem4836377 A x' u) (@lem4836368 A u x' h1)). Qed.
Lemma lem4836407 {A : Type'} (_59866 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term409 A u _59866.
Proof. exact (proj2 (@lem4836198 A _59866 u x' v h1)). Qed.
Lemma lem4836493 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') : @I ((A -> Prop) -> Prop) u x'.
Proof. exact (proj1 (@lem4836005 A u v x' h1)). Qed.
Lemma lem4836494 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') : term410 A u x'.
Proof. exact (fun h0 : term375 A u x' => @lem4836493 A u v x' h1). Qed.
Lemma lem4836496 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836497 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term410 A u x') = (@I ((A -> Prop) -> Prop) u x').
Proof. exact (@lem4836496 (@I ((A -> Prop) -> Prop) u x')). Qed.
Lemma lem4836498 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') : @I ((A -> Prop) -> Prop) u x'.
Proof. exact (EQ_MP (@lem4836497 A u x') (@lem4836494 A u v x' h1)). Qed.
Lemma lem4836504 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4836505 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : (term403 A u v _59864) = (term411 A v u _59864).
Proof. exact (@lem4836504 (@I ((A -> Prop) -> Prop) v _59864) (term375 A u _59864)). Qed.
Lemma lem4836511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4836512 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : (term412 A u v _59864) = (term413 A v u _59864).
Proof. exact (MK_COMB (@lem4836511) (@lem4836505 A v u _59864)). Qed.
Lemma lem4836518 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : (term411 A v u _59864) = (term411 A v u _59864).
Proof. exact (eq_refl (term411 A v u _59864)). Qed.
Lemma lem4836519 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : ((term403 A u v _59864) = (term411 A v u _59864)) = ((term411 A v u _59864) = (term411 A v u _59864)).
Proof. exact (MK_COMB (@lem4836512 A v u _59864) (@lem4836518 A v u _59864)). Qed.
Lemma lem4836521 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4836522 (x : Prop) : (x = x) = True.
Proof. exact (@lem4836521 Prop x). Qed.
Lemma lem4836523 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : ((term411 A v u _59864) = (term411 A v u _59864)) = True.
Proof. exact (@lem4836522 (term411 A v u _59864)). Qed.
Lemma lem4836524 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : ((term403 A u v _59864) = (term411 A v u _59864)) = True.
Proof. exact (TRANS (@lem4836519 A v u _59864) (@lem4836523 A v u _59864)). Qed.
Lemma lem4836525 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : True = ((term403 A u v _59864) = (term411 A v u _59864)).
Proof. exact (SYM (@lem4836524 A v u _59864)). Qed.
Lemma lem4836526 {A : Type'} (v : type686 A) (u : type686 A) (_59864 : A -> Prop) : (term403 A u v _59864) = (term411 A v u _59864).
Proof. exact (EQ_MP (@lem4836525 A v u _59864) (@lem0)). Qed.
Lemma lem4836527 {A : Type'} (_59864 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term411 A v u _59864.
Proof. exact (EQ_MP (@lem4836526 A v u _59864) (@lem4836232 A _59864 u x' v h1)). Qed.
Lemma lem4836529 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4836530 {A : Type'} (u : type686 A) (v : type686 A) (_59864 : A -> Prop) : (term411 A v u _59864) = (term414 A u v _59864).
Proof. exact (@lem4836529 (term375 A u _59864) (@I ((A -> Prop) -> Prop) v _59864)). Qed.
Lemma lem4836532 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4836533 {A : Type'} (u : type686 A) (_59864 : A -> Prop) : (term415 A u _59864) = (@I ((A -> Prop) -> Prop) u _59864).
Proof. exact (@lem4836532 (@I ((A -> Prop) -> Prop) u _59864)). Qed.
Lemma lem4836534 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4836535 {A : Type'} (u : type686 A) (_59864 : A -> Prop) : (term416 A u _59864) = (term417 A u _59864).
Proof. exact (MK_COMB (@lem4836534) (@lem4836533 A u _59864)). Qed.
Lemma lem4836536 {A : Type'} (v : type686 A) (_59864 : A -> Prop) : (@I ((A -> Prop) -> Prop) v _59864) = (@I ((A -> Prop) -> Prop) v _59864).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) v _59864)). Qed.
Lemma lem4836537 {A : Type'} (u : type686 A) (v : type686 A) (_59864 : A -> Prop) : (term414 A u v _59864) = (term418 A u v _59864).
Proof. exact (MK_COMB (@lem4836535 A u _59864) (@lem4836536 A v _59864)). Qed.
Lemma lem4836538 {A : Type'} (u : type686 A) (v : type686 A) (_59864 : A -> Prop) : (term411 A v u _59864) = (term418 A u v _59864).
Proof. exact (TRANS (@lem4836530 A u v _59864) (@lem4836537 A u v _59864)). Qed.
Lemma lem4836541 {A : Type'} (_59864 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term418 A u v _59864.
Proof. exact (EQ_MP (@lem4836538 A u v _59864) (@lem4836527 A _59864 u x' v h1)). Qed.
Lemma lem4836542 {A : Type'} (_59864 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term418 A u v _59864.
Proof. exact (@lem4836541 A _59864 u x' v h1). Qed.
Lemma lem4836543 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term418 A u v x'.
Proof. exact (@lem4836542 A x' u x' v h1). Qed.
Lemma lem4836546 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') : @I ((A -> Prop) -> Prop) v x'.
Proof. exact (@lem4836543 A u x' v h1 (@lem4836498 A u v x' h2)). Qed.
Lemma lem4836547 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') : term410 A v x'.
Proof. exact (fun h0 : term375 A v x' => @lem4836546 A u v x' h1 h2). Qed.
Lemma lem4836549 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836550 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term410 A v x') = (@I ((A -> Prop) -> Prop) v x').
Proof. exact (@lem4836549 (@I ((A -> Prop) -> Prop) v x')). Qed.
Lemma lem4836551 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') : @I ((A -> Prop) -> Prop) v x'.
Proof. exact (EQ_MP (@lem4836550 A v x') (@lem4836547 A u v x' h1 h2)). Qed.
Lemma lem4836554 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4836556 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term375 A v x') = (term419 A v x').
Proof. exact (@lem4836554 (@I ((A -> Prop) -> Prop) v x')). Qed.
Lemma lem4836559 {A : Type'} (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') : term419 A v x'.
Proof. exact (EQ_MP (@lem4836556 A v x') (@lem4836226 A v x' h1)). Qed.
Lemma lem4836562 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : False.
Proof. exact (@lem4836559 A v x' h1 (@lem4836551 A u v x' h2 h3)). Qed.
Lemma lem4836563 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : term184.
Proof. exact (fun h0 : ~ False => @lem4836562 A u v x' h1 h2 h3). Qed.
Lemma lem4836565 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836566 : term184 = False.
Proof. exact (@lem4836565 False). Qed.
Lemma lem4836567 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : False.
Proof. exact (EQ_MP (@lem4836566) (@lem4836563 A u v x' h1 h2 h3)). Qed.
Lemma lem4836653 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') (h2 : x' = (@EMPTY A)) : @I ((A -> Prop) -> Prop) u (@EMPTY A).
Proof. exact (EQ_MP (@lem4836378 A u x' h2) (@lem4836252 A u v x' h1)). Qed.
Lemma lem4836654 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') (h2 : x' = (@EMPTY A)) : term420 A u.
Proof. exact (fun h0 : term421 A u => @lem4836653 A u v x' h1 h2). Qed.
Lemma lem4836656 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836657 {A : Type'} (u : type686 A) : (term420 A u) = (@I ((A -> Prop) -> Prop) u (@EMPTY A)).
Proof. exact (@lem4836656 (@I ((A -> Prop) -> Prop) u (@EMPTY A))). Qed.
Lemma lem4836658 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') (h2 : x' = (@EMPTY A)) : @I ((A -> Prop) -> Prop) u (@EMPTY A).
Proof. exact (EQ_MP (@lem4836657 A u) (@lem4836654 A u v x' h1 h2)). Qed.
Lemma lem4836660 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4836661 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4836660 A x). Qed.
Lemma lem4836662 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (@lem4836661 A (@EMPTY A)). Qed.
Lemma lem4836663 {A : Type'} : term422 A.
Proof. exact (fun h0 : term423 A => @lem4836662 A). Qed.
Lemma lem4836665 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836666 {A : Type'} : (term422 A) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (@lem4836665 ((@EMPTY A) = (@EMPTY A))). Qed.
Lemma lem4836667 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4836666 A) (@lem4836663 A)). Qed.
Lemma lem4836669 (a : Prop) (b : Prop) : (term424 a b) = (term425 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4836670 {A : Type'} (u : type686 A) (_59866 : A -> Prop) : (term409 A u _59866) = (term426 A u _59866).
Proof. exact (@lem4836669 (@I ((A -> Prop) -> Prop) u _59866) (_59866 = (@EMPTY A))). Qed.
Lemma lem4836672 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4836673 {A : Type'} (u : type686 A) (_59866 : A -> Prop) : (term426 A u _59866) = (term427 A u _59866).
Proof. exact (@lem4836672 (term428 A u _59866)). Qed.
Lemma lem4836674 {A : Type'} (u : type686 A) (_59866 : A -> Prop) : (term409 A u _59866) = (term427 A u _59866).
Proof. exact (TRANS (@lem4836670 A u _59866) (@lem4836673 A u _59866)). Qed.
Lemma lem4836676 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term388 A u v x') (h2 : x' = (@EMPTY A)) : term429 A u.
Proof. exact (conj (@lem4836658 A u v x' h1 h2) (@lem4836667 A)). Qed.
Lemma lem4836678 {A : Type'} (_59866 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term427 A u _59866.
Proof. exact (EQ_MP (@lem4836674 A u _59866) (@lem4836407 A _59866 u x' v h1)). Qed.
Lemma lem4836679 {A : Type'} (_59866 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term427 A u _59866.
Proof. exact (@lem4836678 A _59866 u x' v h1). Qed.
Lemma lem4836680 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term430 A u.
Proof. exact (@lem4836679 A (@EMPTY A) u x' v h1). Qed.
Lemma lem4836683 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : False.
Proof. exact (@lem4836680 A u x' v h1 (@lem4836676 A u v x' h2 h3)). Qed.
Lemma lem4836684 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : term184.
Proof. exact (fun h0 : ~ False => @lem4836683 A u v x' h1 h2 h3). Qed.
Lemma lem4836686 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836687 : term184 = False.
Proof. exact (@lem4836686 False). Qed.
Lemma lem4836774 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) (h1 : term243 A u t x) : @I ((A -> Prop) -> Prop) u t.
Proof. exact (proj1 (@lem4835877 A u t x h1)). Qed.
Lemma lem4836775 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) (h1 : term243 A u t x) : term410 A u t.
Proof. exact (fun h0 : term375 A u t => @lem4836774 A u t x h1). Qed.
Lemma lem4836777 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836778 {A : Type'} (u : type686 A) (t : A -> Prop) : (term410 A u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem4836777 (@I ((A -> Prop) -> Prop) u t)). Qed.
Lemma lem4836779 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) (h1 : term243 A u t x) : @I ((A -> Prop) -> Prop) u t.
Proof. exact (EQ_MP (@lem4836778 A u t) (@lem4836775 A u t x h1)). Qed.
Lemma lem4836785 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4836786 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : (term403 A u v _59868) = (term411 A v u _59868).
Proof. exact (@lem4836785 (@I ((A -> Prop) -> Prop) v _59868) (term375 A u _59868)). Qed.
Lemma lem4836792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4836793 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : (term412 A u v _59868) = (term413 A v u _59868).
Proof. exact (MK_COMB (@lem4836792) (@lem4836786 A v u _59868)). Qed.
Lemma lem4836799 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : (term411 A v u _59868) = (term411 A v u _59868).
Proof. exact (eq_refl (term411 A v u _59868)). Qed.
Lemma lem4836800 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : ((term403 A u v _59868) = (term411 A v u _59868)) = ((term411 A v u _59868) = (term411 A v u _59868)).
Proof. exact (MK_COMB (@lem4836793 A v u _59868) (@lem4836799 A v u _59868)). Qed.
Lemma lem4836802 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4836803 (x : Prop) : (x = x) = True.
Proof. exact (@lem4836802 Prop x). Qed.
Lemma lem4836804 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : ((term411 A v u _59868) = (term411 A v u _59868)) = True.
Proof. exact (@lem4836803 (term411 A v u _59868)). Qed.
Lemma lem4836805 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : ((term403 A u v _59868) = (term411 A v u _59868)) = True.
Proof. exact (TRANS (@lem4836800 A v u _59868) (@lem4836804 A v u _59868)). Qed.
Lemma lem4836806 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : True = ((term403 A u v _59868) = (term411 A v u _59868)).
Proof. exact (SYM (@lem4836805 A v u _59868)). Qed.
Lemma lem4836807 {A : Type'} (v : type686 A) (u : type686 A) (_59868 : A -> Prop) : (term403 A u v _59868) = (term411 A v u _59868).
Proof. exact (EQ_MP (@lem4836806 A v u _59868) (@lem0)). Qed.
Lemma lem4836808 {A : Type'} (_59868 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term411 A v u _59868.
Proof. exact (EQ_MP (@lem4836807 A v u _59868) (@lem4836290 A _59868 u x' v h1)). Qed.
Lemma lem4836810 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4836811 {A : Type'} (u : type686 A) (v : type686 A) (_59868 : A -> Prop) : (term411 A v u _59868) = (term414 A u v _59868).
Proof. exact (@lem4836810 (term375 A u _59868) (@I ((A -> Prop) -> Prop) v _59868)). Qed.
Lemma lem4836813 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4836814 {A : Type'} (u : type686 A) (_59868 : A -> Prop) : (term415 A u _59868) = (@I ((A -> Prop) -> Prop) u _59868).
Proof. exact (@lem4836813 (@I ((A -> Prop) -> Prop) u _59868)). Qed.
Lemma lem4836815 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4836816 {A : Type'} (u : type686 A) (_59868 : A -> Prop) : (term416 A u _59868) = (term417 A u _59868).
Proof. exact (MK_COMB (@lem4836815) (@lem4836814 A u _59868)). Qed.
Lemma lem4836817 {A : Type'} (v : type686 A) (_59868 : A -> Prop) : (@I ((A -> Prop) -> Prop) v _59868) = (@I ((A -> Prop) -> Prop) v _59868).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) v _59868)). Qed.
Lemma lem4836818 {A : Type'} (u : type686 A) (v : type686 A) (_59868 : A -> Prop) : (term414 A u v _59868) = (term418 A u v _59868).
Proof. exact (MK_COMB (@lem4836816 A u _59868) (@lem4836817 A v _59868)). Qed.
Lemma lem4836819 {A : Type'} (u : type686 A) (v : type686 A) (_59868 : A -> Prop) : (term411 A v u _59868) = (term418 A u v _59868).
Proof. exact (TRANS (@lem4836811 A u v _59868) (@lem4836818 A u v _59868)). Qed.
Lemma lem4836822 {A : Type'} (_59868 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term418 A u v _59868.
Proof. exact (EQ_MP (@lem4836819 A u v _59868) (@lem4836808 A _59868 u x' v h1)). Qed.
Lemma lem4836823 {A : Type'} (_59868 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term418 A u v _59868.
Proof. exact (@lem4836822 A _59868 u x' v h1). Qed.
Lemma lem4836824 {A : Type'} (t : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term418 A u v t.
Proof. exact (@lem4836823 A t u x' v h1). Qed.
Lemma lem4836827 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term243 A u t x) (h2 : term359 A u x' v) : @I ((A -> Prop) -> Prop) v t.
Proof. exact (@lem4836824 A t u x' v h2 (@lem4836779 A u t x h1)). Qed.
Lemma lem4836828 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term243 A u t x) (h2 : term359 A u x' v) : term410 A v t.
Proof. exact (fun h0 : term375 A v t => @lem4836827 A t x u x' v h1 h2). Qed.
Lemma lem4836830 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836831 {A : Type'} (v : type686 A) (t : A -> Prop) : (term410 A v t) = (@I ((A -> Prop) -> Prop) v t).
Proof. exact (@lem4836830 (@I ((A -> Prop) -> Prop) v t)). Qed.
Lemma lem4836832 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term243 A u t x) (h2 : term359 A u x' v) : @I ((A -> Prop) -> Prop) v t.
Proof. exact (EQ_MP (@lem4836831 A v t) (@lem4836828 A t x u x' v h1 h2)). Qed.
Lemma lem4836834 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) (h1 : term243 A u t x) : @I (A -> Prop) t x.
Proof. exact (proj2 (@lem4835877 A u t x h1)). Qed.
Lemma lem4836835 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) (h1 : term243 A u t x) : term431 A t x.
Proof. exact (fun h0 : term373 A t x => @lem4836834 A u t x h1). Qed.
Lemma lem4836837 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836838 {A : Type'} (t : A -> Prop) (x : A) : (term431 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4836837 (@I (A -> Prop) t x)). Qed.
Lemma lem4836839 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) (h1 : term243 A u t x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4836838 A t x) (@lem4836835 A u t x h1)). Qed.
Lemma lem4836841 (a : Prop) (b : Prop) : (term424 a b) = (term425 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4836842 {A : Type'} (v : type686 A) (_59867 : A -> Prop) (x : A) : (term377 A v _59867 x) = (term432 A v _59867 x).
Proof. exact (@lem4836841 (@I ((A -> Prop) -> Prop) v _59867) (@I (A -> Prop) _59867 x)). Qed.
Lemma lem4836844 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4836845 {A : Type'} (v : type686 A) (_59867 : A -> Prop) (x : A) : (term432 A v _59867 x) = (term433 A v _59867 x).
Proof. exact (@lem4836844 (term381 A v _59867 x)). Qed.
Lemma lem4836846 {A : Type'} (v : type686 A) (_59867 : A -> Prop) (x : A) : (term377 A v _59867 x) = (term433 A v _59867 x).
Proof. exact (TRANS (@lem4836842 A v _59867 x) (@lem4836845 A v _59867 x)). Qed.
Lemma lem4836848 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term243 A u t x) (h2 : term359 A u x' v) : term381 A v t x.
Proof. exact (conj (@lem4836832 A t x u x' v h1 h2) (@lem4836839 A u t x h1)). Qed.
Lemma lem4836850 {A : Type'} (_59867 : A -> Prop) (v : type686 A) (x : A) (h1 : term270 A v x) : term433 A v _59867 x.
Proof. exact (EQ_MP (@lem4836846 A v _59867 x) (@lem4836272 A _59867 v x h1)). Qed.
Lemma lem4836851 {A : Type'} (_59867 : A -> Prop) (v : type686 A) (x : A) (h1 : term270 A v x) : term433 A v _59867 x.
Proof. exact (@lem4836850 A _59867 v x h1). Qed.
Lemma lem4836852 {A : Type'} (t : A -> Prop) (v : type686 A) (x : A) (h1 : term270 A v x) : term433 A v t x.
Proof. exact (@lem4836851 A t v x h1). Qed.
Lemma lem4836855 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term270 A v x) (h2 : term243 A u t x) (h3 : term359 A u x' v) : False.
Proof. exact (@lem4836852 A t v x h1 (@lem4836848 A t x u x' v h2 h3)). Qed.
Lemma lem4836856 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term270 A v x) (h2 : term243 A u t x) (h3 : term359 A u x' v) : term184.
Proof. exact (fun h0 : ~ False => @lem4836855 A t x u x' v h1 h2 h3). Qed.
Lemma lem4836858 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4836859 : term184 = False.
Proof. exact (@lem4836858 False). Qed.
Lemma lem4836860 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term270 A v x) (h2 : term243 A u t x) (h3 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4836859) (@lem4836856 A t x u x' v h1 h2 h3)). Qed.
Lemma lem4836861 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4836687) (@lem4836684 A u v x' h1 h2 h3)). Qed.
Lemma lem4836862 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : (x' = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : x' = (@EMPTY A) => @lem4836861 A u v x' h1 h2 h3) (fun h4 : False => @lem4836254 A x' h3)). Qed.
Lemma lem4836863 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4836862 A u v x' h1 h2 h3) (@lem4836254 A x' h3)). Qed.
Lemma lem4836864 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : (term375 A v x') = False.
Proof. exact (prop_ext (fun h4 : term375 A v x' => @lem4836567 A u v x' h1 h2 h3) (fun h4 : False => @lem4836226 A v x' h1)). Qed.
Lemma lem4836865 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : False.
Proof. exact (EQ_MP (@lem4836864 A u v x' h1 h2 h3) (@lem4836226 A v x' h1)). Qed.
Lemma lem4836866 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : (x' = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : x' = (@EMPTY A) => @lem4836863 A u v x' h1 h2 h3) (fun h4 : False => @lem4836126 A x' h3)). Qed.
Lemma lem4836867 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4836866 A u v x' h1 h2 h3) (@lem4836126 A x' h3)). Qed.
Lemma lem4836868 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : (term375 A v x') = False.
Proof. exact (prop_ext (fun h4 : term375 A v x' => @lem4836865 A u v x' h1 h2 h3) (fun h4 : False => @lem4836070 A v x' h1)). Qed.
Lemma lem4836869 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : False.
Proof. exact (EQ_MP (@lem4836868 A u v x' h1 h2 h3) (@lem4836070 A v x' h1)). Qed.
Lemma lem4836870 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : (x' = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : x' = (@EMPTY A) => @lem4836867 A u v x' h1 h2 h3) (fun h4 : False => @lem4836126 A x' h3)). Qed.
Lemma lem4836871 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') (h3 : x' = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem4836870 A u v x' h1 h2 h3) (@lem4836126 A x' h3)). Qed.
Lemma lem4836872 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : (term375 A v x') = False.
Proof. exact (prop_ext (fun h4 : term375 A v x' => @lem4836869 A u v x' h1 h2 h3) (fun h4 : False => @lem4836070 A v x' h1)). Qed.
Lemma lem4836873 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term375 A v x') (h2 : term359 A u x' v) (h3 : term388 A u v x') : False.
Proof. exact (EQ_MP (@lem4836872 A u v x' h1 h2 h3) (@lem4836070 A v x' h1)). Qed.
Lemma lem4836874 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term359 A u x' v) (h2 : term388 A u v x') : False.
Proof. exact (or_elim (@lem4836007 A u v x' h2) (fun h0 : term375 A v x' => @lem4836873 A u v x' h0 h1 h2) (fun h0 : x' = (@EMPTY A) => @lem4836871 A u v x' h1 h2 h0)). Qed.
Lemma lem4836875 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term270 A v x) (h2 : term243 A u t x) (h3 : term359 A u x' v) : False.
Proof. exact (or_elim (@lem4836001 A u x' v h3) (fun h0 : term388 A u v x' => @lem4836874 A u v x' h3 h0) (fun h0 : term386 A u v x' => @lem4836860 A t x u x' v h1 h2 h3)). Qed.
Lemma lem4836876 {A : Type'} (t : A -> Prop) (x : A) (u : type686 A) (v : type686 A) (h1 : term270 A v x) (h2 : term243 A u t x) (h3 : term238 A u v) : False.
Proof. exact (ex_elim (@lem4835717 A u v h3) (fun x' : A -> Prop => fun h0 : term361 A u v x' => @lem4836875 A t x u x' v h1 h2 h0)). Qed.
Lemma lem4836877 {A : Type'} (x : A) (u : type686 A) (v : type686 A) (h1 : term246 A u x) (h2 : term270 A v x) (h3 : term238 A u v) : False.
Proof. exact (ex_elim (@lem4835758 A u x h1) (fun t : A -> Prop => fun h0 : term245 A u x t => @lem4836876 A t x u v h2 h0 h3)). Qed.
Lemma lem4836878 {A : Type'} (x : A) (u : type686 A) (v : type686 A) (h1 : term246 A u x) (h2 : term270 A v x) (h3 : term238 A u v) : (term246 A u x) = False.
Proof. exact (prop_ext (fun h4 : term246 A u x => @lem4836877 A x u v h1 h2 h3) (fun h4 : False => @lem4835758 A u x h1)). Qed.
Lemma lem4836879 {A : Type'} (x : A) (u : type686 A) (v : type686 A) (h1 : term246 A u x) (h2 : term270 A v x) (h3 : term238 A u v) : False.
Proof. exact (EQ_MP (@lem4836878 A x u v h1 h2 h3) (@lem4835758 A u x h1)). Qed.
Lemma lem4836880 {A : Type'} (x : A) (u : type686 A) (v : type686 A) (h1 : term246 A u x) (h2 : term270 A v x) (h3 : term238 A u v) : (term270 A v x) = False.
Proof. exact (prop_ext (fun h4 : term270 A v x => @lem4836879 A x u v h1 h2 h3) (fun h4 : False => @lem4835420 A v x h2)). Qed.
Lemma lem4836881 {A : Type'} (x : A) (u : type686 A) (v : type686 A) (h1 : term246 A u x) (h2 : term270 A v x) (h3 : term238 A u v) : False.
Proof. exact (EQ_MP (@lem4836880 A x u v h1 h2 h3) (@lem4835420 A v x h2)). Qed.
Lemma lem4836882 {A : Type'} (x : A) (u : type686 A) (v : type686 A) (h1 : term246 A u x) (h2 : term238 A u v) : term269 A v x.
Proof. exact (fun h0 : term270 A v x => @lem4836881 A x u v h1 h0 h2). Qed.
Lemma lem4836883 {A : Type'} (x : A) (u : type686 A) (v : type686 A) (h1 : term246 A u x) (h2 : term238 A u v) : term246 A v x.
Proof. exact (EQ_MP (@lem4835419 A v x) (@lem4836882 A x u v h1 h2)). Qed.
Lemma lem4836884 {A : Type'} (x : A) (u : type686 A) (v : type686 A) (h1 : term238 A u v) : term250 A u v x.
Proof. exact (fun h0 : term246 A u x => @lem4836883 A x u v h0 h1). Qed.
Lemma lem4836889 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term238 A u v) : term253 A u v.
Proof. exact (fun x : A => @lem4836884 A x u v h1). Qed.
Lemma lem4836890 {A : Type'} (u : type686 A) (v : type686 A) : term254 A u v.
Proof. exact (fun h0 : term238 A u v => @lem4836889 A u v h0). Qed.
Lemma lem4836895 {A : Type'} (v : type686 A) : term264 A v.
Proof. exact (fun u : type686 A => @lem4836890 A u v). Qed.
Lemma lem4836900 {A : Type'} : term268 A.
Proof. exact (fun v : type686 A => @lem4836895 A v). Qed.
Lemma lem4836901 {A : Type'} : term267 A.
Proof. exact (EQ_MP (@lem4835413 A) (@lem4836900 A)). Qed.
Lemma lem4836902 {A : Type'} (v : type686 A) : term434 A v.
Proof. exact (@lem4836901 A v). Qed.
Lemma lem4836903 {A : Type'} (v : type686 A) : (term434 A v) = (term263 A v).
Proof. exact (eq_refl (term434 A v)). Qed.
Lemma lem4836904 {A : Type'} (v : type686 A) : term263 A v.
Proof. exact (EQ_MP (@lem4836903 A v) (@lem4836902 A v)). Qed.
Lemma lem4836905 {A : Type'} (v : type686 A) (u : type686 A) : term435 A v u.
Proof. exact (@lem4836904 A v u). Qed.
Lemma lem4836906 {A : Type'} (u : type686 A) (v : type686 A) : (term435 A v u) = (term255 A u v).
Proof. exact (eq_refl (term435 A v u)). Qed.
Lemma lem4836907 {A : Type'} (u : type686 A) (v : type686 A) : term255 A u v.
Proof. exact (EQ_MP (@lem4836906 A u v) (@lem4836905 A v u)). Qed.
Lemma lem4836909 {A : Type'} (u : type686 A) (v : type686 A) : term255 A u v.
Proof. exact (@lem4835162 A u v (@lem4836907 A u v)). Qed.
Lemma lem4836910 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term256 A u v) : False.
Proof. exact (@lem4836909 A u v (@lem4835146 A u v h1)). Qed.
Lemma lem4836911 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term256 A u v) : (term256 A u v) = False.
Proof. exact (prop_ext (fun h2 : term256 A u v => @lem4836910 A u v h1) (fun h2 : False => @lem4835146 A u v h1)). Qed.
Lemma lem4836912 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term256 A u v) : False.
Proof. exact (EQ_MP (@lem4836911 A u v h1) (@lem4835146 A u v h1)). Qed.
Lemma lem4836913 {A : Type'} (u : type686 A) (v : type686 A) : term255 A u v.
Proof. exact (fun h0 : term256 A u v => @lem4836912 A u v h0). Qed.
Lemma lem4836914 {A : Type'} (u : type686 A) (v : type686 A) : term254 A u v.
Proof. exact (EQ_MP (@lem4835145 A u v) (@lem4836913 A u v)). Qed.
Lemma lem4836915 {A : Type'} (u : type686 A) (v : type686 A) : term213 A u v.
Proof. exact (EQ_MP (@lem4835141 A u v) (@lem4836914 A u v)). Qed.
Lemma lem4836916 {A : Type'} (u : type686 A) (v : type686 A) : term212 A u v.
Proof. exact (EQ_MP (@lem4834954 A u v) (@lem4836915 A u v)). Qed.
Lemma lem4836917 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term210 A u v.
Proof. exact (@lem4836916 A u v (@lem4834890 A u v h1 h2)). Qed.
Lemma lem4836919 {A : Type'} (s : type686 A) (t : type686 A) : term30 A s t.
Proof. exact (EQ_MP (@lem4833755 A s t) (@lem4833754 A s t)). Qed.
Lemma lem4836920 {A : Type'} (s : type686 A) (t : type686 A) : term30 A s t.
Proof. exact (@lem4836919 A s t). Qed.
Lemma lem4836921 {A : Type'} (v : type686 A) (u : type686 A) : term30 A v u.
Proof. exact (@lem4836920 A v u). Qed.
Lemma lem4836923 (p : Prop) (q : Prop) (r : Prop) : term436 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem4836924 {A : Type'} (v : type686 A) (u : type686 A) : term437 A v u.
Proof. exact (@lem4836923 (term438 A u v) ((term439 A v u) = (term440 A v u)) (term441 A v u)). Qed.
Lemma lem4836935 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term192 A u v.
Proof. exact (conj (@lem4834874 A u v h1) (@lem4834875 A v h2)). Qed.
Lemma lem4836941 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term42 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem4836942 {A : Type'} (s : type686 A) (t : type686 A) : (@PSUBSET (A -> Prop) s t) = (term193 A s t).
Proof. exact (@lem4836941 (A -> Prop) s t). Qed.
Lemma lem4836943 {A : Type'} (u : type686 A) (v : type686 A) : (term190 A u v) = (term194 A u v).
Proof. exact (@lem4836942 A u (@DELETE (A -> Prop) v (@EMPTY A))). Qed.
Lemma lem4836947 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4836948 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term195 A s t).
Proof. exact (@lem4836947 (A -> Prop) s t). Qed.
Lemma lem4836949 {A : Type'} (u : type686 A) (v : type686 A) : (term196 A u v) = (term197 A u v).
Proof. exact (@lem4836948 A u (@DELETE (A -> Prop) v (@EMPTY A))). Qed.
Lemma lem4836956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4836957 {A : Type'} (u : type686 A) (v : type686 A) : (term198 A u v) = (term199 A u v).
Proof. exact (MK_COMB (@lem4836956) (@lem4836949 A u v)). Qed.
Lemma lem4836961 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term34 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4836962 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term200 A s t).
Proof. exact (@lem4836961 (A -> Prop) s t). Qed.
Lemma lem4836963 {A : Type'} (u : type686 A) (v : type686 A) : (u = (@DELETE (A -> Prop) v (@EMPTY A))) = (term201 A u v).
Proof. exact (@lem4836962 A u (@DELETE (A -> Prop) v (@EMPTY A))). Qed.
Lemma lem4836972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4836973 {A : Type'} (u : type686 A) (v : type686 A) : (term202 A u v) = (term203 A u v).
Proof. exact (MK_COMB (@lem4836972) (@lem4836963 A u v)). Qed.
Lemma lem4836974 {A : Type'} (u : type686 A) (v : type686 A) : (term194 A u v) = (term204 A u v).
Proof. exact (MK_COMB (@lem4836957 A u v) (@lem4836973 A u v)). Qed.
Lemma lem4836977 {A : Type'} (u : type686 A) (v : type686 A) : (term190 A u v) = (term204 A u v).
Proof. exact (TRANS (@lem4836943 A u v) (@lem4836974 A u v)). Qed.
Lemma lem4836978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4836979 {A : Type'} (u : type686 A) (v : type686 A) : (term205 A u v) = (term206 A u v).
Proof. exact (MK_COMB (@lem4836978) (@lem4836977 A u v)). Qed.
Lemma lem4836980 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4836981 {A : Type'} (u : type686 A) (v : type686 A) : (term192 A u v) = (term207 A u v).
Proof. exact (MK_COMB (@lem4836979 A u v) (@lem4836980 A v)). Qed.
Lemma lem4836984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4836985 {A : Type'} (u : type686 A) (v : type686 A) : (term208 A u v) = (term209 A u v).
Proof. exact (MK_COMB (@lem4836984) (@lem4836981 A u v)). Qed.
Lemma lem4836989 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term31 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4836990 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term195 A s t).
Proof. exact (@lem4836989 (A -> Prop) s t). Qed.
Lemma lem4836991 {A : Type'} (u : type686 A) (v : type686 A) : (@SUBSET (A -> Prop) u v) = (term195 A u v).
Proof. exact (@lem4836990 A u v). Qed.
Lemma lem4836998 {A : Type'} (v : type686 A) : (term442 A v) = (term442 A v).
Proof. exact (eq_refl (term442 A v)). Qed.
Lemma lem4836999 {A : Type'} (u : type686 A) (v : type686 A) : (term438 A u v) = (term443 A u v).
Proof. exact (MK_COMB (@lem4836998 A v) (@lem4836991 A u v)). Qed.
Lemma lem4837002 {A : Type'} (u : type686 A) (v : type686 A) : (term444 A u v) = (term445 A u v).
Proof. exact (MK_COMB (@lem4836985 A u v) (@lem4836999 A u v)). Qed.
Lemma lem4837005 {A : Type'} (u : type686 A) (v : type686 A) : (term445 A u v) = (term444 A u v).
Proof. exact (SYM (@lem4837002 A u v)). Qed.
Lemma lem4837019 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4837020 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4837019 (A -> Prop) P x). Qed.
Lemma lem4837021 {A : Type'} (u : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x u) = (u x).
Proof. exact (@lem4837020 A u x). Qed.
Lemma lem4837022 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4837023 {A : Type'} (u : type686 A) (x : A -> Prop) : (term214 A x u) = (term215 A u x).
Proof. exact (MK_COMB (@lem4837022) (@lem4837021 A u x)). Qed.
Lemma lem4837025 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term19 A x s y) = (term20 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4837026 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term216 A x s y) = (term217 A s x y).
Proof. exact (@lem4837025 (A -> Prop) s x y). Qed.
Lemma lem4837027 {A : Type'} (v : type686 A) (x : A -> Prop) : (term218 A x v) = (term219 A v x).
Proof. exact (@lem4837026 A v x (@EMPTY A)). Qed.
Lemma lem4837031 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4837032 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4837031 (A -> Prop) P x). Qed.
Lemma lem4837033 {A : Type'} (v : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x v) = (v x).
Proof. exact (@lem4837032 A v x). Qed.
Lemma lem4837034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837035 {A : Type'} (v : type686 A) (x : A -> Prop) : (term220 A x v) = (term221 A v x).
Proof. exact (MK_COMB (@lem4837034) (@lem4837033 A v x)). Qed.
Lemma lem4837038 {A : Type'} (x : A -> Prop) : (term222 A x) = (term222 A x).
Proof. exact (eq_refl (term222 A x)). Qed.
Lemma lem4837039 {A : Type'} (v : type686 A) (x : A -> Prop) : (term219 A v x) = (term223 A v x).
Proof. exact (MK_COMB (@lem4837035 A v x) (@lem4837038 A x)). Qed.
Lemma lem4837042 {A : Type'} (v : type686 A) (x : A -> Prop) : (term218 A x v) = (term223 A v x).
Proof. exact (TRANS (@lem4837027 A v x) (@lem4837039 A v x)). Qed.
Lemma lem4837043 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term224 A u x v) = (term225 A u v x).
Proof. exact (MK_COMB (@lem4837023 A u x) (@lem4837042 A v x)). Qed.
Lemma lem4837046 {A : Type'} (u : type686 A) (v : type686 A) : (term226 A u v) = (term227 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837043 A u v x)). Qed.
Lemma lem4837047 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837048 {A : Type'} (u : type686 A) (v : type686 A) : (term197 A u v) = (term228 A u v).
Proof. exact (MK_COMB (@lem4837047 A) (@lem4837046 A u v)). Qed.
Lemma lem4837053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837054 {A : Type'} (u : type686 A) (v : type686 A) : (term199 A u v) = (term229 A u v).
Proof. exact (MK_COMB (@lem4837053) (@lem4837048 A u v)). Qed.
Lemma lem4837062 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4837063 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4837062 (A -> Prop) P x). Qed.
Lemma lem4837064 {A : Type'} (u : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x u) = (u x).
Proof. exact (@lem4837063 A u x). Qed.
Lemma lem4837065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4837066 {A : Type'} (u : type686 A) (x : A -> Prop) : (term230 A x u) = (term231 A u x).
Proof. exact (MK_COMB (@lem4837065) (@lem4837064 A u x)). Qed.
Lemma lem4837068 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term19 A x s y) = (term20 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4837069 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term216 A x s y) = (term217 A s x y).
Proof. exact (@lem4837068 (A -> Prop) s x y). Qed.
Lemma lem4837070 {A : Type'} (v : type686 A) (x : A -> Prop) : (term218 A x v) = (term219 A v x).
Proof. exact (@lem4837069 A v x (@EMPTY A)). Qed.
Lemma lem4837074 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4837075 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4837074 (A -> Prop) P x). Qed.
Lemma lem4837076 {A : Type'} (v : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x v) = (v x).
Proof. exact (@lem4837075 A v x). Qed.
Lemma lem4837077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837078 {A : Type'} (v : type686 A) (x : A -> Prop) : (term220 A x v) = (term221 A v x).
Proof. exact (MK_COMB (@lem4837077) (@lem4837076 A v x)). Qed.
Lemma lem4837081 {A : Type'} (x : A -> Prop) : (term222 A x) = (term222 A x).
Proof. exact (eq_refl (term222 A x)). Qed.
Lemma lem4837082 {A : Type'} (v : type686 A) (x : A -> Prop) : (term219 A v x) = (term223 A v x).
Proof. exact (MK_COMB (@lem4837078 A v x) (@lem4837081 A x)). Qed.
Lemma lem4837085 {A : Type'} (v : type686 A) (x : A -> Prop) : (term218 A x v) = (term223 A v x).
Proof. exact (TRANS (@lem4837070 A v x) (@lem4837082 A v x)). Qed.
Lemma lem4837086 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x u) = (term218 A x v)) = ((u x) = (term223 A v x)).
Proof. exact (MK_COMB (@lem4837066 A u x) (@lem4837085 A v x)). Qed.
Lemma lem4837089 {A : Type'} (u : type686 A) (v : type686 A) : (term232 A u v) = (term233 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837086 A u v x)). Qed.
Lemma lem4837090 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837091 {A : Type'} (u : type686 A) (v : type686 A) : (term201 A u v) = (term234 A u v).
Proof. exact (MK_COMB (@lem4837090 A) (@lem4837089 A u v)). Qed.
Lemma lem4837096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4837097 {A : Type'} (u : type686 A) (v : type686 A) : (term203 A u v) = (term235 A u v).
Proof. exact (MK_COMB (@lem4837096) (@lem4837091 A u v)). Qed.
Lemma lem4837098 {A : Type'} (u : type686 A) (v : type686 A) : (term204 A u v) = (term236 A u v).
Proof. exact (MK_COMB (@lem4837054 A u v) (@lem4837097 A u v)). Qed.
Lemma lem4837101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837102 {A : Type'} (u : type686 A) (v : type686 A) : (term206 A u v) = (term237 A u v).
Proof. exact (MK_COMB (@lem4837101) (@lem4837098 A u v)). Qed.
Lemma lem4837103 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837104 {A : Type'} (u : type686 A) (v : type686 A) : (term207 A u v) = (term238 A u v).
Proof. exact (MK_COMB (@lem4837102 A u v) (@lem4837103 A v)). Qed.
Lemma lem4837107 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4837108 {A : Type'} (u : type686 A) (v : type686 A) : (term209 A u v) = (term239 A u v).
Proof. exact (MK_COMB (@lem4837107) (@lem4837104 A u v)). Qed.
Lemma lem4837118 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4837119 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4837118 (A -> Prop) P x). Qed.
Lemma lem4837120 {A : Type'} (u : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x u) = (u x).
Proof. exact (@lem4837119 A u x). Qed.
Lemma lem4837121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4837122 {A : Type'} (u : type686 A) (x : A -> Prop) : (term214 A x u) = (term215 A u x).
Proof. exact (MK_COMB (@lem4837121) (@lem4837120 A u x)). Qed.
Lemma lem4837124 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4837125 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4837124 (A -> Prop) P x). Qed.
Lemma lem4837126 {A : Type'} (v : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x v) = (v x).
Proof. exact (@lem4837125 A v x). Qed.
Lemma lem4837127 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term446 A u x v) = (term447 A u v x).
Proof. exact (MK_COMB (@lem4837122 A u x) (@lem4837126 A v x)). Qed.
Lemma lem4837130 {A : Type'} (u : type686 A) (v : type686 A) : (term448 A u v) = (term449 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837127 A u v x)). Qed.
Lemma lem4837131 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837132 {A : Type'} (u : type686 A) (v : type686 A) : (term195 A u v) = (term450 A u v).
Proof. exact (MK_COMB (@lem4837131 A) (@lem4837130 A u v)). Qed.
Lemma lem4837137 {A : Type'} (v : type686 A) : (term442 A v) = (term442 A v).
Proof. exact (eq_refl (term442 A v)). Qed.
Lemma lem4837138 {A : Type'} (u : type686 A) (v : type686 A) : (term443 A u v) = (term451 A u v).
Proof. exact (MK_COMB (@lem4837137 A v) (@lem4837132 A u v)). Qed.
Lemma lem4837141 {A : Type'} (u : type686 A) (v : type686 A) : (term445 A u v) = (term452 A u v).
Proof. exact (MK_COMB (@lem4837108 A u v) (@lem4837138 A u v)). Qed.
Lemma lem4837144 {A : Type'} (u : type686 A) (v : type686 A) : (term452 A u v) = (term445 A u v).
Proof. exact (SYM (@lem4837141 A u v)). Qed.
Lemma lem4837146 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4837147 {A : Type'} (u : type686 A) (v : type686 A) : (term452 A u v) = (term453 A u v).
Proof. exact (@lem4837146 (term452 A u v)). Qed.
Lemma lem4837148 {A : Type'} (u : type686 A) (v : type686 A) : (term453 A u v) = (term452 A u v).
Proof. exact (SYM (@lem4837147 A u v)). Qed.
Lemma lem4837149 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term454 A u v) : term454 A u v.
Proof. exact (h1). Qed.
Lemma lem4837152 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term453 A u v) : term453 A u v.
Proof. exact (h1). Qed.
Lemma lem4837153 {A : Type'} (u : type686 A) (v : type686 A) : term455 A u v.
Proof. exact (fun h0 : term453 A u v => @lem4837152 A u v h0). Qed.
Lemma lem4837154 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term455 A u v) : term455 A u v.
Proof. exact (h1). Qed.
Lemma lem4837155 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term453 A u v) : term453 A u v.
Proof. exact (h1). Qed.
Lemma lem4837156 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term453 A u v) (h2 : term455 A u v) : term453 A u v.
Proof. exact (@lem4837154 A u v h2 (@lem4837155 A u v h1)). Qed.
Lemma lem4837157 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term453 A u v) : term456 A u v.
Proof. exact (fun h0 : term455 A u v => @lem4837156 A u v h1 h0). Qed.
Lemma lem4837158 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term455 A u v) : term455 A u v.
Proof. exact (h1). Qed.
Lemma lem4837159 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term453 A u v) (h2 : term455 A u v) : term453 A u v.
Proof. exact (@lem4837157 A u v h1 (@lem4837158 A u v h2)). Qed.
Lemma lem4837160 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term455 A u v) : term455 A u v.
Proof. exact (fun h0 : term453 A u v => @lem4837159 A u v h0 h1). Qed.
Lemma lem4837161 {A : Type'} (u : type686 A) (v : type686 A) : term457 A u v.
Proof. exact (fun h0 : term455 A u v => @lem4837160 A u v h0). Qed.
Lemma lem4837164 {A : Type'} (u : type686 A) (v : type686 A) : term455 A u v.
Proof. exact (@lem4837161 A u v (@lem4837153 A u v)). Qed.
Lemma lem4837165 {A : Type'} (u : type686 A) (v : type686 A) : term455 A u v.
Proof. exact (@lem4837164 A u v). Qed.
Lemma lem4837175 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4837176 {A : Type'} (u : type686 A) (v : type686 A) : (term453 A u v) = (term458 A u v).
Proof. exact (@lem4837175 (term454 A u v)). Qed.
Lemma lem4837178 (t : Prop) : (term85 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4837179 {A : Type'} (u : type686 A) (v : type686 A) : (term458 A u v) = (term452 A u v).
Proof. exact (@lem4837178 (term452 A u v)). Qed.
Lemma lem4837182 {A : Type'} (u : type686 A) (v : type686 A) : (term453 A u v) = (term452 A u v).
Proof. exact (TRANS (@lem4837176 A u v) (@lem4837179 A u v)). Qed.
Lemma lem4837209 {A : Type'} (v : type686 A) : (term459 A v) = (term460 A v).
Proof. exact (fun_ext (fun u : type686 A => @lem4837182 A u v)). Qed.
Lemma lem4837210 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4837211 {A : Type'} (v : type686 A) : (term461 A v) = (term462 A v).
Proof. exact (MK_COMB (@lem4837210 A) (@lem4837209 A v)). Qed.
Lemma lem4837216 {A : Type'} : (term463 A) = (term464 A).
Proof. exact (fun_ext (fun v : type686 A => @lem4837211 A v)). Qed.
Lemma lem4837217 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4837226 {A : Type'} : (term465 A) = (term466 A).
Proof. exact (MK_COMB (@lem4837217 A) (@lem4837216 A)). Qed.
Lemma lem4837231 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term447 A u v x) = (term447 A u v x).
Proof. exact (eq_refl (term447 A u v x)). Qed.
Lemma lem4837232 {A : Type'} (u : type686 A) (v : type686 A) : (term449 A u v) = (term449 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837231 A u v x)). Qed.
Lemma lem4837233 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837234 {A : Type'} (u : type686 A) (v : type686 A) : (term450 A u v) = (term450 A u v).
Proof. exact (MK_COMB (@lem4837233 A) (@lem4837232 A u v)). Qed.
Lemma lem4837237 {A : Type'} (v : type686 A) : (term442 A v) = (term442 A v).
Proof. exact (eq_refl (term442 A v)). Qed.
Lemma lem4837238 {A : Type'} (u : type686 A) (v : type686 A) : (term451 A u v) = (term451 A u v).
Proof. exact (MK_COMB (@lem4837237 A v) (@lem4837234 A u v)). Qed.
Lemma lem4837239 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837250 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : ((u x) = (term223 A v x)) = ((u x) = (term223 A v x)).
Proof. exact (eq_refl ((u x) = (term223 A v x))). Qed.
Lemma lem4837251 {A : Type'} (u : type686 A) (v : type686 A) : (term233 A u v) = (term233 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837250 A u v x)). Qed.
Lemma lem4837252 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837253 {A : Type'} (u : type686 A) (v : type686 A) : (term234 A u v) = (term234 A u v).
Proof. exact (MK_COMB (@lem4837252 A) (@lem4837251 A u v)). Qed.
Lemma lem4837254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4837255 {A : Type'} (u : type686 A) (v : type686 A) : (term235 A u v) = (term235 A u v).
Proof. exact (MK_COMB (@lem4837254) (@lem4837253 A u v)). Qed.
Lemma lem4837266 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term225 A u v x) = (term225 A u v x).
Proof. exact (eq_refl (term225 A u v x)). Qed.
Lemma lem4837267 {A : Type'} (u : type686 A) (v : type686 A) : (term227 A u v) = (term227 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837266 A u v x)). Qed.
Lemma lem4837268 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837269 {A : Type'} (u : type686 A) (v : type686 A) : (term228 A u v) = (term228 A u v).
Proof. exact (MK_COMB (@lem4837268 A) (@lem4837267 A u v)). Qed.
Lemma lem4837270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837271 {A : Type'} (u : type686 A) (v : type686 A) : (term229 A u v) = (term229 A u v).
Proof. exact (MK_COMB (@lem4837270) (@lem4837269 A u v)). Qed.
Lemma lem4837272 {A : Type'} (u : type686 A) (v : type686 A) : (term236 A u v) = (term236 A u v).
Proof. exact (MK_COMB (@lem4837271 A u v) (@lem4837255 A u v)). Qed.
Lemma lem4837273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837274 {A : Type'} (u : type686 A) (v : type686 A) : (term237 A u v) = (term237 A u v).
Proof. exact (MK_COMB (@lem4837273) (@lem4837272 A u v)). Qed.
Lemma lem4837275 {A : Type'} (u : type686 A) (v : type686 A) : (term238 A u v) = (term238 A u v).
Proof. exact (MK_COMB (@lem4837274 A u v) (@lem4837239 A v)). Qed.
Lemma lem4837276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4837277 {A : Type'} (u : type686 A) (v : type686 A) : (term239 A u v) = (term239 A u v).
Proof. exact (MK_COMB (@lem4837276) (@lem4837275 A u v)). Qed.
Lemma lem4837278 {A : Type'} (u : type686 A) (v : type686 A) : (term452 A u v) = (term452 A u v).
Proof. exact (MK_COMB (@lem4837277 A u v) (@lem4837238 A u v)). Qed.
Lemma lem4837279 {A : Type'} (v : type686 A) : (term460 A v) = (term460 A v).
Proof. exact (fun_ext (fun u : type686 A => @lem4837278 A u v)). Qed.
Lemma lem4837280 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4837281 {A : Type'} (v : type686 A) : (term462 A v) = (term462 A v).
Proof. exact (MK_COMB (@lem4837280 A) (@lem4837279 A v)). Qed.
Lemma lem4837282 {A : Type'} : (term464 A) = (term464 A).
Proof. exact (fun_ext (fun v : type686 A => @lem4837281 A v)). Qed.
Lemma lem4837283 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4837284 {A : Type'} : (term466 A) = (term466 A).
Proof. exact (MK_COMB (@lem4837283 A) (@lem4837282 A)). Qed.
Lemma lem4837333 {A : Type'} : (term465 A) = (term466 A).
Proof. exact (TRANS (@lem4837226 A) (@lem4837284 A)). Qed.
Lemma lem4837334 {A : Type'} : (term466 A) = (term465 A).
Proof. exact (SYM (@lem4837333 A)). Qed.
Lemma lem4837335 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term238 A u v) : term238 A u v.
Proof. exact (h1). Qed.
Lemma lem4837337 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4837338 {A : Type'} (u : type686 A) (v : type686 A) : (term451 A u v) = (term467 A u v).
Proof. exact (@lem4837337 (term451 A u v)). Qed.
Lemma lem4837339 {A : Type'} (u : type686 A) (v : type686 A) : (term467 A u v) = (term451 A u v).
Proof. exact (SYM (@lem4837338 A u v)). Qed.
Lemma lem4837340 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term468 A u v) : term468 A u v.
Proof. exact (h1). Qed.
Lemma lem4837351 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term225 A u v x) = (term271 A u v x).
Proof. exact (@lem17265 (u x) (term223 A v x)). Qed.
Lemma lem4837352 {A : Type'} (u : type686 A) (v : type686 A) : (term227 A u v) = (term272 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837351 A u v x)). Qed.
Lemma lem4837353 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837354 {A : Type'} (u : type686 A) (v : type686 A) : (term228 A u v) = (term273 A u v).
Proof. exact (MK_COMB (@lem4837353 A) (@lem4837352 A u v)). Qed.
Lemma lem4837362 {A : Type'} (x : A -> Prop) : (term274 A x) = (x = (@EMPTY A)).
Proof. exact (@lem16933 (x = (@EMPTY A))). Qed.
Lemma lem4837364 {A : Type'} (v : type686 A) (x : A -> Prop) : (term275 A v x) = (term275 A v x).
Proof. exact (eq_refl (term275 A v x)). Qed.
Lemma lem4837365 {A : Type'} (v : type686 A) (x : A -> Prop) : (term276 A v x) = (term277 A v x).
Proof. exact (MK_COMB (@lem4837364 A v x) (@lem4837362 A x)). Qed.
Lemma lem4837366 {A : Type'} (v : type686 A) (x : A -> Prop) : (term278 A v x) = (term276 A v x).
Proof. exact (@lem17045 (v x) (term222 A x)). Qed.
Lemma lem4837367 {A : Type'} (v : type686 A) (x : A -> Prop) : (term278 A v x) = (term277 A v x).
Proof. exact (TRANS (@lem4837366 A v x) (@lem4837365 A v x)). Qed.
Lemma lem4837373 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term279 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term279 A u v x)). Qed.
Lemma lem4837375 {A : Type'} (u : type686 A) (x : A -> Prop) : (term221 A u x) = (term221 A u x).
Proof. exact (eq_refl (term221 A u x)). Qed.
Lemma lem4837376 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term280 A u v x) = (term281 A u v x).
Proof. exact (MK_COMB (@lem4837375 A u x) (@lem4837367 A v x)). Qed.
Lemma lem4837377 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4837378 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term282 A u v x) = (term283 A u v x).
Proof. exact (MK_COMB (@lem4837377) (@lem4837376 A u v x)). Qed.
Lemma lem4837379 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term284 A u v x) = (term285 A u v x).
Proof. exact (MK_COMB (@lem4837378 A u v x) (@lem4837373 A u v x)). Qed.
Lemma lem4837380 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term286 A u v x) = (term284 A u v x).
Proof. exact (@lem17646 (u x) (term223 A v x)). Qed.
Lemma lem4837381 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term286 A u v x) = (term285 A u v x).
Proof. exact (TRANS (@lem4837380 A u v x) (@lem4837379 A u v x)). Qed.
Lemma lem4837382 {A : Type'} (P : type686 A) : (term287 A P) = (term288 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4837383 {A : Type'} (u : type686 A) (v : type686 A) : (term235 A u v) = (term289 A u v).
Proof. exact (@lem4837382 A (term233 A u v)). Qed.
Lemma lem4837384 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term290 A u v x) = ((u x) = (term223 A v x)).
Proof. exact (eq_refl (term290 A u v x)). Qed.
Lemma lem4837385 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4837386 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term291 A u v x) = (term286 A u v x).
Proof. exact (MK_COMB (@lem4837385) (@lem4837384 A u v x)). Qed.
Lemma lem4837387 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term291 A u v x) = (term285 A u v x).
Proof. exact (TRANS (@lem4837386 A u v x) (@lem4837381 A u v x)). Qed.
Lemma lem4837388 {A : Type'} (u : type686 A) (v : type686 A) : (term292 A u v) = (term293 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837387 A u v x)). Qed.
Lemma lem4837389 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837390 {A : Type'} (u : type686 A) (v : type686 A) : (term289 A u v) = (term294 A u v).
Proof. exact (MK_COMB (@lem4837389 A) (@lem4837388 A u v)). Qed.
Lemma lem4837391 {A : Type'} (u : type686 A) (v : type686 A) : (term235 A u v) = (term294 A u v).
Proof. exact (TRANS (@lem4837383 A u v) (@lem4837390 A u v)). Qed.
Lemma lem4837392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837393 {A : Type'} (u : type686 A) (v : type686 A) : (term229 A u v) = (term295 A u v).
Proof. exact (MK_COMB (@lem4837392) (@lem4837354 A u v)). Qed.
Lemma lem4837394 {A : Type'} (u : type686 A) (v : type686 A) : (term236 A u v) = (term296 A u v).
Proof. exact (MK_COMB (@lem4837393 A u v) (@lem4837391 A u v)). Qed.
Lemma lem4837395 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837397 {A : Type'} (u : type686 A) (v : type686 A) : (term237 A u v) = (term297 A u v).
Proof. exact (MK_COMB (@lem4837396) (@lem4837394 A u v)). Qed.
Lemma lem4837398 {A : Type'} (u : type686 A) (v : type686 A) : (term238 A u v) = (term298 A u v).
Proof. exact (MK_COMB (@lem4837397 A u v) (@lem4837395 A v)). Qed.
Lemma lem4837448 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term299 A P Q) = (term300 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4837449 {A : Type'} (P : type686 A) (Q : type686 A) : (term301 A P Q) = (term302 A P Q).
Proof. exact (@lem4837448 (A -> Prop) P Q). Qed.
Lemma lem4837450 {A : Type'} (u : type686 A) (v : type686 A) : (term303 A u v) = (term304 A u v).
Proof. exact (@lem4837449 A (term305 A u v) (term306 A u v)). Qed.
Lemma lem4837451 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term307 A u v x) = (term281 A u v x).
Proof. exact (eq_refl (term307 A u v x)). Qed.
Lemma lem4837452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4837453 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term308 A u v x) = (term283 A u v x).
Proof. exact (MK_COMB (@lem4837452) (@lem4837451 A u v x)). Qed.
Lemma lem4837454 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term309 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term309 A u v x)). Qed.
Lemma lem4837455 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term310 A u v x) = (term285 A u v x).
Proof. exact (MK_COMB (@lem4837453 A u v x) (@lem4837454 A u v x)). Qed.
Lemma lem4837456 {A : Type'} (u : type686 A) (v : type686 A) : (term311 A u v) = (term293 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837455 A u v x)). Qed.
Lemma lem4837457 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837458 {A : Type'} (u : type686 A) (v : type686 A) : (term303 A u v) = (term294 A u v).
Proof. exact (MK_COMB (@lem4837457 A) (@lem4837456 A u v)). Qed.
Lemma lem4837459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4837460 {A : Type'} (u : type686 A) (v : type686 A) : (term312 A u v) = (term313 A u v).
Proof. exact (MK_COMB (@lem4837459) (@lem4837458 A u v)). Qed.
Lemma lem4837461 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term307 A u v x) = (term281 A u v x).
Proof. exact (eq_refl (term307 A u v x)). Qed.
Lemma lem4837462 {A : Type'} (u : type686 A) (v : type686 A) : (term314 A u v) = (term305 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837461 A u v x)). Qed.
Lemma lem4837463 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837464 {A : Type'} (u : type686 A) (v : type686 A) : (term315 A u v) = (term316 A u v).
Proof. exact (MK_COMB (@lem4837463 A) (@lem4837462 A u v)). Qed.
Lemma lem4837465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4837466 {A : Type'} (u : type686 A) (v : type686 A) : (term317 A u v) = (term318 A u v).
Proof. exact (MK_COMB (@lem4837465) (@lem4837464 A u v)). Qed.
Lemma lem4837467 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term309 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term309 A u v x)). Qed.
Lemma lem4837468 {A : Type'} (u : type686 A) (v : type686 A) : (term319 A u v) = (term306 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837467 A u v x)). Qed.
Lemma lem4837469 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837470 {A : Type'} (u : type686 A) (v : type686 A) : (term320 A u v) = (term321 A u v).
Proof. exact (MK_COMB (@lem4837469 A) (@lem4837468 A u v)). Qed.
Lemma lem4837471 {A : Type'} (u : type686 A) (v : type686 A) : (term304 A u v) = (term322 A u v).
Proof. exact (MK_COMB (@lem4837466 A u v) (@lem4837470 A u v)). Qed.
Lemma lem4837472 {A : Type'} (u : type686 A) (v : type686 A) : ((term303 A u v) = (term304 A u v)) = ((term294 A u v) = (term322 A u v)).
Proof. exact (MK_COMB (@lem4837460 A u v) (@lem4837471 A u v)). Qed.
Lemma lem4837473 {A : Type'} (u : type686 A) (v : type686 A) : (term294 A u v) = (term322 A u v).
Proof. exact (EQ_MP (@lem4837472 A u v) (@lem4837450 A u v)). Qed.
Lemma lem4837550 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term295 A u v).
Proof. exact (eq_refl (term295 A u v)). Qed.
Lemma lem4837551 {A : Type'} (u : type686 A) (v : type686 A) : (term296 A u v) = (term323 A u v).
Proof. exact (MK_COMB (@lem4837550 A u v) (@lem4837473 A u v)). Qed.
Lemma lem4837552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837553 {A : Type'} (u : type686 A) (v : type686 A) : (term297 A u v) = (term324 A u v).
Proof. exact (MK_COMB (@lem4837552) (@lem4837551 A u v)). Qed.
Lemma lem4837554 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837555 {A : Type'} (u : type686 A) (v : type686 A) : (term298 A u v) = (term325 A u v).
Proof. exact (MK_COMB (@lem4837553 A u v) (@lem4837554 A v)). Qed.
Lemma lem4837557 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term300 A P Q) = (term299 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4837558 {A : Type'} (P : type686 A) (Q : type686 A) : (term302 A P Q) = (term301 A P Q).
Proof. exact (@lem4837557 (A -> Prop) P Q). Qed.
Lemma lem4837559 {A : Type'} (u : type686 A) (v : type686 A) : (term304 A u v) = (term303 A u v).
Proof. exact (@lem4837558 A (term305 A u v) (term306 A u v)). Qed.
Lemma lem4837560 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term307 A u v x) = (term281 A u v x).
Proof. exact (eq_refl (term307 A u v x)). Qed.
Lemma lem4837561 {A : Type'} (u : type686 A) (v : type686 A) : (term314 A u v) = (term305 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837560 A u v x)). Qed.
Lemma lem4837562 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837563 {A : Type'} (u : type686 A) (v : type686 A) : (term315 A u v) = (term316 A u v).
Proof. exact (MK_COMB (@lem4837562 A) (@lem4837561 A u v)). Qed.
Lemma lem4837564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4837565 {A : Type'} (u : type686 A) (v : type686 A) : (term317 A u v) = (term318 A u v).
Proof. exact (MK_COMB (@lem4837564) (@lem4837563 A u v)). Qed.
Lemma lem4837566 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term309 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term309 A u v x)). Qed.
Lemma lem4837567 {A : Type'} (u : type686 A) (v : type686 A) : (term319 A u v) = (term306 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837566 A u v x)). Qed.
Lemma lem4837568 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837569 {A : Type'} (u : type686 A) (v : type686 A) : (term320 A u v) = (term321 A u v).
Proof. exact (MK_COMB (@lem4837568 A) (@lem4837567 A u v)). Qed.
Lemma lem4837570 {A : Type'} (u : type686 A) (v : type686 A) : (term304 A u v) = (term322 A u v).
Proof. exact (MK_COMB (@lem4837565 A u v) (@lem4837569 A u v)). Qed.
Lemma lem4837571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4837572 {A : Type'} (u : type686 A) (v : type686 A) : (term326 A u v) = (term327 A u v).
Proof. exact (MK_COMB (@lem4837571) (@lem4837570 A u v)). Qed.
Lemma lem4837573 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term307 A u v x) = (term281 A u v x).
Proof. exact (eq_refl (term307 A u v x)). Qed.
Lemma lem4837574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4837575 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term308 A u v x) = (term283 A u v x).
Proof. exact (MK_COMB (@lem4837574) (@lem4837573 A u v x)). Qed.
Lemma lem4837576 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term309 A u v x) = (term279 A u v x).
Proof. exact (eq_refl (term309 A u v x)). Qed.
Lemma lem4837577 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term310 A u v x) = (term285 A u v x).
Proof. exact (MK_COMB (@lem4837575 A u v x) (@lem4837576 A u v x)). Qed.
Lemma lem4837578 {A : Type'} (u : type686 A) (v : type686 A) : (term311 A u v) = (term293 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837577 A u v x)). Qed.
Lemma lem4837579 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837580 {A : Type'} (u : type686 A) (v : type686 A) : (term303 A u v) = (term294 A u v).
Proof. exact (MK_COMB (@lem4837579 A) (@lem4837578 A u v)). Qed.
Lemma lem4837581 {A : Type'} (u : type686 A) (v : type686 A) : ((term304 A u v) = (term303 A u v)) = ((term322 A u v) = (term294 A u v)).
Proof. exact (MK_COMB (@lem4837572 A u v) (@lem4837580 A u v)). Qed.
Lemma lem4837582 {A : Type'} (u : type686 A) (v : type686 A) : (term322 A u v) = (term294 A u v).
Proof. exact (EQ_MP (@lem4837581 A u v) (@lem4837559 A u v)). Qed.
Lemma lem4837583 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term295 A u v).
Proof. exact (eq_refl (term295 A u v)). Qed.
Lemma lem4837584 {A : Type'} (u : type686 A) (v : type686 A) : (term323 A u v) = (term296 A u v).
Proof. exact (MK_COMB (@lem4837583 A u v) (@lem4837582 A u v)). Qed.
Lemma lem4837586 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4837587 {A : Type'} (P : Prop) (Q : type686 A) : (term328 A P Q) = (term329 A P Q).
Proof. exact (@lem4837586 (A -> Prop) P Q). Qed.
Lemma lem4837588 {A : Type'} (u : type686 A) (v : type686 A) : (term330 A u v) = (term331 A u v).
Proof. exact (@lem4837587 A (term273 A u v) (term293 A u v)). Qed.
Lemma lem4837589 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term332 A u v x) = (term285 A u v x).
Proof. exact (eq_refl (term332 A u v x)). Qed.
Lemma lem4837590 {A : Type'} (u : type686 A) (v : type686 A) : (term333 A u v) = (term293 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837589 A u v x)). Qed.
Lemma lem4837591 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837592 {A : Type'} (u : type686 A) (v : type686 A) : (term334 A u v) = (term294 A u v).
Proof. exact (MK_COMB (@lem4837591 A) (@lem4837590 A u v)). Qed.
Lemma lem4837593 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term295 A u v).
Proof. exact (eq_refl (term295 A u v)). Qed.
Lemma lem4837594 {A : Type'} (u : type686 A) (v : type686 A) : (term330 A u v) = (term296 A u v).
Proof. exact (MK_COMB (@lem4837593 A u v) (@lem4837592 A u v)). Qed.
Lemma lem4837595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4837596 {A : Type'} (u : type686 A) (v : type686 A) : (term335 A u v) = (term336 A u v).
Proof. exact (MK_COMB (@lem4837595) (@lem4837594 A u v)). Qed.
Lemma lem4837597 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term332 A u v x) = (term285 A u v x).
Proof. exact (eq_refl (term332 A u v x)). Qed.
Lemma lem4837598 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term295 A u v).
Proof. exact (eq_refl (term295 A u v)). Qed.
Lemma lem4837599 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term337 A u v x) = (term338 A u v x).
Proof. exact (MK_COMB (@lem4837598 A u v) (@lem4837597 A u v x)). Qed.
Lemma lem4837600 {A : Type'} (u : type686 A) (v : type686 A) : (term339 A u v) = (term340 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837599 A u v x)). Qed.
Lemma lem4837601 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837602 {A : Type'} (u : type686 A) (v : type686 A) : (term331 A u v) = (term341 A u v).
Proof. exact (MK_COMB (@lem4837601 A) (@lem4837600 A u v)). Qed.
Lemma lem4837603 {A : Type'} (u : type686 A) (v : type686 A) : ((term330 A u v) = (term331 A u v)) = ((term296 A u v) = (term341 A u v)).
Proof. exact (MK_COMB (@lem4837596 A u v) (@lem4837602 A u v)). Qed.
Lemma lem4837604 {A : Type'} (u : type686 A) (v : type686 A) : (term296 A u v) = (term341 A u v).
Proof. exact (EQ_MP (@lem4837603 A u v) (@lem4837588 A u v)). Qed.
Lemma lem4837605 {A : Type'} (u : type686 A) (v : type686 A) : (term323 A u v) = (term341 A u v).
Proof. exact (TRANS (@lem4837584 A u v) (@lem4837604 A u v)). Qed.
Lemma lem4837606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837607 {A : Type'} (u : type686 A) (v : type686 A) : (term324 A u v) = (term342 A u v).
Proof. exact (MK_COMB (@lem4837606) (@lem4837605 A u v)). Qed.
Lemma lem4837608 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837609 {A : Type'} (u : type686 A) (v : type686 A) : (term325 A u v) = (term343 A u v).
Proof. exact (MK_COMB (@lem4837607 A u v) (@lem4837608 A v)). Qed.
Lemma lem4837611 {A : Type'} (P : A -> Prop) (Q : Prop) : (term344 A P Q) = (term345 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4837612 {A : Type'} (P : type686 A) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem4837611 (A -> Prop) P Q). Qed.
Lemma lem4837613 {A : Type'} (u : type686 A) (v : type686 A) : (term348 A u v) = (term349 A u v).
Proof. exact (@lem4837612 A (term340 A u v) (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837614 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term350 A u v x) = (term338 A u v x).
Proof. exact (eq_refl (term350 A u v x)). Qed.
Lemma lem4837615 {A : Type'} (u : type686 A) (v : type686 A) : (term351 A u v) = (term340 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837614 A u v x)). Qed.
Lemma lem4837616 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837617 {A : Type'} (u : type686 A) (v : type686 A) : (term352 A u v) = (term341 A u v).
Proof. exact (MK_COMB (@lem4837616 A) (@lem4837615 A u v)). Qed.
Lemma lem4837618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837619 {A : Type'} (u : type686 A) (v : type686 A) : (term353 A u v) = (term342 A u v).
Proof. exact (MK_COMB (@lem4837618) (@lem4837617 A u v)). Qed.
Lemma lem4837620 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837621 {A : Type'} (u : type686 A) (v : type686 A) : (term348 A u v) = (term343 A u v).
Proof. exact (MK_COMB (@lem4837619 A u v) (@lem4837620 A v)). Qed.
Lemma lem4837622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4837623 {A : Type'} (u : type686 A) (v : type686 A) : (term354 A u v) = (term355 A u v).
Proof. exact (MK_COMB (@lem4837622) (@lem4837621 A u v)). Qed.
Lemma lem4837624 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term350 A u v x) = (term338 A u v x).
Proof. exact (eq_refl (term350 A u v x)). Qed.
Lemma lem4837625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837626 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term356 A u v x) = (term357 A u v x).
Proof. exact (MK_COMB (@lem4837625) (@lem4837624 A u v x)). Qed.
Lemma lem4837627 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837628 {A : Type'} (u : type686 A) (x : A -> Prop) (v : type686 A) : (term358 A u x v) = (term359 A u x v).
Proof. exact (MK_COMB (@lem4837626 A u v x) (@lem4837627 A v)). Qed.
Lemma lem4837629 {A : Type'} (u : type686 A) (v : type686 A) : (term360 A u v) = (term361 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837628 A u x v)). Qed.
Lemma lem4837630 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837631 {A : Type'} (u : type686 A) (v : type686 A) : (term349 A u v) = (term362 A u v).
Proof. exact (MK_COMB (@lem4837630 A) (@lem4837629 A u v)). Qed.
Lemma lem4837632 {A : Type'} (u : type686 A) (v : type686 A) : ((term348 A u v) = (term349 A u v)) = ((term343 A u v) = (term362 A u v)).
Proof. exact (MK_COMB (@lem4837623 A u v) (@lem4837631 A u v)). Qed.
Lemma lem4837633 {A : Type'} (u : type686 A) (v : type686 A) : (term343 A u v) = (term362 A u v).
Proof. exact (EQ_MP (@lem4837632 A u v) (@lem4837613 A u v)). Qed.
Lemma lem4837634 {A : Type'} (u : type686 A) (v : type686 A) : (term325 A u v) = (term362 A u v).
Proof. exact (TRANS (@lem4837609 A u v) (@lem4837633 A u v)). Qed.
Lemma lem4837635 {A : Type'} (u : type686 A) (v : type686 A) : (term298 A u v) = (term362 A u v).
Proof. exact (TRANS (@lem4837555 A u v) (@lem4837634 A u v)). Qed.
Lemma lem4837636 {A : Type'} (u : type686 A) (v : type686 A) : (term238 A u v) = (term362 A u v).
Proof. exact (TRANS (@lem4837398 A u v) (@lem4837635 A u v)). Qed.
Lemma lem4837637 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term238 A u v) : term362 A u v.
Proof. exact (EQ_MP (@lem4837636 A u v) (@lem4837335 A u v h1)). Qed.
Lemma lem4837645 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term469 A u v x) = (term470 A u v x).
Proof. exact (@lem17362 (u x) (v x)). Qed.
Lemma lem4837646 {A : Type'} (P : type686 A) : (term287 A P) = (term288 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4837647 {A : Type'} (u : type686 A) (v : type686 A) : (term471 A u v) = (term472 A u v).
Proof. exact (@lem4837646 A (term449 A u v)). Qed.
Lemma lem4837648 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term473 A u v x) = (term447 A u v x).
Proof. exact (eq_refl (term473 A u v x)). Qed.
Lemma lem4837649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4837650 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term474 A u v x) = (term469 A u v x).
Proof. exact (MK_COMB (@lem4837649) (@lem4837648 A u v x)). Qed.
Lemma lem4837651 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term474 A u v x) = (term470 A u v x).
Proof. exact (TRANS (@lem4837650 A u v x) (@lem4837645 A u v x)). Qed.
Lemma lem4837652 {A : Type'} (u : type686 A) (v : type686 A) : (term475 A u v) = (term476 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837651 A u v x)). Qed.
Lemma lem4837653 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837654 {A : Type'} (u : type686 A) (v : type686 A) : (term472 A u v) = (term477 A u v).
Proof. exact (MK_COMB (@lem4837653 A) (@lem4837652 A u v)). Qed.
Lemma lem4837655 {A : Type'} (u : type686 A) (v : type686 A) : (term471 A u v) = (term477 A u v).
Proof. exact (TRANS (@lem4837647 A u v) (@lem4837654 A u v)). Qed.
Lemma lem4837657 {A : Type'} (v : type686 A) : (term478 A v) = (term478 A v).
Proof. exact (eq_refl (term478 A v)). Qed.
Lemma lem4837658 {A : Type'} (u : type686 A) (v : type686 A) : (term479 A u v) = (term480 A u v).
Proof. exact (MK_COMB (@lem4837657 A v) (@lem4837655 A u v)). Qed.
Lemma lem4837659 {A : Type'} (u : type686 A) (v : type686 A) : (term468 A u v) = (term479 A u v).
Proof. exact (@lem17045 (@pairwise (A -> Prop) (@DISJOINT A) v) (term450 A u v)). Qed.
Lemma lem4837660 {A : Type'} (u : type686 A) (v : type686 A) : (term468 A u v) = (term480 A u v).
Proof. exact (TRANS (@lem4837659 A u v) (@lem4837658 A u v)). Qed.
Lemma lem4837691 {A : Type'} (P : Prop) (Q : A -> Prop) : (term481 A P Q) = (term482 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4837692 {A : Type'} (P : Prop) (Q : type686 A) : (term483 A P Q) = (term484 A P Q).
Proof. exact (@lem4837691 (A -> Prop) P Q). Qed.
Lemma lem4837693 {A : Type'} (u : type686 A) (v : type686 A) : (term485 A u v) = (term486 A u v).
Proof. exact (@lem4837692 A (term487 A v) (term476 A u v)). Qed.
Lemma lem4837694 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term488 A u v x) = (term470 A u v x).
Proof. exact (eq_refl (term488 A u v x)). Qed.
Lemma lem4837695 {A : Type'} (u : type686 A) (v : type686 A) : (term489 A u v) = (term476 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837694 A u v x)). Qed.
Lemma lem4837696 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837697 {A : Type'} (u : type686 A) (v : type686 A) : (term490 A u v) = (term477 A u v).
Proof. exact (MK_COMB (@lem4837696 A) (@lem4837695 A u v)). Qed.
Lemma lem4837698 {A : Type'} (v : type686 A) : (term478 A v) = (term478 A v).
Proof. exact (eq_refl (term478 A v)). Qed.
Lemma lem4837699 {A : Type'} (u : type686 A) (v : type686 A) : (term485 A u v) = (term480 A u v).
Proof. exact (MK_COMB (@lem4837698 A v) (@lem4837697 A u v)). Qed.
Lemma lem4837700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4837701 {A : Type'} (u : type686 A) (v : type686 A) : (term491 A u v) = (term492 A u v).
Proof. exact (MK_COMB (@lem4837700) (@lem4837699 A u v)). Qed.
Lemma lem4837702 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term488 A u v x) = (term470 A u v x).
Proof. exact (eq_refl (term488 A u v x)). Qed.
Lemma lem4837703 {A : Type'} (v : type686 A) : (term478 A v) = (term478 A v).
Proof. exact (eq_refl (term478 A v)). Qed.
Lemma lem4837704 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term493 A u v x) = (term494 A u v x).
Proof. exact (MK_COMB (@lem4837703 A v) (@lem4837702 A u v x)). Qed.
Lemma lem4837705 {A : Type'} (u : type686 A) (v : type686 A) : (term495 A u v) = (term496 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837704 A u v x)). Qed.
Lemma lem4837706 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4837707 {A : Type'} (u : type686 A) (v : type686 A) : (term486 A u v) = (term497 A u v).
Proof. exact (MK_COMB (@lem4837706 A) (@lem4837705 A u v)). Qed.
Lemma lem4837708 {A : Type'} (u : type686 A) (v : type686 A) : ((term485 A u v) = (term486 A u v)) = ((term480 A u v) = (term497 A u v)).
Proof. exact (MK_COMB (@lem4837701 A u v) (@lem4837707 A u v)). Qed.
Lemma lem4837710 {A : Type'} (u : type686 A) (v : type686 A) : (term480 A u v) = (term497 A u v).
Proof. exact (EQ_MP (@lem4837708 A u v) (@lem4837693 A u v)). Qed.
Lemma lem4837711 {A : Type'} (u : type686 A) (v : type686 A) : (term468 A u v) = (term497 A u v).
Proof. exact (TRANS (@lem4837660 A u v) (@lem4837710 A u v)). Qed.
Lemma lem4837712 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term468 A u v) : term497 A u v.
Proof. exact (EQ_MP (@lem4837711 A u v) (@lem4837340 A u v h1)). Qed.
Lemma lem4837713 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term494 A u v x) : term494 A u v x.
Proof. exact (h1). Qed.
Lemma lem4837714 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term359 A u x' v.
Proof. exact (h1). Qed.
Lemma lem4837715 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4837720 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4837721 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4837720 (A -> Prop) Prop f x). Qed.
Lemma lem4837723 {A : Type'} (v : type686 A) (x : A -> Prop) : (v x) = (@I ((A -> Prop) -> Prop) v x).
Proof. exact (@lem4837721 A v x). Qed.
Lemma lem4837724 {A : Type'} (v : type686 A) (x : A -> Prop) : (term374 A v x) = (term375 A v x).
Proof. exact (MK_COMB (@lem4837715) (@lem4837723 A v x)). Qed.
Lemma lem4837729 {A : Type'} (u : type686 A) (x : A -> Prop) : (term221 A u x) = (term221 A u x).
Proof. exact (eq_refl (term221 A u x)). Qed.
Lemma lem4837730 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term470 A u v x) = (term498 A u v x).
Proof. exact (MK_COMB (@lem4837729 A u x) (@lem4837724 A v x)). Qed.
Lemma lem4837739 {A : Type'} (v : type686 A) : (term478 A v) = (term478 A v).
Proof. exact (eq_refl (term478 A v)). Qed.
Lemma lem4837740 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term494 A u v x) = (term499 A u v x).
Proof. exact (MK_COMB (@lem4837739 A v) (@lem4837730 A u v x)). Qed.
Lemma lem4837741 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term494 A u v x) : term499 A u v x.
Proof. exact (EQ_MP (@lem4837740 A u v x) (@lem4837713 A u v x h1)). Qed.
Lemma lem4837746 {A : Type'} (v : type686 A) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (eq_refl (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4837753 {A : Type'} (x' : A -> Prop) : (term222 A x') = (term222 A x').
Proof. exact (eq_refl (term222 A x')). Qed.
Lemma lem4837758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4837759 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4837758 (A -> Prop) Prop f x). Qed.
Lemma lem4837761 {A : Type'} (v : type686 A) (x' : A -> Prop) : (v x') = (@I ((A -> Prop) -> Prop) v x').
Proof. exact (@lem4837759 A v x'). Qed.
Lemma lem4837762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837763 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term221 A v x') = (term380 A v x').
Proof. exact (MK_COMB (@lem4837762) (@lem4837761 A v x')). Qed.
Lemma lem4837764 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term223 A v x') = (term383 A v x').
Proof. exact (MK_COMB (@lem4837763 A v x') (@lem4837753 A x')). Qed.
Lemma lem4837771 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term384 A u x') = (term384 A u x').
Proof. exact (eq_refl (term384 A u x')). Qed.
Lemma lem4837772 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term279 A u v x') = (term500 A u v x').
Proof. exact (MK_COMB (@lem4837771 A u x') (@lem4837764 A v x')). Qed.
Lemma lem4837777 {A : Type'} (x' : A -> Prop) : (x' = (@EMPTY A)) = (x' = (@EMPTY A)).
Proof. exact (eq_refl (x' = (@EMPTY A))). Qed.
Lemma lem4837778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4837783 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4837784 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4837783 (A -> Prop) Prop f x). Qed.
Lemma lem4837786 {A : Type'} (v : type686 A) (x' : A -> Prop) : (v x') = (@I ((A -> Prop) -> Prop) v x').
Proof. exact (@lem4837784 A v x'). Qed.
Lemma lem4837787 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term374 A v x') = (term375 A v x').
Proof. exact (MK_COMB (@lem4837778) (@lem4837786 A v x')). Qed.
Lemma lem4837788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4837789 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term275 A v x') = (term376 A v x').
Proof. exact (MK_COMB (@lem4837788) (@lem4837787 A v x')). Qed.
Lemma lem4837790 {A : Type'} (v : type686 A) (x' : A -> Prop) : (term277 A v x') = (term387 A v x').
Proof. exact (MK_COMB (@lem4837789 A v x') (@lem4837777 A x')). Qed.
Lemma lem4837795 {A : Type'} (u : type686 A) (x' : A -> Prop) : (term221 A u x') = (term221 A u x').
Proof. exact (eq_refl (term221 A u x')). Qed.
Lemma lem4837796 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term281 A u v x') = (term501 A u v x').
Proof. exact (MK_COMB (@lem4837795 A u x') (@lem4837790 A v x')). Qed.
Lemma lem4837797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4837798 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term283 A u v x') = (term502 A u v x').
Proof. exact (MK_COMB (@lem4837797) (@lem4837796 A u v x')). Qed.
Lemma lem4837799 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term285 A u v x') = (term503 A u v x').
Proof. exact (MK_COMB (@lem4837798 A u v x') (@lem4837772 A u v x')). Qed.
Lemma lem4837806 {A : Type'} (x : A -> Prop) : (term222 A x) = (term222 A x).
Proof. exact (eq_refl (term222 A x)). Qed.
Lemma lem4837811 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4837812 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4837811 (A -> Prop) Prop f x). Qed.
Lemma lem4837814 {A : Type'} (v : type686 A) (x : A -> Prop) : (v x) = (@I ((A -> Prop) -> Prop) v x).
Proof. exact (@lem4837812 A v x). Qed.
Lemma lem4837815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837816 {A : Type'} (v : type686 A) (x : A -> Prop) : (term221 A v x) = (term380 A v x).
Proof. exact (MK_COMB (@lem4837815) (@lem4837814 A v x)). Qed.
Lemma lem4837817 {A : Type'} (v : type686 A) (x : A -> Prop) : (term223 A v x) = (term383 A v x).
Proof. exact (MK_COMB (@lem4837816 A v x) (@lem4837806 A x)). Qed.
Lemma lem4837824 {A : Type'} (u : type686 A) (x : A -> Prop) : (term275 A u x) = (term275 A u x).
Proof. exact (eq_refl (term275 A u x)). Qed.
Lemma lem4837825 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) : (term271 A u v x) = (term504 A u v x).
Proof. exact (MK_COMB (@lem4837824 A u x) (@lem4837817 A v x)). Qed.
Lemma lem4837826 {A : Type'} (u : type686 A) (v : type686 A) : (term272 A u v) = (term505 A u v).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837825 A u v x)). Qed.
Lemma lem4837827 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837828 {A : Type'} (u : type686 A) (v : type686 A) : (term273 A u v) = (term506 A u v).
Proof. exact (MK_COMB (@lem4837827 A) (@lem4837826 A u v)). Qed.
Lemma lem4837829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837830 {A : Type'} (u : type686 A) (v : type686 A) : (term295 A u v) = (term507 A u v).
Proof. exact (MK_COMB (@lem4837829) (@lem4837828 A u v)). Qed.
Lemma lem4837831 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term338 A u v x') = (term508 A u v x').
Proof. exact (MK_COMB (@lem4837830 A u v) (@lem4837799 A u v x')). Qed.
Lemma lem4837832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4837833 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) : (term357 A u v x') = (term509 A u v x').
Proof. exact (MK_COMB (@lem4837832) (@lem4837831 A u v x')). Qed.
Lemma lem4837834 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) : (term359 A u x' v) = (term510 A u x' v).
Proof. exact (MK_COMB (@lem4837833 A u v x') (@lem4837746 A v)). Qed.
Lemma lem4837835 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term510 A u x' v.
Proof. exact (EQ_MP (@lem4837834 A u x' v) (@lem4837714 A u x' v h1)). Qed.
Lemma lem4837837 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term508 A u v x'.
Proof. exact (proj1 (@lem4837835 A u x' v h1)). Qed.
Lemma lem4837838 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term503 A u v x'.
Proof. exact (proj2 (@lem4837837 A u x' v h1)). Qed.
Lemma lem4837839 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term506 A u v.
Proof. exact (proj1 (@lem4837837 A u x' v h1)). Qed.
Lemma lem4837840 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term501 A u v x') : term501 A u v x'.
Proof. exact (h1). Qed.
Lemma lem4837842 {A : Type'} (u : type686 A) (v : type686 A) (x' : A -> Prop) (h1 : term501 A u v x') : term387 A v x'.
Proof. exact (proj2 (@lem4837840 A u v x' h1)). Qed.
Lemma lem4837847 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term498 A u v x.
Proof. exact (h1). Qed.
Lemma lem4837851 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term498 A u v x.
Proof. exact (h1). Qed.
Lemma lem4837859 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term498 A u v x.
Proof. exact (h1). Qed.
Lemma lem4837900 {A : Type'} (v : type686 A) (h1 : term487 A v) : term487 A v.
Proof. exact (h1). Qed.
Lemma lem4837922 {A : Type'} (v : type686 A) (u : type686 A) (x : A -> Prop) : (term504 A u v x) = (term511 A v u x).
Proof. exact (@lem19490 (@I ((A -> Prop) -> Prop) v x) (term374 A u x) (term222 A x)). Qed.
Lemma lem4837923 {A : Type'} (v : type686 A) (u : type686 A) : (term505 A u v) = (term512 A v u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4837922 A v u x)). Qed.
Lemma lem4837924 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4837926 {A : Type'} (v : type686 A) (u : type686 A) : (term506 A u v) = (term513 A v u).
Proof. exact (MK_COMB (@lem4837924 A) (@lem4837923 A v u)). Qed.
Lemma lem4837927 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term513 A v u.
Proof. exact (EQ_MP (@lem4837926 A v u) (@lem4837839 A u x' v h1)). Qed.
Lemma lem4837982 {A : Type'} (v : type686 A) (h1 : term487 A v) : term487 A v.
Proof. exact (h1). Qed.
Lemma lem4838004 {A : Type'} (v : type686 A) (u : type686 A) (x : A -> Prop) : (term504 A u v x) = (term511 A v u x).
Proof. exact (@lem19490 (@I ((A -> Prop) -> Prop) v x) (term374 A u x) (term222 A x)). Qed.
Lemma lem4838005 {A : Type'} (v : type686 A) (u : type686 A) : (term505 A u v) = (term512 A v u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4838004 A v u x)). Qed.
Lemma lem4838006 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4838008 {A : Type'} (v : type686 A) (u : type686 A) : (term506 A u v) = (term513 A v u).
Proof. exact (MK_COMB (@lem4838006 A) (@lem4838005 A v u)). Qed.
Lemma lem4838009 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term513 A v u.
Proof. exact (EQ_MP (@lem4838008 A v u) (@lem4837839 A u x' v h1)). Qed.
Lemma lem4838068 {A : Type'} (v : type686 A) (h1 : term487 A v) : term487 A v.
Proof. exact (h1). Qed.
Lemma lem4838090 {A : Type'} (v : type686 A) (u : type686 A) (x : A -> Prop) : (term504 A u v x) = (term511 A v u x).
Proof. exact (@lem19490 (@I ((A -> Prop) -> Prop) v x) (term374 A u x) (term222 A x)). Qed.
Lemma lem4838091 {A : Type'} (v : type686 A) (u : type686 A) : (term505 A u v) = (term512 A v u).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4838090 A v u x)). Qed.
Lemma lem4838092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4838094 {A : Type'} (v : type686 A) (u : type686 A) : (term506 A u v) = (term513 A v u).
Proof. exact (MK_COMB (@lem4838092 A) (@lem4838091 A v u)). Qed.
Lemma lem4838095 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term513 A v u.
Proof. exact (EQ_MP (@lem4838094 A v u) (@lem4837839 A u x' v h1)). Qed.
Lemma lem4838119 {A : Type'} (_59934 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term514 A v u _59934.
Proof. exact (@lem4837927 A u x' v h1 _59934). Qed.
Lemma lem4838120 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : (term514 A v u _59934) = (term511 A v u _59934).
Proof. exact (eq_refl (term514 A v u _59934)). Qed.
Lemma lem4838121 {A : Type'} (_59934 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term511 A v u _59934.
Proof. exact (EQ_MP (@lem4838120 A v u _59934) (@lem4838119 A _59934 u x' v h1)). Qed.
Lemma lem4838125 {A : Type'} (_59936 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term514 A v u _59936.
Proof. exact (@lem4838009 A u x' v h1 _59936). Qed.
Lemma lem4838126 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : (term514 A v u _59936) = (term511 A v u _59936).
Proof. exact (eq_refl (term514 A v u _59936)). Qed.
Lemma lem4838127 {A : Type'} (_59936 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term511 A v u _59936.
Proof. exact (EQ_MP (@lem4838126 A v u _59936) (@lem4838125 A _59936 u x' v h1)). Qed.
Lemma lem4838131 {A : Type'} (_59938 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term514 A v u _59938.
Proof. exact (@lem4838095 A u x' v h1 _59938). Qed.
Lemma lem4838132 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : (term514 A v u _59938) = (term511 A v u _59938).
Proof. exact (eq_refl (term514 A v u _59938)). Qed.
Lemma lem4838133 {A : Type'} (_59938 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term511 A v u _59938.
Proof. exact (EQ_MP (@lem4838132 A v u _59938) (@lem4838131 A _59938 u x' v h1)). Qed.
Lemma lem4838153 {A : Type'} (v : type686 A) (h1 : term487 A v) : term487 A v.
Proof. exact (h1). Qed.
Lemma lem4838175 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term375 A v x.
Proof. exact (proj2 (@lem4837847 A u v x h1)). Qed.
Lemma lem4838181 {A : Type'} (_59934 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term515 A u v _59934.
Proof. exact (proj1 (@lem4838121 A _59934 u x' v h1)). Qed.
Lemma lem4838195 {A : Type'} (v : type686 A) (h1 : term487 A v) : term487 A v.
Proof. exact (h1). Qed.
Lemma lem4838239 {A : Type'} (v : type686 A) (h1 : term487 A v) : term487 A v.
Proof. exact (h1). Qed.
Lemma lem4838263 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term375 A v x.
Proof. exact (proj2 (@lem4837859 A u v x h1)). Qed.
Lemma lem4838269 {A : Type'} (_59938 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term515 A u v _59938.
Proof. exact (proj1 (@lem4838133 A _59938 u x' v h1)). Qed.
Lemma lem4838330 {A : Type'} (v : type686 A) (h1 : term487 A v) : term487 A v.
Proof. exact (h1). Qed.
Lemma lem4838427 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term375 A v x.
Proof. exact (proj2 (@lem4837851 A u v x h1)). Qed.
Lemma lem4838441 {A : Type'} (_59936 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term515 A u v _59936.
Proof. exact (proj1 (@lem4838127 A _59936 u x' v h1)). Qed.
Lemma lem4838513 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : @pairwise (A -> Prop) (@DISJOINT A) v.
Proof. exact (proj2 (@lem4837835 A u x' v h1)). Qed.
Lemma lem4838514 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term516 A v.
Proof. exact (fun h0 : term487 A v => @lem4838513 A u x' v h1). Qed.
Lemma lem4838516 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838517 {A : Type'} (v : type686 A) : (term516 A v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (@lem4838516 (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4838518 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : @pairwise (A -> Prop) (@DISJOINT A) v.
Proof. exact (EQ_MP (@lem4838517 A v) (@lem4838514 A u x' v h1)). Qed.
Lemma lem4838521 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4838523 {A : Type'} (v : type686 A) : (term487 A v) = (term517 A v).
Proof. exact (@lem4838521 (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4838526 {A : Type'} (v : type686 A) (h1 : term487 A v) : term517 A v.
Proof. exact (EQ_MP (@lem4838523 A v) (@lem4838153 A v h1)). Qed.
Lemma lem4838529 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (@lem4838526 A v h1 (@lem4838518 A u x' v h2)). Qed.
Lemma lem4838530 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : term184.
Proof. exact (fun h0 : ~ False => @lem4838529 A u x' v h1 h2). Qed.
Lemma lem4838532 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838533 : term184 = False.
Proof. exact (@lem4838532 False). Qed.
Lemma lem4838534 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4838533) (@lem4838530 A u x' v h1 h2)). Qed.
Lemma lem4838592 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : u x.
Proof. exact (proj1 (@lem4837847 A u v x h1)). Qed.
Lemma lem4838593 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term518 A u x.
Proof. exact (fun h0 : term374 A u x => @lem4838592 A u v x h1). Qed.
Lemma lem4838595 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838596 {A : Type'} (u : type686 A) (x : A -> Prop) : (term518 A u x) = (u x).
Proof. exact (@lem4838595 (u x)). Qed.
Lemma lem4838597 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : u x.
Proof. exact (EQ_MP (@lem4838596 A u x) (@lem4838593 A u v x h1)). Qed.
Lemma lem4838603 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4838604 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : (term515 A u v _59934) = (term519 A v u _59934).
Proof. exact (@lem4838603 (@I ((A -> Prop) -> Prop) v _59934) (term374 A u _59934)). Qed.
Lemma lem4838610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4838611 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : (term520 A u v _59934) = (term521 A v u _59934).
Proof. exact (MK_COMB (@lem4838610) (@lem4838604 A v u _59934)). Qed.
Lemma lem4838617 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : (term519 A v u _59934) = (term519 A v u _59934).
Proof. exact (eq_refl (term519 A v u _59934)). Qed.
Lemma lem4838618 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : ((term515 A u v _59934) = (term519 A v u _59934)) = ((term519 A v u _59934) = (term519 A v u _59934)).
Proof. exact (MK_COMB (@lem4838611 A v u _59934) (@lem4838617 A v u _59934)). Qed.
Lemma lem4838620 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4838621 (x : Prop) : (x = x) = True.
Proof. exact (@lem4838620 Prop x). Qed.
Lemma lem4838622 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : ((term519 A v u _59934) = (term519 A v u _59934)) = True.
Proof. exact (@lem4838621 (term519 A v u _59934)). Qed.
Lemma lem4838623 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : ((term515 A u v _59934) = (term519 A v u _59934)) = True.
Proof. exact (TRANS (@lem4838618 A v u _59934) (@lem4838622 A v u _59934)). Qed.
Lemma lem4838624 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : True = ((term515 A u v _59934) = (term519 A v u _59934)).
Proof. exact (SYM (@lem4838623 A v u _59934)). Qed.
Lemma lem4838625 {A : Type'} (v : type686 A) (u : type686 A) (_59934 : A -> Prop) : (term515 A u v _59934) = (term519 A v u _59934).
Proof. exact (EQ_MP (@lem4838624 A v u _59934) (@lem0)). Qed.
Lemma lem4838626 {A : Type'} (_59934 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term519 A v u _59934.
Proof. exact (EQ_MP (@lem4838625 A v u _59934) (@lem4838181 A _59934 u x' v h1)). Qed.
Lemma lem4838628 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4838629 {A : Type'} (u : type686 A) (v : type686 A) (_59934 : A -> Prop) : (term519 A v u _59934) = (term522 A u v _59934).
Proof. exact (@lem4838628 (term374 A u _59934) (@I ((A -> Prop) -> Prop) v _59934)). Qed.
Lemma lem4838631 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4838632 {A : Type'} (u : type686 A) (_59934 : A -> Prop) : (term523 A u _59934) = (u _59934).
Proof. exact (@lem4838631 (u _59934)). Qed.
Lemma lem4838633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4838634 {A : Type'} (u : type686 A) (_59934 : A -> Prop) : (term524 A u _59934) = (term215 A u _59934).
Proof. exact (MK_COMB (@lem4838633) (@lem4838632 A u _59934)). Qed.
Lemma lem4838635 {A : Type'} (v : type686 A) (_59934 : A -> Prop) : (@I ((A -> Prop) -> Prop) v _59934) = (@I ((A -> Prop) -> Prop) v _59934).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) v _59934)). Qed.
Lemma lem4838636 {A : Type'} (u : type686 A) (v : type686 A) (_59934 : A -> Prop) : (term522 A u v _59934) = (term525 A u v _59934).
Proof. exact (MK_COMB (@lem4838634 A u _59934) (@lem4838635 A v _59934)). Qed.
Lemma lem4838637 {A : Type'} (u : type686 A) (v : type686 A) (_59934 : A -> Prop) : (term519 A v u _59934) = (term525 A u v _59934).
Proof. exact (TRANS (@lem4838629 A u v _59934) (@lem4838636 A u v _59934)). Qed.
Lemma lem4838640 {A : Type'} (_59934 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v _59934.
Proof. exact (EQ_MP (@lem4838637 A u v _59934) (@lem4838626 A _59934 u x' v h1)). Qed.
Lemma lem4838641 {A : Type'} (_59934 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v _59934.
Proof. exact (@lem4838640 A _59934 u x' v h1). Qed.
Lemma lem4838642 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v x.
Proof. exact (@lem4838641 A x u x' v h1). Qed.
Lemma lem4838645 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : @I ((A -> Prop) -> Prop) v x.
Proof. exact (@lem4838642 A x u x' v h2 (@lem4838597 A u v x h1)). Qed.
Lemma lem4838646 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : term410 A v x.
Proof. exact (fun h0 : term375 A v x => @lem4838645 A x u x' v h1 h2). Qed.
Lemma lem4838648 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838649 {A : Type'} (v : type686 A) (x : A -> Prop) : (term410 A v x) = (@I ((A -> Prop) -> Prop) v x).
Proof. exact (@lem4838648 (@I ((A -> Prop) -> Prop) v x)). Qed.
Lemma lem4838650 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : @I ((A -> Prop) -> Prop) v x.
Proof. exact (EQ_MP (@lem4838649 A v x) (@lem4838646 A x u x' v h1 h2)). Qed.
Lemma lem4838653 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4838655 {A : Type'} (v : type686 A) (x : A -> Prop) : (term375 A v x) = (term419 A v x).
Proof. exact (@lem4838653 (@I ((A -> Prop) -> Prop) v x)). Qed.
Lemma lem4838658 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term419 A v x.
Proof. exact (EQ_MP (@lem4838655 A v x) (@lem4838175 A u v x h1)). Qed.
Lemma lem4838661 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : False.
Proof. exact (@lem4838658 A u v x h1 (@lem4838650 A x u x' v h1 h2)). Qed.
Lemma lem4838662 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : term184.
Proof. exact (fun h0 : ~ False => @lem4838661 A x u x' v h1 h2). Qed.
Lemma lem4838664 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838665 : term184 = False.
Proof. exact (@lem4838664 False). Qed.
Lemma lem4838666 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4838665) (@lem4838662 A x u x' v h1 h2)). Qed.
Lemma lem4838724 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : @pairwise (A -> Prop) (@DISJOINT A) v.
Proof. exact (proj2 (@lem4837835 A u x' v h1)). Qed.
Lemma lem4838725 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term516 A v.
Proof. exact (fun h0 : term487 A v => @lem4838724 A u x' v h1). Qed.
Lemma lem4838727 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838728 {A : Type'} (v : type686 A) : (term516 A v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (@lem4838727 (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4838729 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : @pairwise (A -> Prop) (@DISJOINT A) v.
Proof. exact (EQ_MP (@lem4838728 A v) (@lem4838725 A u x' v h1)). Qed.
Lemma lem4838732 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4838734 {A : Type'} (v : type686 A) : (term487 A v) = (term517 A v).
Proof. exact (@lem4838732 (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4838737 {A : Type'} (v : type686 A) (h1 : term487 A v) : term517 A v.
Proof. exact (EQ_MP (@lem4838734 A v) (@lem4838330 A v h1)). Qed.
Lemma lem4838740 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (@lem4838737 A v h1 (@lem4838729 A u x' v h2)). Qed.
Lemma lem4838741 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : term184.
Proof. exact (fun h0 : ~ False => @lem4838740 A u x' v h1 h2). Qed.
Lemma lem4838743 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838744 : term184 = False.
Proof. exact (@lem4838743 False). Qed.
Lemma lem4838745 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4838744) (@lem4838741 A u x' v h1 h2)). Qed.
Lemma lem4838803 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : u x.
Proof. exact (proj1 (@lem4837851 A u v x h1)). Qed.
Lemma lem4838804 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term518 A u x.
Proof. exact (fun h0 : term374 A u x => @lem4838803 A u v x h1). Qed.
Lemma lem4838806 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838807 {A : Type'} (u : type686 A) (x : A -> Prop) : (term518 A u x) = (u x).
Proof. exact (@lem4838806 (u x)). Qed.
Lemma lem4838808 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : u x.
Proof. exact (EQ_MP (@lem4838807 A u x) (@lem4838804 A u v x h1)). Qed.
Lemma lem4838814 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4838815 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : (term515 A u v _59936) = (term519 A v u _59936).
Proof. exact (@lem4838814 (@I ((A -> Prop) -> Prop) v _59936) (term374 A u _59936)). Qed.
Lemma lem4838821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4838822 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : (term520 A u v _59936) = (term521 A v u _59936).
Proof. exact (MK_COMB (@lem4838821) (@lem4838815 A v u _59936)). Qed.
Lemma lem4838828 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : (term519 A v u _59936) = (term519 A v u _59936).
Proof. exact (eq_refl (term519 A v u _59936)). Qed.
Lemma lem4838829 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : ((term515 A u v _59936) = (term519 A v u _59936)) = ((term519 A v u _59936) = (term519 A v u _59936)).
Proof. exact (MK_COMB (@lem4838822 A v u _59936) (@lem4838828 A v u _59936)). Qed.
Lemma lem4838831 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4838832 (x : Prop) : (x = x) = True.
Proof. exact (@lem4838831 Prop x). Qed.
Lemma lem4838833 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : ((term519 A v u _59936) = (term519 A v u _59936)) = True.
Proof. exact (@lem4838832 (term519 A v u _59936)). Qed.
Lemma lem4838834 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : ((term515 A u v _59936) = (term519 A v u _59936)) = True.
Proof. exact (TRANS (@lem4838829 A v u _59936) (@lem4838833 A v u _59936)). Qed.
Lemma lem4838835 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : True = ((term515 A u v _59936) = (term519 A v u _59936)).
Proof. exact (SYM (@lem4838834 A v u _59936)). Qed.
Lemma lem4838836 {A : Type'} (v : type686 A) (u : type686 A) (_59936 : A -> Prop) : (term515 A u v _59936) = (term519 A v u _59936).
Proof. exact (EQ_MP (@lem4838835 A v u _59936) (@lem0)). Qed.
Lemma lem4838837 {A : Type'} (_59936 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term519 A v u _59936.
Proof. exact (EQ_MP (@lem4838836 A v u _59936) (@lem4838441 A _59936 u x' v h1)). Qed.
Lemma lem4838839 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4838840 {A : Type'} (u : type686 A) (v : type686 A) (_59936 : A -> Prop) : (term519 A v u _59936) = (term522 A u v _59936).
Proof. exact (@lem4838839 (term374 A u _59936) (@I ((A -> Prop) -> Prop) v _59936)). Qed.
Lemma lem4838842 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4838843 {A : Type'} (u : type686 A) (_59936 : A -> Prop) : (term523 A u _59936) = (u _59936).
Proof. exact (@lem4838842 (u _59936)). Qed.
Lemma lem4838844 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4838845 {A : Type'} (u : type686 A) (_59936 : A -> Prop) : (term524 A u _59936) = (term215 A u _59936).
Proof. exact (MK_COMB (@lem4838844) (@lem4838843 A u _59936)). Qed.
Lemma lem4838846 {A : Type'} (v : type686 A) (_59936 : A -> Prop) : (@I ((A -> Prop) -> Prop) v _59936) = (@I ((A -> Prop) -> Prop) v _59936).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) v _59936)). Qed.
Lemma lem4838847 {A : Type'} (u : type686 A) (v : type686 A) (_59936 : A -> Prop) : (term522 A u v _59936) = (term525 A u v _59936).
Proof. exact (MK_COMB (@lem4838845 A u _59936) (@lem4838846 A v _59936)). Qed.
Lemma lem4838848 {A : Type'} (u : type686 A) (v : type686 A) (_59936 : A -> Prop) : (term519 A v u _59936) = (term525 A u v _59936).
Proof. exact (TRANS (@lem4838840 A u v _59936) (@lem4838847 A u v _59936)). Qed.
Lemma lem4838851 {A : Type'} (_59936 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v _59936.
Proof. exact (EQ_MP (@lem4838848 A u v _59936) (@lem4838837 A _59936 u x' v h1)). Qed.
Lemma lem4838852 {A : Type'} (_59936 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v _59936.
Proof. exact (@lem4838851 A _59936 u x' v h1). Qed.
Lemma lem4838853 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v x.
Proof. exact (@lem4838852 A x u x' v h1). Qed.
Lemma lem4838856 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : @I ((A -> Prop) -> Prop) v x.
Proof. exact (@lem4838853 A x u x' v h2 (@lem4838808 A u v x h1)). Qed.
Lemma lem4838857 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : term410 A v x.
Proof. exact (fun h0 : term375 A v x => @lem4838856 A x u x' v h1 h2). Qed.
Lemma lem4838859 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838860 {A : Type'} (v : type686 A) (x : A -> Prop) : (term410 A v x) = (@I ((A -> Prop) -> Prop) v x).
Proof. exact (@lem4838859 (@I ((A -> Prop) -> Prop) v x)). Qed.
Lemma lem4838861 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : @I ((A -> Prop) -> Prop) v x.
Proof. exact (EQ_MP (@lem4838860 A v x) (@lem4838857 A x u x' v h1 h2)). Qed.
Lemma lem4838864 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4838866 {A : Type'} (v : type686 A) (x : A -> Prop) : (term375 A v x) = (term419 A v x).
Proof. exact (@lem4838864 (@I ((A -> Prop) -> Prop) v x)). Qed.
Lemma lem4838869 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term419 A v x.
Proof. exact (EQ_MP (@lem4838866 A v x) (@lem4838427 A u v x h1)). Qed.
Lemma lem4838872 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : False.
Proof. exact (@lem4838869 A u v x h1 (@lem4838861 A x u x' v h1 h2)). Qed.
Lemma lem4838873 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : term184.
Proof. exact (fun h0 : ~ False => @lem4838872 A x u x' v h1 h2). Qed.
Lemma lem4838875 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838876 : term184 = False.
Proof. exact (@lem4838875 False). Qed.
Lemma lem4838935 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : @pairwise (A -> Prop) (@DISJOINT A) v.
Proof. exact (proj2 (@lem4837835 A u x' v h1)). Qed.
Lemma lem4838936 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term516 A v.
Proof. exact (fun h0 : term487 A v => @lem4838935 A u x' v h1). Qed.
Lemma lem4838938 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838939 {A : Type'} (v : type686 A) : (term516 A v) = (@pairwise (A -> Prop) (@DISJOINT A) v).
Proof. exact (@lem4838938 (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4838940 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : @pairwise (A -> Prop) (@DISJOINT A) v.
Proof. exact (EQ_MP (@lem4838939 A v) (@lem4838936 A u x' v h1)). Qed.
Lemma lem4838943 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4838945 {A : Type'} (v : type686 A) : (term487 A v) = (term517 A v).
Proof. exact (@lem4838943 (@pairwise (A -> Prop) (@DISJOINT A) v)). Qed.
Lemma lem4838948 {A : Type'} (v : type686 A) (h1 : term487 A v) : term517 A v.
Proof. exact (EQ_MP (@lem4838945 A v) (@lem4838239 A v h1)). Qed.
Lemma lem4838951 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (@lem4838948 A v h1 (@lem4838940 A u x' v h2)). Qed.
Lemma lem4838952 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : term184.
Proof. exact (fun h0 : ~ False => @lem4838951 A u x' v h1 h2). Qed.
Lemma lem4838954 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4838955 : term184 = False.
Proof. exact (@lem4838954 False). Qed.
Lemma lem4838956 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4838955) (@lem4838952 A u x' v h1 h2)). Qed.
Lemma lem4839014 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : u x.
Proof. exact (proj1 (@lem4837859 A u v x h1)). Qed.
Lemma lem4839015 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term518 A u x.
Proof. exact (fun h0 : term374 A u x => @lem4839014 A u v x h1). Qed.
Lemma lem4839017 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4839018 {A : Type'} (u : type686 A) (x : A -> Prop) : (term518 A u x) = (u x).
Proof. exact (@lem4839017 (u x)). Qed.
Lemma lem4839019 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : u x.
Proof. exact (EQ_MP (@lem4839018 A u x) (@lem4839015 A u v x h1)). Qed.
Lemma lem4839025 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4839026 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : (term515 A u v _59938) = (term519 A v u _59938).
Proof. exact (@lem4839025 (@I ((A -> Prop) -> Prop) v _59938) (term374 A u _59938)). Qed.
Lemma lem4839032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4839033 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : (term520 A u v _59938) = (term521 A v u _59938).
Proof. exact (MK_COMB (@lem4839032) (@lem4839026 A v u _59938)). Qed.
Lemma lem4839039 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : (term519 A v u _59938) = (term519 A v u _59938).
Proof. exact (eq_refl (term519 A v u _59938)). Qed.
Lemma lem4839040 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : ((term515 A u v _59938) = (term519 A v u _59938)) = ((term519 A v u _59938) = (term519 A v u _59938)).
Proof. exact (MK_COMB (@lem4839033 A v u _59938) (@lem4839039 A v u _59938)). Qed.
Lemma lem4839042 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4839043 (x : Prop) : (x = x) = True.
Proof. exact (@lem4839042 Prop x). Qed.
Lemma lem4839044 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : ((term519 A v u _59938) = (term519 A v u _59938)) = True.
Proof. exact (@lem4839043 (term519 A v u _59938)). Qed.
Lemma lem4839045 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : ((term515 A u v _59938) = (term519 A v u _59938)) = True.
Proof. exact (TRANS (@lem4839040 A v u _59938) (@lem4839044 A v u _59938)). Qed.
Lemma lem4839046 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : True = ((term515 A u v _59938) = (term519 A v u _59938)).
Proof. exact (SYM (@lem4839045 A v u _59938)). Qed.
Lemma lem4839047 {A : Type'} (v : type686 A) (u : type686 A) (_59938 : A -> Prop) : (term515 A u v _59938) = (term519 A v u _59938).
Proof. exact (EQ_MP (@lem4839046 A v u _59938) (@lem0)). Qed.
Lemma lem4839048 {A : Type'} (_59938 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term519 A v u _59938.
Proof. exact (EQ_MP (@lem4839047 A v u _59938) (@lem4838269 A _59938 u x' v h1)). Qed.
Lemma lem4839050 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4839051 {A : Type'} (u : type686 A) (v : type686 A) (_59938 : A -> Prop) : (term519 A v u _59938) = (term522 A u v _59938).
Proof. exact (@lem4839050 (term374 A u _59938) (@I ((A -> Prop) -> Prop) v _59938)). Qed.
Lemma lem4839053 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4839054 {A : Type'} (u : type686 A) (_59938 : A -> Prop) : (term523 A u _59938) = (u _59938).
Proof. exact (@lem4839053 (u _59938)). Qed.
Lemma lem4839055 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4839056 {A : Type'} (u : type686 A) (_59938 : A -> Prop) : (term524 A u _59938) = (term215 A u _59938).
Proof. exact (MK_COMB (@lem4839055) (@lem4839054 A u _59938)). Qed.
Lemma lem4839057 {A : Type'} (v : type686 A) (_59938 : A -> Prop) : (@I ((A -> Prop) -> Prop) v _59938) = (@I ((A -> Prop) -> Prop) v _59938).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) v _59938)). Qed.
Lemma lem4839058 {A : Type'} (u : type686 A) (v : type686 A) (_59938 : A -> Prop) : (term522 A u v _59938) = (term525 A u v _59938).
Proof. exact (MK_COMB (@lem4839056 A u _59938) (@lem4839057 A v _59938)). Qed.
Lemma lem4839059 {A : Type'} (u : type686 A) (v : type686 A) (_59938 : A -> Prop) : (term519 A v u _59938) = (term525 A u v _59938).
Proof. exact (TRANS (@lem4839051 A u v _59938) (@lem4839058 A u v _59938)). Qed.
Lemma lem4839062 {A : Type'} (_59938 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v _59938.
Proof. exact (EQ_MP (@lem4839059 A u v _59938) (@lem4839048 A _59938 u x' v h1)). Qed.
Lemma lem4839063 {A : Type'} (_59938 : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v _59938.
Proof. exact (@lem4839062 A _59938 u x' v h1). Qed.
Lemma lem4839064 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term359 A u x' v) : term525 A u v x.
Proof. exact (@lem4839063 A x u x' v h1). Qed.
Lemma lem4839067 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : @I ((A -> Prop) -> Prop) v x.
Proof. exact (@lem4839064 A x u x' v h2 (@lem4839019 A u v x h1)). Qed.
Lemma lem4839068 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : term410 A v x.
Proof. exact (fun h0 : term375 A v x => @lem4839067 A x u x' v h1 h2). Qed.
Lemma lem4839070 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4839071 {A : Type'} (v : type686 A) (x : A -> Prop) : (term410 A v x) = (@I ((A -> Prop) -> Prop) v x).
Proof. exact (@lem4839070 (@I ((A -> Prop) -> Prop) v x)). Qed.
Lemma lem4839072 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : @I ((A -> Prop) -> Prop) v x.
Proof. exact (EQ_MP (@lem4839071 A v x) (@lem4839068 A x u x' v h1 h2)). Qed.
Lemma lem4839075 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4839077 {A : Type'} (v : type686 A) (x : A -> Prop) : (term375 A v x) = (term419 A v x).
Proof. exact (@lem4839075 (@I ((A -> Prop) -> Prop) v x)). Qed.
Lemma lem4839080 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term498 A u v x) : term419 A v x.
Proof. exact (EQ_MP (@lem4839077 A v x) (@lem4838263 A u v x h1)). Qed.
Lemma lem4839083 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : False.
Proof. exact (@lem4839080 A u v x h1 (@lem4839072 A x u x' v h1 h2)). Qed.
Lemma lem4839084 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : term184.
Proof. exact (fun h0 : ~ False => @lem4839083 A x u x' v h1 h2). Qed.
Lemma lem4839086 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4839087 : term184 = False.
Proof. exact (@lem4839086 False). Qed.
Lemma lem4839088 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839087) (@lem4839084 A x u x' v h1 h2)). Qed.
Lemma lem4839089 {A : Type'} (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term498 A u v x) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4838876) (@lem4838873 A x u x' v h1 h2)). Qed.
Lemma lem4839090 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4838745 A u x' v h1 h2) (fun h3 : False => @lem4838330 A v h1)). Qed.
Lemma lem4839092 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839090 A u x' v h1 h2) (@lem4838330 A v h1)). Qed.
Lemma lem4839093 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4838956 A u x' v h1 h2) (fun h3 : False => @lem4838239 A v h1)). Qed.
Lemma lem4839094 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839093 A u x' v h1 h2) (@lem4838239 A v h1)). Qed.
Lemma lem4839095 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4839092 A u x' v h1 h2) (fun h3 : False => @lem4838195 A v h1)). Qed.
Lemma lem4839096 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839095 A u x' v h1 h2) (@lem4838195 A v h1)). Qed.
Lemma lem4839097 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4838534 A u x' v h1 h2) (fun h3 : False => @lem4838153 A v h1)). Qed.
Lemma lem4839098 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839097 A u x' v h1 h2) (@lem4838153 A v h1)). Qed.
Lemma lem4839099 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4839094 A u x' v h1 h2) (fun h3 : False => @lem4838068 A v h1)). Qed.
Lemma lem4839100 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839099 A u x' v h1 h2) (@lem4838068 A v h1)). Qed.
Lemma lem4839101 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4839096 A u x' v h1 h2) (fun h3 : False => @lem4837982 A v h1)). Qed.
Lemma lem4839102 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839101 A u x' v h1 h2) (@lem4837982 A v h1)). Qed.
Lemma lem4839103 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4839098 A u x' v h1 h2) (fun h3 : False => @lem4837900 A v h1)). Qed.
Lemma lem4839104 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839103 A u x' v h1 h2) (@lem4837900 A v h1)). Qed.
Lemma lem4839105 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4839100 A u x' v h1 h2) (fun h3 : False => @lem4838068 A v h1)). Qed.
Lemma lem4839106 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839105 A u x' v h1 h2) (@lem4838068 A v h1)). Qed.
Lemma lem4839107 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4839102 A u x' v h1 h2) (fun h3 : False => @lem4837982 A v h1)). Qed.
Lemma lem4839108 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839107 A u x' v h1 h2) (@lem4837982 A v h1)). Qed.
Lemma lem4839109 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : (term487 A v) = False.
Proof. exact (prop_ext (fun h3 : term487 A v => @lem4839104 A u x' v h1 h2) (fun h3 : False => @lem4837900 A v h1)). Qed.
Lemma lem4839110 {A : Type'} (u : type686 A) (x' : A -> Prop) (v : type686 A) (h1 : term487 A v) (h2 : term359 A u x' v) : False.
Proof. exact (EQ_MP (@lem4839109 A u x' v h1 h2) (@lem4837900 A v h1)). Qed.
Lemma lem4839111 {A : Type'} (x' : A -> Prop) (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term359 A u x' v) (h2 : term494 A u v x) : False.
Proof. exact (or_elim (@lem4837741 A u v x h2) (fun h0 : term487 A v => @lem4839106 A u x' v h0 h1) (fun h0 : term498 A u v x => @lem4839088 A x u x' v h0 h1)). Qed.
Lemma lem4839112 {A : Type'} (x' : A -> Prop) (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term359 A u x' v) (h2 : term494 A u v x) : False.
Proof. exact (or_elim (@lem4837741 A u v x h2) (fun h0 : term487 A v => @lem4839108 A u x' v h0 h1) (fun h0 : term498 A u v x => @lem4839089 A x u x' v h0 h1)). Qed.
Lemma lem4839113 {A : Type'} (x' : A -> Prop) (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term359 A u x' v) (h2 : term494 A u v x) : False.
Proof. exact (or_elim (@lem4837741 A u v x h2) (fun h0 : term487 A v => @lem4839110 A u x' v h0 h1) (fun h0 : term498 A u v x => @lem4838666 A x u x' v h0 h1)). Qed.
Lemma lem4839114 {A : Type'} (x' : A -> Prop) (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term501 A u v x') (h2 : term359 A u x' v) (h3 : term494 A u v x) : False.
Proof. exact (or_elim (@lem4837842 A u v x' h1) (fun h0 : term375 A v x' => @lem4839113 A x' u v x h2 h3) (fun h0 : x' = (@EMPTY A) => @lem4839112 A x' u v x h2 h3)). Qed.
Lemma lem4839115 {A : Type'} (x' : A -> Prop) (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term359 A u x' v) (h2 : term494 A u v x) : False.
Proof. exact (or_elim (@lem4837838 A u x' v h1) (fun h0 : term501 A u v x' => @lem4839114 A x' u v x h0 h1 h2) (fun h0 : term500 A u v x' => @lem4839111 A x' u v x h1 h2)). Qed.
Lemma lem4839116 {A : Type'} (u : type686 A) (v : type686 A) (x : A -> Prop) (h1 : term238 A u v) (h2 : term494 A u v x) : False.
Proof. exact (ex_elim (@lem4837637 A u v h1) (fun x' : A -> Prop => fun h0 : term361 A u v x' => @lem4839115 A x' u v x h0 h2)). Qed.
Lemma lem4839117 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term468 A u v) (h2 : term238 A u v) : False.
Proof. exact (ex_elim (@lem4837712 A u v h1) (fun x : A -> Prop => fun h0 : term496 A u v x => @lem4839116 A u v x h2 h0)). Qed.
Lemma lem4839118 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term468 A u v) (h2 : term238 A u v) : (term468 A u v) = False.
Proof. exact (prop_ext (fun h3 : term468 A u v => @lem4839117 A u v h1 h2) (fun h3 : False => @lem4837340 A u v h1)). Qed.
Lemma lem4839119 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term468 A u v) (h2 : term238 A u v) : False.
Proof. exact (EQ_MP (@lem4839118 A u v h1 h2) (@lem4837340 A u v h1)). Qed.
Lemma lem4839120 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term238 A u v) : term467 A u v.
Proof. exact (fun h0 : term468 A u v => @lem4839119 A u v h0 h1). Qed.
Lemma lem4839121 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term238 A u v) : term451 A u v.
Proof. exact (EQ_MP (@lem4837339 A u v) (@lem4839120 A u v h1)). Qed.
Lemma lem4839122 {A : Type'} (u : type686 A) (v : type686 A) : term452 A u v.
Proof. exact (fun h0 : term238 A u v => @lem4839121 A u v h0). Qed.
Lemma lem4839127 {A : Type'} (v : type686 A) : term462 A v.
Proof. exact (fun u : type686 A => @lem4839122 A u v). Qed.
Lemma lem4839132 {A : Type'} : term466 A.
Proof. exact (fun v : type686 A => @lem4839127 A v). Qed.
Lemma lem4839133 {A : Type'} : term465 A.
Proof. exact (EQ_MP (@lem4837334 A) (@lem4839132 A)). Qed.
Lemma lem4839134 {A : Type'} (v : type686 A) : term526 A v.
Proof. exact (@lem4839133 A v). Qed.
Lemma lem4839135 {A : Type'} (v : type686 A) : (term526 A v) = (term461 A v).
Proof. exact (eq_refl (term526 A v)). Qed.
Lemma lem4839136 {A : Type'} (v : type686 A) : term461 A v.
Proof. exact (EQ_MP (@lem4839135 A v) (@lem4839134 A v)). Qed.
Lemma lem4839137 {A : Type'} (v : type686 A) (u : type686 A) : term527 A v u.
Proof. exact (@lem4839136 A v u). Qed.
Lemma lem4839138 {A : Type'} (u : type686 A) (v : type686 A) : (term527 A v u) = (term453 A u v).
Proof. exact (eq_refl (term527 A v u)). Qed.
Lemma lem4839139 {A : Type'} (u : type686 A) (v : type686 A) : term453 A u v.
Proof. exact (EQ_MP (@lem4839138 A u v) (@lem4839137 A v u)). Qed.
Lemma lem4839141 {A : Type'} (u : type686 A) (v : type686 A) : term453 A u v.
Proof. exact (@lem4837165 A u v (@lem4839139 A u v)). Qed.
Lemma lem4839142 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term454 A u v) : False.
Proof. exact (@lem4839141 A u v (@lem4837149 A u v h1)). Qed.
Lemma lem4839143 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term454 A u v) : (term454 A u v) = False.
Proof. exact (prop_ext (fun h2 : term454 A u v => @lem4839142 A u v h1) (fun h2 : False => @lem4837149 A u v h1)). Qed.
Lemma lem4839144 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term454 A u v) : False.
Proof. exact (EQ_MP (@lem4839143 A u v h1) (@lem4837149 A u v h1)). Qed.
Lemma lem4839145 {A : Type'} (u : type686 A) (v : type686 A) : term453 A u v.
Proof. exact (fun h0 : term454 A u v => @lem4839144 A u v h0). Qed.
Lemma lem4839146 {A : Type'} (u : type686 A) (v : type686 A) : term452 A u v.
Proof. exact (EQ_MP (@lem4837148 A u v) (@lem4839145 A u v)). Qed.
Lemma lem4839147 {A : Type'} (u : type686 A) (v : type686 A) : term445 A u v.
Proof. exact (EQ_MP (@lem4837144 A u v) (@lem4839146 A u v)). Qed.
Lemma lem4839148 {A : Type'} (u : type686 A) (v : type686 A) : term444 A u v.
Proof. exact (EQ_MP (@lem4837005 A u v) (@lem4839147 A u v)). Qed.
Lemma lem4839149 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term438 A u v.
Proof. exact (@lem4839148 A u v (@lem4836935 A u v h1 h2)). Qed.
Lemma lem4839150 {A : Type'} (v : type686 A) (u : type686 A) (h1 : (term439 A v u) = (term440 A v u)) : (term439 A v u) = (term440 A v u).
Proof. exact (h1). Qed.
Lemma lem4839151 {A : Type'} : (term528 A) = (term528 A).
Proof. exact (eq_refl (term528 A)). Qed.
Lemma lem4839152 {A : Type'} (v : type686 A) (u : type686 A) (h1 : (term439 A v u) = (term440 A v u)) : (term529 A v u) = (term530 A v u).
Proof. exact (MK_COMB (@lem4839151 A) (@lem4839150 A v u h1)). Qed.
Lemma lem4839153 {A : Type'} (v : type686 A) (u : type686 A) : (term530 A v u) = (term531 A v u).
Proof. exact (eq_refl (term530 A v u)). Qed.
Lemma lem4839154 {A : Type'} (v : type686 A) (u : type686 A) : (term532 A v u) = (term532 A v u).
Proof. exact (eq_refl (term532 A v u)). Qed.
Lemma lem4839155 {A : Type'} (v : type686 A) (u : type686 A) : ((term529 A v u) = (term530 A v u)) = ((term529 A v u) = (term531 A v u)).
Proof. exact (MK_COMB (@lem4839154 A v u) (@lem4839153 A v u)). Qed.
Lemma lem4839156 {A : Type'} (v : type686 A) (u : type686 A) : (term529 A v u) = (term441 A v u).
Proof. exact (eq_refl (term529 A v u)). Qed.
Lemma lem4839157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4839158 {A : Type'} (v : type686 A) (u : type686 A) : (term532 A v u) = (term533 A v u).
Proof. exact (MK_COMB (@lem4839157) (@lem4839156 A v u)). Qed.
Lemma lem4839159 {A : Type'} (v : type686 A) (u : type686 A) : (term531 A v u) = (term531 A v u).
Proof. exact (eq_refl (term531 A v u)). Qed.
Lemma lem4839160 {A : Type'} (v : type686 A) (u : type686 A) : ((term529 A v u) = (term531 A v u)) = ((term441 A v u) = (term531 A v u)).
Proof. exact (MK_COMB (@lem4839158 A v u) (@lem4839159 A v u)). Qed.
Lemma lem4839161 {A : Type'} (v : type686 A) (u : type686 A) : ((term529 A v u) = (term530 A v u)) = ((term441 A v u) = (term531 A v u)).
Proof. exact (TRANS (@lem4839155 A v u) (@lem4839160 A v u)). Qed.
Lemma lem4839162 {A : Type'} (v : type686 A) (u : type686 A) (h1 : (term439 A v u) = (term440 A v u)) : (term441 A v u) = (term531 A v u).
Proof. exact (EQ_MP (@lem4839161 A v u) (@lem4839152 A v u h1)). Qed.
Lemma lem4839163 {A : Type'} (v : type686 A) (u : type686 A) (h1 : (term439 A v u) = (term440 A v u)) : (term531 A v u) = (term441 A v u).
Proof. exact (SYM (@lem4839162 A v u h1)). Qed.
Lemma lem4839165 {_86951 : Type'} (s : type686 _86951) : ((@UNIONS _86951 s) = (@EMPTY _86951)) = (term26 _86951 s).
Proof. exact (EQ_MP (@lem4833749 _86951 s) (@lem4833748 _86951 s)). Qed.
Lemma lem4839166 {A : Type'} (s : type686 A) : ((@UNIONS A s) = (@EMPTY A)) = (term26 A s).
Proof. exact (@lem4839165 A s). Qed.
Lemma lem4839167 {A : Type'} (v : type686 A) (u : type686 A) : ((term440 A v u) = (@EMPTY A)) = (term534 A v u).
Proof. exact (@lem4839166 A (@DIFF (A -> Prop) v u)). Qed.
Lemma lem4839176 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4839177 {A : Type'} (v : type686 A) (u : type686 A) : (term531 A v u) = (term535 A v u).
Proof. exact (MK_COMB (@lem4839176) (@lem4839167 A v u)). Qed.
Lemma lem4839178 {A : Type'} (v : type686 A) (u : type686 A) : (term535 A v u) = (term531 A v u).
Proof. exact (SYM (@lem4839177 A v u)). Qed.
Lemma lem4839180 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@PSUBSET A s t) = (term24 A t s).
Proof. exact (EQ_MP (@lem4833746 A t s) (@lem4833745 A s t)). Qed.
Lemma lem4839181 {A : Type'} (t : type686 A) (s : type686 A) : (@PSUBSET (A -> Prop) s t) = (term536 A t s).
Proof. exact (@lem4839180 (A -> Prop) t s). Qed.
Lemma lem4839182 {A : Type'} (v : type686 A) (u : type686 A) : (term190 A u v) = (term537 A v u).
Proof. exact (@lem4839181 A (@DELETE (A -> Prop) v (@EMPTY A)) u). Qed.
Lemma lem4839183 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) : term537 A v u.
Proof. exact (EQ_MP (@lem4839182 A v u) (@lem4834874 A u v h1)). Qed.
Lemma lem4839184 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) : term538 A v u.
Proof. exact (proj2 (@lem4839183 A u v h1)). Qed.
Lemma lem4839194 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term19 A x s y) = (term20 A s x y).
Proof. exact (EQ_MP (@lem4833740 A s x y) (@lem4833739 A s x y)). Qed.
Lemma lem4839195 {A : Type'} (s : type686 A) (x : A -> Prop) (y : A -> Prop) : (term216 A x s y) = (term217 A s x y).
Proof. exact (@lem4839194 (A -> Prop) s x y). Qed.
Lemma lem4839196 {A : Type'} (v : type686 A) (a : A -> Prop) : (term218 A a v) = (term219 A v a).
Proof. exact (@lem4839195 A v a (@EMPTY A)). Qed.
Lemma lem4839201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4839202 {A : Type'} (v : type686 A) (a : A -> Prop) : (term539 A a v) = (term540 A v a).
Proof. exact (MK_COMB (@lem4839201) (@lem4839196 A v a)). Qed.
Lemma lem4839203 {A : Type'} (a : A -> Prop) (u : type686 A) : (term541 A a u) = (term541 A a u).
Proof. exact (eq_refl (term541 A a u)). Qed.
Lemma lem4839204 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) : (term542 A v a u) = (term543 A v a u).
Proof. exact (MK_COMB (@lem4839202 A v a) (@lem4839203 A a u)). Qed.
Lemma lem4839207 {A : Type'} (v : type686 A) (u : type686 A) : (term544 A v u) = (term545 A v u).
Proof. exact (fun_ext (fun a : A -> Prop => @lem4839204 A v a u)). Qed.
Lemma lem4839208 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4839209 {A : Type'} (v : type686 A) (u : type686 A) : (term538 A v u) = (term546 A v u).
Proof. exact (MK_COMB (@lem4839208 A) (@lem4839207 A v u)). Qed.
Lemma lem4839214 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4839215 {A : Type'} (v : type686 A) (u : type686 A) : (term547 A v u) = (term548 A v u).
Proof. exact (MK_COMB (@lem4839214) (@lem4839209 A v u)). Qed.
Lemma lem4839223 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem4833731 A s x t) (@lem4833730 A s t x)). Qed.
Lemma lem4839224 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term549 A x s t) = (term550 A s x t).
Proof. exact (@lem4839223 (A -> Prop) s x t). Qed.
Lemma lem4839225 {A : Type'} (v : type686 A) (t : A -> Prop) (u : type686 A) : (term549 A t v u) = (term550 A v t u).
Proof. exact (@lem4839224 A v t u). Qed.
Lemma lem4839228 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4839229 {A : Type'} (v : type686 A) (t : A -> Prop) (u : type686 A) : (term551 A t v u) = (term552 A v t u).
Proof. exact (MK_COMB (@lem4839228) (@lem4839225 A v t u)). Qed.
Lemma lem4839232 {A : Type'} (t : A -> Prop) : (t = (@EMPTY A)) = (t = (@EMPTY A)).
Proof. exact (eq_refl (t = (@EMPTY A))). Qed.
Lemma lem4839233 {A : Type'} (v : type686 A) (u : type686 A) (t : A -> Prop) : (term553 A v u t) = (term554 A v u t).
Proof. exact (MK_COMB (@lem4839229 A v t u) (@lem4839232 A t)). Qed.
Lemma lem4839236 {A : Type'} (v : type686 A) (u : type686 A) : (term555 A v u) = (term556 A v u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4839233 A v u t)). Qed.
Lemma lem4839237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4839238 {A : Type'} (v : type686 A) (u : type686 A) : (term534 A v u) = (term557 A v u).
Proof. exact (MK_COMB (@lem4839237 A) (@lem4839236 A v u)). Qed.
Lemma lem4839243 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4839244 {A : Type'} (v : type686 A) (u : type686 A) : (term535 A v u) = (term558 A v u).
Proof. exact (MK_COMB (@lem4839243) (@lem4839238 A v u)). Qed.
Lemma lem4839245 {A : Type'} (v : type686 A) (u : type686 A) : (term559 A v u) = (term560 A v u).
Proof. exact (MK_COMB (@lem4839215 A v u) (@lem4839244 A v u)). Qed.
Lemma lem4839248 {A : Type'} (v : type686 A) (u : type686 A) : (term560 A v u) = (term559 A v u).
Proof. exact (SYM (@lem4839245 A v u)). Qed.
Lemma lem4839250 (p : Prop) : p = (term78 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4839251 {A : Type'} (v : type686 A) (u : type686 A) : (term560 A v u) = (term561 A v u).
Proof. exact (@lem4839250 (term560 A v u)). Qed.
Lemma lem4839252 {A : Type'} (v : type686 A) (u : type686 A) : (term561 A v u) = (term560 A v u).
Proof. exact (SYM (@lem4839251 A v u)). Qed.
Lemma lem4839253 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term562 A v u) : term562 A v u.
Proof. exact (h1). Qed.
Lemma lem4839256 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term561 A v u) : term561 A v u.
Proof. exact (h1). Qed.
Lemma lem4839257 {A : Type'} (v : type686 A) (u : type686 A) : term563 A v u.
Proof. exact (fun h0 : term561 A v u => @lem4839256 A v u h0). Qed.
Lemma lem4839258 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term563 A v u) : term563 A v u.
Proof. exact (h1). Qed.
Lemma lem4839259 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term561 A v u) : term561 A v u.
Proof. exact (h1). Qed.
Lemma lem4839260 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term561 A v u) (h2 : term563 A v u) : term561 A v u.
Proof. exact (@lem4839258 A v u h2 (@lem4839259 A v u h1)). Qed.
Lemma lem4839261 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term561 A v u) : term564 A v u.
Proof. exact (fun h0 : term563 A v u => @lem4839260 A v u h1 h0). Qed.
Lemma lem4839262 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term563 A v u) : term563 A v u.
Proof. exact (h1). Qed.
Lemma lem4839263 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term561 A v u) (h2 : term563 A v u) : term561 A v u.
Proof. exact (@lem4839261 A v u h1 (@lem4839262 A v u h2)). Qed.
Lemma lem4839264 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term563 A v u) : term563 A v u.
Proof. exact (fun h0 : term561 A v u => @lem4839263 A v u h0 h1). Qed.
Lemma lem4839265 {A : Type'} (v : type686 A) (u : type686 A) : term565 A v u.
Proof. exact (fun h0 : term563 A v u => @lem4839264 A v u h0). Qed.
Lemma lem4839268 {A : Type'} (v : type686 A) (u : type686 A) : term563 A v u.
Proof. exact (@lem4839265 A v u (@lem4839257 A v u)). Qed.
Lemma lem4839269 {A : Type'} (v : type686 A) (u : type686 A) : term563 A v u.
Proof. exact (@lem4839268 A v u). Qed.
Lemma lem4839279 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4839280 {A : Type'} (v : type686 A) (u : type686 A) : (term561 A v u) = (term566 A v u).
Proof. exact (@lem4839279 (term562 A v u)). Qed.
Lemma lem4839282 (t : Prop) : (term85 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4839283 {A : Type'} (v : type686 A) (u : type686 A) : (term566 A v u) = (term560 A v u).
Proof. exact (@lem4839282 (term560 A v u)). Qed.
Lemma lem4839286 {A : Type'} (v : type686 A) (u : type686 A) : (term561 A v u) = (term560 A v u).
Proof. exact (TRANS (@lem4839280 A v u) (@lem4839283 A v u)). Qed.
Lemma lem4839347 {A : Type'} (u : type686 A) : (term567 A u) = (term568 A u).
Proof. exact (fun_ext (fun v : type686 A => @lem4839286 A v u)). Qed.
Lemma lem4839348 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4839349 {A : Type'} (u : type686 A) : (term569 A u) = (term570 A u).
Proof. exact (MK_COMB (@lem4839348 A) (@lem4839347 A u)). Qed.
Lemma lem4839354 {A : Type'} : (term571 A) = (term572 A).
Proof. exact (fun_ext (fun u : type686 A => @lem4839349 A u)). Qed.
Lemma lem4839355 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4839364 {A : Type'} : (term573 A) = (term574 A).
Proof. exact (MK_COMB (@lem4839355 A) (@lem4839354 A)). Qed.
Lemma lem4839375 {A : Type'} (v : type686 A) (u : type686 A) (t : A -> Prop) : (term554 A v u t) = (term554 A v u t).
Proof. exact (eq_refl (term554 A v u t)). Qed.
Lemma lem4839376 {A : Type'} (v : type686 A) (u : type686 A) : (term556 A v u) = (term556 A v u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4839375 A v u t)). Qed.
Lemma lem4839377 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4839378 {A : Type'} (v : type686 A) (u : type686 A) : (term557 A v u) = (term557 A v u).
Proof. exact (MK_COMB (@lem4839377 A) (@lem4839376 A v u)). Qed.
Lemma lem4839379 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4839380 {A : Type'} (v : type686 A) (u : type686 A) : (term558 A v u) = (term558 A v u).
Proof. exact (MK_COMB (@lem4839379) (@lem4839378 A v u)). Qed.
Lemma lem4839393 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) : (term543 A v a u) = (term543 A v a u).
Proof. exact (eq_refl (term543 A v a u)). Qed.
Lemma lem4839394 {A : Type'} (v : type686 A) (u : type686 A) : (term545 A v u) = (term545 A v u).
Proof. exact (fun_ext (fun a : A -> Prop => @lem4839393 A v a u)). Qed.
Lemma lem4839395 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4839396 {A : Type'} (v : type686 A) (u : type686 A) : (term546 A v u) = (term546 A v u).
Proof. exact (MK_COMB (@lem4839395 A) (@lem4839394 A v u)). Qed.
Lemma lem4839397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4839398 {A : Type'} (v : type686 A) (u : type686 A) : (term548 A v u) = (term548 A v u).
Proof. exact (MK_COMB (@lem4839397) (@lem4839396 A v u)). Qed.
Lemma lem4839399 {A : Type'} (v : type686 A) (u : type686 A) : (term560 A v u) = (term560 A v u).
Proof. exact (MK_COMB (@lem4839398 A v u) (@lem4839380 A v u)). Qed.
Lemma lem4839400 {A : Type'} (u : type686 A) : (term568 A u) = (term568 A u).
Proof. exact (fun_ext (fun v : type686 A => @lem4839399 A v u)). Qed.
Lemma lem4839401 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4839402 {A : Type'} (u : type686 A) : (term570 A u) = (term570 A u).
Proof. exact (MK_COMB (@lem4839401 A) (@lem4839400 A u)). Qed.
Lemma lem4839403 {A : Type'} : (term572 A) = (term572 A).
Proof. exact (fun_ext (fun u : type686 A => @lem4839402 A u)). Qed.
Lemma lem4839404 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4839405 {A : Type'} : (term574 A) = (term574 A).
Proof. exact (MK_COMB (@lem4839404 A) (@lem4839403 A)). Qed.
Lemma lem4839442 {A : Type'} : (term573 A) = (term574 A).
Proof. exact (TRANS (@lem4839364 A) (@lem4839405 A)). Qed.
Lemma lem4839443 {A : Type'} : (term574 A) = (term573 A).
Proof. exact (SYM (@lem4839442 A)). Qed.
Lemma lem4839444 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term546 A v u) : term546 A v u.
Proof. exact (h1). Qed.
Lemma lem4839445 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term557 A v u.
Proof. exact (h1). Qed.
Lemma lem4839454 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) : (term543 A v a u) = (term543 A v a u).
Proof. exact (eq_refl (term543 A v a u)). Qed.
Lemma lem4839455 {A : Type'} (v : type686 A) (u : type686 A) : (term545 A v u) = (term545 A v u).
Proof. exact (fun_ext (fun a : A -> Prop => @lem4839454 A v a u)). Qed.
Lemma lem4839456 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4839509 {A : Type'} (v : type686 A) (u : type686 A) : (term546 A v u) = (term546 A v u).
Proof. exact (MK_COMB (@lem4839456 A) (@lem4839455 A v u)). Qed.
Lemma lem4839510 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term546 A v u) : term546 A v u.
Proof. exact (EQ_MP (@lem4839509 A v u) (@lem4839444 A v u h1)). Qed.
Lemma lem4839514 {A : Type'} (t : A -> Prop) (u : type686 A) : (term575 A t u) = (@IN (A -> Prop) t u).
Proof. exact (@lem16933 (@IN (A -> Prop) t u)). Qed.
Lemma lem4839516 {A : Type'} (t : A -> Prop) (v : type686 A) : (term576 A t v) = (term576 A t v).
Proof. exact (eq_refl (term576 A t v)). Qed.
Lemma lem4839517 {A : Type'} (v : type686 A) (t : A -> Prop) (u : type686 A) : (term577 A v t u) = (term578 A v t u).
Proof. exact (MK_COMB (@lem4839516 A t v) (@lem4839514 A t u)). Qed.
Lemma lem4839518 {A : Type'} (v : type686 A) (t : A -> Prop) (u : type686 A) : (term579 A v t u) = (term577 A v t u).
Proof. exact (@lem17045 (@IN (A -> Prop) t v) (term541 A t u)). Qed.
Lemma lem4839519 {A : Type'} (v : type686 A) (t : A -> Prop) (u : type686 A) : (term579 A v t u) = (term578 A v t u).
Proof. exact (TRANS (@lem4839518 A v t u) (@lem4839517 A v t u)). Qed.
Lemma lem4839520 {A : Type'} (t : A -> Prop) : (t = (@EMPTY A)) = (t = (@EMPTY A)).
Proof. exact (eq_refl (t = (@EMPTY A))). Qed.
Lemma lem4839521 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4839522 {A : Type'} (v : type686 A) (t : A -> Prop) (u : type686 A) : (term580 A v t u) = (term581 A v t u).
Proof. exact (MK_COMB (@lem4839521) (@lem4839519 A v t u)). Qed.
Lemma lem4839523 {A : Type'} (v : type686 A) (u : type686 A) (t : A -> Prop) : (term582 A v u t) = (term583 A v u t).
Proof. exact (MK_COMB (@lem4839522 A v t u) (@lem4839520 A t)). Qed.
Lemma lem4839524 {A : Type'} (v : type686 A) (u : type686 A) (t : A -> Prop) : (term554 A v u t) = (term582 A v u t).
Proof. exact (@lem17265 (term550 A v t u) (t = (@EMPTY A))). Qed.
Lemma lem4839525 {A : Type'} (v : type686 A) (u : type686 A) (t : A -> Prop) : (term554 A v u t) = (term583 A v u t).
Proof. exact (TRANS (@lem4839524 A v u t) (@lem4839523 A v u t)). Qed.
Lemma lem4839526 {A : Type'} (v : type686 A) (u : type686 A) : (term556 A v u) = (term584 A v u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4839525 A v u t)). Qed.
Lemma lem4839527 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4839580 {A : Type'} (v : type686 A) (u : type686 A) : (term557 A v u) = (term585 A v u).
Proof. exact (MK_COMB (@lem4839527 A) (@lem4839526 A v u)). Qed.
Lemma lem4839581 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term585 A v u.
Proof. exact (EQ_MP (@lem4839580 A v u) (@lem4839445 A v u h1)). Qed.
Lemma lem4839605 {A : Type'} (v : type686 A) (u : type686 A) (t : A -> Prop) : (term583 A v u t) = (term583 A v u t).
Proof. exact (eq_refl (term583 A v u t)). Qed.
Lemma lem4839606 {A : Type'} (v : type686 A) (u : type686 A) : (term584 A v u) = (term584 A v u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4839605 A v u t)). Qed.
Lemma lem4839607 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4839608 {A : Type'} (v : type686 A) (u : type686 A) : (term585 A v u) = (term585 A v u).
Proof. exact (MK_COMB (@lem4839607 A) (@lem4839606 A v u)). Qed.
Lemma lem4839609 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term585 A v u.
Proof. exact (EQ_MP (@lem4839608 A v u) (@lem4839581 A v u h1)). Qed.
Lemma lem4839635 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term543 A v a u.
Proof. exact (h1). Qed.
Lemma lem4839637 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term219 A v a.
Proof. exact (proj1 (@lem4839635 A v a u h1)). Qed.
Lemma lem4839653 {A : Type'} (v : type686 A) (u : type686 A) (t : A -> Prop) : (term583 A v u t) = (term583 A v u t).
Proof. exact (eq_refl (term583 A v u t)). Qed.
Lemma lem4839654 {A : Type'} (v : type686 A) (u : type686 A) : (term584 A v u) = (term584 A v u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4839653 A v u t)). Qed.
Lemma lem4839655 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4839657 {A : Type'} (v : type686 A) (u : type686 A) : (term585 A v u) = (term585 A v u).
Proof. exact (MK_COMB (@lem4839655 A) (@lem4839654 A v u)). Qed.
Lemma lem4839658 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term585 A v u.
Proof. exact (EQ_MP (@lem4839657 A v u) (@lem4839609 A v u h1)). Qed.
Lemma lem4839671 {A : Type'} (_60027 : A -> Prop) (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term586 A v u _60027.
Proof. exact (@lem4839658 A v u h1 _60027). Qed.
Lemma lem4839672 {A : Type'} (v : type686 A) (u : type686 A) (_60027 : A -> Prop) : (term586 A v u _60027) = (term583 A v u _60027).
Proof. exact (eq_refl (term586 A v u _60027)). Qed.
Lemma lem4839673 {A : Type'} (_60027 : A -> Prop) (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term583 A v u _60027.
Proof. exact (EQ_MP (@lem4839672 A v u _60027) (@lem4839671 A _60027 v u h1)). Qed.
Lemma lem4839684 {A : Type'} (v : type686 A) (u : type686 A) (_60027 : A -> Prop) : (term583 A v u _60027) = (term587 A v u _60027).
Proof. exact (@lem4833723 (term541 A _60027 v) (@IN (A -> Prop) _60027 u) (_60027 = (@EMPTY A))). Qed.
Lemma lem4839685 {A : Type'} (_60027 : A -> Prop) (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term587 A v u _60027.
Proof. exact (EQ_MP (@lem4839684 A v u _60027) (@lem4839673 A _60027 v u h1)). Qed.
Lemma lem4839691 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term222 A a.
Proof. exact (proj2 (@lem4839637 A v a u h1)). Qed.
Lemma lem4839716 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : @IN (A -> Prop) a v.
Proof. exact (proj1 (@lem4839637 A v a u h1)). Qed.
Lemma lem4839717 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term588 A a v.
Proof. exact (fun h0 : term541 A a v => @lem4839716 A v a u h1). Qed.
Lemma lem4839719 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4839720 {A : Type'} (a : A -> Prop) (v : type686 A) : (term588 A a v) = (@IN (A -> Prop) a v).
Proof. exact (@lem4839719 (@IN (A -> Prop) a v)). Qed.
Lemma lem4839721 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : @IN (A -> Prop) a v.
Proof. exact (EQ_MP (@lem4839720 A a v) (@lem4839717 A v a u h1)). Qed.
Lemma lem4839723 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term541 A a u.
Proof. exact (proj2 (@lem4839635 A v a u h1)). Qed.
Lemma lem4839724 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term589 A a u.
Proof. exact (fun h0 : @IN (A -> Prop) a u => @lem4839723 A v a u h1). Qed.
Lemma lem4839726 (p : Prop) : (term590 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4839727 {A : Type'} (a : A -> Prop) (u : type686 A) : (term589 A a u) = (term541 A a u).
Proof. exact (@lem4839726 (@IN (A -> Prop) a u)). Qed.
Lemma lem4839728 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term541 A a u.
Proof. exact (EQ_MP (@lem4839727 A a u) (@lem4839724 A v a u h1)). Qed.
Lemma lem4839734 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4839735 {A : Type'} (u : type686 A) (v : type686 A) (_60027 : A -> Prop) : (term587 A v u _60027) = (term591 A u v _60027).
Proof. exact (@lem4839734 (@IN (A -> Prop) _60027 u) (term541 A _60027 v) (_60027 = (@EMPTY A))). Qed.
Lemma lem4839749 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4839750 {A : Type'} (_60027 : A -> Prop) (v : type686 A) : (term592 A v _60027) = (term593 A _60027 v).
Proof. exact (@lem4839749 (_60027 = (@EMPTY A)) (term541 A _60027 v)). Qed.
Lemma lem4839758 {A : Type'} (_60027 : A -> Prop) (u : type686 A) : (term594 A _60027 u) = (term594 A _60027 u).
Proof. exact (eq_refl (term594 A _60027 u)). Qed.
Lemma lem4839759 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : (term591 A u v _60027) = (term595 A u _60027 v).
Proof. exact (MK_COMB (@lem4839758 A _60027 u) (@lem4839750 A _60027 v)). Qed.
Lemma lem4839763 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4839764 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : (term595 A u _60027 v) = (term596 A u _60027 v).
Proof. exact (@lem4839763 (_60027 = (@EMPTY A)) (@IN (A -> Prop) _60027 u) (term541 A _60027 v)). Qed.
Lemma lem4839782 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : (term591 A u v _60027) = (term596 A u _60027 v).
Proof. exact (TRANS (@lem4839759 A u _60027 v) (@lem4839764 A u _60027 v)). Qed.
Lemma lem4839783 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : (term587 A v u _60027) = (term596 A u _60027 v).
Proof. exact (TRANS (@lem4839735 A u v _60027) (@lem4839782 A u _60027 v)). Qed.
Lemma lem4839784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4839785 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : (term597 A v u _60027) = (term598 A u _60027 v).
Proof. exact (MK_COMB (@lem4839784) (@lem4839783 A u _60027 v)). Qed.
Lemma lem4839801 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4839802 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : (term578 A v _60027 u) = (term599 A u _60027 v).
Proof. exact (@lem4839801 (@IN (A -> Prop) _60027 u) (term541 A _60027 v)). Qed.
Lemma lem4839808 {A : Type'} (_60027 : A -> Prop) : (term600 A _60027) = (term600 A _60027).
Proof. exact (eq_refl (term600 A _60027)). Qed.
Lemma lem4839809 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : (term601 A v _60027 u) = (term596 A u _60027 v).
Proof. exact (MK_COMB (@lem4839808 A _60027) (@lem4839802 A u _60027 v)). Qed.
Lemma lem4839820 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : ((term587 A v u _60027) = (term601 A v _60027 u)) = ((term596 A u _60027 v) = (term596 A u _60027 v)).
Proof. exact (MK_COMB (@lem4839785 A u _60027 v) (@lem4839809 A u _60027 v)). Qed.
Lemma lem4839822 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4839823 (x : Prop) : (x = x) = True.
Proof. exact (@lem4839822 Prop x). Qed.
Lemma lem4839824 {A : Type'} (u : type686 A) (_60027 : A -> Prop) (v : type686 A) : ((term596 A u _60027 v) = (term596 A u _60027 v)) = True.
Proof. exact (@lem4839823 (term596 A u _60027 v)). Qed.
Lemma lem4839825 {A : Type'} (v : type686 A) (_60027 : A -> Prop) (u : type686 A) : ((term587 A v u _60027) = (term601 A v _60027 u)) = True.
Proof. exact (TRANS (@lem4839820 A u _60027 v) (@lem4839824 A u _60027 v)). Qed.
Lemma lem4839826 {A : Type'} (v : type686 A) (_60027 : A -> Prop) (u : type686 A) : True = ((term587 A v u _60027) = (term601 A v _60027 u)).
Proof. exact (SYM (@lem4839825 A v _60027 u)). Qed.
Lemma lem4839827 {A : Type'} (v : type686 A) (_60027 : A -> Prop) (u : type686 A) : (term587 A v u _60027) = (term601 A v _60027 u).
Proof. exact (EQ_MP (@lem4839826 A v _60027 u) (@lem0)). Qed.
Lemma lem4839828 {A : Type'} (_60027 : A -> Prop) (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term601 A v _60027 u.
Proof. exact (EQ_MP (@lem4839827 A v _60027 u) (@lem4839685 A _60027 v u h1)). Qed.
Lemma lem4839830 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4839831 {A : Type'} (v : type686 A) (u : type686 A) (_60027 : A -> Prop) : (term601 A v _60027 u) = (term602 A v u _60027).
Proof. exact (@lem4839830 (term578 A v _60027 u) (_60027 = (@EMPTY A))). Qed.
Lemma lem4839833 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4839834 {A : Type'} (v : type686 A) (_60027 : A -> Prop) (u : type686 A) : (term605 A v _60027 u) = (term606 A v _60027 u).
Proof. exact (@lem4839833 (term541 A _60027 v) (@IN (A -> Prop) _60027 u)). Qed.
Lemma lem4839836 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4839837 {A : Type'} (_60027 : A -> Prop) (v : type686 A) : (term575 A _60027 v) = (@IN (A -> Prop) _60027 v).
Proof. exact (@lem4839836 (@IN (A -> Prop) _60027 v)). Qed.
Lemma lem4839838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4839839 {A : Type'} (_60027 : A -> Prop) (v : type686 A) : (term607 A _60027 v) = (term220 A _60027 v).
Proof. exact (MK_COMB (@lem4839838) (@lem4839837 A _60027 v)). Qed.
Lemma lem4839840 {A : Type'} (_60027 : A -> Prop) (u : type686 A) : (term541 A _60027 u) = (term541 A _60027 u).
Proof. exact (eq_refl (term541 A _60027 u)). Qed.
Lemma lem4839841 {A : Type'} (v : type686 A) (_60027 : A -> Prop) (u : type686 A) : (term606 A v _60027 u) = (term550 A v _60027 u).
Proof. exact (MK_COMB (@lem4839839 A _60027 v) (@lem4839840 A _60027 u)). Qed.
Lemma lem4839842 {A : Type'} (v : type686 A) (_60027 : A -> Prop) (u : type686 A) : (term605 A v _60027 u) = (term550 A v _60027 u).
Proof. exact (TRANS (@lem4839834 A v _60027 u) (@lem4839841 A v _60027 u)). Qed.
Lemma lem4839843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4839844 {A : Type'} (v : type686 A) (_60027 : A -> Prop) (u : type686 A) : (term608 A v _60027 u) = (term552 A v _60027 u).
Proof. exact (MK_COMB (@lem4839843) (@lem4839842 A v _60027 u)). Qed.
Lemma lem4839845 {A : Type'} (_60027 : A -> Prop) : (_60027 = (@EMPTY A)) = (_60027 = (@EMPTY A)).
Proof. exact (eq_refl (_60027 = (@EMPTY A))). Qed.
Lemma lem4839846 {A : Type'} (v : type686 A) (u : type686 A) (_60027 : A -> Prop) : (term602 A v u _60027) = (term554 A v u _60027).
Proof. exact (MK_COMB (@lem4839844 A v _60027 u) (@lem4839845 A _60027)). Qed.
Lemma lem4839847 {A : Type'} (v : type686 A) (u : type686 A) (_60027 : A -> Prop) : (term601 A v _60027 u) = (term554 A v u _60027).
Proof. exact (TRANS (@lem4839831 A v u _60027) (@lem4839846 A v u _60027)). Qed.
Lemma lem4839849 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term550 A v a u.
Proof. exact (conj (@lem4839721 A v a u h1) (@lem4839728 A v a u h1)). Qed.
Lemma lem4839851 {A : Type'} (_60027 : A -> Prop) (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term554 A v u _60027.
Proof. exact (EQ_MP (@lem4839847 A v u _60027) (@lem4839828 A _60027 v u h1)). Qed.
Lemma lem4839852 {A : Type'} (_60027 : A -> Prop) (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term554 A v u _60027.
Proof. exact (@lem4839851 A _60027 v u h1). Qed.
Lemma lem4839853 {A : Type'} (a : A -> Prop) (v : type686 A) (u : type686 A) (h1 : term557 A v u) : term554 A v u a.
Proof. exact (@lem4839852 A a v u h1). Qed.
Lemma lem4839856 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term557 A v u) (h2 : term543 A v a u) : a = (@EMPTY A).
Proof. exact (@lem4839853 A a v u h1 (@lem4839849 A v a u h2)). Qed.
Lemma lem4839857 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term557 A v u) (h2 : term543 A v a u) : term609 A a.
Proof. exact (fun h0 : term222 A a => @lem4839856 A v a u h1 h2). Qed.
Lemma lem4839859 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4839860 {A : Type'} (a : A -> Prop) : (term609 A a) = (a = (@EMPTY A)).
Proof. exact (@lem4839859 (a = (@EMPTY A))). Qed.
Lemma lem4839861 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term557 A v u) (h2 : term543 A v a u) : a = (@EMPTY A).
Proof. exact (EQ_MP (@lem4839860 A a) (@lem4839857 A v a u h1 h2)). Qed.
Lemma lem4839864 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4839866 {A : Type'} (a : A -> Prop) : (term222 A a) = (term610 A a).
Proof. exact (@lem4839864 (a = (@EMPTY A))). Qed.
Lemma lem4839869 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term543 A v a u) : term610 A a.
Proof. exact (EQ_MP (@lem4839866 A a) (@lem4839691 A v a u h1)). Qed.
Lemma lem4839872 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term557 A v u) (h2 : term543 A v a u) : False.
Proof. exact (@lem4839869 A v a u h2 (@lem4839861 A v a u h1 h2)). Qed.
Lemma lem4839873 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term557 A v u) (h2 : term543 A v a u) : term184.
Proof. exact (fun h0 : ~ False => @lem4839872 A v a u h1 h2). Qed.
Lemma lem4839875 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4839876 : term184 = False.
Proof. exact (@lem4839875 False). Qed.
Lemma lem4839877 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term557 A v u) (h2 : term543 A v a u) : False.
Proof. exact (EQ_MP (@lem4839876) (@lem4839873 A v a u h1 h2)). Qed.
Lemma lem4839878 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term557 A v u) (h2 : term543 A v a u) : (term543 A v a u) = False.
Proof. exact (prop_ext (fun h3 : term543 A v a u => @lem4839877 A v a u h1 h2) (fun h3 : False => @lem4839635 A v a u h2)). Qed.
Lemma lem4839879 {A : Type'} (v : type686 A) (a : A -> Prop) (u : type686 A) (h1 : term557 A v u) (h2 : term543 A v a u) : False.
Proof. exact (EQ_MP (@lem4839878 A v a u h1 h2) (@lem4839635 A v a u h2)). Qed.
Lemma lem4839880 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term557 A v u) (h2 : term546 A v u) : False.
Proof. exact (ex_elim (@lem4839510 A v u h2) (fun a : A -> Prop => fun h0 : term545 A v u a => @lem4839879 A v a u h1 h0)). Qed.
Lemma lem4839881 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term557 A v u) (h2 : term546 A v u) : (term546 A v u) = False.
Proof. exact (prop_ext (fun h3 : term546 A v u => @lem4839880 A v u h1 h2) (fun h3 : False => @lem4839510 A v u h2)). Qed.
Lemma lem4839882 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term557 A v u) (h2 : term546 A v u) : False.
Proof. exact (EQ_MP (@lem4839881 A v u h1 h2) (@lem4839510 A v u h2)). Qed.
Lemma lem4839883 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term546 A v u) : term611 A v u.
Proof. exact (fun h0 : term557 A v u => @lem4839882 A v u h0 h1). Qed.
Lemma lem4839884 {A : Type'} (v : type686 A) (u : type686 A) : (term611 A v u) = (term558 A v u).
Proof. exact (@lem69 (term557 A v u)). Qed.
Lemma lem4839885 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term546 A v u) : term558 A v u.
Proof. exact (EQ_MP (@lem4839884 A v u) (@lem4839883 A v u h1)). Qed.
Lemma lem4839886 {A : Type'} (v : type686 A) (u : type686 A) : term560 A v u.
Proof. exact (fun h0 : term546 A v u => @lem4839885 A v u h0). Qed.
Lemma lem4839891 {A : Type'} (u : type686 A) : term570 A u.
Proof. exact (fun v : type686 A => @lem4839886 A v u). Qed.
Lemma lem4839896 {A : Type'} : term574 A.
Proof. exact (fun u : type686 A => @lem4839891 A u). Qed.
Lemma lem4839897 {A : Type'} : term573 A.
Proof. exact (EQ_MP (@lem4839443 A) (@lem4839896 A)). Qed.
Lemma lem4839898 {A : Type'} (u : type686 A) : term612 A u.
Proof. exact (@lem4839897 A u). Qed.
Lemma lem4839899 {A : Type'} (u : type686 A) : (term612 A u) = (term569 A u).
Proof. exact (eq_refl (term612 A u)). Qed.
Lemma lem4839900 {A : Type'} (u : type686 A) : term569 A u.
Proof. exact (EQ_MP (@lem4839899 A u) (@lem4839898 A u)). Qed.
Lemma lem4839901 {A : Type'} (u : type686 A) (v : type686 A) : term613 A u v.
Proof. exact (@lem4839900 A u v). Qed.
Lemma lem4839902 {A : Type'} (v : type686 A) (u : type686 A) : (term613 A u v) = (term561 A v u).
Proof. exact (eq_refl (term613 A u v)). Qed.
Lemma lem4839903 {A : Type'} (v : type686 A) (u : type686 A) : term561 A v u.
Proof. exact (EQ_MP (@lem4839902 A v u) (@lem4839901 A u v)). Qed.
Lemma lem4839905 {A : Type'} (v : type686 A) (u : type686 A) : term561 A v u.
Proof. exact (@lem4839269 A v u (@lem4839903 A v u)). Qed.
Lemma lem4839906 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term562 A v u) : False.
Proof. exact (@lem4839905 A v u (@lem4839253 A v u h1)). Qed.
Lemma lem4839907 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term562 A v u) : (term562 A v u) = False.
Proof. exact (prop_ext (fun h2 : term562 A v u => @lem4839906 A v u h1) (fun h2 : False => @lem4839253 A v u h1)). Qed.
Lemma lem4839908 {A : Type'} (v : type686 A) (u : type686 A) (h1 : term562 A v u) : False.
Proof. exact (EQ_MP (@lem4839907 A v u h1) (@lem4839253 A v u h1)). Qed.
Lemma lem4839909 {A : Type'} (v : type686 A) (u : type686 A) : term561 A v u.
Proof. exact (fun h0 : term562 A v u => @lem4839908 A v u h0). Qed.
Lemma lem4839910 {A : Type'} (v : type686 A) (u : type686 A) : term560 A v u.
Proof. exact (EQ_MP (@lem4839252 A v u) (@lem4839909 A v u)). Qed.
Lemma lem4839911 {A : Type'} (v : type686 A) (u : type686 A) : term559 A v u.
Proof. exact (EQ_MP (@lem4839248 A v u) (@lem4839910 A v u)). Qed.
Lemma lem4839912 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) : term535 A v u.
Proof. exact (@lem4839911 A v u (@lem4839184 A u v h1)). Qed.
Lemma lem4839913 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) : term531 A v u.
Proof. exact (EQ_MP (@lem4839178 A v u) (@lem4839912 A u v h1)). Qed.
Lemma lem4839914 {A : Type'} (u : type686 A) (v : type686 A) (h1 : (term439 A v u) = (term440 A v u)) (h2 : term190 A u v) : term441 A v u.
Proof. exact (EQ_MP (@lem4839163 A v u h1) (@lem4839913 A u v h2)). Qed.
Lemma lem4839915 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) : term614 A v u.
Proof. exact (fun h0 : (term439 A v u) = (term440 A v u) => @lem4839914 A u v h0 h1). Qed.
Lemma lem4839916 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term615 A v u.
Proof. exact (conj (@lem4839149 A u v h1 h2) (@lem4839915 A u v h1)). Qed.
Lemma lem4839917 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term616 A v u.
Proof. exact (@lem4836924 A v u (@lem4839916 A u v h1 h2)). Qed.
Lemma lem4839918 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term441 A v u.
Proof. exact (@lem4839917 A u v h1 h2 (@lem4836921 A v u)). Qed.
Lemma lem4839919 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term617 A v u.
Proof. exact (conj (@lem4836917 A u v h1 h2) (@lem4839918 A u v h1 h2)). Qed.
Lemma lem4839920 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term618 A u v.
Proof. exact (@lem4834879 A u v (@lem4839919 A u v h1 h2)). Qed.
Lemma lem4839921 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term189 A u v) : term190 A u v.
Proof. exact (proj2 (@lem4834873 A u v h1)). Qed.
Lemma lem4839922 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term189 A u v) : @pairwise (A -> Prop) (@DISJOINT A) v.
Proof. exact (proj1 (@lem4834873 A u v h1)). Qed.
Lemma lem4839923 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : (term190 A u v) = (term618 A u v).
Proof. exact (prop_ext (fun h3 : term190 A u v => @lem4839920 A u v h1 h2) (fun h3 : term618 A u v => @lem4834874 A u v h1)). Qed.
Lemma lem4839924 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term618 A u v.
Proof. exact (EQ_MP (@lem4839923 A u v h1 h2) (@lem4834874 A u v h1)). Qed.
Lemma lem4839925 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (term618 A u v).
Proof. exact (prop_ext (fun h3 : @pairwise (A -> Prop) (@DISJOINT A) v => @lem4839924 A u v h1 h2) (fun h3 : term618 A u v => @lem4834875 A v h2)). Qed.
Lemma lem4839926 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term190 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term618 A u v.
Proof. exact (EQ_MP (@lem4839925 A u v h1 h2) (@lem4834875 A v h2)). Qed.
Lemma lem4839927 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term189 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : (term190 A u v) = (term618 A u v).
Proof. exact (prop_ext (fun h3 : term190 A u v => @lem4839926 A u v h3 h2) (fun h3 : term618 A u v => @lem4839921 A u v h1)). Qed.
Lemma lem4839928 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term189 A u v) (h2 : @pairwise (A -> Prop) (@DISJOINT A) v) : term618 A u v.
Proof. exact (EQ_MP (@lem4839927 A u v h1 h2) (@lem4839921 A u v h1)). Qed.
Lemma lem4839929 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term189 A u v) : (@pairwise (A -> Prop) (@DISJOINT A) v) = (term618 A u v).
Proof. exact (prop_ext (fun h2 : @pairwise (A -> Prop) (@DISJOINT A) v => @lem4839928 A u v h1 h2) (fun h2 : term618 A u v => @lem4839922 A u v h1)). Qed.
Lemma lem4839930 {A : Type'} (u : type686 A) (v : type686 A) (h1 : term189 A u v) : term618 A u v.
Proof. exact (EQ_MP (@lem4839929 A u v h1) (@lem4839922 A u v h1)). Qed.
Lemma lem4839931 {A : Type'} (u : type686 A) (v : type686 A) : term619 A u v.
Proof. exact (fun h0 : term189 A u v => @lem4839930 A u v h0). Qed.
Lemma lem4839936 {A : Type'} (u : type686 A) : term620 A u.
Proof. exact (fun v : type686 A => @lem4839931 A u v). Qed.
Lemma lem4839941 {A : Type'} : term621 A.
Proof. exact (fun u : type686 A => @lem4839936 A u). Qed.
