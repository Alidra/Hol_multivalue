Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_UNION_LZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NSUM_UNION_RZERO_spec.
Require Import UNION_COMM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem6967616 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6967617 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6967618 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6967617 t1) (@lem6967616 t1)). Qed.
Lemma lem6967619 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6967618 t1 t2). Qed.
Lemma lem6967620 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6967621 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6967620 t1 t2) (@lem6967619 t1 t2)). Qed.
Lemma lem6967622 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6967621 t1 t2 t3). Qed.
Lemma lem6967623 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6967624 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6967623 t1 t2 t3) (@lem6967622 t1 t2 t3)). Qed.
Lemma lem6967625 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6967624 t1 t2 t3)). Qed.
Lemma lem6967627 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6967628 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem6967627 (term8 A)). Qed.
Lemma lem6967629 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem6967628 A)). Qed.
Lemma lem6967630 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem6967631 {A : Type'} : term11 A.
Proof. exact (@lem6967615 A). Qed.
Lemma lem6967635 {A : Type'} : term12 A.
Proof. exact (@lem3233393 A). Qed.
Lemma lem6967638 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem6967639 {A : Type'} : term14 A.
Proof. exact (fun h0 : term13 A => @lem6967638 A h0). Qed.
Lemma lem6967640 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem6967641 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem6967642 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem6967640 A h2 (@lem6967641 A h1)). Qed.
Lemma lem6967643 {A : Type'} (h1 : term13 A) : term15 A.
Proof. exact (fun h0 : term14 A => @lem6967642 A h1 h0). Qed.
Lemma lem6967644 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem6967645 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem6967643 A h1 (@lem6967644 A h2)). Qed.
Lemma lem6967646 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (fun h0 : term13 A => @lem6967645 A h0 h1). Qed.
Lemma lem6967647 {A : Type'} : term16 A.
Proof. exact (fun h0 : term14 A => @lem6967646 A h0). Qed.
Lemma lem6967650 {A : Type'} : term14 A.
Proof. exact (@lem6967647 A (@lem6967639 A)). Qed.
Lemma lem6967651 {A : Type'} : term14 A.
Proof. exact (@lem6967650 A). Qed.
Lemma lem6967689 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6967690 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem6967689 (term11 A)). Qed.
Lemma lem6967715 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem6967716 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem6967715 A) (@lem6967690 A)). Qed.
Lemma lem6967719 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem6967726 {A : Type'} : (term13 A) = (term23 A).
Proof. exact (MK_COMB (@lem6967719 A) (@lem6967716 A)). Qed.
Lemma lem6967727 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term24 A u v f) = (@nsum A u f)) = ((term24 A u v f) = (@nsum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@nsum A u f))). Qed.
Lemma lem6967738 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term25 A v u f x) = (term25 A v u f x).
Proof. exact (eq_refl (term25 A v u f x)). Qed.
Lemma lem6967739 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term26 A v u f) = (term26 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6967738 A v u f x)). Qed.
Lemma lem6967740 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6967741 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term27 A v u f) = (term27 A v u f).
Proof. exact (MK_COMB (@lem6967740 A) (@lem6967739 A v u f)). Qed.
Lemma lem6967744 {A : Type'} (u : A -> Prop) : (term28 A u) = (term28 A u).
Proof. exact (eq_refl (term28 A u)). Qed.
Lemma lem6967745 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term29 A v u f) = (term29 A v u f).
Proof. exact (MK_COMB (@lem6967744 A u) (@lem6967741 A v u f)). Qed.
Lemma lem6967746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6967747 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term30 A v u f) = (term30 A v u f).
Proof. exact (MK_COMB (@lem6967746) (@lem6967745 A v u f)). Qed.
Lemma lem6967748 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term31 A v u f) = (term31 A v u f).
Proof. exact (MK_COMB (@lem6967747 A v u f) (@lem6967727 A v u f)). Qed.
Lemma lem6967749 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term32 A u f) = (term32 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6967748 A v u f)). Qed.
Lemma lem6967750 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6967751 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term33 A u f) = (term33 A u f).
Proof. exact (MK_COMB (@lem6967750 A) (@lem6967749 A u f)). Qed.
Lemma lem6967752 {A : Type'} (f : A -> nat) : (term34 A f) = (term34 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6967751 A u f)). Qed.
Lemma lem6967753 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6967754 {A : Type'} (f : A -> nat) : (term35 A f) = (term35 A f).
Proof. exact (MK_COMB (@lem6967753 A) (@lem6967752 A f)). Qed.
Lemma lem6967755 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6967754 A f)). Qed.
Lemma lem6967756 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6967757 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem6967756 A) (@lem6967755 A)). Qed.
Lemma lem6967758 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6967759 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem6967758) (@lem6967757 A)). Qed.
Lemma lem6967760 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@UNION A s t) = (@UNION A t s)) = ((@UNION A s t) = (@UNION A t s)).
Proof. exact (eq_refl ((@UNION A s t) = (@UNION A t s))). Qed.
Lemma lem6967761 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6967760 A t s)). Qed.
Lemma lem6967762 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6967763 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem6967762 A) (@lem6967761 A s)). Qed.
Lemma lem6967764 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6967763 A s)). Qed.
Lemma lem6967765 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6967766 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem6967765 A) (@lem6967764 A)). Qed.
Lemma lem6967767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6967768 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem6967767) (@lem6967766 A)). Qed.
Lemma lem6967769 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem6967768 A) (@lem6967759 A)). Qed.
Lemma lem6967770 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : ((term24 A u v f) = (@nsum A v f)) = ((term24 A u v f) = (@nsum A v f)).
Proof. exact (eq_refl ((term24 A u v f) = (@nsum A v f))). Qed.
Lemma lem6967781 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) : (term25 A u v f x) = (term25 A u v f x).
Proof. exact (eq_refl (term25 A u v f x)). Qed.
Lemma lem6967782 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term26 A u v f) = (term26 A u v f).
Proof. exact (fun_ext (fun x : A => @lem6967781 A u v f x)). Qed.
Lemma lem6967783 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6967784 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term27 A u v f) = (term27 A u v f).
Proof. exact (MK_COMB (@lem6967783 A) (@lem6967782 A u v f)). Qed.
Lemma lem6967787 {A : Type'} (v : A -> Prop) : (term28 A v) = (term28 A v).
Proof. exact (eq_refl (term28 A v)). Qed.
Lemma lem6967788 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term29 A u v f) = (term29 A u v f).
Proof. exact (MK_COMB (@lem6967787 A v) (@lem6967784 A u v f)). Qed.
Lemma lem6967789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6967790 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term30 A u v f) = (term30 A u v f).
Proof. exact (MK_COMB (@lem6967789) (@lem6967788 A u v f)). Qed.
Lemma lem6967791 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term40 A u v f) = (term40 A u v f).
Proof. exact (MK_COMB (@lem6967790 A u v f) (@lem6967770 A u v f)). Qed.
Lemma lem6967792 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term41 A u f) = (term41 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6967791 A u v f)). Qed.
Lemma lem6967793 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6967794 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term42 A u f) = (term42 A u f).
Proof. exact (MK_COMB (@lem6967793 A) (@lem6967792 A u f)). Qed.
Lemma lem6967795 {A : Type'} (f : A -> nat) : (term43 A f) = (term43 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6967794 A u f)). Qed.
Lemma lem6967796 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6967797 {A : Type'} (f : A -> nat) : (term44 A f) = (term44 A f).
Proof. exact (MK_COMB (@lem6967796 A) (@lem6967795 A f)). Qed.
Lemma lem6967798 {A : Type'} : (term45 A) = (term45 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6967797 A f)). Qed.
Lemma lem6967799 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6967800 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem6967799 A) (@lem6967798 A)). Qed.
Lemma lem6967801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6967802 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem6967801) (@lem6967800 A)). Qed.
Lemma lem6967803 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6967804 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem6967803) (@lem6967802 A)). Qed.
Lemma lem6967805 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem6967804 A) (@lem6967769 A)). Qed.
Lemma lem6967888 {A : Type'} : (term13 A) = (term23 A).
Proof. exact (TRANS (@lem6967726 A) (@lem6967805 A)). Qed.
Lemma lem6967889 {A : Type'} : (term23 A) = (term13 A).
Proof. exact (SYM (@lem6967888 A)). Qed.
Lemma lem6967890 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem6967891 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem6967892 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem6967897 {A : Type'} (x : A) (v : A -> Prop) : (term46 A x v) = (@IN A x v).
Proof. exact (@lem16933 (@IN A x v)). Qed.
Lemma lem6967899 {A : Type'} (x : A) (u : A -> Prop) : (term47 A x u) = (term47 A x u).
Proof. exact (eq_refl (term47 A x u)). Qed.
Lemma lem6967900 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term48 A u x v) = (term49 A u x v).
Proof. exact (MK_COMB (@lem6967899 A x u) (@lem6967897 A x v)). Qed.
Lemma lem6967901 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term50 A u x v) = (term48 A u x v).
Proof. exact (@lem17045 (@IN A x u) (term51 A x v)). Qed.
Lemma lem6967902 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term50 A u x v) = (term49 A u x v).
Proof. exact (TRANS (@lem6967901 A u x v) (@lem6967900 A u x v)). Qed.
Lemma lem6967903 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem6967904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6967905 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term52 A u x v) = (term53 A u x v).
Proof. exact (MK_COMB (@lem6967904) (@lem6967902 A u x v)). Qed.
Lemma lem6967906 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) : (term54 A u v f x) = (term55 A u v f x).
Proof. exact (MK_COMB (@lem6967905 A u x v) (@lem6967903 A f x)). Qed.
Lemma lem6967907 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) : (term25 A u v f x) = (term54 A u v f x).
Proof. exact (@lem17265 (term56 A u x v) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6967908 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) : (term25 A u v f x) = (term55 A u v f x).
Proof. exact (TRANS (@lem6967907 A u v f x) (@lem6967906 A u v f x)). Qed.
Lemma lem6967909 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term26 A u v f) = (term57 A u v f).
Proof. exact (fun_ext (fun x : A => @lem6967908 A u v f x)). Qed.
Lemma lem6967910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6967911 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term27 A u v f) = (term58 A u v f).
Proof. exact (MK_COMB (@lem6967910 A) (@lem6967909 A u v f)). Qed.
Lemma lem6967913 {A : Type'} (v : A -> Prop) : (term28 A v) = (term28 A v).
Proof. exact (eq_refl (term28 A v)). Qed.
Lemma lem6967914 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term29 A u v f) = (term59 A u v f).
Proof. exact (MK_COMB (@lem6967913 A v) (@lem6967911 A u v f)). Qed.
Lemma lem6967915 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term60 A u v f) = (term60 A u v f).
Proof. exact (eq_refl (term60 A u v f)). Qed.
Lemma lem6967916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6967917 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term61 A u v f) = (term62 A u v f).
Proof. exact (MK_COMB (@lem6967916) (@lem6967914 A u v f)). Qed.
Lemma lem6967918 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term63 A u v f) = (term64 A u v f).
Proof. exact (MK_COMB (@lem6967917 A u v f) (@lem6967915 A u v f)). Qed.
Lemma lem6967919 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term65 A u v f) = (term63 A u v f).
Proof. exact (@lem17362 (term29 A u v f) ((term24 A u v f) = (@nsum A v f))). Qed.
Lemma lem6967920 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term65 A u v f) = (term64 A u v f).
Proof. exact (TRANS (@lem6967919 A u v f) (@lem6967918 A u v f)). Qed.
Lemma lem6967921 {A : Type'} (P : type686 A) : (term66 A P) = (term67 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem6967922 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term68 A u f) = (term69 A u f).
Proof. exact (@lem6967921 A (term41 A u f)). Qed.
Lemma lem6967923 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term70 A u f v) = (term40 A u v f).
Proof. exact (eq_refl (term70 A u f v)). Qed.
Lemma lem6967924 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6967925 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term71 A u f v) = (term65 A u v f).
Proof. exact (MK_COMB (@lem6967924) (@lem6967923 A u v f)). Qed.
Lemma lem6967926 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term71 A u f v) = (term64 A u v f).
Proof. exact (TRANS (@lem6967925 A u v f) (@lem6967920 A u v f)). Qed.
Lemma lem6967927 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term72 A u f) = (term73 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6967926 A u v f)). Qed.
Lemma lem6967928 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem6967929 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term69 A u f) = (term74 A u f).
Proof. exact (MK_COMB (@lem6967928 A) (@lem6967927 A u f)). Qed.
Lemma lem6967930 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term68 A u f) = (term74 A u f).
Proof. exact (TRANS (@lem6967922 A u f) (@lem6967929 A u f)). Qed.
Lemma lem6967931 {A : Type'} (P : type686 A) : (term66 A P) = (term67 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem6967932 {A : Type'} (f : A -> nat) : (term75 A f) = (term76 A f).
Proof. exact (@lem6967931 A (term43 A f)). Qed.
Lemma lem6967933 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term77 A f u) = (term42 A u f).
Proof. exact (eq_refl (term77 A f u)). Qed.
Lemma lem6967934 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6967935 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term78 A f u) = (term68 A u f).
Proof. exact (MK_COMB (@lem6967934) (@lem6967933 A u f)). Qed.
Lemma lem6967936 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term78 A f u) = (term74 A u f).
Proof. exact (TRANS (@lem6967935 A u f) (@lem6967930 A u f)). Qed.
Lemma lem6967937 {A : Type'} (f : A -> nat) : (term79 A f) = (term80 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6967936 A u f)). Qed.
Lemma lem6967938 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem6967939 {A : Type'} (f : A -> nat) : (term76 A f) = (term81 A f).
Proof. exact (MK_COMB (@lem6967938 A) (@lem6967937 A f)). Qed.
Lemma lem6967940 {A : Type'} (f : A -> nat) : (term75 A f) = (term81 A f).
Proof. exact (TRANS (@lem6967932 A f) (@lem6967939 A f)). Qed.
Lemma lem6967941 {A : Type'} (P : type704 A) : (term82 A P) = (term83 A P).
Proof. exact (@lem18392 (A -> nat) P). Qed.
Lemma lem6967942 {A : Type'} : (term10 A) = (term84 A).
Proof. exact (@lem6967941 A (term45 A)). Qed.
Lemma lem6967943 {A : Type'} (f : A -> nat) : (term85 A f) = (term44 A f).
Proof. exact (eq_refl (term85 A f)). Qed.
Lemma lem6967944 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6967945 {A : Type'} (f : A -> nat) : (term86 A f) = (term75 A f).
Proof. exact (MK_COMB (@lem6967944) (@lem6967943 A f)). Qed.
Lemma lem6967946 {A : Type'} (f : A -> nat) : (term86 A f) = (term81 A f).
Proof. exact (TRANS (@lem6967945 A f) (@lem6967940 A f)). Qed.
Lemma lem6967947 {A : Type'} : (term87 A) = (term88 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6967946 A f)). Qed.
Lemma lem6967948 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem6967949 {A : Type'} : (term84 A) = (term89 A).
Proof. exact (MK_COMB (@lem6967948 A) (@lem6967947 A)). Qed.
Lemma lem6968058 {A : Type'} : (term10 A) = (term89 A).
Proof. exact (TRANS (@lem6967942 A) (@lem6967949 A)). Qed.
Lemma lem6968059 {A : Type'} (h1 : term10 A) : term89 A.
Proof. exact (EQ_MP (@lem6968058 A) (@lem6967890 A h1)). Qed.
Lemma lem6968060 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@UNION A s t) = (@UNION A t s)) = ((@UNION A s t) = (@UNION A t s)).
Proof. exact (eq_refl ((@UNION A s t) = (@UNION A t s))). Qed.
Lemma lem6968061 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6968060 A t s)). Qed.
Lemma lem6968062 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968063 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem6968062 A) (@lem6968061 A s)). Qed.
Lemma lem6968064 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6968063 A s)). Qed.
Lemma lem6968065 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968078 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem6968065 A) (@lem6968064 A)). Qed.
Lemma lem6968079 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (EQ_MP (@lem6968078 A) (@lem6967891 A h1)). Qed.
Lemma lem6968091 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term90 A v u f x) = (term91 A v u f x).
Proof. exact (@lem17362 (term56 A v x u) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6968092 {A : Type'} (P : A -> Prop) : (term92 A P) = (term93 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6968093 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term94 A v u f) = (term95 A v u f).
Proof. exact (@lem6968092 A (term26 A v u f)). Qed.
Lemma lem6968094 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term96 A v u f x) = (term25 A v u f x).
Proof. exact (eq_refl (term96 A v u f x)). Qed.
Lemma lem6968095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6968096 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term97 A v u f x) = (term90 A v u f x).
Proof. exact (MK_COMB (@lem6968095) (@lem6968094 A v u f x)). Qed.
Lemma lem6968097 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term97 A v u f x) = (term91 A v u f x).
Proof. exact (TRANS (@lem6968096 A v u f x) (@lem6968091 A v u f x)). Qed.
Lemma lem6968098 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term98 A v u f) = (term99 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6968097 A v u f x)). Qed.
Lemma lem6968099 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6968100 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term95 A v u f) = (term100 A v u f).
Proof. exact (MK_COMB (@lem6968099 A) (@lem6968098 A v u f)). Qed.
Lemma lem6968101 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term94 A v u f) = (term100 A v u f).
Proof. exact (TRANS (@lem6968093 A v u f) (@lem6968100 A v u f)). Qed.
Lemma lem6968103 {A : Type'} (u : A -> Prop) : (term101 A u) = (term101 A u).
Proof. exact (eq_refl (term101 A u)). Qed.
Lemma lem6968104 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term102 A v u f) = (term103 A v u f).
Proof. exact (MK_COMB (@lem6968103 A u) (@lem6968101 A v u f)). Qed.
Lemma lem6968105 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term104 A v u f) = (term102 A v u f).
Proof. exact (@lem17045 (@FINITE A u) (term27 A v u f)). Qed.
Lemma lem6968106 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term104 A v u f) = (term103 A v u f).
Proof. exact (TRANS (@lem6968105 A v u f) (@lem6968104 A v u f)). Qed.
Lemma lem6968107 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term24 A u v f) = (@nsum A u f)) = ((term24 A u v f) = (@nsum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@nsum A u f))). Qed.
Lemma lem6968108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968109 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term105 A v u f) = (term106 A v u f).
Proof. exact (MK_COMB (@lem6968108) (@lem6968106 A v u f)). Qed.
Lemma lem6968110 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term107 A v u f) = (term108 A v u f).
Proof. exact (MK_COMB (@lem6968109 A v u f) (@lem6968107 A v u f)). Qed.
Lemma lem6968111 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term31 A v u f) = (term107 A v u f).
Proof. exact (@lem17265 (term29 A v u f) ((term24 A u v f) = (@nsum A u f))). Qed.
Lemma lem6968112 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term31 A v u f) = (term108 A v u f).
Proof. exact (TRANS (@lem6968111 A v u f) (@lem6968110 A v u f)). Qed.
Lemma lem6968113 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term32 A u f) = (term109 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6968112 A v u f)). Qed.
Lemma lem6968114 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968115 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term33 A u f) = (term110 A u f).
Proof. exact (MK_COMB (@lem6968114 A) (@lem6968113 A u f)). Qed.
Lemma lem6968116 {A : Type'} (f : A -> nat) : (term34 A f) = (term111 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6968115 A u f)). Qed.
Lemma lem6968117 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968118 {A : Type'} (f : A -> nat) : (term35 A f) = (term112 A f).
Proof. exact (MK_COMB (@lem6968117 A) (@lem6968116 A f)). Qed.
Lemma lem6968119 {A : Type'} : (term36 A) = (term113 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6968118 A f)). Qed.
Lemma lem6968120 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6968121 {A : Type'} : (term11 A) = (term114 A).
Proof. exact (MK_COMB (@lem6968120 A) (@lem6968119 A)). Qed.
Lemma lem6968228 {A : Type'} (P : Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6968229 {A : Type'} (P : Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (@lem6968228 A P Q). Qed.
Lemma lem6968230 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term117 A v u f) = (term118 A v u f).
Proof. exact (@lem6968229 A (term119 A u) (term99 A v u f)). Qed.
Lemma lem6968231 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term120 A v u f x) = (term91 A v u f x).
Proof. exact (eq_refl (term120 A v u f x)). Qed.
Lemma lem6968232 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term121 A v u f) = (term99 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6968231 A v u f x)). Qed.
Lemma lem6968233 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6968234 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term122 A v u f) = (term100 A v u f).
Proof. exact (MK_COMB (@lem6968233 A) (@lem6968232 A v u f)). Qed.
Lemma lem6968235 {A : Type'} (u : A -> Prop) : (term101 A u) = (term101 A u).
Proof. exact (eq_refl (term101 A u)). Qed.
Lemma lem6968236 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term117 A v u f) = (term103 A v u f).
Proof. exact (MK_COMB (@lem6968235 A u) (@lem6968234 A v u f)). Qed.
Lemma lem6968237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6968238 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term123 A v u f) = (term124 A v u f).
Proof. exact (MK_COMB (@lem6968237) (@lem6968236 A v u f)). Qed.
Lemma lem6968239 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term120 A v u f x) = (term91 A v u f x).
Proof. exact (eq_refl (term120 A v u f x)). Qed.
Lemma lem6968240 {A : Type'} (u : A -> Prop) : (term101 A u) = (term101 A u).
Proof. exact (eq_refl (term101 A u)). Qed.
Lemma lem6968241 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term125 A v u f x) = (term126 A v u f x).
Proof. exact (MK_COMB (@lem6968240 A u) (@lem6968239 A v u f x)). Qed.
Lemma lem6968242 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term127 A v u f) = (term128 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6968241 A v u f x)). Qed.
Lemma lem6968243 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6968244 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term118 A v u f) = (term129 A v u f).
Proof. exact (MK_COMB (@lem6968243 A) (@lem6968242 A v u f)). Qed.
Lemma lem6968245 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term117 A v u f) = (term118 A v u f)) = ((term103 A v u f) = (term129 A v u f)).
Proof. exact (MK_COMB (@lem6968238 A v u f) (@lem6968244 A v u f)). Qed.
Lemma lem6968246 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term103 A v u f) = (term129 A v u f).
Proof. exact (EQ_MP (@lem6968245 A v u f) (@lem6968230 A v u f)). Qed.
Lemma lem6968247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968248 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term106 A v u f) = (term130 A v u f).
Proof. exact (MK_COMB (@lem6968247) (@lem6968246 A v u f)). Qed.
Lemma lem6968249 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term24 A u v f) = (@nsum A u f)) = ((term24 A u v f) = (@nsum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@nsum A u f))). Qed.
Lemma lem6968250 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term108 A v u f) = (term131 A v u f).
Proof. exact (MK_COMB (@lem6968248 A v u f) (@lem6968249 A v u f)). Qed.
Lemma lem6968252 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6968253 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (@lem6968252 A P Q). Qed.
Lemma lem6968254 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term134 A v u f) = (term135 A v u f).
Proof. exact (@lem6968253 A (term128 A v u f) ((term24 A u v f) = (@nsum A u f))). Qed.
Lemma lem6968255 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term136 A v u f x) = (term126 A v u f x).
Proof. exact (eq_refl (term136 A v u f x)). Qed.
Lemma lem6968256 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term137 A v u f) = (term128 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6968255 A v u f x)). Qed.
Lemma lem6968257 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6968258 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term138 A v u f) = (term129 A v u f).
Proof. exact (MK_COMB (@lem6968257 A) (@lem6968256 A v u f)). Qed.
Lemma lem6968259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968260 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term139 A v u f) = (term130 A v u f).
Proof. exact (MK_COMB (@lem6968259) (@lem6968258 A v u f)). Qed.
Lemma lem6968261 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term24 A u v f) = (@nsum A u f)) = ((term24 A u v f) = (@nsum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@nsum A u f))). Qed.
Lemma lem6968262 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term134 A v u f) = (term131 A v u f).
Proof. exact (MK_COMB (@lem6968260 A v u f) (@lem6968261 A v u f)). Qed.
Lemma lem6968263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6968264 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term140 A v u f) = (term141 A v u f).
Proof. exact (MK_COMB (@lem6968263) (@lem6968262 A v u f)). Qed.
Lemma lem6968265 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term136 A v u f x) = (term126 A v u f x).
Proof. exact (eq_refl (term136 A v u f x)). Qed.
Lemma lem6968266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968267 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term142 A v u f x) = (term143 A v u f x).
Proof. exact (MK_COMB (@lem6968266) (@lem6968265 A v u f x)). Qed.
Lemma lem6968268 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term24 A u v f) = (@nsum A u f)) = ((term24 A u v f) = (@nsum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@nsum A u f))). Qed.
Lemma lem6968269 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term144 A x v u f) = (term145 A x v u f).
Proof. exact (MK_COMB (@lem6968267 A v u f x) (@lem6968268 A v u f)). Qed.
Lemma lem6968270 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term146 A v u f) = (term147 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6968269 A x v u f)). Qed.
Lemma lem6968271 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6968272 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term135 A v u f) = (term148 A v u f).
Proof. exact (MK_COMB (@lem6968271 A) (@lem6968270 A v u f)). Qed.
Lemma lem6968273 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term134 A v u f) = (term135 A v u f)) = ((term131 A v u f) = (term148 A v u f)).
Proof. exact (MK_COMB (@lem6968264 A v u f) (@lem6968272 A v u f)). Qed.
Lemma lem6968274 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term131 A v u f) = (term148 A v u f).
Proof. exact (EQ_MP (@lem6968273 A v u f) (@lem6968254 A v u f)). Qed.
Lemma lem6968275 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term108 A v u f) = (term148 A v u f).
Proof. exact (TRANS (@lem6968250 A v u f) (@lem6968274 A v u f)). Qed.
Lemma lem6968276 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term109 A u f) = (term149 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6968275 A v u f)). Qed.
Lemma lem6968277 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968278 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term110 A u f) = (term150 A u f).
Proof. exact (MK_COMB (@lem6968277 A) (@lem6968276 A u f)). Qed.
Lemma lem6968280 {A B : Type'} (P : type1413 A B) : (term151 A B P) = (term152 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6968281 {A : Type'} (P : type672 A) : (term153 A P) = (term154 A P).
Proof. exact (@lem6968280 (A -> Prop) A P). Qed.
Lemma lem6968282 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term155 A u f) = (term156 A u f).
Proof. exact (@lem6968281 A (term157 A u f)). Qed.
Lemma lem6968283 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term158 A u f v) = (term147 A v u f).
Proof. exact (eq_refl (term158 A u f v)). Qed.
Lemma lem6968284 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6968285 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (x : A) : (term159 A u f v x) = (term160 A v u f x).
Proof. exact (MK_COMB (@lem6968283 A v u f) (@lem6968284 A x)). Qed.
Lemma lem6968286 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term160 A v u f x) = (term145 A x v u f).
Proof. exact (eq_refl (term160 A v u f x)). Qed.
Lemma lem6968287 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term159 A u f v x) = (term145 A x v u f).
Proof. exact (TRANS (@lem6968285 A v u f x) (@lem6968286 A x v u f)). Qed.
Lemma lem6968288 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term161 A u f v) = (term147 A v u f).
Proof. exact (fun_ext (fun x : A => @lem6968287 A x v u f)). Qed.
Lemma lem6968289 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6968290 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term162 A u f v) = (term148 A v u f).
Proof. exact (MK_COMB (@lem6968289 A) (@lem6968288 A v u f)). Qed.
Lemma lem6968291 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term163 A u f) = (term149 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6968290 A v u f)). Qed.
Lemma lem6968292 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968293 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term155 A u f) = (term150 A u f).
Proof. exact (MK_COMB (@lem6968292 A) (@lem6968291 A u f)). Qed.
Lemma lem6968294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6968295 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term164 A u f) = (term165 A u f).
Proof. exact (MK_COMB (@lem6968294) (@lem6968293 A u f)). Qed.
Lemma lem6968296 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term158 A u f v) = (term147 A v u f).
Proof. exact (eq_refl (term158 A u f v)). Qed.
Lemma lem6968297 {A : Type'} (x : type684 A) (v : A -> Prop) : (x v) = (x v).
Proof. exact (eq_refl (x v)). Qed.
Lemma lem6968298 {A : Type'} (u : A -> Prop) (f : A -> nat) (x : type684 A) (v : A -> Prop) : (term166 A u f x v) = (term167 A u f x v).
Proof. exact (MK_COMB (@lem6968296 A v u f) (@lem6968297 A x v)). Qed.
Lemma lem6968299 {A : Type'} (x : type684 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term167 A u f x v) = (term168 A x v u f).
Proof. exact (eq_refl (term167 A u f x v)). Qed.
Lemma lem6968300 {A : Type'} (x : type684 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term166 A u f x v) = (term168 A x v u f).
Proof. exact (TRANS (@lem6968298 A u f x v) (@lem6968299 A x v u f)). Qed.
Lemma lem6968301 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> nat) : (term169 A u f x) = (term170 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6968300 A x v u f)). Qed.
Lemma lem6968302 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968303 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> nat) : (term171 A u f x) = (term172 A x u f).
Proof. exact (MK_COMB (@lem6968302 A) (@lem6968301 A x u f)). Qed.
Lemma lem6968304 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term173 A u f) = (term174 A u f).
Proof. exact (fun_ext (fun x : type684 A => @lem6968303 A x u f)). Qed.
Lemma lem6968305 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6968306 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term156 A u f) = (term175 A u f).
Proof. exact (MK_COMB (@lem6968305 A) (@lem6968304 A u f)). Qed.
Lemma lem6968307 {A : Type'} (u : A -> Prop) (f : A -> nat) : ((term155 A u f) = (term156 A u f)) = ((term150 A u f) = (term175 A u f)).
Proof. exact (MK_COMB (@lem6968295 A u f) (@lem6968306 A u f)). Qed.
Lemma lem6968308 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term150 A u f) = (term175 A u f).
Proof. exact (EQ_MP (@lem6968307 A u f) (@lem6968282 A u f)). Qed.
Lemma lem6968309 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term110 A u f) = (term175 A u f).
Proof. exact (TRANS (@lem6968278 A u f) (@lem6968308 A u f)). Qed.
Lemma lem6968310 {A : Type'} (f : A -> nat) : (term111 A f) = (term176 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6968309 A u f)). Qed.
Lemma lem6968311 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968312 {A : Type'} (f : A -> nat) : (term112 A f) = (term177 A f).
Proof. exact (MK_COMB (@lem6968311 A) (@lem6968310 A f)). Qed.
Lemma lem6968314 {A B : Type'} (P : type1413 A B) : (term151 A B P) = (term152 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6968315 {A : Type'} (P : type597 A) : (term178 A P) = (term179 A P).
Proof. exact (@lem6968314 (A -> Prop) (type684 A) P). Qed.
Lemma lem6968316 {A : Type'} (f : A -> nat) : (term180 A f) = (term181 A f).
Proof. exact (@lem6968315 A (term182 A f)). Qed.
Lemma lem6968317 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term183 A f u) = (term174 A u f).
Proof. exact (eq_refl (term183 A f u)). Qed.
Lemma lem6968318 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6968319 {A : Type'} (u : A -> Prop) (f : A -> nat) (x : type684 A) : (term184 A f u x) = (term185 A u f x).
Proof. exact (MK_COMB (@lem6968317 A u f) (@lem6968318 A x)). Qed.
Lemma lem6968320 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> nat) : (term185 A u f x) = (term172 A x u f).
Proof. exact (eq_refl (term185 A u f x)). Qed.
Lemma lem6968321 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> nat) : (term184 A f u x) = (term172 A x u f).
Proof. exact (TRANS (@lem6968319 A u f x) (@lem6968320 A x u f)). Qed.
Lemma lem6968322 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term186 A f u) = (term174 A u f).
Proof. exact (fun_ext (fun x : type684 A => @lem6968321 A x u f)). Qed.
Lemma lem6968323 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem6968324 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term187 A f u) = (term175 A u f).
Proof. exact (MK_COMB (@lem6968323 A) (@lem6968322 A u f)). Qed.
Lemma lem6968325 {A : Type'} (f : A -> nat) : (term188 A f) = (term176 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6968324 A u f)). Qed.
Lemma lem6968326 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968327 {A : Type'} (f : A -> nat) : (term180 A f) = (term177 A f).
Proof. exact (MK_COMB (@lem6968326 A) (@lem6968325 A f)). Qed.
Lemma lem6968328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6968329 {A : Type'} (f : A -> nat) : (term189 A f) = (term190 A f).
Proof. exact (MK_COMB (@lem6968328) (@lem6968327 A f)). Qed.
Lemma lem6968330 {A : Type'} (u : A -> Prop) (f : A -> nat) : (term183 A f u) = (term174 A u f).
Proof. exact (eq_refl (term183 A f u)). Qed.
Lemma lem6968331 {A : Type'} (x : type638 A) (u : A -> Prop) : (x u) = (x u).
Proof. exact (eq_refl (x u)). Qed.
Lemma lem6968332 {A : Type'} (f : A -> nat) (x : type638 A) (u : A -> Prop) : (term191 A f x u) = (term192 A f x u).
Proof. exact (MK_COMB (@lem6968330 A u f) (@lem6968331 A x u)). Qed.
Lemma lem6968333 {A : Type'} (x : type638 A) (u : A -> Prop) (f : A -> nat) : (term192 A f x u) = (term193 A x u f).
Proof. exact (eq_refl (term192 A f x u)). Qed.
Lemma lem6968334 {A : Type'} (x : type638 A) (u : A -> Prop) (f : A -> nat) : (term191 A f x u) = (term193 A x u f).
Proof. exact (TRANS (@lem6968332 A f x u) (@lem6968333 A x u f)). Qed.
Lemma lem6968335 {A : Type'} (x : type638 A) (f : A -> nat) : (term194 A f x) = (term195 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6968334 A x u f)). Qed.
Lemma lem6968336 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968337 {A : Type'} (x : type638 A) (f : A -> nat) : (term196 A f x) = (term197 A x f).
Proof. exact (MK_COMB (@lem6968336 A) (@lem6968335 A x f)). Qed.
Lemma lem6968338 {A : Type'} (f : A -> nat) : (term198 A f) = (term199 A f).
Proof. exact (fun_ext (fun x : type638 A => @lem6968337 A x f)). Qed.
Lemma lem6968339 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6968340 {A : Type'} (f : A -> nat) : (term181 A f) = (term200 A f).
Proof. exact (MK_COMB (@lem6968339 A) (@lem6968338 A f)). Qed.
Lemma lem6968341 {A : Type'} (f : A -> nat) : ((term180 A f) = (term181 A f)) = ((term177 A f) = (term200 A f)).
Proof. exact (MK_COMB (@lem6968329 A f) (@lem6968340 A f)). Qed.
Lemma lem6968342 {A : Type'} (f : A -> nat) : (term177 A f) = (term200 A f).
Proof. exact (EQ_MP (@lem6968341 A f) (@lem6968316 A f)). Qed.
Lemma lem6968343 {A : Type'} (f : A -> nat) : (term112 A f) = (term200 A f).
Proof. exact (TRANS (@lem6968312 A f) (@lem6968342 A f)). Qed.
Lemma lem6968344 {A : Type'} : (term113 A) = (term201 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6968343 A f)). Qed.
Lemma lem6968345 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6968346 {A : Type'} : (term114 A) = (term202 A).
Proof. exact (MK_COMB (@lem6968345 A) (@lem6968344 A)). Qed.
Lemma lem6968348 {A B : Type'} (P : type1413 A B) : (term151 A B P) = (term152 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6968349 {A : Type'} (P : type689 A) : (term203 A P) = (term204 A P).
Proof. exact (@lem6968348 (A -> nat) (type638 A) P). Qed.
Lemma lem6968350 {A : Type'} : (term205 A) = (term206 A).
Proof. exact (@lem6968349 A (term207 A)). Qed.
Lemma lem6968351 {A : Type'} (f : A -> nat) : (term208 A f) = (term199 A f).
Proof. exact (eq_refl (term208 A f)). Qed.
Lemma lem6968352 {A : Type'} (x : type638 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6968353 {A : Type'} (f : A -> nat) (x : type638 A) : (term209 A f x) = (term210 A f x).
Proof. exact (MK_COMB (@lem6968351 A f) (@lem6968352 A x)). Qed.
Lemma lem6968354 {A : Type'} (x : type638 A) (f : A -> nat) : (term210 A f x) = (term197 A x f).
Proof. exact (eq_refl (term210 A f x)). Qed.
Lemma lem6968355 {A : Type'} (x : type638 A) (f : A -> nat) : (term209 A f x) = (term197 A x f).
Proof. exact (TRANS (@lem6968353 A f x) (@lem6968354 A x f)). Qed.
Lemma lem6968356 {A : Type'} (f : A -> nat) : (term211 A f) = (term199 A f).
Proof. exact (fun_ext (fun x : type638 A => @lem6968355 A x f)). Qed.
Lemma lem6968357 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6968358 {A : Type'} (f : A -> nat) : (term212 A f) = (term200 A f).
Proof. exact (MK_COMB (@lem6968357 A) (@lem6968356 A f)). Qed.
Lemma lem6968359 {A : Type'} : (term213 A) = (term201 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6968358 A f)). Qed.
Lemma lem6968360 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6968361 {A : Type'} : (term205 A) = (term202 A).
Proof. exact (MK_COMB (@lem6968360 A) (@lem6968359 A)). Qed.
Lemma lem6968362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6968363 {A : Type'} : (term214 A) = (term215 A).
Proof. exact (MK_COMB (@lem6968362) (@lem6968361 A)). Qed.
Lemma lem6968364 {A : Type'} (f : A -> nat) : (term208 A f) = (term199 A f).
Proof. exact (eq_refl (term208 A f)). Qed.
Lemma lem6968365 {A : Type'} (x : type693 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem6968366 {A : Type'} (x : type693 A) (f : A -> nat) : (term216 A x f) = (term217 A x f).
Proof. exact (MK_COMB (@lem6968364 A f) (@lem6968365 A x f)). Qed.
Lemma lem6968367 {A : Type'} (x : type693 A) (f : A -> nat) : (term217 A x f) = (term218 A x f).
Proof. exact (eq_refl (term217 A x f)). Qed.
Lemma lem6968368 {A : Type'} (x : type693 A) (f : A -> nat) : (term216 A x f) = (term218 A x f).
Proof. exact (TRANS (@lem6968366 A x f) (@lem6968367 A x f)). Qed.
Lemma lem6968369 {A : Type'} (x : type693 A) : (term219 A x) = (term220 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem6968368 A x f)). Qed.
Lemma lem6968370 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6968371 {A : Type'} (x : type693 A) : (term221 A x) = (term222 A x).
Proof. exact (MK_COMB (@lem6968370 A) (@lem6968369 A x)). Qed.
Lemma lem6968372 {A : Type'} : (term223 A) = (term224 A).
Proof. exact (fun_ext (fun x : type693 A => @lem6968371 A x)). Qed.
Lemma lem6968373 {A : Type'} : (@ex ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem6968374 {A : Type'} : (term206 A) = (term225 A).
Proof. exact (MK_COMB (@lem6968373 A) (@lem6968372 A)). Qed.
Lemma lem6968375 {A : Type'} : ((term205 A) = (term206 A)) = ((term202 A) = (term225 A)).
Proof. exact (MK_COMB (@lem6968363 A) (@lem6968374 A)). Qed.
Lemma lem6968376 {A : Type'} : (term202 A) = (term225 A).
Proof. exact (EQ_MP (@lem6968375 A) (@lem6968350 A)). Qed.
Lemma lem6968378 {A : Type'} : (term114 A) = (term225 A).
Proof. exact (TRANS (@lem6968346 A) (@lem6968376 A)). Qed.
Lemma lem6968379 {A : Type'} : (term11 A) = (term225 A).
Proof. exact (TRANS (@lem6968121 A) (@lem6968378 A)). Qed.
Lemma lem6968380 {A : Type'} (h1 : term11 A) : term225 A.
Proof. exact (EQ_MP (@lem6968379 A) (@lem6967892 A h1)). Qed.
Lemma lem6968381 {A : Type'} (x : type693 A) (h1 : term222 A x) : term222 A x.
Proof. exact (h1). Qed.
Lemma lem6968382 {A : Type'} (f : A -> nat) (h1 : term81 A f) : term81 A f.
Proof. exact (h1). Qed.
Lemma lem6968383 {A : Type'} (u : A -> Prop) (f : A -> nat) (h1 : term74 A u f) : term74 A u f.
Proof. exact (h1). Qed.
Lemma lem6968384 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term64 A u v f.
Proof. exact (h1). Qed.
Lemma lem6968385 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem6968392 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968393 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6968392 (A -> Prop) (type672 A) f x). Qed.
Lemma lem6968394 {A : Type'} (s : A -> Prop) : (@UNION A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s).
Proof. exact (@lem6968393 A (@UNION A) s). Qed.
Lemma lem6968395 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6968396 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t).
Proof. exact (MK_COMB (@lem6968394 A s) (@lem6968395 A t)). Qed.
Lemma lem6968398 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968399 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6968398 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem6968400 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t) = (term226 A s t).
Proof. exact (@lem6968399 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s) t). Qed.
Lemma lem6968402 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term226 A s t).
Proof. exact (TRANS (@lem6968396 A s t) (@lem6968400 A s t)). Qed.
Lemma lem6968409 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968410 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6968409 (A -> Prop) (type672 A) f x). Qed.
Lemma lem6968411 {A : Type'} (t : A -> Prop) : (@UNION A t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t).
Proof. exact (@lem6968410 A (@UNION A) t). Qed.
Lemma lem6968412 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6968413 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@UNION A t s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t s).
Proof. exact (MK_COMB (@lem6968411 A t) (@lem6968412 A s)). Qed.
Lemma lem6968415 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968416 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6968415 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem6968417 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t s) = (term226 A t s).
Proof. exact (@lem6968416 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t) s). Qed.
Lemma lem6968419 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@UNION A t s) = (term226 A t s).
Proof. exact (TRANS (@lem6968413 A t s) (@lem6968417 A t s)). Qed.
Lemma lem6968420 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term227 A s t) = (term228 A s t).
Proof. exact (MK_COMB (@lem6968385 A) (@lem6968402 A s t)). Qed.
Lemma lem6968421 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@UNION A s t) = (@UNION A t s)) = ((term226 A s t) = (term226 A t s)).
Proof. exact (MK_COMB (@lem6968420 A s t) (@lem6968419 A t s)). Qed.
Lemma lem6968422 {A : Type'} (s : A -> Prop) : (term37 A s) = (term229 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6968421 A t s)). Qed.
Lemma lem6968423 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968424 {A : Type'} (s : A -> Prop) : (term38 A s) = (term230 A s).
Proof. exact (MK_COMB (@lem6968423 A) (@lem6968422 A s)). Qed.
Lemma lem6968425 {A : Type'} : (term39 A) = (term231 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6968424 A s)). Qed.
Lemma lem6968426 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968427 {A : Type'} : (term12 A) = (term232 A).
Proof. exact (MK_COMB (@lem6968426 A) (@lem6968425 A)). Qed.
Lemma lem6968428 {A : Type'} (h1 : term12 A) : term232 A.
Proof. exact (EQ_MP (@lem6968427 A) (@lem6968079 A h1)). Qed.
Lemma lem6968429 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6968430 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem6968437 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968438 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6968437 (A -> Prop) (type672 A) f x). Qed.
Lemma lem6968439 {A : Type'} (u : A -> Prop) : (@UNION A u) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u).
Proof. exact (@lem6968438 A (@UNION A) u). Qed.
Lemma lem6968440 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6968441 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@UNION A u v) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u v).
Proof. exact (MK_COMB (@lem6968439 A u) (@lem6968440 A v)). Qed.
Lemma lem6968443 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968444 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6968443 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem6968445 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u v) = (term226 A u v).
Proof. exact (@lem6968444 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u) v). Qed.
Lemma lem6968447 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@UNION A u v) = (term226 A u v).
Proof. exact (TRANS (@lem6968441 A u v) (@lem6968445 A u v)). Qed.
Lemma lem6968448 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6968449 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term233 A u v) = (term234 A u v).
Proof. exact (MK_COMB (@lem6968430 A) (@lem6968447 A u v)). Qed.
Lemma lem6968450 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term24 A u v f) = (term235 A u v f).
Proof. exact (MK_COMB (@lem6968449 A u v) (@lem6968448 A f)). Qed.
Lemma lem6968452 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968453 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6968452 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6968454 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term234 A u v) = (term236 A u v).
Proof. exact (@lem6968453 A (@nsum A) (term226 A u v)). Qed.
Lemma lem6968455 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6968456 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term235 A u v f) = (term237 A u v f).
Proof. exact (MK_COMB (@lem6968454 A u v) (@lem6968455 A f)). Qed.
Lemma lem6968458 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968459 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6968458 (A -> nat) nat f x). Qed.
Lemma lem6968460 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term237 A u v f) = (term238 A u v f).
Proof. exact (@lem6968459 A (term236 A u v) f). Qed.
Lemma lem6968461 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term235 A u v f) = (term238 A u v f).
Proof. exact (TRANS (@lem6968456 A u v f) (@lem6968460 A u v f)). Qed.
Lemma lem6968462 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term24 A u v f) = (term238 A u v f).
Proof. exact (TRANS (@lem6968450 A u v f) (@lem6968461 A u v f)). Qed.
Lemma lem6968469 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968470 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6968469 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6968471 {A : Type'} (u : A -> Prop) : (@nsum A u) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) u).
Proof. exact (@lem6968470 A (@nsum A) u). Qed.
Lemma lem6968472 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6968473 {A : Type'} (u : A -> Prop) (f : A -> nat) : (@nsum A u f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) u f).
Proof. exact (MK_COMB (@lem6968471 A u) (@lem6968472 A f)). Qed.
Lemma lem6968475 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968476 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6968475 (A -> nat) nat f x). Qed.
Lemma lem6968477 {A : Type'} (u : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) u f) = (term239 A u f).
Proof. exact (@lem6968476 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) u) f). Qed.
Lemma lem6968479 {A : Type'} (u : A -> Prop) (f : A -> nat) : (@nsum A u f) = (term239 A u f).
Proof. exact (TRANS (@lem6968473 A u f) (@lem6968477 A u f)). Qed.
Lemma lem6968480 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term240 A u v f) = (term241 A u v f).
Proof. exact (MK_COMB (@lem6968429) (@lem6968462 A u v f)). Qed.
Lemma lem6968481 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term24 A u v f) = (@nsum A u f)) = ((term238 A u v f) = (term239 A u f)).
Proof. exact (MK_COMB (@lem6968480 A u v f) (@lem6968479 A u f)). Qed.
Lemma lem6968482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6968483 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6968484 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6968493 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968494 {A : Type'} (f : type693 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6968493 (A -> nat) (type638 A) f x). Qed.
Lemma lem6968495 {A : Type'} (x : type693 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem6968494 A x f). Qed.
Lemma lem6968496 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6968497 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem6968495 A x f) (@lem6968496 A u)). Qed.
Lemma lem6968499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968500 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6968499 (A -> Prop) (type684 A) f x). Qed.
Lemma lem6968501 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term242 A x f u).
Proof. exact (@lem6968500 A (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem6968502 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (term242 A x f u).
Proof. exact (TRANS (@lem6968497 A x f u) (@lem6968501 A x f u)). Qed.
Lemma lem6968503 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6968504 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term243 A x f u v).
Proof. exact (MK_COMB (@lem6968502 A x f u) (@lem6968503 A v)). Qed.
Lemma lem6968506 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968507 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6968506 (A -> Prop) A f x). Qed.
Lemma lem6968508 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term243 A x f u v) = (term244 A x f u v).
Proof. exact (@lem6968507 A (term242 A x f u) v). Qed.
Lemma lem6968510 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term244 A x f u v).
Proof. exact (TRANS (@lem6968504 A x f u v) (@lem6968508 A x f u v)). Qed.
Lemma lem6968511 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term245 A x f u v) = (term246 A x f u v).
Proof. exact (MK_COMB (@lem6968484 A f) (@lem6968510 A x f u v)). Qed.
Lemma lem6968513 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968514 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6968513 A nat f x). Qed.
Lemma lem6968515 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term246 A x f u v) = (term247 A x f u v).
Proof. exact (@lem6968514 A f (term244 A x f u v)). Qed.
Lemma lem6968516 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term245 A x f u v) = (term247 A x f u v).
Proof. exact (TRANS (@lem6968511 A x f u v) (@lem6968515 A x f u v)). Qed.
Lemma lem6968521 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968522 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6968521 nat nat f x). Qed.
Lemma lem6968524 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6968522 NUMERAL 0). Qed.
Lemma lem6968525 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term248 A x f u v) = (term249 A x f u v).
Proof. exact (MK_COMB (@lem6968483) (@lem6968516 A x f u v)). Qed.
Lemma lem6968526 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : ((term245 A x f u v) = (NUMERAL 0)) = ((term247 A x f u v) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem6968525 A x f u v) (@lem6968524)). Qed.
Lemma lem6968527 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term250 A x f u v) = (term251 A x f u v).
Proof. exact (MK_COMB (@lem6968482) (@lem6968526 A x f u v)). Qed.
Lemma lem6968528 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6968529 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem6968538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968539 {A : Type'} (f : type693 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6968538 (A -> nat) (type638 A) f x). Qed.
Lemma lem6968540 {A : Type'} (x : type693 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem6968539 A x f). Qed.
Lemma lem6968541 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6968542 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem6968540 A x f) (@lem6968541 A u)). Qed.
Lemma lem6968544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968545 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6968544 (A -> Prop) (type684 A) f x). Qed.
Lemma lem6968546 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term242 A x f u).
Proof. exact (@lem6968545 A (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem6968547 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (term242 A x f u).
Proof. exact (TRANS (@lem6968542 A x f u) (@lem6968546 A x f u)). Qed.
Lemma lem6968548 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6968549 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term243 A x f u v).
Proof. exact (MK_COMB (@lem6968547 A x f u) (@lem6968548 A v)). Qed.
Lemma lem6968551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968552 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6968551 (A -> Prop) A f x). Qed.
Lemma lem6968553 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term243 A x f u v) = (term244 A x f u v).
Proof. exact (@lem6968552 A (term242 A x f u) v). Qed.
Lemma lem6968555 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term244 A x f u v).
Proof. exact (TRANS (@lem6968549 A x f u v) (@lem6968553 A x f u v)). Qed.
Lemma lem6968556 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6968557 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term252 A x f u v) = (term253 A x f u v).
Proof. exact (MK_COMB (@lem6968529 A) (@lem6968555 A x f u v)). Qed.
Lemma lem6968558 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term254 A x f v u) = (term255 A x f v u).
Proof. exact (MK_COMB (@lem6968557 A x f u v) (@lem6968556 A u)). Qed.
Lemma lem6968560 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968561 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6968560 A (type686 A) f x). Qed.
Lemma lem6968562 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term253 A x f u v) = (term256 A x f u v).
Proof. exact (@lem6968561 A (@IN A) (term244 A x f u v)). Qed.
Lemma lem6968563 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6968564 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term255 A x f v u) = (term257 A x f v u).
Proof. exact (MK_COMB (@lem6968562 A x f u v) (@lem6968563 A u)). Qed.
Lemma lem6968566 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968567 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6968566 (A -> Prop) Prop f x). Qed.
Lemma lem6968568 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term257 A x f v u) = (term258 A x f v u).
Proof. exact (@lem6968567 A (term256 A x f u v) u). Qed.
Lemma lem6968569 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term255 A x f v u) = (term258 A x f v u).
Proof. exact (TRANS (@lem6968564 A x f v u) (@lem6968568 A x f v u)). Qed.
Lemma lem6968570 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term254 A x f v u) = (term258 A x f v u).
Proof. exact (TRANS (@lem6968558 A x f v u) (@lem6968569 A x f v u)). Qed.
Lemma lem6968571 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term259 A x f v u) = (term260 A x f v u).
Proof. exact (MK_COMB (@lem6968528) (@lem6968570 A x f v u)). Qed.
Lemma lem6968572 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem6968581 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968582 {A : Type'} (f : type693 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6968581 (A -> nat) (type638 A) f x). Qed.
Lemma lem6968583 {A : Type'} (x : type693 A) (f : A -> nat) : (x f) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem6968582 A x f). Qed.
Lemma lem6968584 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6968585 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem6968583 A x f) (@lem6968584 A u)). Qed.
Lemma lem6968587 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968588 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem6968587 (A -> Prop) (type684 A) f x). Qed.
Lemma lem6968589 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term242 A x f u).
Proof. exact (@lem6968588 A (@I ((A -> nat) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem6968590 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) : (x f u) = (term242 A x f u).
Proof. exact (TRANS (@lem6968585 A x f u) (@lem6968589 A x f u)). Qed.
Lemma lem6968591 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6968592 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term243 A x f u v).
Proof. exact (MK_COMB (@lem6968590 A x f u) (@lem6968591 A v)). Qed.
Lemma lem6968594 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968595 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem6968594 (A -> Prop) A f x). Qed.
Lemma lem6968596 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term243 A x f u v) = (term244 A x f u v).
Proof. exact (@lem6968595 A (term242 A x f u) v). Qed.
Lemma lem6968598 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term244 A x f u v).
Proof. exact (TRANS (@lem6968592 A x f u v) (@lem6968596 A x f u v)). Qed.
Lemma lem6968599 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6968600 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term252 A x f u v) = (term253 A x f u v).
Proof. exact (MK_COMB (@lem6968572 A) (@lem6968598 A x f u v)). Qed.
Lemma lem6968601 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term261 A x f u v) = (term262 A x f u v).
Proof. exact (MK_COMB (@lem6968600 A x f u v) (@lem6968599 A v)). Qed.
Lemma lem6968603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968604 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6968603 A (type686 A) f x). Qed.
Lemma lem6968605 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term253 A x f u v) = (term256 A x f u v).
Proof. exact (@lem6968604 A (@IN A) (term244 A x f u v)). Qed.
Lemma lem6968606 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6968607 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term262 A x f u v) = (term263 A x f u v).
Proof. exact (MK_COMB (@lem6968605 A x f u v) (@lem6968606 A v)). Qed.
Lemma lem6968609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968610 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6968609 (A -> Prop) Prop f x). Qed.
Lemma lem6968611 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term263 A x f u v) = (term264 A x f u v).
Proof. exact (@lem6968610 A (term256 A x f u v) v). Qed.
Lemma lem6968612 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term262 A x f u v) = (term264 A x f u v).
Proof. exact (TRANS (@lem6968607 A x f u v) (@lem6968611 A x f u v)). Qed.
Lemma lem6968613 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term261 A x f u v) = (term264 A x f u v).
Proof. exact (TRANS (@lem6968601 A x f u v) (@lem6968612 A x f u v)). Qed.
Lemma lem6968614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6968615 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term265 A x f u v) = (term266 A x f u v).
Proof. exact (MK_COMB (@lem6968614) (@lem6968613 A x f u v)). Qed.
Lemma lem6968616 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term267 A x f v u) = (term268 A x f v u).
Proof. exact (MK_COMB (@lem6968615 A x f u v) (@lem6968571 A x f v u)). Qed.
Lemma lem6968617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6968618 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term269 A x f v u) = (term270 A x f v u).
Proof. exact (MK_COMB (@lem6968617) (@lem6968616 A x f v u)). Qed.
Lemma lem6968619 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term271 A x f u v) = (term272 A x f u v).
Proof. exact (MK_COMB (@lem6968618 A x f v u) (@lem6968527 A x f u v)). Qed.
Lemma lem6968620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6968625 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968626 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6968625 (A -> Prop) Prop f x). Qed.
Lemma lem6968628 {A : Type'} (u : A -> Prop) : (@FINITE A u) = (@I ((A -> Prop) -> Prop) (@FINITE A) u).
Proof. exact (@lem6968626 A (@FINITE A) u). Qed.
Lemma lem6968629 {A : Type'} (u : A -> Prop) : (term119 A u) = (term273 A u).
Proof. exact (MK_COMB (@lem6968620) (@lem6968628 A u)). Qed.
Lemma lem6968630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968631 {A : Type'} (u : A -> Prop) : (term101 A u) = (term274 A u).
Proof. exact (MK_COMB (@lem6968630) (@lem6968629 A u)). Qed.
Lemma lem6968632 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term275 A x f u v) = (term276 A x f u v).
Proof. exact (MK_COMB (@lem6968631 A u) (@lem6968619 A x f u v)). Qed.
Lemma lem6968633 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968634 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term277 A x f u v) = (term278 A x f u v).
Proof. exact (MK_COMB (@lem6968633) (@lem6968632 A x f u v)). Qed.
Lemma lem6968635 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term279 A x v u f) = (term280 A x v u f).
Proof. exact (MK_COMB (@lem6968634 A x f u v) (@lem6968481 A v u f)). Qed.
Lemma lem6968636 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) : (term281 A x u f) = (term282 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6968635 A x v u f)). Qed.
Lemma lem6968637 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968638 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) : (term283 A x u f) = (term284 A x u f).
Proof. exact (MK_COMB (@lem6968637 A) (@lem6968636 A x u f)). Qed.
Lemma lem6968639 {A : Type'} (x : type693 A) (f : A -> nat) : (term285 A x f) = (term286 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6968638 A x u f)). Qed.
Lemma lem6968640 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968641 {A : Type'} (x : type693 A) (f : A -> nat) : (term218 A x f) = (term287 A x f).
Proof. exact (MK_COMB (@lem6968640 A) (@lem6968639 A x f)). Qed.
Lemma lem6968642 {A : Type'} (x : type693 A) : (term220 A x) = (term288 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem6968641 A x f)). Qed.
Lemma lem6968643 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6968644 {A : Type'} (x : type693 A) : (term222 A x) = (term289 A x).
Proof. exact (MK_COMB (@lem6968643 A) (@lem6968642 A x)). Qed.
Lemma lem6968645 {A : Type'} (x : type693 A) (h1 : term222 A x) : term289 A x.
Proof. exact (EQ_MP (@lem6968644 A x) (@lem6968381 A x h1)). Qed.
Lemma lem6968646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6968647 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6968648 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem6968655 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968656 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6968655 (A -> Prop) (type672 A) f x). Qed.
Lemma lem6968657 {A : Type'} (u : A -> Prop) : (@UNION A u) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u).
Proof. exact (@lem6968656 A (@UNION A) u). Qed.
Lemma lem6968658 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6968659 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@UNION A u v) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u v).
Proof. exact (MK_COMB (@lem6968657 A u) (@lem6968658 A v)). Qed.
Lemma lem6968661 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968662 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6968661 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem6968663 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u v) = (term226 A u v).
Proof. exact (@lem6968662 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u) v). Qed.
Lemma lem6968665 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@UNION A u v) = (term226 A u v).
Proof. exact (TRANS (@lem6968659 A u v) (@lem6968663 A u v)). Qed.
Lemma lem6968666 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6968667 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term233 A u v) = (term234 A u v).
Proof. exact (MK_COMB (@lem6968648 A) (@lem6968665 A u v)). Qed.
Lemma lem6968668 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term24 A u v f) = (term235 A u v f).
Proof. exact (MK_COMB (@lem6968667 A u v) (@lem6968666 A f)). Qed.
Lemma lem6968670 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968671 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6968670 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6968672 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term234 A u v) = (term236 A u v).
Proof. exact (@lem6968671 A (@nsum A) (term226 A u v)). Qed.
Lemma lem6968673 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6968674 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term235 A u v f) = (term237 A u v f).
Proof. exact (MK_COMB (@lem6968672 A u v) (@lem6968673 A f)). Qed.
Lemma lem6968676 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968677 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6968676 (A -> nat) nat f x). Qed.
Lemma lem6968678 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term237 A u v f) = (term238 A u v f).
Proof. exact (@lem6968677 A (term236 A u v) f). Qed.
Lemma lem6968679 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term235 A u v f) = (term238 A u v f).
Proof. exact (TRANS (@lem6968674 A u v f) (@lem6968678 A u v f)). Qed.
Lemma lem6968680 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term24 A u v f) = (term238 A u v f).
Proof. exact (TRANS (@lem6968668 A u v f) (@lem6968679 A u v f)). Qed.
Lemma lem6968687 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968688 {A : Type'} (f : type644 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> nat) -> nat) f x).
Proof. exact (@lem6968687 (A -> Prop) (type705 A) f x). Qed.
Lemma lem6968689 {A : Type'} (v : A -> Prop) : (@nsum A v) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) v).
Proof. exact (@lem6968688 A (@nsum A) v). Qed.
Lemma lem6968690 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6968691 {A : Type'} (v : A -> Prop) (f : A -> nat) : (@nsum A v f) = (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) v f).
Proof. exact (MK_COMB (@lem6968689 A v) (@lem6968690 A f)). Qed.
Lemma lem6968693 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968694 {A : Type'} (f : type705 A) (x : A -> nat) : (f x) = (@I ((A -> nat) -> nat) f x).
Proof. exact (@lem6968693 (A -> nat) nat f x). Qed.
Lemma lem6968695 {A : Type'} (v : A -> Prop) (f : A -> nat) : (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) v f) = (term239 A v f).
Proof. exact (@lem6968694 A (@I ((A -> Prop) -> (A -> nat) -> nat) (@nsum A) v) f). Qed.
Lemma lem6968697 {A : Type'} (v : A -> Prop) (f : A -> nat) : (@nsum A v f) = (term239 A v f).
Proof. exact (TRANS (@lem6968691 A v f) (@lem6968695 A v f)). Qed.
Lemma lem6968698 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term240 A u v f) = (term241 A u v f).
Proof. exact (MK_COMB (@lem6968647) (@lem6968680 A u v f)). Qed.
Lemma lem6968699 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : ((term24 A u v f) = (@nsum A v f)) = ((term238 A u v f) = (term239 A v f)).
Proof. exact (MK_COMB (@lem6968698 A u v f) (@lem6968697 A v f)). Qed.
Lemma lem6968700 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term60 A u v f) = (term290 A u v f).
Proof. exact (MK_COMB (@lem6968646) (@lem6968699 A u v f)). Qed.
Lemma lem6968701 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6968706 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968708 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem6968706 A nat f x). Qed.
Lemma lem6968713 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968714 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6968713 nat nat f x). Qed.
Lemma lem6968716 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem6968714 NUMERAL 0). Qed.
Lemma lem6968717 {A : Type'} (f : A -> nat) (x : A) : (term291 A f x) = (term292 A f x).
Proof. exact (MK_COMB (@lem6968701) (@lem6968708 A f x)). Qed.
Lemma lem6968718 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem6968717 A f x) (@lem6968716)). Qed.
Lemma lem6968725 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968726 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6968725 A (type686 A) f x). Qed.
Lemma lem6968727 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem6968726 A (@IN A) x). Qed.
Lemma lem6968728 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem6968729 {A : Type'} (x : A) (v : A -> Prop) : (@IN A x v) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x v).
Proof. exact (MK_COMB (@lem6968727 A x) (@lem6968728 A v)). Qed.
Lemma lem6968731 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968732 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6968731 (A -> Prop) Prop f x). Qed.
Lemma lem6968733 {A : Type'} (x : A) (v : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x v) = (term293 A x v).
Proof. exact (@lem6968732 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) v). Qed.
Lemma lem6968735 {A : Type'} (x : A) (v : A -> Prop) : (@IN A x v) = (term293 A x v).
Proof. exact (TRANS (@lem6968729 A x v) (@lem6968733 A x v)). Qed.
Lemma lem6968736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6968743 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968744 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6968743 A (type686 A) f x). Qed.
Lemma lem6968745 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem6968744 A (@IN A) x). Qed.
Lemma lem6968746 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem6968747 {A : Type'} (x : A) (u : A -> Prop) : (@IN A x u) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x u).
Proof. exact (MK_COMB (@lem6968745 A x) (@lem6968746 A u)). Qed.
Lemma lem6968749 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968750 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6968749 (A -> Prop) Prop f x). Qed.
Lemma lem6968751 {A : Type'} (x : A) (u : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x u) = (term293 A x u).
Proof. exact (@lem6968750 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) u). Qed.
Lemma lem6968753 {A : Type'} (x : A) (u : A -> Prop) : (@IN A x u) = (term293 A x u).
Proof. exact (TRANS (@lem6968747 A x u) (@lem6968751 A x u)). Qed.
Lemma lem6968754 {A : Type'} (x : A) (u : A -> Prop) : (term51 A x u) = (term294 A x u).
Proof. exact (MK_COMB (@lem6968736) (@lem6968753 A x u)). Qed.
Lemma lem6968755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968756 {A : Type'} (x : A) (u : A -> Prop) : (term47 A x u) = (term295 A x u).
Proof. exact (MK_COMB (@lem6968755) (@lem6968754 A x u)). Qed.
Lemma lem6968757 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term49 A u x v) = (term296 A u x v).
Proof. exact (MK_COMB (@lem6968756 A x u) (@lem6968735 A x v)). Qed.
Lemma lem6968758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968759 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term53 A u x v) = (term297 A u x v).
Proof. exact (MK_COMB (@lem6968758) (@lem6968757 A u x v)). Qed.
Lemma lem6968760 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) : (term55 A u v f x) = (term298 A u v f x).
Proof. exact (MK_COMB (@lem6968759 A u x v) (@lem6968718 A f x)). Qed.
Lemma lem6968761 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term57 A u v f) = (term299 A u v f).
Proof. exact (fun_ext (fun x : A => @lem6968760 A u v f x)). Qed.
Lemma lem6968762 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6968763 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term58 A u v f) = (term300 A u v f).
Proof. exact (MK_COMB (@lem6968762 A) (@lem6968761 A u v f)). Qed.
Lemma lem6968768 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6968769 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6968768 (A -> Prop) Prop f x). Qed.
Lemma lem6968771 {A : Type'} (v : A -> Prop) : (@FINITE A v) = (@I ((A -> Prop) -> Prop) (@FINITE A) v).
Proof. exact (@lem6968769 A (@FINITE A) v). Qed.
Lemma lem6968772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6968773 {A : Type'} (v : A -> Prop) : (term28 A v) = (term301 A v).
Proof. exact (MK_COMB (@lem6968772) (@lem6968771 A v)). Qed.
Lemma lem6968774 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term59 A u v f) = (term302 A u v f).
Proof. exact (MK_COMB (@lem6968773 A v) (@lem6968763 A u v f)). Qed.
Lemma lem6968775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6968776 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term62 A u v f) = (term303 A u v f).
Proof. exact (MK_COMB (@lem6968775) (@lem6968774 A u v f)). Qed.
Lemma lem6968777 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term64 A u v f) = (term304 A u v f).
Proof. exact (MK_COMB (@lem6968776 A u v f) (@lem6968700 A u v f)). Qed.
Lemma lem6968778 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term304 A u v f.
Proof. exact (EQ_MP (@lem6968777 A u v f) (@lem6968384 A u v f h1)). Qed.
Lemma lem6968780 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term302 A u v f.
Proof. exact (proj1 (@lem6968778 A u v f h1)). Qed.
Lemma lem6968781 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term300 A u v f.
Proof. exact (proj2 (@lem6968780 A u v f h1)). Qed.
Lemma lem6968784 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term226 A s t) = (term226 A t s)) = ((term226 A s t) = (term226 A t s)).
Proof. exact (eq_refl ((term226 A s t) = (term226 A t s))). Qed.
Lemma lem6968785 {A : Type'} (s : A -> Prop) : (term229 A s) = (term229 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6968784 A t s)). Qed.
Lemma lem6968786 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968787 {A : Type'} (s : A -> Prop) : (term230 A s) = (term230 A s).
Proof. exact (MK_COMB (@lem6968786 A) (@lem6968785 A s)). Qed.
Lemma lem6968788 {A : Type'} : (term231 A) = (term231 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6968787 A s)). Qed.
Lemma lem6968789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968791 {A : Type'} : (term232 A) = (term232 A).
Proof. exact (MK_COMB (@lem6968789 A) (@lem6968788 A)). Qed.
Lemma lem6968792 {A : Type'} (h1 : term12 A) : term232 A.
Proof. exact (EQ_MP (@lem6968791 A) (@lem6968428 A h1)). Qed.
Lemma lem6968794 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : ((term238 A u v f) = (term239 A u f)) = ((term238 A u v f) = (term239 A u f)).
Proof. exact (eq_refl ((term238 A u v f) = (term239 A u f))). Qed.
Lemma lem6968808 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term276 A x f u v) = (term305 A x f u v).
Proof. exact (@lem19490 (term268 A x f v u) (term273 A u) (term251 A x f u v)). Qed.
Lemma lem6968809 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term306 A x f u v) = (term306 A x f u v).
Proof. exact (eq_refl (term306 A x f u v)). Qed.
Lemma lem6968816 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term307 A x f v u) = (term308 A x f v u).
Proof. exact (@lem19490 (term264 A x f u v) (term273 A u) (term260 A x f v u)). Qed.
Lemma lem6968817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6968818 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term309 A x f v u) = (term310 A x f v u).
Proof. exact (MK_COMB (@lem6968817) (@lem6968816 A x f v u)). Qed.
Lemma lem6968819 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term305 A x f u v) = (term311 A x f u v).
Proof. exact (MK_COMB (@lem6968818 A x f v u) (@lem6968809 A x f u v)). Qed.
Lemma lem6968821 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term276 A x f u v) = (term311 A x f u v).
Proof. exact (TRANS (@lem6968808 A x f u v) (@lem6968819 A x f u v)). Qed.
Lemma lem6968822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6968823 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term278 A x f u v) = (term312 A x f u v).
Proof. exact (MK_COMB (@lem6968822) (@lem6968821 A x f u v)). Qed.
Lemma lem6968824 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term280 A x v u f) = (term313 A x v u f).
Proof. exact (MK_COMB (@lem6968823 A x f u v) (@lem6968794 A v u f)). Qed.
Lemma lem6968825 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term313 A x v u f) = (term314 A x v u f).
Proof. exact (@lem19699 (term308 A x f v u) (term306 A x f u v) ((term238 A u v f) = (term239 A u f))). Qed.
Lemma lem6968826 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term315 A x v u f) = (term315 A x v u f).
Proof. exact (eq_refl (term315 A x v u f)). Qed.
Lemma lem6968833 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term316 A x v u f) = (term317 A x v u f).
Proof. exact (@lem19699 (term318 A x f u v) (term319 A x f v u) ((term238 A u v f) = (term239 A u f))). Qed.
Lemma lem6968834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6968835 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term320 A x v u f) = (term321 A x v u f).
Proof. exact (MK_COMB (@lem6968834) (@lem6968833 A x v u f)). Qed.
Lemma lem6968836 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term314 A x v u f) = (term322 A x v u f).
Proof. exact (MK_COMB (@lem6968835 A x v u f) (@lem6968826 A x v u f)). Qed.
Lemma lem6968837 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term313 A x v u f) = (term322 A x v u f).
Proof. exact (TRANS (@lem6968825 A x v u f) (@lem6968836 A x v u f)). Qed.
Lemma lem6968838 {A : Type'} (x : type693 A) (v : A -> Prop) (u : A -> Prop) (f : A -> nat) : (term280 A x v u f) = (term322 A x v u f).
Proof. exact (TRANS (@lem6968824 A x v u f) (@lem6968837 A x v u f)). Qed.
Lemma lem6968839 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) : (term282 A x u f) = (term323 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem6968838 A x v u f)). Qed.
Lemma lem6968840 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968841 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) : (term284 A x u f) = (term324 A x u f).
Proof. exact (MK_COMB (@lem6968840 A) (@lem6968839 A x u f)). Qed.
Lemma lem6968842 {A : Type'} (x : type693 A) (f : A -> nat) : (term286 A x f) = (term325 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem6968841 A x u f)). Qed.
Lemma lem6968843 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6968844 {A : Type'} (x : type693 A) (f : A -> nat) : (term287 A x f) = (term326 A x f).
Proof. exact (MK_COMB (@lem6968843 A) (@lem6968842 A x f)). Qed.
Lemma lem6968845 {A : Type'} (x : type693 A) : (term288 A x) = (term327 A x).
Proof. exact (fun_ext (fun f : A -> nat => @lem6968844 A x f)). Qed.
Lemma lem6968846 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6968848 {A : Type'} (x : type693 A) : (term289 A x) = (term328 A x).
Proof. exact (MK_COMB (@lem6968846 A) (@lem6968845 A x)). Qed.
Lemma lem6968849 {A : Type'} (x : type693 A) (h1 : term222 A x) : term328 A x.
Proof. exact (EQ_MP (@lem6968848 A x) (@lem6968645 A x h1)). Qed.
Lemma lem6968871 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : A) : (term298 A u v f x) = (term298 A u v f x).
Proof. exact (eq_refl (term298 A u v f x)). Qed.
Lemma lem6968872 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term299 A u v f) = (term299 A u v f).
Proof. exact (fun_ext (fun x : A => @lem6968871 A u v f x)). Qed.
Lemma lem6968873 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6968875 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term300 A u v f) = (term300 A u v f).
Proof. exact (MK_COMB (@lem6968873 A) (@lem6968872 A u v f)). Qed.
Lemma lem6968876 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term300 A u v f.
Proof. exact (EQ_MP (@lem6968875 A u v f) (@lem6968781 A u v f h1)). Qed.
Lemma lem6968877 {A : Type'} (_92824 : A -> Prop) (h1 : term12 A) : term329 A _92824.
Proof. exact (@lem6968792 A h1 _92824). Qed.
Lemma lem6968878 {A : Type'} (_92824 : A -> Prop) : (term329 A _92824) = (term230 A _92824).
Proof. exact (eq_refl (term329 A _92824)). Qed.
Lemma lem6968879 {A : Type'} (_92824 : A -> Prop) (h1 : term12 A) : term230 A _92824.
Proof. exact (EQ_MP (@lem6968878 A _92824) (@lem6968877 A _92824 h1)). Qed.
Lemma lem6968880 {A : Type'} (_92824 : A -> Prop) (_92825 : A -> Prop) (h1 : term12 A) : term330 A _92824 _92825.
Proof. exact (@lem6968879 A _92824 h1 _92825). Qed.
Lemma lem6968881 {A : Type'} (_92825 : A -> Prop) (_92824 : A -> Prop) : (term330 A _92824 _92825) = ((term226 A _92824 _92825) = (term226 A _92825 _92824)).
Proof. exact (eq_refl (term330 A _92824 _92825)). Qed.
Lemma lem6968883 {A : Type'} (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term331 A x _92826.
Proof. exact (@lem6968849 A x h1 _92826). Qed.
Lemma lem6968884 {A : Type'} (x : type693 A) (_92826 : A -> nat) : (term331 A x _92826) = (term326 A x _92826).
Proof. exact (eq_refl (term331 A x _92826)). Qed.
Lemma lem6968885 {A : Type'} (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term326 A x _92826.
Proof. exact (EQ_MP (@lem6968884 A x _92826) (@lem6968883 A _92826 x h1)). Qed.
Lemma lem6968886 {A : Type'} (_92826 : A -> nat) (_92827 : A -> Prop) (x : type693 A) (h1 : term222 A x) : term332 A x _92826 _92827.
Proof. exact (@lem6968885 A _92826 x h1 _92827). Qed.
Lemma lem6968887 {A : Type'} (x : type693 A) (_92827 : A -> Prop) (_92826 : A -> nat) : (term332 A x _92826 _92827) = (term324 A x _92827 _92826).
Proof. exact (eq_refl (term332 A x _92826 _92827)). Qed.
Lemma lem6968888 {A : Type'} (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term324 A x _92827 _92826.
Proof. exact (EQ_MP (@lem6968887 A x _92827 _92826) (@lem6968886 A _92826 _92827 x h1)). Qed.
Lemma lem6968889 {A : Type'} (_92827 : A -> Prop) (_92826 : A -> nat) (_92828 : A -> Prop) (x : type693 A) (h1 : term222 A x) : term333 A x _92827 _92826 _92828.
Proof. exact (@lem6968888 A _92827 _92826 x h1 _92828). Qed.
Lemma lem6968890 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term333 A x _92827 _92826 _92828) = (term322 A x _92828 _92827 _92826).
Proof. exact (eq_refl (term333 A x _92827 _92826 _92828)). Qed.
Lemma lem6968891 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term322 A x _92828 _92827 _92826.
Proof. exact (EQ_MP (@lem6968890 A x _92828 _92827 _92826) (@lem6968889 A _92827 _92826 _92828 x h1)). Qed.
Lemma lem6968892 {A : Type'} (_92829 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term334 A u v f _92829.
Proof. exact (@lem6968876 A u v f h1 _92829). Qed.
Lemma lem6968893 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (_92829 : A) : (term334 A u v f _92829) = (term298 A u v f _92829).
Proof. exact (eq_refl (term334 A u v f _92829)). Qed.
Lemma lem6968894 {A : Type'} (_92829 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term298 A u v f _92829.
Proof. exact (EQ_MP (@lem6968893 A u v f _92829) (@lem6968892 A _92829 u v f h1)). Qed.
Lemma lem6968895 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term315 A x _92828 _92827 _92826.
Proof. exact (proj2 (@lem6968891 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6968896 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term317 A x _92828 _92827 _92826.
Proof. exact (proj1 (@lem6968891 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6968897 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term335 A x _92828 _92827 _92826.
Proof. exact (proj2 (@lem6968896 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6968898 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term336 A x _92828 _92827 _92826.
Proof. exact (proj1 (@lem6968896 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6968902 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term290 A u v f.
Proof. exact (proj2 (@lem6968778 A u v f h1)). Qed.
Lemma lem6968915 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (_92829 : A) : (term298 A u v f _92829) = (term337 A u v f _92829).
Proof. exact (@lem6967625 (term294 A _92829 u) (term293 A _92829 v) ((@I (A -> nat) f _92829) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6968916 {A : Type'} (_92829 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term337 A u v f _92829.
Proof. exact (EQ_MP (@lem6968915 A u v f _92829) (@lem6968894 A _92829 u v f h1)). Qed.
Lemma lem6968927 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term315 A x _92828 _92827 _92826) = (term338 A x _92828 _92827 _92826).
Proof. exact (@lem6967625 (term273 A _92827) (term251 A x _92826 _92827 _92828) ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6968928 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term338 A x _92828 _92827 _92826.
Proof. exact (EQ_MP (@lem6968927 A x _92828 _92827 _92826) (@lem6968895 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6968939 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term336 A x _92828 _92827 _92826) = (term339 A x _92828 _92827 _92826).
Proof. exact (@lem6967625 (term273 A _92827) (term264 A x _92826 _92827 _92828) ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6968940 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term339 A x _92828 _92827 _92826.
Proof. exact (EQ_MP (@lem6968939 A x _92828 _92827 _92826) (@lem6968898 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6968951 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term335 A x _92828 _92827 _92826) = (term340 A x _92828 _92827 _92826).
Proof. exact (@lem6967625 (term273 A _92827) (term260 A x _92826 _92828 _92827) ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6968952 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term340 A x _92828 _92827 _92826.
Proof. exact (EQ_MP (@lem6968951 A x _92828 _92827 _92826) (@lem6968897 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6969062 {A : Type'} : (@I ((A -> Prop) -> (A -> nat) -> nat)) = (@I ((A -> Prop) -> (A -> nat) -> nat)).
Proof. exact (eq_refl (@I ((A -> Prop) -> (A -> nat) -> nat))). Qed.
Lemma lem6969063 {A : Type'} (_92858 : type644 A) (_92860 : type644 A) (h1 : _92858 = _92860) : _92858 = _92860.
Proof. exact (h1). Qed.
Lemma lem6969064 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (h1 : _92859 = _92861) : _92859 = _92861.
Proof. exact (h1). Qed.
Lemma lem6969065 {A : Type'} (_92858 : type644 A) (_92860 : type644 A) (h1 : _92858 = _92860) : (@I ((A -> Prop) -> (A -> nat) -> nat) _92858) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860).
Proof. exact (MK_COMB (@lem6969062 A) (@lem6969063 A _92858 _92860 h1)). Qed.
Lemma lem6969066 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) (h1 : _92859 = _92861) (h2 : _92858 = _92860) : (@I ((A -> Prop) -> (A -> nat) -> nat) _92858 _92859) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860 _92861).
Proof. exact (MK_COMB (@lem6969065 A _92858 _92860 h2) (@lem6969064 A _92859 _92861 h1)). Qed.
Lemma lem6969067 {A : Type'} (_92858 : type644 A) (_92860 : type644 A) (_92859 : A -> Prop) (_92861 : A -> Prop) (h1 : _92859 = _92861) : term341 A _92858 _92859 _92860 _92861.
Proof. exact (fun h0 : _92858 = _92860 => @lem6969066 A _92859 _92861 _92858 _92860 h1 h0). Qed.
Lemma lem6969069 (a : Prop) (b : Prop) : (a -> b) = (term342 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6969070 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : (term341 A _92858 _92859 _92860 _92861) = (term343 A _92858 _92859 _92860 _92861).
Proof. exact (@lem6969069 (_92858 = _92860) ((@I ((A -> Prop) -> (A -> nat) -> nat) _92858 _92859) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860 _92861))). Qed.
Lemma lem6969071 {A : Type'} (_92858 : type644 A) (_92860 : type644 A) (_92859 : A -> Prop) (_92861 : A -> Prop) (h1 : _92859 = _92861) : term343 A _92858 _92859 _92860 _92861.
Proof. exact (EQ_MP (@lem6969070 A _92858 _92859 _92860 _92861) (@lem6969067 A _92858 _92860 _92859 _92861 h1)). Qed.
Lemma lem6969072 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : term344 A _92858 _92859 _92860 _92861.
Proof. exact (fun h0 : _92859 = _92861 => @lem6969071 A _92858 _92860 _92859 _92861 h0). Qed.
Lemma lem6969074 (a : Prop) (b : Prop) : (a -> b) = (term342 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6969075 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : (term344 A _92858 _92859 _92860 _92861) = (term345 A _92858 _92859 _92860 _92861).
Proof. exact (@lem6969074 (_92859 = _92861) (term343 A _92858 _92859 _92860 _92861)). Qed.
Lemma lem6969076 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : term345 A _92858 _92859 _92860 _92861.
Proof. exact (EQ_MP (@lem6969075 A _92858 _92859 _92860 _92861) (@lem6969072 A _92858 _92859 _92860 _92861)). Qed.
Lemma lem6969077 {A : Type'} : (@I ((A -> nat) -> nat)) = (@I ((A -> nat) -> nat)).
Proof. exact (eq_refl (@I ((A -> nat) -> nat))). Qed.
Lemma lem6969078 {A : Type'} (_92862 : type705 A) (_92864 : type705 A) (h1 : _92862 = _92864) : _92862 = _92864.
Proof. exact (h1). Qed.
Lemma lem6969079 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (h1 : _92863 = _92865) : _92863 = _92865.
Proof. exact (h1). Qed.
Lemma lem6969080 {A : Type'} (_92862 : type705 A) (_92864 : type705 A) (h1 : _92862 = _92864) : (@I ((A -> nat) -> nat) _92862) = (@I ((A -> nat) -> nat) _92864).
Proof. exact (MK_COMB (@lem6969077 A) (@lem6969078 A _92862 _92864 h1)). Qed.
Lemma lem6969081 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) (h1 : _92863 = _92865) (h2 : _92862 = _92864) : (@I ((A -> nat) -> nat) _92862 _92863) = (@I ((A -> nat) -> nat) _92864 _92865).
Proof. exact (MK_COMB (@lem6969080 A _92862 _92864 h2) (@lem6969079 A _92863 _92865 h1)). Qed.
Lemma lem6969082 {A : Type'} (_92862 : type705 A) (_92864 : type705 A) (_92863 : A -> nat) (_92865 : A -> nat) (h1 : _92863 = _92865) : term346 A _92862 _92863 _92864 _92865.
Proof. exact (fun h0 : _92862 = _92864 => @lem6969081 A _92863 _92865 _92862 _92864 h1 h0). Qed.
Lemma lem6969084 (a : Prop) (b : Prop) : (a -> b) = (term342 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6969085 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : (term346 A _92862 _92863 _92864 _92865) = (term347 A _92862 _92863 _92864 _92865).
Proof. exact (@lem6969084 (_92862 = _92864) ((@I ((A -> nat) -> nat) _92862 _92863) = (@I ((A -> nat) -> nat) _92864 _92865))). Qed.
Lemma lem6969086 {A : Type'} (_92862 : type705 A) (_92864 : type705 A) (_92863 : A -> nat) (_92865 : A -> nat) (h1 : _92863 = _92865) : term347 A _92862 _92863 _92864 _92865.
Proof. exact (EQ_MP (@lem6969085 A _92862 _92863 _92864 _92865) (@lem6969082 A _92862 _92864 _92863 _92865 h1)). Qed.
Lemma lem6969087 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : term348 A _92862 _92863 _92864 _92865.
Proof. exact (fun h0 : _92863 = _92865 => @lem6969086 A _92862 _92864 _92863 _92865 h0). Qed.
Lemma lem6969089 (a : Prop) (b : Prop) : (a -> b) = (term342 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6969090 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : (term348 A _92862 _92863 _92864 _92865) = (term349 A _92862 _92863 _92864 _92865).
Proof. exact (@lem6969089 (_92863 = _92865) (term347 A _92862 _92863 _92864 _92865)). Qed.
Lemma lem6969091 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : term349 A _92862 _92863 _92864 _92865.
Proof. exact (EQ_MP (@lem6969090 A _92862 _92863 _92864 _92865) (@lem6969087 A _92862 _92863 _92864 _92865)). Qed.
Lemma lem6969129 (x : nat) (y : nat) (z : nat) : term350 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem6969151 {A : Type'} (x : A -> nat) : x = x.
Proof. exact (@lem21386 (A -> nat) x). Qed.
Lemma lem6969152 {A : Type'} (x : A -> nat) : x = x.
Proof. exact (@lem6969151 A x). Qed.
Lemma lem6969153 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (@lem6969152 A f). Qed.
Lemma lem6969154 {A : Type'} (f : A -> nat) : term351 A f.
Proof. exact (fun h0 : term352 A f => @lem6969153 A f). Qed.
Lemma lem6969156 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969157 {A : Type'} (f : A -> nat) : (term351 A f) = (f = f).
Proof. exact (@lem6969156 (f = f)). Qed.
Lemma lem6969158 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (EQ_MP (@lem6969157 A f) (@lem6969154 A f)). Qed.
Lemma lem6969160 {A : Type'} (_92825 : A -> Prop) (_92824 : A -> Prop) (h1 : term12 A) : (term226 A _92824 _92825) = (term226 A _92825 _92824).
Proof. exact (EQ_MP (@lem6968881 A _92825 _92824) (@lem6968880 A _92824 _92825 h1)). Qed.
Lemma lem6969161 {A : Type'} (_92825 : A -> Prop) (_92824 : A -> Prop) (h1 : term12 A) : (term226 A _92824 _92825) = (term226 A _92825 _92824).
Proof. exact (@lem6969160 A _92825 _92824 h1). Qed.
Lemma lem6969162 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term226 A v u) = (term226 A u v).
Proof. exact (@lem6969161 A u v h1). Qed.
Lemma lem6969163 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : term354 A u v.
Proof. exact (fun h0 : term355 A u v => @lem6969162 A u v h1). Qed.
Lemma lem6969165 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969166 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term354 A u v) = ((term226 A v u) = (term226 A u v)).
Proof. exact (@lem6969165 ((term226 A v u) = (term226 A u v))). Qed.
Lemma lem6969167 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term226 A v u) = (term226 A u v).
Proof. exact (EQ_MP (@lem6969166 A u v) (@lem6969163 A u v h1)). Qed.
Lemma lem6969169 {A : Type'} (x : type644 A) : x = x.
Proof. exact (@lem21386 (type644 A) x). Qed.
Lemma lem6969170 {A : Type'} (x : type644 A) : x = x.
Proof. exact (@lem6969169 A x). Qed.
Lemma lem6969171 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (@lem6969170 A (@nsum A)). Qed.
Lemma lem6969172 {A : Type'} : term356 A.
Proof. exact (fun h0 : term357 A => @lem6969171 A). Qed.
Lemma lem6969174 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969175 {A : Type'} : (term356 A) = ((@nsum A) = (@nsum A)).
Proof. exact (@lem6969174 ((@nsum A) = (@nsum A))). Qed.
Lemma lem6969176 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (EQ_MP (@lem6969175 A) (@lem6969172 A)). Qed.
Lemma lem6969194 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969195 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term343 A _92858 _92859 _92860 _92861) = (term358 A _92859 _92861 _92858 _92860).
Proof. exact (@lem6969194 ((@I ((A -> Prop) -> (A -> nat) -> nat) _92858 _92859) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860 _92861)) (term359 A _92858 _92860)). Qed.
Lemma lem6969205 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) : (term360 A _92859 _92861) = (term360 A _92859 _92861).
Proof. exact (eq_refl (term360 A _92859 _92861)). Qed.
Lemma lem6969206 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term345 A _92858 _92859 _92860 _92861) = (term361 A _92859 _92861 _92858 _92860).
Proof. exact (MK_COMB (@lem6969205 A _92859 _92861) (@lem6969195 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969210 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969211 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term361 A _92859 _92861 _92858 _92860) = (term362 A _92859 _92861 _92858 _92860).
Proof. exact (@lem6969210 ((@I ((A -> Prop) -> (A -> nat) -> nat) _92858 _92859) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860 _92861)) (term363 A _92859 _92861) (term359 A _92858 _92860)). Qed.
Lemma lem6969233 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term345 A _92858 _92859 _92860 _92861) = (term362 A _92859 _92861 _92858 _92860).
Proof. exact (TRANS (@lem6969206 A _92859 _92861 _92858 _92860) (@lem6969211 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6969235 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term364 A _92858 _92859 _92860 _92861) = (term365 A _92859 _92861 _92858 _92860).
Proof. exact (MK_COMB (@lem6969234) (@lem6969233 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969257 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term362 A _92859 _92861 _92858 _92860) = (term362 A _92859 _92861 _92858 _92860).
Proof. exact (eq_refl (term362 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969258 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : ((term345 A _92858 _92859 _92860 _92861) = (term362 A _92859 _92861 _92858 _92860)) = ((term362 A _92859 _92861 _92858 _92860) = (term362 A _92859 _92861 _92858 _92860)).
Proof. exact (MK_COMB (@lem6969235 A _92859 _92861 _92858 _92860) (@lem6969257 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969260 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6969261 (x : Prop) : (x = x) = True.
Proof. exact (@lem6969260 Prop x). Qed.
Lemma lem6969262 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : ((term362 A _92859 _92861 _92858 _92860) = (term362 A _92859 _92861 _92858 _92860)) = True.
Proof. exact (@lem6969261 (term362 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969263 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : ((term345 A _92858 _92859 _92860 _92861) = (term362 A _92859 _92861 _92858 _92860)) = True.
Proof. exact (TRANS (@lem6969258 A _92859 _92861 _92858 _92860) (@lem6969262 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969264 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : True = ((term345 A _92858 _92859 _92860 _92861) = (term362 A _92859 _92861 _92858 _92860)).
Proof. exact (SYM (@lem6969263 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969265 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term345 A _92858 _92859 _92860 _92861) = (term362 A _92859 _92861 _92858 _92860).
Proof. exact (EQ_MP (@lem6969264 A _92859 _92861 _92858 _92860) (@lem0)). Qed.
Lemma lem6969266 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : term362 A _92859 _92861 _92858 _92860.
Proof. exact (EQ_MP (@lem6969265 A _92859 _92861 _92858 _92860) (@lem6969076 A _92858 _92859 _92860 _92861)). Qed.
Lemma lem6969268 (b : Prop) (a : Prop) : (a \/ b) = (term366 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6969269 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : (term362 A _92859 _92861 _92858 _92860) = (term367 A _92858 _92859 _92860 _92861).
Proof. exact (@lem6969268 (term368 A _92859 _92861 _92858 _92860) ((@I ((A -> Prop) -> (A -> nat) -> nat) _92858 _92859) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860 _92861))). Qed.
Lemma lem6969271 (a : Prop) (b : Prop) : (term369 a b) = (term370 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6969272 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term371 A _92859 _92861 _92858 _92860) = (term372 A _92859 _92861 _92858 _92860).
Proof. exact (@lem6969271 (term363 A _92859 _92861) (term359 A _92858 _92860)). Qed.
Lemma lem6969274 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6969275 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) : (term374 A _92859 _92861) = (_92859 = _92861).
Proof. exact (@lem6969274 (_92859 = _92861)). Qed.
Lemma lem6969276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6969277 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) : (term375 A _92859 _92861) = (term376 A _92859 _92861).
Proof. exact (MK_COMB (@lem6969276) (@lem6969275 A _92859 _92861)). Qed.
Lemma lem6969279 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6969280 {A : Type'} (_92858 : type644 A) (_92860 : type644 A) : (term377 A _92858 _92860) = (_92858 = _92860).
Proof. exact (@lem6969279 (_92858 = _92860)). Qed.
Lemma lem6969281 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term372 A _92859 _92861 _92858 _92860) = (term378 A _92859 _92861 _92858 _92860).
Proof. exact (MK_COMB (@lem6969277 A _92859 _92861) (@lem6969280 A _92858 _92860)). Qed.
Lemma lem6969282 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term371 A _92859 _92861 _92858 _92860) = (term378 A _92859 _92861 _92858 _92860).
Proof. exact (TRANS (@lem6969272 A _92859 _92861 _92858 _92860) (@lem6969281 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6969284 {A : Type'} (_92859 : A -> Prop) (_92861 : A -> Prop) (_92858 : type644 A) (_92860 : type644 A) : (term379 A _92859 _92861 _92858 _92860) = (term380 A _92859 _92861 _92858 _92860).
Proof. exact (MK_COMB (@lem6969283) (@lem6969282 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969285 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : ((@I ((A -> Prop) -> (A -> nat) -> nat) _92858 _92859) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860 _92861)) = ((@I ((A -> Prop) -> (A -> nat) -> nat) _92858 _92859) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860 _92861)).
Proof. exact (eq_refl ((@I ((A -> Prop) -> (A -> nat) -> nat) _92858 _92859) = (@I ((A -> Prop) -> (A -> nat) -> nat) _92860 _92861))). Qed.
Lemma lem6969286 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : (term367 A _92858 _92859 _92860 _92861) = (term381 A _92858 _92859 _92860 _92861).
Proof. exact (MK_COMB (@lem6969284 A _92859 _92861 _92858 _92860) (@lem6969285 A _92858 _92859 _92860 _92861)). Qed.
Lemma lem6969287 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : (term362 A _92859 _92861 _92858 _92860) = (term381 A _92858 _92859 _92860 _92861).
Proof. exact (TRANS (@lem6969269 A _92858 _92859 _92860 _92861) (@lem6969286 A _92858 _92859 _92860 _92861)). Qed.
Lemma lem6969289 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : term382 A u v.
Proof. exact (conj (@lem6969167 A u v h1) (@lem6969176 A)). Qed.
Lemma lem6969291 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : term381 A _92858 _92859 _92860 _92861.
Proof. exact (EQ_MP (@lem6969287 A _92858 _92859 _92860 _92861) (@lem6969266 A _92859 _92861 _92858 _92860)). Qed.
Lemma lem6969292 {A : Type'} (_92858 : type644 A) (_92859 : A -> Prop) (_92860 : type644 A) (_92861 : A -> Prop) : term381 A _92858 _92859 _92860 _92861.
Proof. exact (@lem6969291 A _92858 _92859 _92860 _92861). Qed.
Lemma lem6969293 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term383 A u v.
Proof. exact (@lem6969292 A (@nsum A) (term226 A v u) (@nsum A) (term226 A u v)). Qed.
Lemma lem6969296 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term236 A v u) = (term236 A u v).
Proof. exact (@lem6969293 A u v (@lem6969289 A u v h1)). Qed.
Lemma lem6969297 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term236 A v u) = (term236 A u v).
Proof. exact (@lem6969296 A u v h1). Qed.
Lemma lem6969298 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : term384 A u v.
Proof. exact (fun h0 : term385 A u v => @lem6969297 A u v h1). Qed.
Lemma lem6969300 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969301 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term384 A u v) = ((term236 A v u) = (term236 A u v)).
Proof. exact (@lem6969300 ((term236 A v u) = (term236 A u v))). Qed.
Lemma lem6969302 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term236 A v u) = (term236 A u v).
Proof. exact (EQ_MP (@lem6969301 A u v) (@lem6969298 A u v h1)). Qed.
Lemma lem6969320 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969321 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term347 A _92862 _92863 _92864 _92865) = (term386 A _92863 _92865 _92862 _92864).
Proof. exact (@lem6969320 ((@I ((A -> nat) -> nat) _92862 _92863) = (@I ((A -> nat) -> nat) _92864 _92865)) (term387 A _92862 _92864)). Qed.
Lemma lem6969331 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) : (term388 A _92863 _92865) = (term388 A _92863 _92865).
Proof. exact (eq_refl (term388 A _92863 _92865)). Qed.
Lemma lem6969332 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term349 A _92862 _92863 _92864 _92865) = (term389 A _92863 _92865 _92862 _92864).
Proof. exact (MK_COMB (@lem6969331 A _92863 _92865) (@lem6969321 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969336 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969337 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term389 A _92863 _92865 _92862 _92864) = (term390 A _92863 _92865 _92862 _92864).
Proof. exact (@lem6969336 ((@I ((A -> nat) -> nat) _92862 _92863) = (@I ((A -> nat) -> nat) _92864 _92865)) (term391 A _92863 _92865) (term387 A _92862 _92864)). Qed.
Lemma lem6969359 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term349 A _92862 _92863 _92864 _92865) = (term390 A _92863 _92865 _92862 _92864).
Proof. exact (TRANS (@lem6969332 A _92863 _92865 _92862 _92864) (@lem6969337 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6969361 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term392 A _92862 _92863 _92864 _92865) = (term393 A _92863 _92865 _92862 _92864).
Proof. exact (MK_COMB (@lem6969360) (@lem6969359 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969383 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term390 A _92863 _92865 _92862 _92864) = (term390 A _92863 _92865 _92862 _92864).
Proof. exact (eq_refl (term390 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969384 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : ((term349 A _92862 _92863 _92864 _92865) = (term390 A _92863 _92865 _92862 _92864)) = ((term390 A _92863 _92865 _92862 _92864) = (term390 A _92863 _92865 _92862 _92864)).
Proof. exact (MK_COMB (@lem6969361 A _92863 _92865 _92862 _92864) (@lem6969383 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969386 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6969387 (x : Prop) : (x = x) = True.
Proof. exact (@lem6969386 Prop x). Qed.
Lemma lem6969388 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : ((term390 A _92863 _92865 _92862 _92864) = (term390 A _92863 _92865 _92862 _92864)) = True.
Proof. exact (@lem6969387 (term390 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969389 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : ((term349 A _92862 _92863 _92864 _92865) = (term390 A _92863 _92865 _92862 _92864)) = True.
Proof. exact (TRANS (@lem6969384 A _92863 _92865 _92862 _92864) (@lem6969388 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969390 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : True = ((term349 A _92862 _92863 _92864 _92865) = (term390 A _92863 _92865 _92862 _92864)).
Proof. exact (SYM (@lem6969389 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969391 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term349 A _92862 _92863 _92864 _92865) = (term390 A _92863 _92865 _92862 _92864).
Proof. exact (EQ_MP (@lem6969390 A _92863 _92865 _92862 _92864) (@lem0)). Qed.
Lemma lem6969392 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : term390 A _92863 _92865 _92862 _92864.
Proof. exact (EQ_MP (@lem6969391 A _92863 _92865 _92862 _92864) (@lem6969091 A _92862 _92863 _92864 _92865)). Qed.
Lemma lem6969394 (b : Prop) (a : Prop) : (a \/ b) = (term366 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6969395 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : (term390 A _92863 _92865 _92862 _92864) = (term394 A _92862 _92863 _92864 _92865).
Proof. exact (@lem6969394 (term395 A _92863 _92865 _92862 _92864) ((@I ((A -> nat) -> nat) _92862 _92863) = (@I ((A -> nat) -> nat) _92864 _92865))). Qed.
Lemma lem6969397 (a : Prop) (b : Prop) : (term369 a b) = (term370 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6969398 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term396 A _92863 _92865 _92862 _92864) = (term397 A _92863 _92865 _92862 _92864).
Proof. exact (@lem6969397 (term391 A _92863 _92865) (term387 A _92862 _92864)). Qed.
Lemma lem6969400 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6969401 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) : (term398 A _92863 _92865) = (_92863 = _92865).
Proof. exact (@lem6969400 (_92863 = _92865)). Qed.
Lemma lem6969402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6969403 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) : (term399 A _92863 _92865) = (term400 A _92863 _92865).
Proof. exact (MK_COMB (@lem6969402) (@lem6969401 A _92863 _92865)). Qed.
Lemma lem6969405 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6969406 {A : Type'} (_92862 : type705 A) (_92864 : type705 A) : (term401 A _92862 _92864) = (_92862 = _92864).
Proof. exact (@lem6969405 (_92862 = _92864)). Qed.
Lemma lem6969407 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term397 A _92863 _92865 _92862 _92864) = (term402 A _92863 _92865 _92862 _92864).
Proof. exact (MK_COMB (@lem6969403 A _92863 _92865) (@lem6969406 A _92862 _92864)). Qed.
Lemma lem6969408 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term396 A _92863 _92865 _92862 _92864) = (term402 A _92863 _92865 _92862 _92864).
Proof. exact (TRANS (@lem6969398 A _92863 _92865 _92862 _92864) (@lem6969407 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6969410 {A : Type'} (_92863 : A -> nat) (_92865 : A -> nat) (_92862 : type705 A) (_92864 : type705 A) : (term403 A _92863 _92865 _92862 _92864) = (term404 A _92863 _92865 _92862 _92864).
Proof. exact (MK_COMB (@lem6969409) (@lem6969408 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969411 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : ((@I ((A -> nat) -> nat) _92862 _92863) = (@I ((A -> nat) -> nat) _92864 _92865)) = ((@I ((A -> nat) -> nat) _92862 _92863) = (@I ((A -> nat) -> nat) _92864 _92865)).
Proof. exact (eq_refl ((@I ((A -> nat) -> nat) _92862 _92863) = (@I ((A -> nat) -> nat) _92864 _92865))). Qed.
Lemma lem6969412 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : (term394 A _92862 _92863 _92864 _92865) = (term405 A _92862 _92863 _92864 _92865).
Proof. exact (MK_COMB (@lem6969410 A _92863 _92865 _92862 _92864) (@lem6969411 A _92862 _92863 _92864 _92865)). Qed.
Lemma lem6969413 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : (term390 A _92863 _92865 _92862 _92864) = (term405 A _92862 _92863 _92864 _92865).
Proof. exact (TRANS (@lem6969395 A _92862 _92863 _92864 _92865) (@lem6969412 A _92862 _92863 _92864 _92865)). Qed.
Lemma lem6969415 {A : Type'} (f : A -> nat) (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : term406 A f u v.
Proof. exact (conj (@lem6969158 A f) (@lem6969302 A u v h1)). Qed.
Lemma lem6969417 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : term405 A _92862 _92863 _92864 _92865.
Proof. exact (EQ_MP (@lem6969413 A _92862 _92863 _92864 _92865) (@lem6969392 A _92863 _92865 _92862 _92864)). Qed.
Lemma lem6969418 {A : Type'} (_92862 : type705 A) (_92863 : A -> nat) (_92864 : type705 A) (_92865 : A -> nat) : term405 A _92862 _92863 _92864 _92865.
Proof. exact (@lem6969417 A _92862 _92863 _92864 _92865). Qed.
Lemma lem6969419 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term407 A u v f.
Proof. exact (@lem6969418 A (term236 A v u) f (term236 A u v) f). Qed.
Lemma lem6969422 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) : (term238 A v u f) = (term238 A u v f).
Proof. exact (@lem6969419 A u v f (@lem6969415 A f u v h1)). Qed.
Lemma lem6969423 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) : (term238 A v u f) = (term238 A u v f).
Proof. exact (@lem6969422 A u v f h1). Qed.
Lemma lem6969424 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) : term408 A u v f.
Proof. exact (fun h0 : term409 A u v f => @lem6969423 A u v f h1). Qed.
Lemma lem6969426 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969427 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term408 A u v f) = ((term238 A v u f) = (term238 A u v f)).
Proof. exact (@lem6969426 ((term238 A v u f) = (term238 A u v f))). Qed.
Lemma lem6969428 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) : (term238 A v u f) = (term238 A u v f).
Proof. exact (EQ_MP (@lem6969427 A u v f) (@lem6969424 A u v f h1)). Qed.
Lemma lem6969430 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (proj1 (@lem6968780 A u v f h1)). Qed.
Lemma lem6969431 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term410 A v.
Proof. exact (fun h0 : term273 A v => @lem6969430 A u v f h1). Qed.
Lemma lem6969433 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969434 {A : Type'} (v : A -> Prop) : (term410 A v) = (@I ((A -> Prop) -> Prop) (@FINITE A) v).
Proof. exact (@lem6969433 (@I ((A -> Prop) -> Prop) (@FINITE A) v)). Qed.
Lemma lem6969435 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (EQ_MP (@lem6969434 A v) (@lem6969431 A u v f h1)). Qed.
Lemma lem6969437 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (proj1 (@lem6968780 A u v f h1)). Qed.
Lemma lem6969438 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term410 A v.
Proof. exact (fun h0 : term273 A v => @lem6969437 A u v f h1). Qed.
Lemma lem6969440 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969441 {A : Type'} (v : A -> Prop) : (term410 A v) = (@I ((A -> Prop) -> Prop) (@FINITE A) v).
Proof. exact (@lem6969440 (@I ((A -> Prop) -> Prop) (@FINITE A) v)). Qed.
Lemma lem6969442 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (EQ_MP (@lem6969441 A v) (@lem6969438 A u v f h1)). Qed.
Lemma lem6969445 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term411 A u v f) : term411 A u v f.
Proof. exact (h1). Qed.
Lemma lem6969446 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term411 A u v f) : term412 A u v f.
Proof. exact (fun h0 : (term238 A v u f) = (term239 A v f) => @lem6969445 A u v f h1). Qed.
Lemma lem6969448 (p : Prop) : (term413 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6969449 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term412 A u v f) = (term411 A u v f).
Proof. exact (@lem6969448 ((term238 A v u f) = (term239 A v f))). Qed.
Lemma lem6969450 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term411 A u v f) : term411 A u v f.
Proof. exact (EQ_MP (@lem6969449 A u v f) (@lem6969446 A u v f h1)). Qed.
Lemma lem6969456 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969457 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term339 A x _92828 _92827 _92826) = (term414 A x _92828 _92827 _92826).
Proof. exact (@lem6969456 (term264 A x _92826 _92827 _92828) (term273 A _92827) ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6969471 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969472 {A : Type'} (_92828 : A -> Prop) (_92826 : A -> nat) (_92827 : A -> Prop) : (term415 A _92828 _92827 _92826) = (term416 A _92828 _92826 _92827).
Proof. exact (@lem6969471 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term273 A _92827)). Qed.
Lemma lem6969480 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term417 A x _92826 _92827 _92828) = (term417 A x _92826 _92827 _92828).
Proof. exact (eq_refl (term417 A x _92826 _92827 _92828)). Qed.
Lemma lem6969481 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92826 : A -> nat) (_92827 : A -> Prop) : (term414 A x _92828 _92827 _92826) = (term418 A x _92828 _92826 _92827).
Proof. exact (MK_COMB (@lem6969480 A x _92826 _92827 _92828) (@lem6969472 A _92828 _92826 _92827)). Qed.
Lemma lem6969485 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969486 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term418 A x _92828 _92826 _92827) = (term419 A x _92826 _92828 _92827).
Proof. exact (@lem6969485 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term264 A x _92826 _92827 _92828) (term273 A _92827)). Qed.
Lemma lem6969504 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term414 A x _92828 _92827 _92826) = (term419 A x _92826 _92828 _92827).
Proof. exact (TRANS (@lem6969481 A x _92828 _92826 _92827) (@lem6969486 A x _92826 _92828 _92827)). Qed.
Lemma lem6969505 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term339 A x _92828 _92827 _92826) = (term419 A x _92826 _92828 _92827).
Proof. exact (TRANS (@lem6969457 A x _92828 _92827 _92826) (@lem6969504 A x _92826 _92828 _92827)). Qed.
Lemma lem6969506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6969507 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term420 A x _92828 _92827 _92826) = (term421 A x _92826 _92828 _92827).
Proof. exact (MK_COMB (@lem6969506) (@lem6969505 A x _92826 _92828 _92827)). Qed.
Lemma lem6969521 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969522 {A : Type'} (_92828 : A -> Prop) (_92826 : A -> nat) (_92827 : A -> Prop) : (term415 A _92828 _92827 _92826) = (term416 A _92828 _92826 _92827).
Proof. exact (@lem6969521 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term273 A _92827)). Qed.
Lemma lem6969530 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term417 A x _92826 _92827 _92828) = (term417 A x _92826 _92827 _92828).
Proof. exact (eq_refl (term417 A x _92826 _92827 _92828)). Qed.
Lemma lem6969531 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92826 : A -> nat) (_92827 : A -> Prop) : (term414 A x _92828 _92827 _92826) = (term418 A x _92828 _92826 _92827).
Proof. exact (MK_COMB (@lem6969530 A x _92826 _92827 _92828) (@lem6969522 A _92828 _92826 _92827)). Qed.
Lemma lem6969535 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969536 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term418 A x _92828 _92826 _92827) = (term419 A x _92826 _92828 _92827).
Proof. exact (@lem6969535 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term264 A x _92826 _92827 _92828) (term273 A _92827)). Qed.
Lemma lem6969554 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term414 A x _92828 _92827 _92826) = (term419 A x _92826 _92828 _92827).
Proof. exact (TRANS (@lem6969531 A x _92828 _92826 _92827) (@lem6969536 A x _92826 _92828 _92827)). Qed.
Lemma lem6969555 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : ((term339 A x _92828 _92827 _92826) = (term414 A x _92828 _92827 _92826)) = ((term419 A x _92826 _92828 _92827) = (term419 A x _92826 _92828 _92827)).
Proof. exact (MK_COMB (@lem6969507 A x _92826 _92828 _92827) (@lem6969554 A x _92826 _92828 _92827)). Qed.
Lemma lem6969557 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6969558 (x : Prop) : (x = x) = True.
Proof. exact (@lem6969557 Prop x). Qed.
Lemma lem6969559 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : ((term419 A x _92826 _92828 _92827) = (term419 A x _92826 _92828 _92827)) = True.
Proof. exact (@lem6969558 (term419 A x _92826 _92828 _92827)). Qed.
Lemma lem6969560 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : ((term339 A x _92828 _92827 _92826) = (term414 A x _92828 _92827 _92826)) = True.
Proof. exact (TRANS (@lem6969555 A x _92826 _92828 _92827) (@lem6969559 A x _92826 _92828 _92827)). Qed.
Lemma lem6969561 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : True = ((term339 A x _92828 _92827 _92826) = (term414 A x _92828 _92827 _92826)).
Proof. exact (SYM (@lem6969560 A x _92828 _92827 _92826)). Qed.
Lemma lem6969562 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term339 A x _92828 _92827 _92826) = (term414 A x _92828 _92827 _92826).
Proof. exact (EQ_MP (@lem6969561 A x _92828 _92827 _92826) (@lem0)). Qed.
Lemma lem6969563 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term414 A x _92828 _92827 _92826.
Proof. exact (EQ_MP (@lem6969562 A x _92828 _92827 _92826) (@lem6968940 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6969565 (b : Prop) (a : Prop) : (a \/ b) = (term366 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6969566 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term414 A x _92828 _92827 _92826) = (term422 A x _92826 _92827 _92828).
Proof. exact (@lem6969565 (term415 A _92828 _92827 _92826) (term264 A x _92826 _92827 _92828)). Qed.
Lemma lem6969568 (a : Prop) (b : Prop) : (term369 a b) = (term370 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6969569 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term423 A _92828 _92827 _92826) = (term424 A _92828 _92827 _92826).
Proof. exact (@lem6969568 (term273 A _92827) ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6969571 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6969572 {A : Type'} (_92827 : A -> Prop) : (term425 A _92827) = (@I ((A -> Prop) -> Prop) (@FINITE A) _92827).
Proof. exact (@lem6969571 (@I ((A -> Prop) -> Prop) (@FINITE A) _92827)). Qed.
Lemma lem6969573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6969574 {A : Type'} (_92827 : A -> Prop) : (term426 A _92827) = (term301 A _92827).
Proof. exact (MK_COMB (@lem6969573) (@lem6969572 A _92827)). Qed.
Lemma lem6969575 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term411 A _92828 _92827 _92826) = (term411 A _92828 _92827 _92826).
Proof. exact (eq_refl (term411 A _92828 _92827 _92826)). Qed.
Lemma lem6969576 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term424 A _92828 _92827 _92826) = (term427 A _92828 _92827 _92826).
Proof. exact (MK_COMB (@lem6969574 A _92827) (@lem6969575 A _92828 _92827 _92826)). Qed.
Lemma lem6969577 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term423 A _92828 _92827 _92826) = (term427 A _92828 _92827 _92826).
Proof. exact (TRANS (@lem6969569 A _92828 _92827 _92826) (@lem6969576 A _92828 _92827 _92826)). Qed.
Lemma lem6969578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6969579 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term428 A _92828 _92827 _92826) = (term429 A _92828 _92827 _92826).
Proof. exact (MK_COMB (@lem6969578) (@lem6969577 A _92828 _92827 _92826)). Qed.
Lemma lem6969580 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term264 A x _92826 _92827 _92828) = (term264 A x _92826 _92827 _92828).
Proof. exact (eq_refl (term264 A x _92826 _92827 _92828)). Qed.
Lemma lem6969581 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term422 A x _92826 _92827 _92828) = (term430 A x _92826 _92827 _92828).
Proof. exact (MK_COMB (@lem6969579 A _92828 _92827 _92826) (@lem6969580 A x _92826 _92827 _92828)). Qed.
Lemma lem6969582 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term414 A x _92828 _92827 _92826) = (term430 A x _92826 _92827 _92828).
Proof. exact (TRANS (@lem6969566 A x _92826 _92827 _92828) (@lem6969581 A x _92826 _92827 _92828)). Qed.
Lemma lem6969584 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term411 A u v f) (h2 : term64 A u v f) : term427 A u v f.
Proof. exact (conj (@lem6969442 A u v f h2) (@lem6969450 A u v f h1)). Qed.
Lemma lem6969586 {A : Type'} (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) (x : type693 A) (h1 : term222 A x) : term430 A x _92826 _92827 _92828.
Proof. exact (EQ_MP (@lem6969582 A x _92826 _92827 _92828) (@lem6969563 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6969587 {A : Type'} (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) (x : type693 A) (h1 : term222 A x) : term430 A x _92826 _92827 _92828.
Proof. exact (@lem6969586 A _92826 _92827 _92828 x h1). Qed.
Lemma lem6969588 {A : Type'} (f : A -> nat) (v : A -> Prop) (u : A -> Prop) (x : type693 A) (h1 : term222 A x) : term430 A x f v u.
Proof. exact (@lem6969587 A f v u x h1). Qed.
Lemma lem6969591 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term264 A x f v u.
Proof. exact (@lem6969588 A f v u x h1 (@lem6969584 A u v f h2 h3)). Qed.
Lemma lem6969592 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term431 A x f v u.
Proof. exact (fun h0 : term432 A x f v u => @lem6969591 A x u v f h1 h2 h3). Qed.
Lemma lem6969594 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969595 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term431 A x f v u) = (term264 A x f v u).
Proof. exact (@lem6969594 (term264 A x f v u)). Qed.
Lemma lem6969596 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term264 A x f v u.
Proof. exact (EQ_MP (@lem6969595 A x f v u) (@lem6969592 A x u v f h1 h2 h3)). Qed.
Lemma lem6969598 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (proj1 (@lem6968780 A u v f h1)). Qed.
Lemma lem6969599 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term410 A v.
Proof. exact (fun h0 : term273 A v => @lem6969598 A u v f h1). Qed.
Lemma lem6969601 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969602 {A : Type'} (v : A -> Prop) : (term410 A v) = (@I ((A -> Prop) -> Prop) (@FINITE A) v).
Proof. exact (@lem6969601 (@I ((A -> Prop) -> Prop) (@FINITE A) v)). Qed.
Lemma lem6969603 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (EQ_MP (@lem6969602 A v) (@lem6969599 A u v f h1)). Qed.
Lemma lem6969606 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term411 A u v f) : term411 A u v f.
Proof. exact (h1). Qed.
Lemma lem6969607 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term411 A u v f) : term412 A u v f.
Proof. exact (fun h0 : (term238 A v u f) = (term239 A v f) => @lem6969606 A u v f h1). Qed.
Lemma lem6969609 (p : Prop) : (term413 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6969610 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term412 A u v f) = (term411 A u v f).
Proof. exact (@lem6969609 ((term238 A v u f) = (term239 A v f))). Qed.
Lemma lem6969611 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term411 A u v f) : term411 A u v f.
Proof. exact (EQ_MP (@lem6969610 A u v f) (@lem6969607 A u v f h1)). Qed.
Lemma lem6969617 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969618 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term338 A x _92828 _92827 _92826) = (term433 A x _92828 _92827 _92826).
Proof. exact (@lem6969617 (term251 A x _92826 _92827 _92828) (term273 A _92827) ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6969634 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969635 {A : Type'} (_92828 : A -> Prop) (_92826 : A -> nat) (_92827 : A -> Prop) : (term415 A _92828 _92827 _92826) = (term416 A _92828 _92826 _92827).
Proof. exact (@lem6969634 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term273 A _92827)). Qed.
Lemma lem6969643 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term434 A x _92826 _92827 _92828) = (term434 A x _92826 _92827 _92828).
Proof. exact (eq_refl (term434 A x _92826 _92827 _92828)). Qed.
Lemma lem6969644 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92826 : A -> nat) (_92827 : A -> Prop) : (term433 A x _92828 _92827 _92826) = (term435 A x _92828 _92826 _92827).
Proof. exact (MK_COMB (@lem6969643 A x _92826 _92827 _92828) (@lem6969635 A _92828 _92826 _92827)). Qed.
Lemma lem6969648 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969649 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term435 A x _92828 _92826 _92827) = (term436 A x _92826 _92828 _92827).
Proof. exact (@lem6969648 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term251 A x _92826 _92827 _92828) (term273 A _92827)). Qed.
Lemma lem6969669 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term433 A x _92828 _92827 _92826) = (term436 A x _92826 _92828 _92827).
Proof. exact (TRANS (@lem6969644 A x _92828 _92826 _92827) (@lem6969649 A x _92826 _92828 _92827)). Qed.
Lemma lem6969670 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term338 A x _92828 _92827 _92826) = (term436 A x _92826 _92828 _92827).
Proof. exact (TRANS (@lem6969618 A x _92828 _92827 _92826) (@lem6969669 A x _92826 _92828 _92827)). Qed.
Lemma lem6969671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6969672 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term437 A x _92828 _92827 _92826) = (term438 A x _92826 _92828 _92827).
Proof. exact (MK_COMB (@lem6969671) (@lem6969670 A x _92826 _92828 _92827)). Qed.
Lemma lem6969688 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969689 {A : Type'} (_92828 : A -> Prop) (_92826 : A -> nat) (_92827 : A -> Prop) : (term415 A _92828 _92827 _92826) = (term416 A _92828 _92826 _92827).
Proof. exact (@lem6969688 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term273 A _92827)). Qed.
Lemma lem6969697 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term434 A x _92826 _92827 _92828) = (term434 A x _92826 _92827 _92828).
Proof. exact (eq_refl (term434 A x _92826 _92827 _92828)). Qed.
Lemma lem6969698 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92826 : A -> nat) (_92827 : A -> Prop) : (term433 A x _92828 _92827 _92826) = (term435 A x _92828 _92826 _92827).
Proof. exact (MK_COMB (@lem6969697 A x _92826 _92827 _92828) (@lem6969689 A _92828 _92826 _92827)). Qed.
Lemma lem6969702 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969703 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term435 A x _92828 _92826 _92827) = (term436 A x _92826 _92828 _92827).
Proof. exact (@lem6969702 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term251 A x _92826 _92827 _92828) (term273 A _92827)). Qed.
Lemma lem6969723 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term433 A x _92828 _92827 _92826) = (term436 A x _92826 _92828 _92827).
Proof. exact (TRANS (@lem6969698 A x _92828 _92826 _92827) (@lem6969703 A x _92826 _92828 _92827)). Qed.
Lemma lem6969724 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : ((term338 A x _92828 _92827 _92826) = (term433 A x _92828 _92827 _92826)) = ((term436 A x _92826 _92828 _92827) = (term436 A x _92826 _92828 _92827)).
Proof. exact (MK_COMB (@lem6969672 A x _92826 _92828 _92827) (@lem6969723 A x _92826 _92828 _92827)). Qed.
Lemma lem6969726 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6969727 (x : Prop) : (x = x) = True.
Proof. exact (@lem6969726 Prop x). Qed.
Lemma lem6969728 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : ((term436 A x _92826 _92828 _92827) = (term436 A x _92826 _92828 _92827)) = True.
Proof. exact (@lem6969727 (term436 A x _92826 _92828 _92827)). Qed.
Lemma lem6969729 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : ((term338 A x _92828 _92827 _92826) = (term433 A x _92828 _92827 _92826)) = True.
Proof. exact (TRANS (@lem6969724 A x _92826 _92828 _92827) (@lem6969728 A x _92826 _92828 _92827)). Qed.
Lemma lem6969730 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : True = ((term338 A x _92828 _92827 _92826) = (term433 A x _92828 _92827 _92826)).
Proof. exact (SYM (@lem6969729 A x _92828 _92827 _92826)). Qed.
Lemma lem6969731 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term338 A x _92828 _92827 _92826) = (term433 A x _92828 _92827 _92826).
Proof. exact (EQ_MP (@lem6969730 A x _92828 _92827 _92826) (@lem0)). Qed.
Lemma lem6969732 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term433 A x _92828 _92827 _92826.
Proof. exact (EQ_MP (@lem6969731 A x _92828 _92827 _92826) (@lem6968928 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6969734 (b : Prop) (a : Prop) : (a \/ b) = (term366 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6969735 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term433 A x _92828 _92827 _92826) = (term439 A x _92826 _92827 _92828).
Proof. exact (@lem6969734 (term415 A _92828 _92827 _92826) (term251 A x _92826 _92827 _92828)). Qed.
Lemma lem6969737 (a : Prop) (b : Prop) : (term369 a b) = (term370 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6969738 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term423 A _92828 _92827 _92826) = (term424 A _92828 _92827 _92826).
Proof. exact (@lem6969737 (term273 A _92827) ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6969740 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6969741 {A : Type'} (_92827 : A -> Prop) : (term425 A _92827) = (@I ((A -> Prop) -> Prop) (@FINITE A) _92827).
Proof. exact (@lem6969740 (@I ((A -> Prop) -> Prop) (@FINITE A) _92827)). Qed.
Lemma lem6969742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6969743 {A : Type'} (_92827 : A -> Prop) : (term426 A _92827) = (term301 A _92827).
Proof. exact (MK_COMB (@lem6969742) (@lem6969741 A _92827)). Qed.
Lemma lem6969744 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term411 A _92828 _92827 _92826) = (term411 A _92828 _92827 _92826).
Proof. exact (eq_refl (term411 A _92828 _92827 _92826)). Qed.
Lemma lem6969745 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term424 A _92828 _92827 _92826) = (term427 A _92828 _92827 _92826).
Proof. exact (MK_COMB (@lem6969743 A _92827) (@lem6969744 A _92828 _92827 _92826)). Qed.
Lemma lem6969746 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term423 A _92828 _92827 _92826) = (term427 A _92828 _92827 _92826).
Proof. exact (TRANS (@lem6969738 A _92828 _92827 _92826) (@lem6969745 A _92828 _92827 _92826)). Qed.
Lemma lem6969747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6969748 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term428 A _92828 _92827 _92826) = (term429 A _92828 _92827 _92826).
Proof. exact (MK_COMB (@lem6969747) (@lem6969746 A _92828 _92827 _92826)). Qed.
Lemma lem6969749 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term251 A x _92826 _92827 _92828) = (term251 A x _92826 _92827 _92828).
Proof. exact (eq_refl (term251 A x _92826 _92827 _92828)). Qed.
Lemma lem6969750 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term439 A x _92826 _92827 _92828) = (term440 A x _92826 _92827 _92828).
Proof. exact (MK_COMB (@lem6969748 A _92828 _92827 _92826) (@lem6969749 A x _92826 _92827 _92828)). Qed.
Lemma lem6969751 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) : (term433 A x _92828 _92827 _92826) = (term440 A x _92826 _92827 _92828).
Proof. exact (TRANS (@lem6969735 A x _92826 _92827 _92828) (@lem6969750 A x _92826 _92827 _92828)). Qed.
Lemma lem6969753 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term411 A u v f) (h2 : term64 A u v f) : term427 A u v f.
Proof. exact (conj (@lem6969603 A u v f h2) (@lem6969611 A u v f h1)). Qed.
Lemma lem6969755 {A : Type'} (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) (x : type693 A) (h1 : term222 A x) : term440 A x _92826 _92827 _92828.
Proof. exact (EQ_MP (@lem6969751 A x _92826 _92827 _92828) (@lem6969732 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6969756 {A : Type'} (_92826 : A -> nat) (_92827 : A -> Prop) (_92828 : A -> Prop) (x : type693 A) (h1 : term222 A x) : term440 A x _92826 _92827 _92828.
Proof. exact (@lem6969755 A _92826 _92827 _92828 x h1). Qed.
Lemma lem6969757 {A : Type'} (f : A -> nat) (v : A -> Prop) (u : A -> Prop) (x : type693 A) (h1 : term222 A x) : term440 A x f v u.
Proof. exact (@lem6969756 A f v u x h1). Qed.
Lemma lem6969760 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term251 A x f v u.
Proof. exact (@lem6969757 A f v u x h1 (@lem6969753 A u v f h2 h3)). Qed.
Lemma lem6969761 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term441 A x f v u.
Proof. exact (fun h0 : (term247 A x f v u) = (@I (nat -> nat) NUMERAL 0) => @lem6969760 A x u v f h1 h2 h3). Qed.
Lemma lem6969763 (p : Prop) : (term413 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6969764 {A : Type'} (x : type693 A) (f : A -> nat) (v : A -> Prop) (u : A -> Prop) : (term441 A x f v u) = (term251 A x f v u).
Proof. exact (@lem6969763 ((term247 A x f v u) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6969765 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term251 A x f v u.
Proof. exact (EQ_MP (@lem6969764 A x f v u) (@lem6969761 A x u v f h1 h2 h3)). Qed.
Lemma lem6969771 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969772 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (_92829 : A) : (term337 A u v f _92829) = (term442 A v u f _92829).
Proof. exact (@lem6969771 (term293 A _92829 v) (term294 A _92829 u) ((@I (A -> nat) f _92829) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6969786 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969787 {A : Type'} (f : A -> nat) (_92829 : A) (u : A -> Prop) : (term443 A u f _92829) = (term444 A f _92829 u).
Proof. exact (@lem6969786 ((@I (A -> nat) f _92829) = (@I (nat -> nat) NUMERAL 0)) (term294 A _92829 u)). Qed.
Lemma lem6969795 {A : Type'} (_92829 : A) (v : A -> Prop) : (term445 A _92829 v) = (term445 A _92829 v).
Proof. exact (eq_refl (term445 A _92829 v)). Qed.
Lemma lem6969796 {A : Type'} (v : A -> Prop) (f : A -> nat) (_92829 : A) (u : A -> Prop) : (term442 A v u f _92829) = (term446 A v f _92829 u).
Proof. exact (MK_COMB (@lem6969795 A _92829 v) (@lem6969787 A f _92829 u)). Qed.
Lemma lem6969800 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969801 {A : Type'} (f : A -> nat) (v : A -> Prop) (_92829 : A) (u : A -> Prop) : (term446 A v f _92829 u) = (term447 A f v _92829 u).
Proof. exact (@lem6969800 ((@I (A -> nat) f _92829) = (@I (nat -> nat) NUMERAL 0)) (term293 A _92829 v) (term294 A _92829 u)). Qed.
Lemma lem6969819 {A : Type'} (f : A -> nat) (v : A -> Prop) (_92829 : A) (u : A -> Prop) : (term442 A v u f _92829) = (term447 A f v _92829 u).
Proof. exact (TRANS (@lem6969796 A v f _92829 u) (@lem6969801 A f v _92829 u)). Qed.
Lemma lem6969820 {A : Type'} (f : A -> nat) (v : A -> Prop) (_92829 : A) (u : A -> Prop) : (term337 A u v f _92829) = (term447 A f v _92829 u).
Proof. exact (TRANS (@lem6969772 A v u f _92829) (@lem6969819 A f v _92829 u)). Qed.
Lemma lem6969821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6969822 {A : Type'} (f : A -> nat) (v : A -> Prop) (_92829 : A) (u : A -> Prop) : (term448 A u v f _92829) = (term449 A f v _92829 u).
Proof. exact (MK_COMB (@lem6969821) (@lem6969820 A f v _92829 u)). Qed.
Lemma lem6969836 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969837 {A : Type'} (f : A -> nat) (_92829 : A) (u : A -> Prop) : (term443 A u f _92829) = (term444 A f _92829 u).
Proof. exact (@lem6969836 ((@I (A -> nat) f _92829) = (@I (nat -> nat) NUMERAL 0)) (term294 A _92829 u)). Qed.
Lemma lem6969845 {A : Type'} (_92829 : A) (v : A -> Prop) : (term445 A _92829 v) = (term445 A _92829 v).
Proof. exact (eq_refl (term445 A _92829 v)). Qed.
Lemma lem6969846 {A : Type'} (v : A -> Prop) (f : A -> nat) (_92829 : A) (u : A -> Prop) : (term442 A v u f _92829) = (term446 A v f _92829 u).
Proof. exact (MK_COMB (@lem6969845 A _92829 v) (@lem6969837 A f _92829 u)). Qed.
Lemma lem6969850 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969851 {A : Type'} (f : A -> nat) (v : A -> Prop) (_92829 : A) (u : A -> Prop) : (term446 A v f _92829 u) = (term447 A f v _92829 u).
Proof. exact (@lem6969850 ((@I (A -> nat) f _92829) = (@I (nat -> nat) NUMERAL 0)) (term293 A _92829 v) (term294 A _92829 u)). Qed.
Lemma lem6969869 {A : Type'} (f : A -> nat) (v : A -> Prop) (_92829 : A) (u : A -> Prop) : (term442 A v u f _92829) = (term447 A f v _92829 u).
Proof. exact (TRANS (@lem6969846 A v f _92829 u) (@lem6969851 A f v _92829 u)). Qed.
Lemma lem6969870 {A : Type'} (f : A -> nat) (v : A -> Prop) (_92829 : A) (u : A -> Prop) : ((term337 A u v f _92829) = (term442 A v u f _92829)) = ((term447 A f v _92829 u) = (term447 A f v _92829 u)).
Proof. exact (MK_COMB (@lem6969822 A f v _92829 u) (@lem6969869 A f v _92829 u)). Qed.
Lemma lem6969872 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6969873 (x : Prop) : (x = x) = True.
Proof. exact (@lem6969872 Prop x). Qed.
Lemma lem6969874 {A : Type'} (f : A -> nat) (v : A -> Prop) (_92829 : A) (u : A -> Prop) : ((term447 A f v _92829 u) = (term447 A f v _92829 u)) = True.
Proof. exact (@lem6969873 (term447 A f v _92829 u)). Qed.
Lemma lem6969875 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (_92829 : A) : ((term337 A u v f _92829) = (term442 A v u f _92829)) = True.
Proof. exact (TRANS (@lem6969870 A f v _92829 u) (@lem6969874 A f v _92829 u)). Qed.
Lemma lem6969876 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (_92829 : A) : True = ((term337 A u v f _92829) = (term442 A v u f _92829)).
Proof. exact (SYM (@lem6969875 A v u f _92829)). Qed.
Lemma lem6969877 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> nat) (_92829 : A) : (term337 A u v f _92829) = (term442 A v u f _92829).
Proof. exact (EQ_MP (@lem6969876 A v u f _92829) (@lem0)). Qed.
Lemma lem6969878 {A : Type'} (_92829 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term442 A v u f _92829.
Proof. exact (EQ_MP (@lem6969877 A v u f _92829) (@lem6968916 A _92829 u v f h1)). Qed.
Lemma lem6969880 (b : Prop) (a : Prop) : (a \/ b) = (term366 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6969881 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92829 : A) (v : A -> Prop) : (term442 A v u f _92829) = (term450 A u f _92829 v).
Proof. exact (@lem6969880 (term443 A u f _92829) (term293 A _92829 v)). Qed.
Lemma lem6969883 (a : Prop) (b : Prop) : (term369 a b) = (term370 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6969884 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92829 : A) : (term451 A u f _92829) = (term452 A u f _92829).
Proof. exact (@lem6969883 (term294 A _92829 u) ((@I (A -> nat) f _92829) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem6969886 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6969887 {A : Type'} (_92829 : A) (u : A -> Prop) : (term453 A _92829 u) = (term293 A _92829 u).
Proof. exact (@lem6969886 (term293 A _92829 u)). Qed.
Lemma lem6969888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6969889 {A : Type'} (_92829 : A) (u : A -> Prop) : (term454 A _92829 u) = (term455 A _92829 u).
Proof. exact (MK_COMB (@lem6969888) (@lem6969887 A _92829 u)). Qed.
Lemma lem6969890 {A : Type'} (f : A -> nat) (_92829 : A) : (term456 A f _92829) = (term456 A f _92829).
Proof. exact (eq_refl (term456 A f _92829)). Qed.
Lemma lem6969891 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92829 : A) : (term452 A u f _92829) = (term457 A u f _92829).
Proof. exact (MK_COMB (@lem6969889 A _92829 u) (@lem6969890 A f _92829)). Qed.
Lemma lem6969892 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92829 : A) : (term451 A u f _92829) = (term457 A u f _92829).
Proof. exact (TRANS (@lem6969884 A u f _92829) (@lem6969891 A u f _92829)). Qed.
Lemma lem6969893 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6969894 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92829 : A) : (term458 A u f _92829) = (term459 A u f _92829).
Proof. exact (MK_COMB (@lem6969893) (@lem6969892 A u f _92829)). Qed.
Lemma lem6969895 {A : Type'} (_92829 : A) (v : A -> Prop) : (term293 A _92829 v) = (term293 A _92829 v).
Proof. exact (eq_refl (term293 A _92829 v)). Qed.
Lemma lem6969896 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92829 : A) (v : A -> Prop) : (term450 A u f _92829 v) = (term460 A u f _92829 v).
Proof. exact (MK_COMB (@lem6969894 A u f _92829) (@lem6969895 A _92829 v)). Qed.
Lemma lem6969897 {A : Type'} (u : A -> Prop) (f : A -> nat) (_92829 : A) (v : A -> Prop) : (term442 A v u f _92829) = (term460 A u f _92829 v).
Proof. exact (TRANS (@lem6969881 A u f _92829 v) (@lem6969896 A u f _92829 v)). Qed.
Lemma lem6969899 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term461 A x f v u.
Proof. exact (conj (@lem6969596 A x u v f h1 h2 h3) (@lem6969765 A x u v f h1 h2 h3)). Qed.
Lemma lem6969901 {A : Type'} (_92829 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term460 A u f _92829 v.
Proof. exact (EQ_MP (@lem6969897 A u f _92829 v) (@lem6969878 A _92829 u v f h1)). Qed.
Lemma lem6969902 {A : Type'} (_92829 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term460 A u f _92829 v.
Proof. exact (@lem6969901 A _92829 u v f h1). Qed.
Lemma lem6969903 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term462 A x f u v.
Proof. exact (@lem6969902 A (term244 A x f v u) u v f h1). Qed.
Lemma lem6969906 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term258 A x f u v.
Proof. exact (@lem6969903 A x u v f h3 (@lem6969899 A x u v f h1 h2 h3)). Qed.
Lemma lem6969907 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term463 A x f u v.
Proof. exact (fun h0 : term260 A x f u v => @lem6969906 A x u v f h1 h2 h3). Qed.
Lemma lem6969909 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6969910 {A : Type'} (x : type693 A) (f : A -> nat) (u : A -> Prop) (v : A -> Prop) : (term463 A x f u v) = (term258 A x f u v).
Proof. exact (@lem6969909 (term258 A x f u v)). Qed.
Lemma lem6969911 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term258 A x f u v.
Proof. exact (EQ_MP (@lem6969910 A x f u v) (@lem6969907 A x u v f h1 h2 h3)). Qed.
Lemma lem6969927 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6969928 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term464 A x _92828 _92827 _92826) = (term465 A x _92826 _92828 _92827).
Proof. exact (@lem6969927 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term260 A x _92826 _92828 _92827)). Qed.
Lemma lem6969936 {A : Type'} (_92827 : A -> Prop) : (term274 A _92827) = (term274 A _92827).
Proof. exact (eq_refl (term274 A _92827)). Qed.
Lemma lem6969937 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term340 A x _92828 _92827 _92826) = (term466 A x _92826 _92828 _92827).
Proof. exact (MK_COMB (@lem6969936 A _92827) (@lem6969928 A x _92826 _92828 _92827)). Qed.
Lemma lem6969941 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6969942 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term466 A x _92826 _92828 _92827) = (term467 A x _92826 _92828 _92827).
Proof. exact (@lem6969941 ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) (term273 A _92827) (term260 A x _92826 _92828 _92827)). Qed.
Lemma lem6969960 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term340 A x _92828 _92827 _92826) = (term467 A x _92826 _92828 _92827).
Proof. exact (TRANS (@lem6969937 A x _92826 _92828 _92827) (@lem6969942 A x _92826 _92828 _92827)). Qed.
Lemma lem6969961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6969962 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term468 A x _92828 _92827 _92826) = (term469 A x _92826 _92828 _92827).
Proof. exact (MK_COMB (@lem6969961) (@lem6969960 A x _92826 _92828 _92827)). Qed.
Lemma lem6969980 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term467 A x _92826 _92828 _92827) = (term467 A x _92826 _92828 _92827).
Proof. exact (eq_refl (term467 A x _92826 _92828 _92827)). Qed.
Lemma lem6969981 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : ((term340 A x _92828 _92827 _92826) = (term467 A x _92826 _92828 _92827)) = ((term467 A x _92826 _92828 _92827) = (term467 A x _92826 _92828 _92827)).
Proof. exact (MK_COMB (@lem6969962 A x _92826 _92828 _92827) (@lem6969980 A x _92826 _92828 _92827)). Qed.
Lemma lem6969983 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6969984 (x : Prop) : (x = x) = True.
Proof. exact (@lem6969983 Prop x). Qed.
Lemma lem6969985 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : ((term467 A x _92826 _92828 _92827) = (term467 A x _92826 _92828 _92827)) = True.
Proof. exact (@lem6969984 (term467 A x _92826 _92828 _92827)). Qed.
Lemma lem6969986 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : ((term340 A x _92828 _92827 _92826) = (term467 A x _92826 _92828 _92827)) = True.
Proof. exact (TRANS (@lem6969981 A x _92826 _92828 _92827) (@lem6969985 A x _92826 _92828 _92827)). Qed.
Lemma lem6969987 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : True = ((term340 A x _92828 _92827 _92826) = (term467 A x _92826 _92828 _92827)).
Proof. exact (SYM (@lem6969986 A x _92826 _92828 _92827)). Qed.
Lemma lem6969988 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term340 A x _92828 _92827 _92826) = (term467 A x _92826 _92828 _92827).
Proof. exact (EQ_MP (@lem6969987 A x _92826 _92828 _92827) (@lem0)). Qed.
Lemma lem6969989 {A : Type'} (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) (x : type693 A) (h1 : term222 A x) : term467 A x _92826 _92828 _92827.
Proof. exact (EQ_MP (@lem6969988 A x _92826 _92828 _92827) (@lem6968952 A _92828 _92827 _92826 x h1)). Qed.
Lemma lem6969991 (b : Prop) (a : Prop) : (a \/ b) = (term366 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6969992 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term467 A x _92826 _92828 _92827) = (term470 A x _92828 _92827 _92826).
Proof. exact (@lem6969991 (term319 A x _92826 _92828 _92827) ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6969994 (a : Prop) (b : Prop) : (term369 a b) = (term370 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6969995 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term471 A x _92826 _92828 _92827) = (term472 A x _92826 _92828 _92827).
Proof. exact (@lem6969994 (term273 A _92827) (term260 A x _92826 _92828 _92827)). Qed.
Lemma lem6969997 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6969998 {A : Type'} (_92827 : A -> Prop) : (term425 A _92827) = (@I ((A -> Prop) -> Prop) (@FINITE A) _92827).
Proof. exact (@lem6969997 (@I ((A -> Prop) -> Prop) (@FINITE A) _92827)). Qed.
Lemma lem6969999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6970000 {A : Type'} (_92827 : A -> Prop) : (term426 A _92827) = (term301 A _92827).
Proof. exact (MK_COMB (@lem6969999) (@lem6969998 A _92827)). Qed.
Lemma lem6970002 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6970003 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term473 A x _92826 _92828 _92827) = (term258 A x _92826 _92828 _92827).
Proof. exact (@lem6970002 (term258 A x _92826 _92828 _92827)). Qed.
Lemma lem6970004 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term472 A x _92826 _92828 _92827) = (term474 A x _92826 _92828 _92827).
Proof. exact (MK_COMB (@lem6970000 A _92827) (@lem6970003 A x _92826 _92828 _92827)). Qed.
Lemma lem6970005 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term471 A x _92826 _92828 _92827) = (term474 A x _92826 _92828 _92827).
Proof. exact (TRANS (@lem6969995 A x _92826 _92828 _92827) (@lem6970004 A x _92826 _92828 _92827)). Qed.
Lemma lem6970006 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6970007 {A : Type'} (x : type693 A) (_92826 : A -> nat) (_92828 : A -> Prop) (_92827 : A -> Prop) : (term475 A x _92826 _92828 _92827) = (term476 A x _92826 _92828 _92827).
Proof. exact (MK_COMB (@lem6970006) (@lem6970005 A x _92826 _92828 _92827)). Qed.
Lemma lem6970008 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)) = ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826)).
Proof. exact (eq_refl ((term238 A _92827 _92828 _92826) = (term239 A _92827 _92826))). Qed.
Lemma lem6970009 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term470 A x _92828 _92827 _92826) = (term477 A x _92828 _92827 _92826).
Proof. exact (MK_COMB (@lem6970007 A x _92826 _92828 _92827) (@lem6970008 A _92828 _92827 _92826)). Qed.
Lemma lem6970010 {A : Type'} (x : type693 A) (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) : (term467 A x _92826 _92828 _92827) = (term477 A x _92828 _92827 _92826).
Proof. exact (TRANS (@lem6969992 A x _92828 _92827 _92826) (@lem6970009 A x _92828 _92827 _92826)). Qed.
Lemma lem6970012 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : term474 A x f u v.
Proof. exact (conj (@lem6969435 A u v f h3) (@lem6969911 A x u v f h1 h2 h3)). Qed.
Lemma lem6970014 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term477 A x _92828 _92827 _92826.
Proof. exact (EQ_MP (@lem6970010 A x _92828 _92827 _92826) (@lem6969989 A _92826 _92828 _92827 x h1)). Qed.
Lemma lem6970015 {A : Type'} (_92828 : A -> Prop) (_92827 : A -> Prop) (_92826 : A -> nat) (x : type693 A) (h1 : term222 A x) : term477 A x _92828 _92827 _92826.
Proof. exact (@lem6970014 A _92828 _92827 _92826 x h1). Qed.
Lemma lem6970016 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (x : type693 A) (h1 : term222 A x) : term477 A x u v f.
Proof. exact (@lem6970015 A u v f x h1). Qed.
Lemma lem6970019 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term411 A u v f) (h3 : term64 A u v f) : (term238 A v u f) = (term239 A v f).
Proof. exact (@lem6970016 A u v f x h1 (@lem6970012 A x u v f h1 h2 h3)). Qed.
Lemma lem6970020 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term64 A u v f) : term478 A u v f.
Proof. exact (fun h0 : term411 A u v f => @lem6970019 A x u v f h1 h0 h2). Qed.
Lemma lem6970022 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6970023 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term478 A u v f) = ((term238 A v u f) = (term239 A v f)).
Proof. exact (@lem6970022 ((term238 A v u f) = (term239 A v f))). Qed.
Lemma lem6970024 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term222 A x) (h2 : term64 A u v f) : (term238 A v u f) = (term239 A v f).
Proof. exact (EQ_MP (@lem6970023 A u v f) (@lem6970020 A x u v f h1 h2)). Qed.
Lemma lem6970042 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6970043 (y : nat) (x : nat) (z : nat) : (term479 x y z) = (term480 y x z).
Proof. exact (@lem6970042 (y = z) (term481 x z)). Qed.
Lemma lem6970053 (x : nat) (y : nat) : (term482 x y) = (term482 x y).
Proof. exact (eq_refl (term482 x y)). Qed.
Lemma lem6970054 (y : nat) (x : nat) (z : nat) : (term350 x y z) = (term483 y x z).
Proof. exact (MK_COMB (@lem6970053 x y) (@lem6970043 y x z)). Qed.
Lemma lem6970058 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6970059 (y : nat) (x : nat) (z : nat) : (term483 y x z) = (term484 y x z).
Proof. exact (@lem6970058 (y = z) (term481 x y) (term481 x z)). Qed.
Lemma lem6970081 (y : nat) (x : nat) (z : nat) : (term350 x y z) = (term484 y x z).
Proof. exact (TRANS (@lem6970054 y x z) (@lem6970059 y x z)). Qed.
Lemma lem6970082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6970083 (y : nat) (x : nat) (z : nat) : (term485 x y z) = (term486 y x z).
Proof. exact (MK_COMB (@lem6970082) (@lem6970081 y x z)). Qed.
Lemma lem6970105 (y : nat) (x : nat) (z : nat) : (term484 y x z) = (term484 y x z).
Proof. exact (eq_refl (term484 y x z)). Qed.
Lemma lem6970106 (y : nat) (x : nat) (z : nat) : ((term350 x y z) = (term484 y x z)) = ((term484 y x z) = (term484 y x z)).
Proof. exact (MK_COMB (@lem6970083 y x z) (@lem6970105 y x z)). Qed.
Lemma lem6970108 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6970109 (x : Prop) : (x = x) = True.
Proof. exact (@lem6970108 Prop x). Qed.
Lemma lem6970110 (y : nat) (x : nat) (z : nat) : ((term484 y x z) = (term484 y x z)) = True.
Proof. exact (@lem6970109 (term484 y x z)). Qed.
Lemma lem6970111 (y : nat) (x : nat) (z : nat) : ((term350 x y z) = (term484 y x z)) = True.
Proof. exact (TRANS (@lem6970106 y x z) (@lem6970110 y x z)). Qed.
Lemma lem6970112 (y : nat) (x : nat) (z : nat) : True = ((term350 x y z) = (term484 y x z)).
Proof. exact (SYM (@lem6970111 y x z)). Qed.
Lemma lem6970113 (y : nat) (x : nat) (z : nat) : (term350 x y z) = (term484 y x z).
Proof. exact (EQ_MP (@lem6970112 y x z) (@lem0)). Qed.
Lemma lem6970114 (y : nat) (x : nat) (z : nat) : term484 y x z.
Proof. exact (EQ_MP (@lem6970113 y x z) (@lem6969129 x y z)). Qed.
Lemma lem6970116 (b : Prop) (a : Prop) : (a \/ b) = (term366 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6970117 (x : nat) (y : nat) (z : nat) : (term484 y x z) = (term487 x y z).
Proof. exact (@lem6970116 (term488 y x z) (y = z)). Qed.
Lemma lem6970119 (a : Prop) (b : Prop) : (term369 a b) = (term370 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6970120 (y : nat) (x : nat) (z : nat) : (term489 y x z) = (term490 y x z).
Proof. exact (@lem6970119 (term481 x y) (term481 x z)). Qed.
Lemma lem6970122 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6970123 (x : nat) (y : nat) : (term491 x y) = (x = y).
Proof. exact (@lem6970122 (x = y)). Qed.
Lemma lem6970124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6970125 (x : nat) (y : nat) : (term492 x y) = (term493 x y).
Proof. exact (MK_COMB (@lem6970124) (@lem6970123 x y)). Qed.
Lemma lem6970127 (a : Prop) : (term373 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6970128 (x : nat) (z : nat) : (term491 x z) = (x = z).
Proof. exact (@lem6970127 (x = z)). Qed.
Lemma lem6970129 (y : nat) (x : nat) (z : nat) : (term490 y x z) = (term494 y x z).
Proof. exact (MK_COMB (@lem6970125 x y) (@lem6970128 x z)). Qed.
Lemma lem6970130 (y : nat) (x : nat) (z : nat) : (term489 y x z) = (term494 y x z).
Proof. exact (TRANS (@lem6970120 y x z) (@lem6970129 y x z)). Qed.
Lemma lem6970131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6970132 (y : nat) (x : nat) (z : nat) : (term495 y x z) = (term496 y x z).
Proof. exact (MK_COMB (@lem6970131) (@lem6970130 y x z)). Qed.
Lemma lem6970133 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6970134 (x : nat) (y : nat) (z : nat) : (term487 x y z) = (term497 x y z).
Proof. exact (MK_COMB (@lem6970132 y x z) (@lem6970133 y z)). Qed.
Lemma lem6970135 (x : nat) (y : nat) (z : nat) : (term484 y x z) = (term497 x y z).
Proof. exact (TRANS (@lem6970117 x y z) (@lem6970134 x y z)). Qed.
Lemma lem6970137 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term64 A u v f) : term498 A u v f.
Proof. exact (conj (@lem6969428 A u v f h1) (@lem6970024 A x u v f h2 h3)). Qed.
Lemma lem6970139 (x : nat) (y : nat) (z : nat) : term497 x y z.
Proof. exact (EQ_MP (@lem6970135 x y z) (@lem6970114 y x z)). Qed.
Lemma lem6970140 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term499 A u v f.
Proof. exact (@lem6970139 (term238 A v u f) (term238 A u v f) (term239 A v f)). Qed.
Lemma lem6970143 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term64 A u v f) : (term238 A u v f) = (term239 A v f).
Proof. exact (@lem6970140 A u v f (@lem6970137 A x u v f h1 h2 h3)). Qed.
Lemma lem6970144 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term64 A u v f) : term500 A u v f.
Proof. exact (fun h0 : term290 A u v f => @lem6970143 A x u v f h1 h2 h3). Qed.
Lemma lem6970146 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6970147 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term500 A u v f) = ((term238 A u v f) = (term239 A v f)).
Proof. exact (@lem6970146 ((term238 A u v f) = (term239 A v f))). Qed.
Lemma lem6970148 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term64 A u v f) : (term238 A u v f) = (term239 A v f).
Proof. exact (EQ_MP (@lem6970147 A u v f) (@lem6970144 A x u v f h1 h2 h3)). Qed.
Lemma lem6970151 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6970153 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term290 A u v f) = (term501 A u v f).
Proof. exact (@lem6970151 ((term238 A u v f) = (term239 A v f))). Qed.
Lemma lem6970156 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term64 A u v f) : term501 A u v f.
Proof. exact (EQ_MP (@lem6970153 A u v f) (@lem6968902 A u v f h1)). Qed.
Lemma lem6970159 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term64 A u v f) : False.
Proof. exact (@lem6970156 A u v f h3 (@lem6970148 A x u v f h1 h2 h3)). Qed.
Lemma lem6970160 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term64 A u v f) : term502.
Proof. exact (fun h0 : ~ False => @lem6970159 A x u v f h1 h2 h3). Qed.
Lemma lem6970162 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6970163 : term502 = False.
Proof. exact (@lem6970162 False). Qed.
Lemma lem6970164 {A : Type'} (x : type693 A) (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term64 A u v f) : False.
Proof. exact (EQ_MP (@lem6970163) (@lem6970160 A x u v f h1 h2 h3)). Qed.
Lemma lem6970165 {A : Type'} (x : type693 A) (u : A -> Prop) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term74 A u f) : False.
Proof. exact (ex_elim (@lem6968383 A u f h3) (fun v : A -> Prop => fun h0 : term73 A u f v => @lem6970164 A x u v f h1 h2 h0)). Qed.
Lemma lem6970166 {A : Type'} (x : type693 A) (f : A -> nat) (h1 : term12 A) (h2 : term222 A x) (h3 : term81 A f) : False.
Proof. exact (ex_elim (@lem6968382 A f h3) (fun u : A -> Prop => fun h0 : term80 A f u => @lem6970165 A x u f h1 h2 h0)). Qed.
Lemma lem6970167 {A : Type'} (x : type693 A) (h1 : term12 A) (h2 : term222 A x) (h3 : term10 A) : False.
Proof. exact (ex_elim (@lem6968059 A h3) (fun f : A -> nat => fun h0 : term88 A f => @lem6970166 A x f h1 h2 h0)). Qed.
Lemma lem6970168 {A : Type'} (h1 : term12 A) (h2 : term11 A) (h3 : term10 A) : False.
Proof. exact (ex_elim (@lem6968380 A h2) (fun x : type693 A => fun h0 : term224 A x => @lem6970167 A x h1 h0 h3)). Qed.
Lemma lem6970169 {A : Type'} (h1 : term12 A) (h2 : term11 A) (h3 : term10 A) : (term12 A) = False.
Proof. exact (prop_ext (fun h4 : term12 A => @lem6970168 A h1 h2 h3) (fun h4 : False => @lem6968079 A h1)). Qed.
Lemma lem6970170 {A : Type'} (h1 : term12 A) (h2 : term11 A) (h3 : term10 A) : False.
Proof. exact (EQ_MP (@lem6970169 A h1 h2 h3) (@lem6968079 A h1)). Qed.
Lemma lem6970171 {A : Type'} (h1 : term12 A) (h2 : term10 A) : term17 A.
Proof. exact (fun h0 : term11 A => @lem6970170 A h1 h0 h2). Qed.
Lemma lem6970172 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem6970173 {A : Type'} (h1 : term12 A) (h2 : term10 A) : term18 A.
Proof. exact (EQ_MP (@lem6970172 A) (@lem6970171 A h1 h2)). Qed.
Lemma lem6970174 {A : Type'} (h1 : term10 A) : term21 A.
Proof. exact (fun h0 : term12 A => @lem6970173 A h0 h1). Qed.
Lemma lem6970175 {A : Type'} : term23 A.
Proof. exact (fun h0 : term10 A => @lem6970174 A h0). Qed.
Lemma lem6970176 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem6967889 A) (@lem6970175 A)). Qed.
Lemma lem6970178 {A : Type'} : term13 A.
Proof. exact (@lem6967651 A (@lem6970176 A)). Qed.
Lemma lem6970179 {A : Type'} (h1 : term10 A) : term20 A.
Proof. exact (@lem6970178 A (@lem6967630 A h1)). Qed.
Lemma lem6970180 {A : Type'} (h1 : term10 A) : term17 A.
Proof. exact (@lem6970179 A h1 (@lem6967635 A)). Qed.
Lemma lem6970181 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem6970180 A h1 (@lem6967631 A)). Qed.
Lemma lem6970182 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem6970181 A h1) (fun h2 : False => @lem6967630 A h1)). Qed.
Lemma lem6970183 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem6970182 A h1) (@lem6967630 A h1)). Qed.
Lemma lem6970184 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem6970183 A h0). Qed.
Lemma lem6970185 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem6967629 A) (@lem6970184 A)). Qed.
