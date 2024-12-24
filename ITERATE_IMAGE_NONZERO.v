Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_IMAGE_NONZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INSERT_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import MONOIDAL_AC_spec.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm196_spec.
Require Import thm19699_spec.
Require Import thm197_spec.
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
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem6113746 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6113747 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6113748 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6113747 t1) (@lem6113746 t1)). Qed.
Lemma lem6113749 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6113748 t1 t2). Qed.
Lemma lem6113750 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6113751 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6113750 t1 t2) (@lem6113749 t1 t2)). Qed.
Lemma lem6113752 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6113751 t1 t2 t3). Qed.
Lemma lem6113753 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6113754 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6113753 t1 t2 t3) (@lem6113752 t1 t2 t3)). Qed.
Lemma lem6113755 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6113754 t1 t2 t3)). Qed.
Lemma lem6113756 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem6113757 {A B : Type'} (y : B) : (term7 A B y) = (term8 A B y).
Proof. exact (eq_refl (term7 A B y)). Qed.
Lemma lem6113758 {A B : Type'} (y : B) : term8 A B y.
Proof. exact (EQ_MP (@lem6113757 A B y) (@lem6113756 A B y)). Qed.
Lemma lem6113759 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (@lem6113758 A B y s). Qed.
Lemma lem6113760 {A B : Type'} (y : B) (s : A -> Prop) : (term9 A B y s) = (term10 A B y s).
Proof. exact (eq_refl (term9 A B y s)). Qed.
Lemma lem6113761 {A B : Type'} (y : B) (s : A -> Prop) : term10 A B y s.
Proof. exact (EQ_MP (@lem6113760 A B y s) (@lem6113759 A B y s)). Qed.
Lemma lem6113762 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term11 A B y s f.
Proof. exact (@lem6113761 A B y s f). Qed.
Lemma lem6113763 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y s f) = ((term12 A B y f s) = (term13 A B y f s)).
Proof. exact (eq_refl (term11 A B y s f)). Qed.
Lemma lem6113765 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6113766 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6113767 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6113766 t1) (@lem6113765 t1)). Qed.
Lemma lem6113768 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6113767 t1 t2). Qed.
Lemma lem6113769 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6113770 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6113769 t1 t2) (@lem6113768 t1 t2)). Qed.
Lemma lem6113771 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6113770 t1 t2 t3). Qed.
Lemma lem6113772 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6113773 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6113772 t1 t2 t3) (@lem6113771 t1 t2 t3)). Qed.
Lemma lem6113774 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6113773 t1 t2 t3)). Qed.
Lemma lem6113775 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem6113776 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem6113777 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem6113776 A x) (@lem6113775 A x)). Qed.
Lemma lem6113778 {A : Type'} (x : A) (y : A) : term16 A x y.
Proof. exact (@lem6113777 A x y). Qed.
Lemma lem6113779 {A : Type'} (y : A) (x : A) : (term16 A x y) = (term17 A y x).
Proof. exact (eq_refl (term16 A x y)). Qed.
Lemma lem6113780 {A : Type'} (y : A) (x : A) : term17 A y x.
Proof. exact (EQ_MP (@lem6113779 A y x) (@lem6113778 A x y)). Qed.
Lemma lem6113781 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term18 A y x s.
Proof. exact (@lem6113780 A y x s). Qed.
Lemma lem6113782 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term18 A y x s) = ((term19 A x y s) = (term20 A y x s)).
Proof. exact (eq_refl (term18 A y x s)). Qed.
Lemma lem6113784 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem6113785 {A : Type'} (P : type686 A) (h1 : term21 A) : term22 A P.
Proof. exact (@lem6113784 A h1 P). Qed.
Lemma lem6113786 {A : Type'} (P : type686 A) : (term22 A P) = (term23 A P).
Proof. exact (eq_refl (term22 A P)). Qed.
Lemma lem6113787 {A : Type'} (P : type686 A) (h1 : term21 A) : term23 A P.
Proof. exact (EQ_MP (@lem6113786 A P) (@lem6113785 A P h1)). Qed.
Lemma lem6113788 {A : Type'} (P : type686 A) (h1 : term24 A P) : term24 A P.
Proof. exact (h1). Qed.
Lemma lem6113789 {A : Type'} (P : type686 A) (h1 : term21 A) (h2 : term24 A P) : term25 A P.
Proof. exact (@lem6113787 A P h1 (@lem6113788 A P h2)). Qed.
Lemma lem6113790 {A : Type'} (P : type686 A) (h1 : term24 A P) : term26 A P.
Proof. exact (fun h0 : term21 A => @lem6113789 A P h0 h1). Qed.
Lemma lem6113791 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem6113792 {A : Type'} (P : type686 A) (h1 : term21 A) (h2 : term24 A P) : term25 A P.
Proof. exact (@lem6113790 A P h2 (@lem6113791 A h1)). Qed.
Lemma lem6113793 {A : Type'} (P : type686 A) (h1 : term21 A) : term23 A P.
Proof. exact (fun h0 : term24 A P => @lem6113792 A P h1 h0). Qed.
Lemma lem6113794 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (fun P : type686 A => @lem6113793 A P h1). Qed.
Lemma lem6113795 {A : Type'} : term27 A.
Proof. exact (fun h0 : term21 A => @lem6113794 A h0). Qed.
Lemma lem6113796 {A : Type'} : term21 A.
Proof. exact (@lem6113795 A (@lem3558722 A)). Qed.
Lemma lem6113797 {A : Type'} (P : type686 A) : term22 A P.
Proof. exact (@lem6113796 A P). Qed.
Lemma lem6113798 {A : Type'} (P : type686 A) : (term22 A P) = (term23 A P).
Proof. exact (eq_refl (term22 A P)). Qed.
Lemma lem6113800 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem6113806 (p : Prop) (q : Prop) (r : Prop) : (term28 p q r) = (term29 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem6113807 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term30 A B C op s g f) = (term31 A B C op s g f).
Proof. exact (@lem6113806 (@FINITE A s) (term32 A B C s g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6113808 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term35 A B C op g f) = (term36 A B C op g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6113807 A B C op s g f)). Qed.
Lemma lem6113809 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6113810 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term37 A B C op g f) = (term38 A B C op g f).
Proof. exact (MK_COMB (@lem6113809 A) (@lem6113808 A B C op g f)). Qed.
Lemma lem6113811 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term38 A B C op g f) = (term37 A B C op g f).
Proof. exact (SYM (@lem6113810 A B C op g f)). Qed.
Lemma lem6113813 {A : Type'} (P : type686 A) : term23 A P.
Proof. exact (EQ_MP (@lem6113798 A P) (@lem6113797 A P)). Qed.
Lemma lem6113814 {A : Type'} (P : type686 A) : term23 A P.
Proof. exact (@lem6113813 A P). Qed.
Lemma lem6113815 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : term39 A B C op g f.
Proof. exact (@lem6113814 A (term40 A B C op g f)). Qed.
Lemma lem6113816 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term41 A B C op g f) = (term42 A B C op g f).
Proof. exact (eq_refl (term41 A B C op g f)). Qed.
Lemma lem6113817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6113818 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term43 A B C op g f) = (term44 A B C op g f).
Proof. exact (MK_COMB (@lem6113817) (@lem6113816 A B C op g f)). Qed.
Lemma lem6113819 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term45 A B C op g f s) = (term46 A B C op s g f).
Proof. exact (eq_refl (term45 A B C op g f s)). Qed.
Lemma lem6113820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6113821 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term47 A B C op g f s) = (term48 A B C op s g f).
Proof. exact (MK_COMB (@lem6113820) (@lem6113819 A B C op s g f)). Qed.
Lemma lem6113822 {A : Type'} (x : A) (s : A -> Prop) : (term49 A x s) = (term49 A x s).
Proof. exact (eq_refl (term49 A x s)). Qed.
Lemma lem6113823 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) : (term50 A B C op g f x s) = (term51 A B C op g f x s).
Proof. exact (MK_COMB (@lem6113821 A B C op s g f) (@lem6113822 A x s)). Qed.
Lemma lem6113824 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6113825 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) : (term52 A B C op g f x s) = (term53 A B C op g f x s).
Proof. exact (MK_COMB (@lem6113824) (@lem6113823 A B C op g f x s)). Qed.
Lemma lem6113826 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term54 A B C op g f x s) = (term55 A B C op x s g f).
Proof. exact (eq_refl (term54 A B C op g f x s)). Qed.
Lemma lem6113827 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term56 A B C op g f x s) = (term57 A B C op x s g f).
Proof. exact (MK_COMB (@lem6113825 A B C op g f x s) (@lem6113826 A B C op x s g f)). Qed.
Lemma lem6113828 {A B C : Type'} (op : type1400 C) (x : A) (g : B -> C) (f : A -> B) : (term58 A B C op g f x) = (term59 A B C op x g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6113827 A B C op x s g f)). Qed.
Lemma lem6113829 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6113830 {A B C : Type'} (op : type1400 C) (x : A) (g : B -> C) (f : A -> B) : (term60 A B C op g f x) = (term61 A B C op x g f).
Proof. exact (MK_COMB (@lem6113829 A) (@lem6113828 A B C op x g f)). Qed.
Lemma lem6113831 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term62 A B C op g f) = (term63 A B C op g f).
Proof. exact (fun_ext (fun x : A => @lem6113830 A B C op x g f)). Qed.
Lemma lem6113832 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6113833 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term64 A B C op g f) = (term65 A B C op g f).
Proof. exact (MK_COMB (@lem6113832 A) (@lem6113831 A B C op g f)). Qed.
Lemma lem6113834 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term66 A B C op g f) = (term67 A B C op g f).
Proof. exact (MK_COMB (@lem6113818 A B C op g f) (@lem6113833 A B C op g f)). Qed.
Lemma lem6113835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6113836 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term68 A B C op g f) = (term69 A B C op g f).
Proof. exact (MK_COMB (@lem6113835) (@lem6113834 A B C op g f)). Qed.
Lemma lem6113837 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term45 A B C op g f s) = (term46 A B C op s g f).
Proof. exact (eq_refl (term45 A B C op g f s)). Qed.
Lemma lem6113838 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem6113839 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term71 A B C op g f s) = (term31 A B C op s g f).
Proof. exact (MK_COMB (@lem6113838 A s) (@lem6113837 A B C op s g f)). Qed.
Lemma lem6113840 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term72 A B C op g f) = (term36 A B C op g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6113839 A B C op s g f)). Qed.
Lemma lem6113841 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6113842 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term73 A B C op g f) = (term38 A B C op g f).
Proof. exact (MK_COMB (@lem6113841 A) (@lem6113840 A B C op g f)). Qed.
Lemma lem6113843 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term39 A B C op g f) = (term74 A B C op g f).
Proof. exact (MK_COMB (@lem6113836 A B C op g f) (@lem6113842 A B C op g f)). Qed.
Lemma lem6113844 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : term74 A B C op g f.
Proof. exact (EQ_MP (@lem6113843 A B C op g f) (@lem6113815 A B C op g f)). Qed.
Lemma lem6113845 {A B : Type'} (f : A -> B) : term75 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem6113846 {A B : Type'} (f : A -> B) : (term75 A B f) = (term76 A B f).
Proof. exact (eq_refl (term75 A B f)). Qed.
Lemma lem6113847 {A B : Type'} (f : A -> B) : term76 A B f.
Proof. exact (EQ_MP (@lem6113846 A B f) (@lem6113845 A B f)). Qed.
Lemma lem6113848 {A B : Type'} (f : A -> B) (s : A -> Prop) : term77 A B f s.
Proof. exact (@lem6113847 A B f s). Qed.
Lemma lem6113849 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term77 A B f s) = (term78 A B f s).
Proof. exact (eq_refl (term77 A B f s)). Qed.
Lemma lem6113850 {A B : Type'} (f : A -> B) (s : A -> Prop) : term78 A B f s.
Proof. exact (EQ_MP (@lem6113849 A B f s) (@lem6113848 A B f s)). Qed.
Lemma lem6113851 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6113852 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term79 A B f s.
Proof. exact (@lem6113850 A B f s (@lem6113851 A s h1)). Qed.
Lemma lem6113853 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term79 A B f s) = ((term79 A B f s) = True).
Proof. exact (@lem7 (term79 A B f s)). Qed.
Lemma lem6113854 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term79 A B f s) = True.
Proof. exact (EQ_MP (@lem6113853 A B f s) (@lem6113852 A B f s h1)). Qed.
Lemma lem6113860 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term80 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6113861 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term80 _120477 _120519 _120521 op) = (term81 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term80 _120477 _120519 _120521 op)). Qed.
Lemma lem6113862 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term81 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6113861 _120477 _120519 _120521 op) (@lem6113860 _120477 _120519 _120521 op)). Qed.
Lemma lem6113863 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6113864 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term82 _120477 _120519 _120521 op.
Proof. exact (@lem6113862 _120477 _120519 _120521 op (@lem6113863 _120519 op h1)). Qed.
Lemma lem6113865 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term83 _120519 _120521 op.
Proof. exact (proj2 (@lem6113864 Prop _120519 _120521 op h1)). Qed.
Lemma lem6113866 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term84 _120519 _120521 op f.
Proof. exact (@lem6113865 _120519 _120521 op h1 f). Qed.
Lemma lem6113867 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term84 _120519 _120521 op f) = (term85 _120519 _120521 op f).
Proof. exact (eq_refl (term84 _120519 _120521 op f)). Qed.
Lemma lem6113868 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term85 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem6113867 _120519 _120521 op f) (@lem6113866 _120519 _120521 f op h1)). Qed.
Lemma lem6113869 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term86 _120519 _120521 op f x.
Proof. exact (@lem6113868 _120519 _120521 f op h1 x). Qed.
Lemma lem6113870 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term86 _120519 _120521 op f x) = (term87 _120519 _120521 x op f).
Proof. exact (eq_refl (term86 _120519 _120521 op f x)). Qed.
Lemma lem6113871 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term87 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem6113870 _120519 _120521 x op f) (@lem6113869 _120519 _120521 f x op h1)). Qed.
Lemma lem6113872 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term88 _120519 _120521 x op f s.
Proof. exact (@lem6113871 _120519 _120521 x f op h1 s). Qed.
Lemma lem6113873 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term88 _120519 _120521 x op f s) = (term89 _120519 _120521 x op s f).
Proof. exact (eq_refl (term88 _120519 _120521 x op f s)). Qed.
Lemma lem6113874 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term89 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6113873 _120519 _120521 x op s f) (@lem6113872 _120519 _120521 x f s op h1)). Qed.
Lemma lem6113875 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem6113876 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term90 _120519 _120521 op x s f) = (term91 _120519 _120521 x op s f).
Proof. exact (@lem6113874 _120519 _120521 x s f op h2 (@lem6113875 _120521 s h1)). Qed.
Lemma lem6113877 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term92 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6113876 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem6113878 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term93 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem6113877 _120519 _120521 x op f s h0). Qed.
Lemma lem6113880 (p : Prop) (q : Prop) (r : Prop) : (term29 p q r) = (term28 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6113885 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term93 _120519 _120521 x op s f) = (term94 _120519 _120521 x op s f).
Proof. exact (@lem6113880 (@FINITE _120521 s) (@monoidal _120519 op) ((term90 _120519 _120521 op x s f) = (term91 _120519 _120521 x op s f))). Qed.
Lemma lem6113887 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term95 _120477 _120519 op.
Proof. exact (proj1 (@lem6113864 _120477 _120519 Prop op h1)). Qed.
Lemma lem6113888 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term96 _120477 _120519 op f.
Proof. exact (@lem6113887 _120477 _120519 op h1 f). Qed.
Lemma lem6113889 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term96 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term96 _120477 _120519 op f)). Qed.
Lemma lem6113890 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem6113889 _120477 _120519 f op) (@lem6113888 _120477 _120519 f op h1)). Qed.
Lemma lem6113898 {C : Type'} (op : type1400 C) : (@monoidal C op) = ((@monoidal C op) = True).
Proof. exact (@lem7 (@monoidal C op)). Qed.
Lemma lem6113905 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term97 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6113906 (p : Prop) (q : Prop) (p' : Prop) : term98 p q p'.
Proof. exact (fun q' : Prop => @lem6113905 p q p' q'). Qed.
Lemma lem6113907 (p : Prop) (q : Prop) : term99 p q.
Proof. exact (fun p' : Prop => @lem6113906 p q p'). Qed.
Lemma lem6113908 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : term100 A B C op g f.
Proof. exact (@lem6113907 (term101 A B C g f op) ((term102 A B C op f g) = (term103 A B C op g f))). Qed.
Lemma lem6113909 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (p' : Prop) : term104 A B C op g f p'.
Proof. exact (@lem6113908 A B C op g f p'). Qed.
Lemma lem6113910 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (p' : Prop) : (term104 A B C op g f p') = (term105 A B C op g f p').
Proof. exact (eq_refl (term104 A B C op g f p')). Qed.
Lemma lem6113911 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (p' : Prop) : term105 A B C op g f p'.
Proof. exact (EQ_MP (@lem6113910 A B C op g f p') (@lem6113909 A B C op g f p')). Qed.
Lemma lem6113912 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term106 A B C op g f p' q'.
Proof. exact (@lem6113911 A B C op g f p' q'). Qed.
Lemma lem6113913 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : (term106 A B C op g f p' q') = (term107 A B C op g f p' q').
Proof. exact (eq_refl (term106 A B C op g f p' q')). Qed.
Lemma lem6113914 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term107 A B C op g f p' q'.
Proof. exact (EQ_MP (@lem6113913 A B C op g f p' q') (@lem6113912 A B C op g f p' q')). Qed.
Lemma lem6113926 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term97 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6113927 (p : Prop) (q : Prop) (p' : Prop) : term98 p q p'.
Proof. exact (fun q' : Prop => @lem6113926 p q p' q'). Qed.
Lemma lem6113928 (p : Prop) (q : Prop) : term99 p q.
Proof. exact (fun p' : Prop => @lem6113927 p q p'). Qed.
Lemma lem6113929 {A B C : Type'} (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) : term108 A B C y g f x op.
Proof. exact (@lem6113928 (term109 A B x f y) ((term110 A B C g f x) = (@neutral C op))). Qed.
Lemma lem6113930 {A B C : Type'} (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) : term111 A B C y g f x op p'.
Proof. exact (@lem6113929 A B C y g f x op p'). Qed.
Lemma lem6113931 {A B C : Type'} (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) : (term111 A B C y g f x op p') = (term112 A B C y g f x op p').
Proof. exact (eq_refl (term111 A B C y g f x op p')). Qed.
Lemma lem6113932 {A B C : Type'} (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) : term112 A B C y g f x op p'.
Proof. exact (EQ_MP (@lem6113931 A B C y g f x op p') (@lem6113930 A B C y g f x op p')). Qed.
Lemma lem6113933 {A B C : Type'} (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) (q' : Prop) : term113 A B C y g f x op p' q'.
Proof. exact (@lem6113932 A B C y g f x op p' q'). Qed.
Lemma lem6113934 {A B C : Type'} (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) (q' : Prop) : (term113 A B C y g f x op p' q') = (term114 A B C y g f x op p' q').
Proof. exact (eq_refl (term113 A B C y g f x op p' q')). Qed.
Lemma lem6113935 {A B C : Type'} (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) (q' : Prop) : term114 A B C y g f x op p' q'.
Proof. exact (EQ_MP (@lem6113934 A B C y g f x op p' q') (@lem6113933 A B C y g f x op p' q')). Qed.
Lemma lem6113946 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term109 A B x f y) = (term109 A B x f y).
Proof. exact (eq_refl (term109 A B x f y)). Qed.
Lemma lem6113947 {A B C : Type'} (g : B -> C) (op : type1400 C) (x : A) (f : A -> B) (y : A) (q' : Prop) : term115 A B C g op x f y q'.
Proof. exact (@lem6113935 A B C y g f x op (term109 A B x f y) q'). Qed.
Lemma lem6113948 {A B C : Type'} (g : B -> C) (op : type1400 C) (x : A) (f : A -> B) (y : A) (q' : Prop) : term116 A B C g op x f y q'.
Proof. exact (@lem6113947 A B C g op x f y q' (@lem6113946 A B x f y)). Qed.
Lemma lem6113949 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : term109 A B x f y) : term109 A B x f y.
Proof. exact (h1). Qed.
Lemma lem6113950 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : term109 A B x f y) : term117 A B x f y.
Proof. exact (proj2 (@lem6113949 A B x f y h1)). Qed.
Lemma lem6113951 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : term109 A B x f y) : term118 A B x f y.
Proof. exact (proj2 (@lem6113950 A B x f y h1)). Qed.
Lemma lem6113976 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : term109 A B x f y) : (f x) = (f y).
Proof. exact (proj2 (@lem6113951 A B x f y h1)). Qed.
Lemma lem6113977 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6113978 {A B C : Type'} (g : B -> C) (x : A) (f : A -> B) (y : A) (h1 : term109 A B x f y) : (term110 A B C g f x) = (term110 A B C g f y).
Proof. exact (MK_COMB (@lem6113977 B C g) (@lem6113976 A B x f y h1)). Qed.
Lemma lem6113979 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6113980 {A B C : Type'} (g : B -> C) (x : A) (f : A -> B) (y : A) (h1 : term109 A B x f y) : (term119 A B C g f x) = (term119 A B C g f y).
Proof. exact (MK_COMB (@lem6113979 C) (@lem6113978 A B C g x f y h1)). Qed.
Lemma lem6113981 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6113982 {A B C : Type'} (g : B -> C) (op : type1400 C) (x : A) (f : A -> B) (y : A) (h1 : term109 A B x f y) : ((term110 A B C g f x) = (@neutral C op)) = ((term110 A B C g f y) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6113980 A B C g x f y h1) (@lem6113981 C op)). Qed.
Lemma lem6113985 {A B C : Type'} (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : term120 A B C x g f y op.
Proof. exact (fun h0 : term109 A B x f y => @lem6113982 A B C g op x f y h0). Qed.
Lemma lem6113986 {A B C : Type'} (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : term121 A B C x g f y op.
Proof. exact (@lem6113948 A B C g op x f y ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6113987 {A B C : Type'} (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term122 A B C y g f x op) = (term123 A B C x g f y op).
Proof. exact (@lem6113986 A B C x g f y op (@lem6113985 A B C x g f y op)). Qed.
Lemma lem6114056 {A B C : Type'} (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term124 A B C g f x op) = (term125 A B C x g f op).
Proof. exact (fun_ext (fun y : A => @lem6113987 A B C x g f y op)). Qed.
Lemma lem6114125 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6114126 {A B C : Type'} (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term126 A B C g f x op) = (term127 A B C x g f op).
Proof. exact (MK_COMB (@lem6114125 A) (@lem6114056 A B C x g f op)). Qed.
Lemma lem6114199 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) : (term128 A B C g f op) = (term129 A B C g f op).
Proof. exact (fun_ext (fun x : A => @lem6114126 A B C x g f op)). Qed.
Lemma lem6114272 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6114273 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) : (term101 A B C g f op) = (term130 A B C g f op).
Proof. exact (MK_COMB (@lem6114272 A) (@lem6114199 A B C g f op)). Qed.
Lemma lem6114350 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (q' : Prop) : term131 A B C g f op q'.
Proof. exact (@lem6113914 A B C op g f (term130 A B C g f op) q'). Qed.
Lemma lem6114351 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (q' : Prop) : term132 A B C g f op q'.
Proof. exact (@lem6114350 A B C g f op q' (@lem6114273 A B C g f op)). Qed.
Lemma lem6114395 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem6114396 {A B : Type'} (f : A -> B) : (@IMAGE A B f (@EMPTY A)) = (@EMPTY B).
Proof. exact (@lem6114395 A B f). Qed.
Lemma lem6114397 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@iterate C B op).
Proof. exact (eq_refl (@iterate C B op)). Qed.
Lemma lem6114398 {A B C : Type'} (f : A -> B) (op : type1400 C) : (term133 A B C op f) = (@iterate C B op (@EMPTY B)).
Proof. exact (MK_COMB (@lem6114397 B C op) (@lem6114396 A B f)). Qed.
Lemma lem6114399 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6114400 {A B C : Type'} (f : A -> B) (op : type1400 C) (g : B -> C) : (term102 A B C op f g) = (@iterate C B op (@EMPTY B) g).
Proof. exact (MK_COMB (@lem6114398 A B C f op) (@lem6114399 B C g)). Qed.
Lemma lem6114402 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term134 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6113890 _120477 _120519 f op h0). Qed.
Lemma lem6114403 {B C : Type'} (f : B -> C) (op : type1400 C) : term134 B C f op.
Proof. exact (@lem6114402 B C f op). Qed.
Lemma lem6114404 {B C : Type'} (g : B -> C) (op : type1400 C) : term134 B C g op.
Proof. exact (@lem6114403 B C g op). Qed.
Lemma lem6114406 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6113898 C op) (@lem6113800 C op h1)). Qed.
Lemma lem6114407 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem6114406 C op h1)). Qed.
Lemma lem6114408 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem6114407 C op h1) (@lem0)). Qed.
Lemma lem6114409 {B C : Type'} (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : (@iterate C B op (@EMPTY B) g) = (@neutral C op).
Proof. exact (@lem6114404 B C g op (@lem6114408 C op h1)). Qed.
Lemma lem6114410 {A B C : Type'} (f : A -> B) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : (term102 A B C op f g) = (@neutral C op).
Proof. exact (TRANS (@lem6114400 A B C f op g) (@lem6114409 B C g op h1)). Qed.
Lemma lem6114411 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6114412 {A B C : Type'} (f : A -> B) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : (term135 A B C op f g) = (term136 C op).
Proof. exact (MK_COMB (@lem6114411 C) (@lem6114410 A B C f g op h1)). Qed.
Lemma lem6114414 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term134 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6113890 _120477 _120519 f op h0). Qed.
Lemma lem6114415 {A C : Type'} (f : A -> C) (op : type1400 C) : term134 A C f op.
Proof. exact (@lem6114414 A C f op). Qed.
Lemma lem6114416 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) : term137 A B C g f op.
Proof. exact (@lem6114415 A C (@o A B C g f) op). Qed.
Lemma lem6114418 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6113898 C op) (@lem6113800 C op h1)). Qed.
Lemma lem6114419 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem6114418 C op h1)). Qed.
Lemma lem6114420 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem6114419 C op h1) (@lem0)). Qed.
Lemma lem6114421 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term103 A B C op g f) = (@neutral C op).
Proof. exact (@lem6114416 A B C g f op (@lem6114420 C op h1)). Qed.
Lemma lem6114422 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : ((term102 A B C op f g) = (term103 A B C op g f)) = ((@neutral C op) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6114412 A B C f g op h1) (@lem6114421 A B C g f op h1)). Qed.
Lemma lem6114424 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6114425 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem6114424 C x). Qed.
Lemma lem6114426 {C : Type'} (op : type1400 C) : ((@neutral C op) = (@neutral C op)) = True.
Proof. exact (@lem6114425 C (@neutral C op)). Qed.
Lemma lem6114427 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : ((term102 A B C op f g) = (term103 A B C op g f)) = True.
Proof. exact (TRANS (@lem6114422 A B C g f op h1) (@lem6114426 C op)). Qed.
Lemma lem6114428 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term138 A B C op g f.
Proof. exact (fun h0 : term130 A B C g f op => @lem6114427 A B C g f op h1). Qed.
Lemma lem6114429 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) : term139 A B C g f op.
Proof. exact (@lem6114351 A B C g f op True). Qed.
Lemma lem6114430 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term42 A B C op g f) = (term140 A B C g f op).
Proof. exact (@lem6114429 A B C g f op (@lem6114428 A B C g f op h1)). Qed.
Lemma lem6114432 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6114433 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) : (term140 A B C g f op) = True.
Proof. exact (@lem6114432 (term130 A B C g f op)). Qed.
Lemma lem6114434 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term42 A B C op g f) = True.
Proof. exact (TRANS (@lem6114430 A B C g f op h1) (@lem6114433 A B C g f op)). Qed.
Lemma lem6114435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6114436 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term44 A B C op g f) = (and True).
Proof. exact (MK_COMB (@lem6114435) (@lem6114434 A B C g f op h1)). Qed.
Lemma lem6114448 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term97 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6114449 (p : Prop) (q : Prop) (p' : Prop) : term98 p q p'.
Proof. exact (fun q' : Prop => @lem6114448 p q p' q'). Qed.
Lemma lem6114450 (p : Prop) (q : Prop) : term99 p q.
Proof. exact (fun p' : Prop => @lem6114449 p q p'). Qed.
Lemma lem6114451 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) : term141 A B C op x s g f.
Proof. exact (@lem6114450 (term51 A B C op g f x s) (term55 A B C op x s g f)). Qed.
Lemma lem6114452 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term142 A B C op x s g f p'.
Proof. exact (@lem6114451 A B C op x s g f p'). Qed.
Lemma lem6114453 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : (term142 A B C op x s g f p') = (term143 A B C op x s g f p').
Proof. exact (eq_refl (term142 A B C op x s g f p')). Qed.
Lemma lem6114454 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term143 A B C op x s g f p'.
Proof. exact (EQ_MP (@lem6114453 A B C op x s g f p') (@lem6114452 A B C op x s g f p')). Qed.
Lemma lem6114455 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term144 A B C op x s g f p' q'.
Proof. exact (@lem6114454 A B C op x s g f p' q'). Qed.
Lemma lem6114456 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : (term144 A B C op x s g f p' q') = (term145 A B C op x s g f p' q').
Proof. exact (eq_refl (term144 A B C op x s g f p' q')). Qed.
Lemma lem6114457 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term145 A B C op x s g f p' q'.
Proof. exact (EQ_MP (@lem6114456 A B C op x s g f p' q') (@lem6114455 A B C op x s g f p' q')). Qed.
Lemma lem6114463 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term97 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6114464 (p : Prop) (q : Prop) (p' : Prop) : term98 p q p'.
Proof. exact (fun q' : Prop => @lem6114463 p q p' q'). Qed.
Lemma lem6114465 (p : Prop) (q : Prop) : term99 p q.
Proof. exact (fun p' : Prop => @lem6114464 p q p'). Qed.
Lemma lem6114466 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term146 A B C op s g f.
Proof. exact (@lem6114465 (term32 A B C s g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6114467 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term147 A B C op s g f p'.
Proof. exact (@lem6114466 A B C op s g f p'). Qed.
Lemma lem6114468 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : (term147 A B C op s g f p') = (term148 A B C op s g f p').
Proof. exact (eq_refl (term147 A B C op s g f p')). Qed.
Lemma lem6114469 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term148 A B C op s g f p'.
Proof. exact (EQ_MP (@lem6114468 A B C op s g f p') (@lem6114467 A B C op s g f p')). Qed.
Lemma lem6114470 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term149 A B C op s g f p' q'.
Proof. exact (@lem6114469 A B C op s g f p' q'). Qed.
Lemma lem6114471 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : (term149 A B C op s g f p' q') = (term150 A B C op s g f p' q').
Proof. exact (eq_refl (term149 A B C op s g f p' q')). Qed.
Lemma lem6114472 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term150 A B C op s g f p' q'.
Proof. exact (EQ_MP (@lem6114471 A B C op s g f p' q') (@lem6114470 A B C op s g f p' q')). Qed.
Lemma lem6114484 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term97 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6114485 (p : Prop) (q : Prop) (p' : Prop) : term98 p q p'.
Proof. exact (fun q' : Prop => @lem6114484 p q p' q'). Qed.
Lemma lem6114486 (p : Prop) (q : Prop) : term99 p q.
Proof. exact (fun p' : Prop => @lem6114485 p q p'). Qed.
Lemma lem6114487 {A B C : Type'} (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) : term151 A B C s y g f x op.
Proof. exact (@lem6114486 (term152 A B s x f y) ((term110 A B C g f x) = (@neutral C op))). Qed.
Lemma lem6114488 {A B C : Type'} (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) : term153 A B C s y g f x op p'.
Proof. exact (@lem6114487 A B C s y g f x op p'). Qed.
Lemma lem6114489 {A B C : Type'} (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) : (term153 A B C s y g f x op p') = (term154 A B C s y g f x op p').
Proof. exact (eq_refl (term153 A B C s y g f x op p')). Qed.
Lemma lem6114490 {A B C : Type'} (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) : term154 A B C s y g f x op p'.
Proof. exact (EQ_MP (@lem6114489 A B C s y g f x op p') (@lem6114488 A B C s y g f x op p')). Qed.
Lemma lem6114491 {A B C : Type'} (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) (q' : Prop) : term155 A B C s y g f x op p' q'.
Proof. exact (@lem6114490 A B C s y g f x op p' q'). Qed.
Lemma lem6114492 {A B C : Type'} (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) (q' : Prop) : (term155 A B C s y g f x op p' q') = (term156 A B C s y g f x op p' q').
Proof. exact (eq_refl (term155 A B C s y g f x op p' q')). Qed.
Lemma lem6114493 {A B C : Type'} (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x : A) (op : type1400 C) (p' : Prop) (q' : Prop) : term156 A B C s y g f x op p' q'.
Proof. exact (EQ_MP (@lem6114492 A B C s y g f x op p' q') (@lem6114491 A B C s y g f x op p' q')). Qed.
Lemma lem6114504 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term152 A B s x f y) = (term152 A B s x f y).
Proof. exact (eq_refl (term152 A B s x f y)). Qed.
Lemma lem6114505 {A B C : Type'} (g : B -> C) (op : type1400 C) (s : A -> Prop) (x : A) (f : A -> B) (y : A) (q' : Prop) : term157 A B C g op s x f y q'.
Proof. exact (@lem6114493 A B C s y g f x op (term152 A B s x f y) q'). Qed.
Lemma lem6114506 {A B C : Type'} (g : B -> C) (op : type1400 C) (s : A -> Prop) (x : A) (f : A -> B) (y : A) (q' : Prop) : term158 A B C g op s x f y q'.
Proof. exact (@lem6114505 A B C g op s x f y q' (@lem6114504 A B s x f y)). Qed.
Lemma lem6114507 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term152 A B s x f y) : term152 A B s x f y.
Proof. exact (h1). Qed.
Lemma lem6114508 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term152 A B s x f y) : term159 A B s x f y.
Proof. exact (proj2 (@lem6114507 A B s x f y h1)). Qed.
Lemma lem6114509 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term152 A B s x f y) : term118 A B x f y.
Proof. exact (proj2 (@lem6114508 A B s x f y h1)). Qed.
Lemma lem6114534 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term152 A B s x f y) : (f x) = (f y).
Proof. exact (proj2 (@lem6114509 A B s x f y h1)). Qed.
Lemma lem6114535 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6114536 {A B C : Type'} (g : B -> C) (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term152 A B s x f y) : (term110 A B C g f x) = (term110 A B C g f y).
Proof. exact (MK_COMB (@lem6114535 B C g) (@lem6114534 A B s x f y h1)). Qed.
Lemma lem6114537 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6114538 {A B C : Type'} (g : B -> C) (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term152 A B s x f y) : (term119 A B C g f x) = (term119 A B C g f y).
Proof. exact (MK_COMB (@lem6114537 C) (@lem6114536 A B C g s x f y h1)). Qed.
Lemma lem6114539 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6114540 {A B C : Type'} (g : B -> C) (op : type1400 C) (s : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term152 A B s x f y) : ((term110 A B C g f x) = (@neutral C op)) = ((term110 A B C g f y) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6114538 A B C g s x f y h1) (@lem6114539 C op)). Qed.
Lemma lem6114543 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : term160 A B C s x g f y op.
Proof. exact (fun h0 : term152 A B s x f y => @lem6114540 A B C g op s x f y h0). Qed.
Lemma lem6114544 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : term161 A B C s x g f y op.
Proof. exact (@lem6114506 A B C g op s x f y ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6114545 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term162 A B C s y g f x op) = (term163 A B C s x g f y op).
Proof. exact (@lem6114544 A B C s x g f y op (@lem6114543 A B C s x g f y op)). Qed.
Lemma lem6114614 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term164 A B C s g f x op) = (term165 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6114545 A B C s x g f y op)). Qed.
Lemma lem6114683 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6114684 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term166 A B C s g f x op) = (term167 A B C s x g f op).
Proof. exact (MK_COMB (@lem6114683 A) (@lem6114614 A B C s x g f op)). Qed.
Lemma lem6114757 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term168 A B C s g f op) = (term169 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6114684 A B C s x g f op)). Qed.
Lemma lem6114830 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6114831 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term32 A B C s g f op) = (term170 A B C s g f op).
Proof. exact (MK_COMB (@lem6114830 A) (@lem6114757 A B C s g f op)). Qed.
Lemma lem6114908 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (q' : Prop) : term171 A B C s g f op q'.
Proof. exact (@lem6114472 A B C op s g f (term170 A B C s g f op) q'). Qed.
Lemma lem6114909 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (q' : Prop) : term172 A B C s g f op q'.
Proof. exact (@lem6114908 A B C s g f op q' (@lem6114831 A B C s g f op)). Qed.
Lemma lem6114952 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6114953 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term173 A B C op s g f.
Proof. exact (fun h0 : term170 A B C s g f op => @lem6114952 A B C op s g f). Qed.
Lemma lem6114954 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term174 A B C op s g f.
Proof. exact (@lem6114909 A B C s g f op ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6114955 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term46 A B C op s g f) = (term175 A B C op s g f).
Proof. exact (@lem6114954 A B C op s g f (@lem6114953 A B C op s g f)). Qed.
Lemma lem6115172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6115173 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term48 A B C op s g f) = (term176 A B C op s g f).
Proof. exact (MK_COMB (@lem6115172) (@lem6114955 A B C op s g f)). Qed.
Lemma lem6115392 {A : Type'} (x : A) (s : A -> Prop) : (term49 A x s) = (term49 A x s).
Proof. exact (eq_refl (term49 A x s)). Qed.
Lemma lem6115393 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) : (term51 A B C op g f x s) = (term177 A B C op g f x s).
Proof. exact (MK_COMB (@lem6115173 A B C op s g f) (@lem6115392 A x s)). Qed.
Lemma lem6115614 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term178 A B C op g f x s q'.
Proof. exact (@lem6114457 A B C op x s g f (term177 A B C op g f x s) q'). Qed.
Lemma lem6115615 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term179 A B C op g f x s q'.
Proof. exact (@lem6115614 A B C op g f x s q' (@lem6115393 A B C op g f x s)). Qed.
Lemma lem6115616 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : term177 A B C op g f x s.
Proof. exact (h1). Qed.
Lemma lem6115617 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : term49 A x s.
Proof. exact (proj2 (@lem6115616 A B C op g f x s h1)). Qed.
Lemma lem6115618 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : @FINITE A s.
Proof. exact (proj2 (@lem6115617 A B C op g f x s h1)). Qed.
Lemma lem6115619 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6115621 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : term180 A x s.
Proof. exact (proj1 (@lem6115617 A B C op g f x s h1)). Qed.
Lemma lem6115622 {A : Type'} (x : A) (s : A -> Prop) : term181 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem6115635 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term97 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6115636 (p : Prop) (q : Prop) (p' : Prop) : term98 p q p'.
Proof. exact (fun q' : Prop => @lem6115635 p q p' q'). Qed.
Lemma lem6115637 (p : Prop) (q : Prop) : term99 p q.
Proof. exact (fun p' : Prop => @lem6115636 p q p'). Qed.
Lemma lem6115638 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) : term182 A B C op x s g f.
Proof. exact (@lem6115637 (term183 A B C x s g f op) ((term184 A B C op f x s g) = (term185 A B C op x s g f))). Qed.
Lemma lem6115639 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term186 A B C op x s g f p'.
Proof. exact (@lem6115638 A B C op x s g f p'). Qed.
Lemma lem6115640 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : (term186 A B C op x s g f p') = (term187 A B C op x s g f p').
Proof. exact (eq_refl (term186 A B C op x s g f p')). Qed.
Lemma lem6115641 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term187 A B C op x s g f p'.
Proof. exact (EQ_MP (@lem6115640 A B C op x s g f p') (@lem6115639 A B C op x s g f p')). Qed.
Lemma lem6115642 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term188 A B C op x s g f p' q'.
Proof. exact (@lem6115641 A B C op x s g f p' q'). Qed.
Lemma lem6115643 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : (term188 A B C op x s g f p' q') = (term189 A B C op x s g f p' q').
Proof. exact (eq_refl (term188 A B C op x s g f p' q')). Qed.
Lemma lem6115644 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term189 A B C op x s g f p' q'.
Proof. exact (EQ_MP (@lem6115643 A B C op x s g f p' q') (@lem6115642 A B C op x s g f p' q')). Qed.
Lemma lem6115656 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term97 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6115657 (p : Prop) (q : Prop) (p' : Prop) : term98 p q p'.
Proof. exact (fun q' : Prop => @lem6115656 p q p' q'). Qed.
Lemma lem6115658 (p : Prop) (q : Prop) : term99 p q.
Proof. exact (fun p' : Prop => @lem6115657 p q p'). Qed.
Lemma lem6115659 {A B C : Type'} (x : A) (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x' : A) (op : type1400 C) : term190 A B C x s y g f x' op.
Proof. exact (@lem6115658 (term191 A B x s x' f y) ((term110 A B C g f x') = (@neutral C op))). Qed.
Lemma lem6115660 {A B C : Type'} (x : A) (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x' : A) (op : type1400 C) (p' : Prop) : term192 A B C x s y g f x' op p'.
Proof. exact (@lem6115659 A B C x s y g f x' op p'). Qed.
Lemma lem6115661 {A B C : Type'} (x : A) (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x' : A) (op : type1400 C) (p' : Prop) : (term192 A B C x s y g f x' op p') = (term193 A B C x s y g f x' op p').
Proof. exact (eq_refl (term192 A B C x s y g f x' op p')). Qed.
Lemma lem6115662 {A B C : Type'} (x : A) (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x' : A) (op : type1400 C) (p' : Prop) : term193 A B C x s y g f x' op p'.
Proof. exact (EQ_MP (@lem6115661 A B C x s y g f x' op p') (@lem6115660 A B C x s y g f x' op p')). Qed.
Lemma lem6115663 {A B C : Type'} (x : A) (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x' : A) (op : type1400 C) (p' : Prop) (q' : Prop) : term194 A B C x s y g f x' op p' q'.
Proof. exact (@lem6115662 A B C x s y g f x' op p' q'). Qed.
Lemma lem6115664 {A B C : Type'} (x : A) (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x' : A) (op : type1400 C) (p' : Prop) (q' : Prop) : (term194 A B C x s y g f x' op p' q') = (term195 A B C x s y g f x' op p' q').
Proof. exact (eq_refl (term194 A B C x s y g f x' op p' q')). Qed.
Lemma lem6115665 {A B C : Type'} (x : A) (s : A -> Prop) (y : A) (g : B -> C) (f : A -> B) (x' : A) (op : type1400 C) (p' : Prop) (q' : Prop) : term195 A B C x s y g f x' op p' q'.
Proof. exact (EQ_MP (@lem6115664 A B C x s y g f x' op p' q') (@lem6115663 A B C x s y g f x' op p' q')). Qed.
Lemma lem6115676 {A B : Type'} (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term191 A B x s x' f y) = (term191 A B x s x' f y).
Proof. exact (eq_refl (term191 A B x s x' f y)). Qed.
Lemma lem6115677 {A B C : Type'} (g : B -> C) (op : type1400 C) (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (q' : Prop) : term196 A B C g op x s x' f y q'.
Proof. exact (@lem6115665 A B C x s y g f x' op (term191 A B x s x' f y) q'). Qed.
Lemma lem6115678 {A B C : Type'} (g : B -> C) (op : type1400 C) (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (q' : Prop) : term197 A B C g op x s x' f y q'.
Proof. exact (@lem6115677 A B C g op x s x' f y q' (@lem6115676 A B x s x' f y)). Qed.
Lemma lem6115679 {A B : Type'} (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (h1 : term191 A B x s x' f y) : term191 A B x s x' f y.
Proof. exact (h1). Qed.
Lemma lem6115680 {A B : Type'} (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (h1 : term191 A B x s x' f y) : term198 A B x s x' f y.
Proof. exact (proj2 (@lem6115679 A B x s x' f y h1)). Qed.
Lemma lem6115681 {A B : Type'} (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (h1 : term191 A B x s x' f y) : term118 A B x' f y.
Proof. exact (proj2 (@lem6115680 A B x s x' f y h1)). Qed.
Lemma lem6115706 {A B : Type'} (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (h1 : term191 A B x s x' f y) : (f x') = (f y).
Proof. exact (proj2 (@lem6115681 A B x s x' f y h1)). Qed.
Lemma lem6115707 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6115708 {A B C : Type'} (g : B -> C) (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (h1 : term191 A B x s x' f y) : (term110 A B C g f x') = (term110 A B C g f y).
Proof. exact (MK_COMB (@lem6115707 B C g) (@lem6115706 A B x s x' f y h1)). Qed.
Lemma lem6115709 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6115710 {A B C : Type'} (g : B -> C) (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (h1 : term191 A B x s x' f y) : (term119 A B C g f x') = (term119 A B C g f y).
Proof. exact (MK_COMB (@lem6115709 C) (@lem6115708 A B C g x s x' f y h1)). Qed.
Lemma lem6115711 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6115712 {A B C : Type'} (g : B -> C) (op : type1400 C) (x : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) (h1 : term191 A B x s x' f y) : ((term110 A B C g f x') = (@neutral C op)) = ((term110 A B C g f y) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6115710 A B C g x s x' f y h1) (@lem6115711 C op)). Qed.
Lemma lem6115715 {A B C : Type'} (x : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : term199 A B C x s x' g f y op.
Proof. exact (fun h0 : term191 A B x s x' f y => @lem6115712 A B C g op x s x' f y h0). Qed.
Lemma lem6115716 {A B C : Type'} (x : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : term200 A B C x s x' g f y op.
Proof. exact (@lem6115678 A B C g op x s x' f y ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6115717 {A B C : Type'} (x : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term201 A B C x s y g f x' op) = (term202 A B C x s x' g f y op).
Proof. exact (@lem6115716 A B C x s x' g f y op (@lem6115715 A B C x s x' g f y op)). Qed.
Lemma lem6115786 {A B C : Type'} (x : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term203 A B C x s g f x' op) = (term204 A B C x s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6115717 A B C x s x' g f y op)). Qed.
Lemma lem6115855 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6115856 {A B C : Type'} (x : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term205 A B C x s g f x' op) = (term206 A B C x s x' g f op).
Proof. exact (MK_COMB (@lem6115855 A) (@lem6115786 A B C x s x' g f op)). Qed.
Lemma lem6115929 {A B C : Type'} (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term207 A B C x s g f op) = (term208 A B C x s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6115856 A B C x s x' g f op)). Qed.
Lemma lem6116002 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6116003 {A B C : Type'} (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term183 A B C x s g f op) = (term209 A B C x s g f op).
Proof. exact (MK_COMB (@lem6116002 A) (@lem6115929 A B C x s g f op)). Qed.
Lemma lem6116080 {A B C : Type'} (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (q' : Prop) : term210 A B C x s g f op q'.
Proof. exact (@lem6115644 A B C op x s g f (term209 A B C x s g f op) q'). Qed.
Lemma lem6116081 {A B C : Type'} (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (q' : Prop) : term211 A B C x s g f op q'.
Proof. exact (@lem6116080 A B C x s g f op q' (@lem6116003 A B C x s g f op)). Qed.
Lemma lem6116125 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term212 _87477 _87481 f x s) = (term213 _87477 _87481 x f s).
Proof. exact (proj2 (@lem3366870 _87477 _87481 x f s)). Qed.
Lemma lem6116126 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term212 A B f x s) = (term213 A B x f s).
Proof. exact (@lem6116125 A B x f s). Qed.
Lemma lem6116127 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@iterate C B op).
Proof. exact (eq_refl (@iterate C B op)). Qed.
Lemma lem6116128 {A B C : Type'} (op : type1400 C) (x : A) (f : A -> B) (s : A -> Prop) : (term214 A B C op f x s) = (term215 A B C op x f s).
Proof. exact (MK_COMB (@lem6116127 B C op) (@lem6116126 A B x f s)). Qed.
Lemma lem6116129 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6116130 {A B C : Type'} (op : type1400 C) (x : A) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term184 A B C op f x s g) = (term216 A B C op x f s g).
Proof. exact (MK_COMB (@lem6116128 A B C op x f s) (@lem6116129 B C g)). Qed.
Lemma lem6116132 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term94 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6113885 _120519 _120521 x op s f) (@lem6113878 _120519 _120521 x op s f)). Qed.
Lemma lem6116133 {B C : Type'} (x : B) (op : type1400 C) (s : B -> Prop) (f : B -> C) : term217 B C x op s f.
Proof. exact (@lem6116132 C B x op s f). Qed.
Lemma lem6116134 {A B C : Type'} (x : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term218 A B C x op f s g.
Proof. exact (@lem6116133 B C (f x) op (@IMAGE A B f s) g). Qed.
Lemma lem6116138 {A B : Type'} (f : A -> B) (s : A -> Prop) : term219 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem6113854 A B f s h0). Qed.
Lemma lem6116139 {A B : Type'} (f : A -> B) (s : A -> Prop) : term219 A B f s.
Proof. exact (@lem6116138 A B f s). Qed.
Lemma lem6116141 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6115619 A s) (@lem6115618 A B C op g f x s h1)). Qed.
Lemma lem6116142 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6116141 A B C op g f x s h1)). Qed.
Lemma lem6116143 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6116142 A B C op g f x s h1) (@lem0)). Qed.
Lemma lem6116144 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : (term79 A B f s) = True.
Proof. exact (@lem6116139 A B f s (@lem6116143 A B C op g f x s h1)). Qed.
Lemma lem6116145 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6116146 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : (term220 A B f s) = (and True).
Proof. exact (MK_COMB (@lem6116145) (@lem6116144 A B C op g f x s h1)). Qed.
Lemma lem6116148 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6113898 C op) (@lem6113800 C op h1)). Qed.
Lemma lem6116149 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term221 A B C f s op) = (True /\ True).
Proof. exact (MK_COMB (@lem6116146 A B C op g f x s h2) (@lem6116148 C op h1)). Qed.
Lemma lem6116151 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6116152 : (True /\ True) = True.
Proof. exact (@lem6116151 True). Qed.
Lemma lem6116153 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term221 A B C f s op) = True.
Proof. exact (TRANS (@lem6116149 A B C op g f x s h1 h2) (@lem6116152)). Qed.
Lemma lem6116154 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : True = (term221 A B C f s op).
Proof. exact (SYM (@lem6116153 A B C op g f x s h1 h2)). Qed.
Lemma lem6116155 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : term221 A B C f s op.
Proof. exact (EQ_MP (@lem6116154 A B C op g f x s h1 h2) (@lem0)). Qed.
Lemma lem6116156 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term216 A B C op x f s g) = (term222 A B C x op f s g).
Proof. exact (@lem6116134 A B C x op f s g (@lem6116155 A B C op g f x s h1 h2)). Qed.
Lemma lem6117018 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term184 A B C op f x s g) = (term222 A B C x op f s g).
Proof. exact (TRANS (@lem6116130 A B C op x f s g) (@lem6116156 A B C op g f x s h1 h2)). Qed.
Lemma lem6117019 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6117020 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term223 A B C op f x s g) = (term224 A B C x op f s g).
Proof. exact (MK_COMB (@lem6117019 C) (@lem6117018 A B C op g f x s h1 h2)). Qed.
Lemma lem6117883 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term94 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6113885 _120519 _120521 x op s f) (@lem6113878 _120519 _120521 x op s f)). Qed.
Lemma lem6117884 {A C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : A -> C) : term217 A C x op s f.
Proof. exact (@lem6117883 C A x op s f). Qed.
Lemma lem6117885 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term225 A B C x op s g f.
Proof. exact (@lem6117884 A C x op s (@o A B C g f)). Qed.
Lemma lem6117889 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6115619 A s) (@lem6115618 A B C op g f x s h1)). Qed.
Lemma lem6117890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6117891 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : (term226 A s) = (and True).
Proof. exact (MK_COMB (@lem6117890) (@lem6117889 A B C op g f x s h1)). Qed.
Lemma lem6117893 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6113898 C op) (@lem6113800 C op h1)). Qed.
Lemma lem6117894 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term227 A C s op) = (True /\ True).
Proof. exact (MK_COMB (@lem6117891 A B C op g f x s h2) (@lem6117893 C op h1)). Qed.
Lemma lem6117896 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6117897 : (True /\ True) = True.
Proof. exact (@lem6117896 True). Qed.
Lemma lem6117898 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term227 A C s op) = True.
Proof. exact (TRANS (@lem6117894 A B C op g f x s h1 h2) (@lem6117897)). Qed.
Lemma lem6117899 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : True = (term227 A C s op).
Proof. exact (SYM (@lem6117898 A B C op g f x s h1 h2)). Qed.
Lemma lem6117900 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : term227 A C s op.
Proof. exact (EQ_MP (@lem6117899 A B C op g f x s h1 h2) (@lem0)). Qed.
Lemma lem6117901 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term185 A B C op x s g f) = (term228 A B C x op s g f).
Proof. exact (@lem6117885 A B C x op s g f (@lem6117900 A B C op g f x s h1 h2)). Qed.
Lemma lem6117903 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term229 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6117904 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term230 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6117903 _2963 g t e g' t' e'). Qed.
Lemma lem6117905 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term231 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6117904 _2963 g t e g' t'). Qed.
Lemma lem6117906 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term232 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6117905 _2963 g t e g'). Qed.
Lemma lem6117907 {C : Type'} (g : Prop) (t : C) (e : C) : term232 C g t e.
Proof. exact (@lem6117906 C g t e). Qed.
Lemma lem6117908 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term233 A B C x op s g f.
Proof. exact (@lem6117907 C (@IN A x s) (term34 A B C op s g f) (term234 A B C x op s g f)). Qed.
Lemma lem6117909 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) : term235 A B C x op s g f g'.
Proof. exact (@lem6117908 A B C x op s g f g'). Qed.
Lemma lem6117910 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) : (term235 A B C x op s g f g') = (term236 A B C x op s g f g').
Proof. exact (eq_refl (term235 A B C x op s g f g')). Qed.
Lemma lem6117911 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) : term236 A B C x op s g f g'.
Proof. exact (EQ_MP (@lem6117910 A B C x op s g f g') (@lem6117909 A B C x op s g f g')). Qed.
Lemma lem6117912 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) (t' : C) : term237 A B C x op s g f g' t'.
Proof. exact (@lem6117911 A B C x op s g f g' t'). Qed.
Lemma lem6117913 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) (t' : C) : (term237 A B C x op s g f g' t') = (term238 A B C x op s g f g' t').
Proof. exact (eq_refl (term237 A B C x op s g f g' t')). Qed.
Lemma lem6117914 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) (t' : C) : term238 A B C x op s g f g' t'.
Proof. exact (EQ_MP (@lem6117913 A B C x op s g f g' t') (@lem6117912 A B C x op s g f g' t')). Qed.
Lemma lem6117915 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) (t' : C) (e' : C) : term239 A B C x op s g f g' t' e'.
Proof. exact (@lem6117914 A B C x op s g f g' t' e'). Qed.
Lemma lem6117916 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) (t' : C) (e' : C) : (term239 A B C x op s g f g' t' e') = (term240 A B C x op s g f g' t' e').
Proof. exact (eq_refl (term239 A B C x op s g f g' t' e')). Qed.
Lemma lem6117917 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (g' : Prop) (t' : C) (e' : C) : term240 A B C x op s g f g' t' e'.
Proof. exact (EQ_MP (@lem6117916 A B C x op s g f g' t' e') (@lem6117915 A B C x op s g f g' t' e')). Qed.
Lemma lem6117919 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : (@IN A x s) = False.
Proof. exact (@lem6115622 A x s (@lem6115621 A B C op g f x s h1)). Qed.
Lemma lem6117920 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (t' : C) (e' : C) : term241 A B C x op s g f t' e'.
Proof. exact (@lem6117917 A B C x op s g f False t' e'). Qed.
Lemma lem6117921 {A B C : Type'} (t' : C) (e' : C) (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : term242 A B C x op s g f t' e'.
Proof. exact (@lem6117920 A B C x op s g f t' e' (@lem6117919 A B C op g f x s h1)). Qed.
Lemma lem6117925 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term34 A B C op s g f) = (term34 A B C op s g f).
Proof. exact (eq_refl (term34 A B C op s g f)). Qed.
Lemma lem6117926 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term243 A B C op s g f.
Proof. exact (fun h0 : False => @lem6117925 A B C op s g f). Qed.
Lemma lem6117927 {A B C : Type'} (e' : C) (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : term244 A B C x op s g f e'.
Proof. exact (@lem6117921 A B C (term34 A B C op s g f) e' op g f x s h1). Qed.
Lemma lem6117928 {A B C : Type'} (e' : C) (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : term245 A B C x op s g f e'.
Proof. exact (@lem6117927 A B C e' op g f x s h1 (@lem6117926 A B C op s g f)). Qed.
Lemma lem6117934 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term234 A B C x op s g f) = (term234 A B C x op s g f).
Proof. exact (eq_refl (term234 A B C x op s g f)). Qed.
Lemma lem6117935 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term246 A B C x op s g f.
Proof. exact (fun h0 : ~ False => @lem6117934 A B C x op s g f). Qed.
Lemma lem6117936 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : term247 A B C x op s g f.
Proof. exact (@lem6117928 A B C (term234 A B C x op s g f) op g f x s h1). Qed.
Lemma lem6117937 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : (term228 A B C x op s g f) = (term248 A B C x op s g f).
Proof. exact (@lem6117936 A B C op g f x s h1 (@lem6117935 A B C x op s g f)). Qed.
Lemma lem6117939 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6117940 {C : Type'} (t1 : C) (t2 : C) : (@COND C False t1 t2) = t2.
Proof. exact (@lem6117939 C t1 t2). Qed.
Lemma lem6117941 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term248 A B C x op s g f) = (term234 A B C x op s g f).
Proof. exact (@lem6117940 C (term34 A B C op s g f) (term234 A B C x op s g f)). Qed.
Lemma lem6117942 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term177 A B C op g f x s) : (term228 A B C x op s g f) = (term234 A B C x op s g f).
Proof. exact (TRANS (@lem6117937 A B C op g f x s h1) (@lem6117941 A B C x op s g f)). Qed.
Lemma lem6117943 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term185 A B C op x s g f) = (term234 A B C x op s g f).
Proof. exact (TRANS (@lem6117901 A B C op g f x s h1 h2) (@lem6117942 A B C op g f x s h2)). Qed.
Lemma lem6117944 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : ((term184 A B C op f x s g) = (term185 A B C op x s g f)) = ((term222 A B C x op f s g) = (term234 A B C x op s g f)).
Proof. exact (MK_COMB (@lem6117020 A B C op g f x s h1 h2) (@lem6117943 A B C op g f x s h1 h2)). Qed.
Lemma lem6118808 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : term249 A B C x op s g f.
Proof. exact (fun h0 : term209 A B C x s g f op => @lem6117944 A B C op g f x s h1 h2). Qed.
Lemma lem6118809 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term250 A B C x op s g f.
Proof. exact (@lem6116081 A B C x s g f op ((term222 A B C x op f s g) = (term234 A B C x op s g f))). Qed.
Lemma lem6118810 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f x s) : (term55 A B C op x s g f) = (term251 A B C x op s g f).
Proof. exact (@lem6118809 A B C x op s g f (@lem6118808 A B C op g f x s h1 h2)). Qed.
Lemma lem6120481 {A B C : Type'} (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term252 A B C x op s g f.
Proof. exact (fun h0 : term177 A B C op g f x s => @lem6118810 A B C op g f x s h1 h0). Qed.
Lemma lem6120482 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : term253 A B C x op s g f.
Proof. exact (@lem6115615 A B C op g f x s (term251 A B C x op s g f)). Qed.
Lemma lem6120483 {A B C : Type'} (x : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term57 A B C op x s g f) = (term254 A B C x op s g f).
Proof. exact (@lem6120482 A B C x op s g f (@lem6120481 A B C x s g f op h1)). Qed.
Lemma lem6122952 {A B C : Type'} (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term59 A B C op x g f) = (term255 A B C x op g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6120483 A B C x s g f op h1)). Qed.
Lemma lem6125421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6125422 {A B C : Type'} (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term61 A B C op x g f) = (term256 A B C x op g f).
Proof. exact (MK_COMB (@lem6125421 A) (@lem6122952 A B C x g f op h1)). Qed.
Lemma lem6127895 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term63 A B C op g f) = (term257 A B C op g f).
Proof. exact (fun_ext (fun x : A => @lem6125422 A B C x g f op h1)). Qed.
Lemma lem6130368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6130369 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term65 A B C op g f) = (term258 A B C op g f).
Proof. exact (MK_COMB (@lem6130368 A) (@lem6127895 A B C g f op h1)). Qed.
Lemma lem6132846 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term67 A B C op g f) = (term259 A B C op g f).
Proof. exact (MK_COMB (@lem6114436 A B C g f op h1) (@lem6130369 A B C g f op h1)). Qed.
Lemma lem6132848 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6132849 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term259 A B C op g f) = (term258 A B C op g f).
Proof. exact (@lem6132848 (term258 A B C op g f)). Qed.
Lemma lem6135326 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term67 A B C op g f) = (term258 A B C op g f).
Proof. exact (TRANS (@lem6132846 A B C g f op h1) (@lem6132849 A B C op g f)). Qed.
Lemma lem6135327 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : (term258 A B C op g f) = (term67 A B C op g f).
Proof. exact (SYM (@lem6135326 A B C g f op h1)). Qed.
Lemma lem6135375 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (EQ_MP (@lem6113782 A y x s) (@lem6113781 A y x s)). Qed.
Lemma lem6135376 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (@lem6135375 A y x s). Qed.
Lemma lem6135377 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term19 A x' a s) = (term20 A a x' s).
Proof. exact (@lem6135376 A a x' s). Qed.
Lemma lem6135382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6135383 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term260 A x' a s) = (term261 A a x' s).
Proof. exact (MK_COMB (@lem6135382) (@lem6135377 A a x' s)). Qed.
Lemma lem6135387 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (EQ_MP (@lem6113782 A y x s) (@lem6113781 A y x s)). Qed.
Lemma lem6135388 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (@lem6135387 A y x s). Qed.
Lemma lem6135389 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term19 A y a s) = (term20 A a y s).
Proof. exact (@lem6135388 A a y s). Qed.
Lemma lem6135394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6135395 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term260 A y a s) = (term261 A a y s).
Proof. exact (MK_COMB (@lem6135394) (@lem6135389 A a y s)). Qed.
Lemma lem6135402 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term118 A B x' f y) = (term118 A B x' f y).
Proof. exact (eq_refl (term118 A B x' f y)). Qed.
Lemma lem6135403 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term198 A B a s x' f y) = (term262 A B a s x' f y).
Proof. exact (MK_COMB (@lem6135395 A a y s) (@lem6135402 A B x' f y)). Qed.
Lemma lem6135406 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term191 A B a s x' f y) = (term263 A B a s x' f y).
Proof. exact (MK_COMB (@lem6135383 A a x' s) (@lem6135403 A B a s x' f y)). Qed.
Lemma lem6135409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6135410 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term264 A B a s x' f y) = (term265 A B a s x' f y).
Proof. exact (MK_COMB (@lem6135409) (@lem6135406 A B a s x' f y)). Qed.
Lemma lem6135413 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term110 A B C g f y) = (@neutral C op)) = ((term110 A B C g f y) = (@neutral C op)).
Proof. exact (eq_refl ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6135414 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term202 A B C a s x' g f y op) = (term266 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6135410 A B a s x' f y) (@lem6135413 A B C g f y op)). Qed.
Lemma lem6135417 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term204 A B C a s x' g f op) = (term267 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6135414 A B C a s x' g f y op)). Qed.
Lemma lem6135418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6135419 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term206 A B C a s x' g f op) = (term268 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6135418 A) (@lem6135417 A B C a s x' g f op)). Qed.
Lemma lem6135424 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term208 A B C a s g f op) = (term269 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6135419 A B C a s x' g f op)). Qed.
Lemma lem6135425 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6135426 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term209 A B C a s g f op) = (term270 A B C a s g f op).
Proof. exact (MK_COMB (@lem6135425 A) (@lem6135424 A B C a s g f op)). Qed.
Lemma lem6135431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6135432 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term271 A B C a s g f op) = (term272 A B C a s g f op).
Proof. exact (MK_COMB (@lem6135431) (@lem6135426 A B C a s g f op)). Qed.
Lemma lem6135435 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term222 A B C a op f s g) = (term234 A B C a op s g f)) = ((term222 A B C a op f s g) = (term234 A B C a op s g f)).
Proof. exact (eq_refl ((term222 A B C a op f s g) = (term234 A B C a op s g f))). Qed.
Lemma lem6135436 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term251 A B C a op s g f) = (term273 A B C a op s g f).
Proof. exact (MK_COMB (@lem6135432 A B C a s g f op) (@lem6135435 A B C a op s g f)). Qed.
Lemma lem6135439 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) (s : A -> Prop) : (term274 A B C op g f a s) = (term274 A B C op g f a s).
Proof. exact (eq_refl (term274 A B C op g f a s)). Qed.
Lemma lem6135440 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term254 A B C a op s g f) = (term275 A B C a op s g f).
Proof. exact (MK_COMB (@lem6135439 A B C op g f a s) (@lem6135436 A B C a op s g f)). Qed.
Lemma lem6135443 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term275 A B C a op s g f) = (term254 A B C a op s g f).
Proof. exact (SYM (@lem6135440 A B C a op s g f)). Qed.
Lemma lem6135444 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) (s : A -> Prop) (h1 : term177 A B C op g f a s) : term177 A B C op g f a s.
Proof. exact (h1). Qed.
Lemma lem6135445 {A : Type'} (a : A) (s : A -> Prop) (h1 : term49 A a s) : term49 A a s.
Proof. exact (h1). Qed.
Lemma lem6135446 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term175 A B C op s g f.
Proof. exact (h1). Qed.
Lemma lem6135447 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6135448 {A : Type'} (a : A) (s : A -> Prop) (h1 : term180 A a s) : term180 A a s.
Proof. exact (h1). Qed.
Lemma lem6135449 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term270 A B C a s g f op.
Proof. exact (h1). Qed.
Lemma lem6135450 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : (term34 A B C op s g f) = (term33 A B C op f s g)) : (term34 A B C op s g f) = (term33 A B C op f s g).
Proof. exact (h1). Qed.
Lemma lem6135451 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) : (term276 A B C s op g f a) = (term276 A B C s op g f a).
Proof. exact (eq_refl (term276 A B C s op g f a)). Qed.
Lemma lem6135452 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : (term34 A B C op s g f) = (term33 A B C op f s g)) : (term277 A B C a op s g f) = (term278 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135451 A B C s op g f a) (@lem6135450 A B C op f s g h1)). Qed.
Lemma lem6135453 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term278 A B C a op f s g) = ((term222 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (eq_refl (term278 A B C a op f s g)). Qed.
Lemma lem6135454 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term280 A B C a op s g f) = (term280 A B C a op s g f).
Proof. exact (eq_refl (term280 A B C a op s g f)). Qed.
Lemma lem6135455 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term277 A B C a op s g f) = (term278 A B C a op f s g)) = ((term277 A B C a op s g f) = ((term222 A B C a op f s g) = (term279 A B C a op f s g))).
Proof. exact (MK_COMB (@lem6135454 A B C a op s g f) (@lem6135453 A B C a op f s g)). Qed.
Lemma lem6135456 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term277 A B C a op s g f) = ((term222 A B C a op f s g) = (term234 A B C a op s g f)).
Proof. exact (eq_refl (term277 A B C a op s g f)). Qed.
Lemma lem6135457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6135458 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term280 A B C a op s g f) = (term281 A B C a op s g f).
Proof. exact (MK_COMB (@lem6135457) (@lem6135456 A B C a op s g f)). Qed.
Lemma lem6135459 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term222 A B C a op f s g) = (term279 A B C a op f s g)) = ((term222 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (eq_refl ((term222 A B C a op f s g) = (term279 A B C a op f s g))). Qed.
Lemma lem6135460 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term277 A B C a op s g f) = ((term222 A B C a op f s g) = (term279 A B C a op f s g))) = (((term222 A B C a op f s g) = (term234 A B C a op s g f)) = ((term222 A B C a op f s g) = (term279 A B C a op f s g))).
Proof. exact (MK_COMB (@lem6135458 A B C a op s g f) (@lem6135459 A B C a op f s g)). Qed.
Lemma lem6135461 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term277 A B C a op s g f) = (term278 A B C a op f s g)) = (((term222 A B C a op f s g) = (term234 A B C a op s g f)) = ((term222 A B C a op f s g) = (term279 A B C a op f s g))).
Proof. exact (TRANS (@lem6135455 A B C a op f s g) (@lem6135460 A B C a op f s g)). Qed.
Lemma lem6135462 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : (term34 A B C op s g f) = (term33 A B C op f s g)) : ((term222 A B C a op f s g) = (term234 A B C a op s g f)) = ((term222 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (EQ_MP (@lem6135461 A B C a op f s g) (@lem6135452 A B C a op f s g h1)). Qed.
Lemma lem6135463 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : (term34 A B C op s g f) = (term33 A B C op f s g)) : ((term222 A B C a op f s g) = (term279 A B C a op f s g)) = ((term222 A B C a op f s g) = (term234 A B C a op s g f)).
Proof. exact (SYM (@lem6135462 A B C a op f s g h1)). Qed.
Lemma lem6135465 (p : Prop) : p = (term282 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6135466 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term34 A B C op s g f) = (term33 A B C op f s g)) = (term283 A B C op f s g).
Proof. exact (@lem6135465 ((term34 A B C op s g f) = (term33 A B C op f s g))). Qed.
Lemma lem6135467 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term283 A B C op f s g) = ((term34 A B C op s g f) = (term33 A B C op f s g)).
Proof. exact (SYM (@lem6135466 A B C op f s g)). Qed.
Lemma lem6135468 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term284 A B C op f s g) : term284 A B C op f s g.
Proof. exact (h1). Qed.
Lemma lem6135471 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term285 A B C a op f s g) : term285 A B C a op f s g.
Proof. exact (h1). Qed.
Lemma lem6135472 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term286 A B C a op f s g.
Proof. exact (fun h0 : term285 A B C a op f s g => @lem6135471 A B C a op f s g h0). Qed.
Lemma lem6135473 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term286 A B C a op f s g) : term286 A B C a op f s g.
Proof. exact (h1). Qed.
Lemma lem6135474 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term285 A B C a op f s g) : term285 A B C a op f s g.
Proof. exact (h1). Qed.
Lemma lem6135475 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term285 A B C a op f s g) (h2 : term286 A B C a op f s g) : term285 A B C a op f s g.
Proof. exact (@lem6135473 A B C a op f s g h2 (@lem6135474 A B C a op f s g h1)). Qed.
Lemma lem6135476 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term285 A B C a op f s g) : term287 A B C a op f s g.
Proof. exact (fun h0 : term286 A B C a op f s g => @lem6135475 A B C a op f s g h1 h0). Qed.
Lemma lem6135477 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term286 A B C a op f s g) : term286 A B C a op f s g.
Proof. exact (h1). Qed.
Lemma lem6135478 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term285 A B C a op f s g) (h2 : term286 A B C a op f s g) : term285 A B C a op f s g.
Proof. exact (@lem6135476 A B C a op f s g h1 (@lem6135477 A B C a op f s g h2)). Qed.
Lemma lem6135479 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term286 A B C a op f s g) : term286 A B C a op f s g.
Proof. exact (fun h0 : term285 A B C a op f s g => @lem6135478 A B C a op f s g h0 h1). Qed.
Lemma lem6135480 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term288 A B C a op f s g.
Proof. exact (fun h0 : term286 A B C a op f s g => @lem6135479 A B C a op f s g h0). Qed.
Lemma lem6135483 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term286 A B C a op f s g.
Proof. exact (@lem6135480 A B C a op f s g (@lem6135472 A B C a op f s g)). Qed.
Lemma lem6135484 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term286 A B C a op f s g.
Proof. exact (@lem6135483 A B C a op f s g). Qed.
Lemma lem6135554 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6135555 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term283 A B C op f s g) = (term289 A B C op f s g).
Proof. exact (@lem6135554 (term284 A B C op f s g)). Qed.
Lemma lem6135557 (t : Prop) : (term290 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6135558 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term289 A B C op f s g) = ((term34 A B C op s g f) = (term33 A B C op f s g)).
Proof. exact (@lem6135557 ((term34 A B C op s g f) = (term33 A B C op f s g))). Qed.
Lemma lem6135559 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term283 A B C op f s g) = ((term34 A B C op s g f) = (term33 A B C op f s g)).
Proof. exact (TRANS (@lem6135555 A B C op f s g) (@lem6135558 A B C op f s g)). Qed.
Lemma lem6135560 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term272 A B C a s g f op) = (term272 A B C a s g f op).
Proof. exact (eq_refl (term272 A B C a s g f op)). Qed.
Lemma lem6135561 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term291 A B C a op f s g) = (term292 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135560 A B C a s g f op) (@lem6135559 A B C op f s g)). Qed.
Lemma lem6135564 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem6135565 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term293 A B C a op f s g) = (term294 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135564 A s) (@lem6135561 A B C a op f s g)). Qed.
Lemma lem6135568 {A : Type'} (a : A) (s : A -> Prop) : (term295 A a s) = (term295 A a s).
Proof. exact (eq_refl (term295 A a s)). Qed.
Lemma lem6135569 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term296 A B C a op f s g) = (term297 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135568 A a s) (@lem6135565 A B C a op f s g)). Qed.
Lemma lem6135572 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term298 A B C op s g f) = (term298 A B C op s g f).
Proof. exact (eq_refl (term298 A B C op s g f)). Qed.
Lemma lem6135573 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term299 A B C a op f s g) = (term300 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135572 A B C op s g f) (@lem6135569 A B C a op f s g)). Qed.
Lemma lem6135576 {C : Type'} (op : type1400 C) : (term301 C op) = (term301 C op).
Proof. exact (eq_refl (term301 C op)). Qed.
Lemma lem6135577 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term285 A B C a op f s g) = (term302 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135576 C op) (@lem6135573 A B C a op f s g)). Qed.
Lemma lem6135580 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term303 A B C op f s g) = (term304 A B C op f s g).
Proof. exact (fun_ext (fun a : A => @lem6135577 A B C a op f s g)). Qed.
Lemma lem6135581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6135582 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term305 A B C op f s g) = (term306 A B C op f s g).
Proof. exact (MK_COMB (@lem6135581 A) (@lem6135580 A B C op f s g)). Qed.
Lemma lem6135587 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term307 A B C f s g) = (term308 A B C f s g).
Proof. exact (fun_ext (fun op : type1400 C => @lem6135582 A B C op f s g)). Qed.
Lemma lem6135588 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6135589 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term309 A B C f s g) = (term310 A B C f s g).
Proof. exact (MK_COMB (@lem6135588 C) (@lem6135587 A B C f s g)). Qed.
Lemma lem6135594 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term311 A B C s g) = (term312 A B C s g).
Proof. exact (fun_ext (fun f : A -> B => @lem6135589 A B C f s g)). Qed.
Lemma lem6135595 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6135596 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term313 A B C s g) = (term314 A B C s g).
Proof. exact (MK_COMB (@lem6135595 A B) (@lem6135594 A B C s g)). Qed.
Lemma lem6135601 {A B C : Type'} (g : B -> C) : (term315 A B C g) = (term316 A B C g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6135596 A B C s g)). Qed.
Lemma lem6135602 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6135603 {A B C : Type'} (g : B -> C) : (term317 A B C g) = (term318 A B C g).
Proof. exact (MK_COMB (@lem6135602 A) (@lem6135601 A B C g)). Qed.
Lemma lem6135608 {A B C : Type'} : (term319 A B C) = (term320 A B C).
Proof. exact (fun_ext (fun g : B -> C => @lem6135603 A B C g)). Qed.
Lemma lem6135609 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem6135618 {A B C : Type'} : (term321 A B C) = (term322 A B C).
Proof. exact (MK_COMB (@lem6135609 B C) (@lem6135608 A B C)). Qed.
Lemma lem6135619 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term34 A B C op s g f) = (term33 A B C op f s g)) = ((term34 A B C op s g f) = (term33 A B C op f s g)).
Proof. exact (eq_refl ((term34 A B C op s g f) = (term33 A B C op f s g))). Qed.
Lemma lem6135646 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term266 A B C a s x' g f y op) = (term266 A B C a s x' g f y op).
Proof. exact (eq_refl (term266 A B C a s x' g f y op)). Qed.
Lemma lem6135647 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term267 A B C a s x' g f op) = (term267 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6135646 A B C a s x' g f y op)). Qed.
Lemma lem6135648 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6135649 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term268 A B C a s x' g f op) = (term268 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6135648 A) (@lem6135647 A B C a s x' g f op)). Qed.
Lemma lem6135650 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term269 A B C a s g f op) = (term269 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6135649 A B C a s x' g f op)). Qed.
Lemma lem6135651 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6135652 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term270 A B C a s g f op) = (term270 A B C a s g f op).
Proof. exact (MK_COMB (@lem6135651 A) (@lem6135650 A B C a s g f op)). Qed.
Lemma lem6135653 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6135654 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term272 A B C a s g f op) = (term272 A B C a s g f op).
Proof. exact (MK_COMB (@lem6135653) (@lem6135652 A B C a s g f op)). Qed.
Lemma lem6135655 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term292 A B C a op f s g) = (term292 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135654 A B C a s g f op) (@lem6135619 A B C op f s g)). Qed.
Lemma lem6135658 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem6135659 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term294 A B C a op f s g) = (term294 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135658 A s) (@lem6135655 A B C a op f s g)). Qed.
Lemma lem6135664 {A : Type'} (a : A) (s : A -> Prop) : (term295 A a s) = (term295 A a s).
Proof. exact (eq_refl (term295 A a s)). Qed.
Lemma lem6135665 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term297 A B C a op f s g) = (term297 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135664 A a s) (@lem6135659 A B C a op f s g)). Qed.
Lemma lem6135666 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135685 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term163 A B C s x g f y op) = (term163 A B C s x g f y op).
Proof. exact (eq_refl (term163 A B C s x g f y op)). Qed.
Lemma lem6135686 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term165 A B C s x g f op) = (term165 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6135685 A B C s x g f y op)). Qed.
Lemma lem6135687 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6135688 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term167 A B C s x g f op) = (term167 A B C s x g f op).
Proof. exact (MK_COMB (@lem6135687 A) (@lem6135686 A B C s x g f op)). Qed.
Lemma lem6135689 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term169 A B C s g f op) = (term169 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6135688 A B C s x g f op)). Qed.
Lemma lem6135690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6135691 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term170 A B C s g f op) = (term170 A B C s g f op).
Proof. exact (MK_COMB (@lem6135690 A) (@lem6135689 A B C s g f op)). Qed.
Lemma lem6135692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6135693 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term323 A B C s g f op) = (term323 A B C s g f op).
Proof. exact (MK_COMB (@lem6135692) (@lem6135691 A B C s g f op)). Qed.
Lemma lem6135694 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term175 A B C op s g f).
Proof. exact (MK_COMB (@lem6135693 A B C s g f op) (@lem6135666 A B C op s g f)). Qed.
Lemma lem6135695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6135696 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term298 A B C op s g f) = (term298 A B C op s g f).
Proof. exact (MK_COMB (@lem6135695) (@lem6135694 A B C op s g f)). Qed.
Lemma lem6135697 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term300 A B C a op f s g) = (term300 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135696 A B C op s g f) (@lem6135665 A B C a op f s g)). Qed.
Lemma lem6135700 {C : Type'} (op : type1400 C) : (term301 C op) = (term301 C op).
Proof. exact (eq_refl (term301 C op)). Qed.
Lemma lem6135701 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term302 A B C a op f s g) = (term302 A B C a op f s g).
Proof. exact (MK_COMB (@lem6135700 C op) (@lem6135697 A B C a op f s g)). Qed.
Lemma lem6135702 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term304 A B C op f s g) = (term304 A B C op f s g).
Proof. exact (fun_ext (fun a : A => @lem6135701 A B C a op f s g)). Qed.
Lemma lem6135703 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6135704 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term306 A B C op f s g) = (term306 A B C op f s g).
Proof. exact (MK_COMB (@lem6135703 A) (@lem6135702 A B C op f s g)). Qed.
Lemma lem6135705 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term308 A B C f s g) = (term308 A B C f s g).
Proof. exact (fun_ext (fun op : type1400 C => @lem6135704 A B C op f s g)). Qed.
Lemma lem6135706 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6135707 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term310 A B C f s g) = (term310 A B C f s g).
Proof. exact (MK_COMB (@lem6135706 C) (@lem6135705 A B C f s g)). Qed.
Lemma lem6135708 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term312 A B C s g) = (term312 A B C s g).
Proof. exact (fun_ext (fun f : A -> B => @lem6135707 A B C f s g)). Qed.
Lemma lem6135709 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6135710 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term314 A B C s g) = (term314 A B C s g).
Proof. exact (MK_COMB (@lem6135709 A B) (@lem6135708 A B C s g)). Qed.
Lemma lem6135711 {A B C : Type'} (g : B -> C) : (term316 A B C g) = (term316 A B C g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6135710 A B C s g)). Qed.
Lemma lem6135712 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6135713 {A B C : Type'} (g : B -> C) : (term318 A B C g) = (term318 A B C g).
Proof. exact (MK_COMB (@lem6135712 A) (@lem6135711 A B C g)). Qed.
Lemma lem6135714 {A B C : Type'} : (term320 A B C) = (term320 A B C).
Proof. exact (fun_ext (fun g : B -> C => @lem6135713 A B C g)). Qed.
Lemma lem6135715 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem6135716 {A B C : Type'} : (term322 A B C) = (term322 A B C).
Proof. exact (MK_COMB (@lem6135715 B C) (@lem6135714 A B C)). Qed.
Lemma lem6135805 {A B C : Type'} : (term321 A B C) = (term322 A B C).
Proof. exact (TRANS (@lem6135618 A B C) (@lem6135716 A B C)). Qed.
Lemma lem6135806 {A B C : Type'} : (term322 A B C) = (term321 A B C).
Proof. exact (SYM (@lem6135805 A B C)). Qed.
Lemma lem6135808 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term175 A B C op s g f.
Proof. exact (h1). Qed.
Lemma lem6135811 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term270 A B C a s g f op.
Proof. exact (h1). Qed.
Lemma lem6135813 (p : Prop) : p = (term282 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6135814 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term34 A B C op s g f) = (term33 A B C op f s g)) = (term283 A B C op f s g).
Proof. exact (@lem6135813 ((term34 A B C op s g f) = (term33 A B C op f s g))). Qed.
Lemma lem6135815 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term283 A B C op f s g) = ((term34 A B C op s g f) = (term33 A B C op f s g)).
Proof. exact (SYM (@lem6135814 A B C op f s g)). Qed.
Lemma lem6135816 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term284 A B C op f s g) : term284 A B C op f s g.
Proof. exact (h1). Qed.
Lemma lem6135841 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term324 A B C s x g f y op) = (term325 A B C s x g f y op).
Proof. exact (@lem17362 (term152 A B s x f y) ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6135842 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6135843 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term328 A B C s x g f op) = (term329 A B C s x g f op).
Proof. exact (@lem6135842 A (term165 A B C s x g f op)). Qed.
Lemma lem6135844 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term330 A B C s x g f op y) = (term163 A B C s x g f y op).
Proof. exact (eq_refl (term330 A B C s x g f op y)). Qed.
Lemma lem6135845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6135846 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term331 A B C s x g f op y) = (term324 A B C s x g f y op).
Proof. exact (MK_COMB (@lem6135845) (@lem6135844 A B C s x g f y op)). Qed.
Lemma lem6135847 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term331 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (TRANS (@lem6135846 A B C s x g f y op) (@lem6135841 A B C s x g f y op)). Qed.
Lemma lem6135848 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term332 A B C s x g f op) = (term333 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6135847 A B C s x g f y op)). Qed.
Lemma lem6135849 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6135850 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term329 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (MK_COMB (@lem6135849 A) (@lem6135848 A B C s x g f op)). Qed.
Lemma lem6135851 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term328 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (TRANS (@lem6135843 A B C s x g f op) (@lem6135850 A B C s x g f op)). Qed.
Lemma lem6135852 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6135853 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term335 A B C s g f op) = (term336 A B C s g f op).
Proof. exact (@lem6135852 A (term169 A B C s g f op)). Qed.
Lemma lem6135854 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term337 A B C s g f op x) = (term167 A B C s x g f op).
Proof. exact (eq_refl (term337 A B C s g f op x)). Qed.
Lemma lem6135855 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6135856 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term338 A B C s g f op x) = (term328 A B C s x g f op).
Proof. exact (MK_COMB (@lem6135855) (@lem6135854 A B C s x g f op)). Qed.
Lemma lem6135857 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term338 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (TRANS (@lem6135856 A B C s x g f op) (@lem6135851 A B C s x g f op)). Qed.
Lemma lem6135858 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term339 A B C s g f op) = (term340 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6135857 A B C s x g f op)). Qed.
Lemma lem6135859 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6135860 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term336 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (MK_COMB (@lem6135859 A) (@lem6135858 A B C s g f op)). Qed.
Lemma lem6135861 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term335 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (TRANS (@lem6135853 A B C s g f op) (@lem6135860 A B C s g f op)). Qed.
Lemma lem6135862 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6135864 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term342 A B C s g f op) = (term343 A B C s g f op).
Proof. exact (MK_COMB (@lem6135863) (@lem6135861 A B C s g f op)). Qed.
Lemma lem6135865 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term344 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (MK_COMB (@lem6135864 A B C s g f op) (@lem6135862 A B C op s g f)). Qed.
Lemma lem6135866 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term344 A B C op s g f).
Proof. exact (@lem17265 (term170 A B C s g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135867 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (TRANS (@lem6135866 A B C op s g f) (@lem6135865 A B C op s g f)). Qed.
Lemma lem6135922 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6135923 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem6135922 A P Q). Qed.
Lemma lem6135924 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term348 A B C op s g f) = (term349 A B C op s g f).
Proof. exact (@lem6135923 A (term340 A B C s g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135925 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term350 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (eq_refl (term350 A B C s g f op x)). Qed.
Lemma lem6135926 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term351 A B C s g f op) = (term340 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6135925 A B C s x g f op)). Qed.
Lemma lem6135927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6135928 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term352 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (MK_COMB (@lem6135927 A) (@lem6135926 A B C s g f op)). Qed.
Lemma lem6135929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6135930 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term353 A B C s g f op) = (term343 A B C s g f op).
Proof. exact (MK_COMB (@lem6135929) (@lem6135928 A B C s g f op)). Qed.
Lemma lem6135931 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135932 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term348 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (MK_COMB (@lem6135930 A B C s g f op) (@lem6135931 A B C op s g f)). Qed.
Lemma lem6135933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6135934 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term354 A B C op s g f) = (term355 A B C op s g f).
Proof. exact (MK_COMB (@lem6135933) (@lem6135932 A B C op s g f)). Qed.
Lemma lem6135935 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term350 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (eq_refl (term350 A B C s g f op x)). Qed.
Lemma lem6135936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6135937 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term356 A B C s g f op x) = (term357 A B C s x g f op).
Proof. exact (MK_COMB (@lem6135936) (@lem6135935 A B C s x g f op)). Qed.
Lemma lem6135938 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135939 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term358 A B C x op s g f) = (term359 A B C x op s g f).
Proof. exact (MK_COMB (@lem6135937 A B C s x g f op) (@lem6135938 A B C op s g f)). Qed.
Lemma lem6135940 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term360 A B C op s g f) = (term361 A B C op s g f).
Proof. exact (fun_ext (fun x : A => @lem6135939 A B C x op s g f)). Qed.
Lemma lem6135941 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6135942 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term349 A B C op s g f) = (term362 A B C op s g f).
Proof. exact (MK_COMB (@lem6135941 A) (@lem6135940 A B C op s g f)). Qed.
Lemma lem6135943 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term348 A B C op s g f) = (term349 A B C op s g f)) = ((term345 A B C op s g f) = (term362 A B C op s g f)).
Proof. exact (MK_COMB (@lem6135934 A B C op s g f) (@lem6135942 A B C op s g f)). Qed.
Lemma lem6135944 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term345 A B C op s g f) = (term362 A B C op s g f).
Proof. exact (EQ_MP (@lem6135943 A B C op s g f) (@lem6135924 A B C op s g f)). Qed.
Lemma lem6135946 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6135947 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem6135946 A P Q). Qed.
Lemma lem6135948 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term363 A B C x op s g f) = (term364 A B C x op s g f).
Proof. exact (@lem6135947 A (term333 A B C s x g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135949 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term365 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (eq_refl (term365 A B C s x g f op y)). Qed.
Lemma lem6135950 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term366 A B C s x g f op) = (term333 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6135949 A B C s x g f y op)). Qed.
Lemma lem6135951 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6135952 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term367 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (MK_COMB (@lem6135951 A) (@lem6135950 A B C s x g f op)). Qed.
Lemma lem6135953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6135954 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term368 A B C s x g f op) = (term357 A B C s x g f op).
Proof. exact (MK_COMB (@lem6135953) (@lem6135952 A B C s x g f op)). Qed.
Lemma lem6135955 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135956 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term363 A B C x op s g f) = (term359 A B C x op s g f).
Proof. exact (MK_COMB (@lem6135954 A B C s x g f op) (@lem6135955 A B C op s g f)). Qed.
Lemma lem6135957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6135958 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term369 A B C x op s g f) = (term370 A B C x op s g f).
Proof. exact (MK_COMB (@lem6135957) (@lem6135956 A B C x op s g f)). Qed.
Lemma lem6135959 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term365 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (eq_refl (term365 A B C s x g f op y)). Qed.
Lemma lem6135960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6135961 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term371 A B C s x g f op y) = (term372 A B C s x g f y op).
Proof. exact (MK_COMB (@lem6135960) (@lem6135959 A B C s x g f y op)). Qed.
Lemma lem6135962 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6135963 {A B C : Type'} (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term373 A B C x y op s g f) = (term374 A B C x y op s g f).
Proof. exact (MK_COMB (@lem6135961 A B C s x g f y op) (@lem6135962 A B C op s g f)). Qed.
Lemma lem6135964 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term375 A B C x op s g f) = (term376 A B C x op s g f).
Proof. exact (fun_ext (fun y : A => @lem6135963 A B C x y op s g f)). Qed.
Lemma lem6135965 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6135966 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term364 A B C x op s g f) = (term377 A B C x op s g f).
Proof. exact (MK_COMB (@lem6135965 A) (@lem6135964 A B C x op s g f)). Qed.
Lemma lem6135967 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term363 A B C x op s g f) = (term364 A B C x op s g f)) = ((term359 A B C x op s g f) = (term377 A B C x op s g f)).
Proof. exact (MK_COMB (@lem6135958 A B C x op s g f) (@lem6135966 A B C x op s g f)). Qed.
Lemma lem6135968 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term359 A B C x op s g f) = (term377 A B C x op s g f).
Proof. exact (EQ_MP (@lem6135967 A B C x op s g f) (@lem6135948 A B C x op s g f)). Qed.
Lemma lem6135969 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term361 A B C op s g f) = (term378 A B C op s g f).
Proof. exact (fun_ext (fun x : A => @lem6135968 A B C x op s g f)). Qed.
Lemma lem6135970 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6135971 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term362 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (MK_COMB (@lem6135970 A) (@lem6135969 A B C op s g f)). Qed.
Lemma lem6135973 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term345 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (TRANS (@lem6135944 A B C op s g f) (@lem6135971 A B C op s g f)). Qed.
Lemma lem6135974 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (TRANS (@lem6135867 A B C op s g f) (@lem6135973 A B C op s g f)). Qed.
Lemma lem6135975 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term379 A B C op s g f.
Proof. exact (EQ_MP (@lem6135974 A B C op s g f) (@lem6135808 A B C op s g f h1)). Qed.
Lemma lem6135994 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term380 A a x' s) = (term381 A a x' s).
Proof. exact (@lem17160 (x' = a) (@IN A x' s)). Qed.
Lemma lem6136001 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term380 A a y s) = (term381 A a y s).
Proof. exact (@lem17160 (y = a) (@IN A y s)). Qed.
Lemma lem6136004 {A : Type'} (x' : A) (y : A) : (term382 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem6136005 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term383 A B x' f y) = (term383 A B x' f y).
Proof. exact (eq_refl (term383 A B x' f y)). Qed.
Lemma lem6136006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6136007 {A : Type'} (x' : A) (y : A) : (term384 A x' y) = (term385 A x' y).
Proof. exact (MK_COMB (@lem6136006) (@lem6136004 A x' y)). Qed.
Lemma lem6136008 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term386 A B x' f y) = (term387 A B x' f y).
Proof. exact (MK_COMB (@lem6136007 A x' y) (@lem6136005 A B x' f y)). Qed.
Lemma lem6136009 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term388 A B x' f y) = (term386 A B x' f y).
Proof. exact (@lem17045 (term389 A x' y) ((f x') = (f y))). Qed.
Lemma lem6136010 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term388 A B x' f y) = (term387 A B x' f y).
Proof. exact (TRANS (@lem6136009 A B x' f y) (@lem6136008 A B x' f y)). Qed.
Lemma lem6136011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6136012 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term390 A a y s) = (term391 A a y s).
Proof. exact (MK_COMB (@lem6136011) (@lem6136001 A a y s)). Qed.
Lemma lem6136013 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term392 A B a s x' f y) = (term393 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136012 A a y s) (@lem6136010 A B x' f y)). Qed.
Lemma lem6136014 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term394 A B a s x' f y) = (term392 A B a s x' f y).
Proof. exact (@lem17045 (term20 A a y s) (term118 A B x' f y)). Qed.
Lemma lem6136015 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term394 A B a s x' f y) = (term393 A B a s x' f y).
Proof. exact (TRANS (@lem6136014 A B a s x' f y) (@lem6136013 A B a s x' f y)). Qed.
Lemma lem6136016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6136017 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term390 A a x' s) = (term391 A a x' s).
Proof. exact (MK_COMB (@lem6136016) (@lem6135994 A a x' s)). Qed.
Lemma lem6136018 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term395 A B a s x' f y) = (term396 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136017 A a x' s) (@lem6136015 A B a s x' f y)). Qed.
Lemma lem6136019 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term397 A B a s x' f y) = (term395 A B a s x' f y).
Proof. exact (@lem17045 (term20 A a x' s) (term262 A B a s x' f y)). Qed.
Lemma lem6136020 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term397 A B a s x' f y) = (term396 A B a s x' f y).
Proof. exact (TRANS (@lem6136019 A B a s x' f y) (@lem6136018 A B a s x' f y)). Qed.
Lemma lem6136021 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term110 A B C g f y) = (@neutral C op)) = ((term110 A B C g f y) = (@neutral C op)).
Proof. exact (eq_refl ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6136022 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6136023 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term398 A B a s x' f y) = (term399 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136022) (@lem6136020 A B a s x' f y)). Qed.
Lemma lem6136024 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term400 A B C a s x' g f y op) = (term401 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6136023 A B a s x' f y) (@lem6136021 A B C g f y op)). Qed.
Lemma lem6136025 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term266 A B C a s x' g f y op) = (term400 A B C a s x' g f y op).
Proof. exact (@lem17265 (term263 A B a s x' f y) ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6136026 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term266 A B C a s x' g f y op) = (term401 A B C a s x' g f y op).
Proof. exact (TRANS (@lem6136025 A B C a s x' g f y op) (@lem6136024 A B C a s x' g f y op)). Qed.
Lemma lem6136027 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term267 A B C a s x' g f op) = (term402 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6136026 A B C a s x' g f y op)). Qed.
Lemma lem6136028 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6136029 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term268 A B C a s x' g f op) = (term403 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6136028 A) (@lem6136027 A B C a s x' g f op)). Qed.
Lemma lem6136030 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term269 A B C a s g f op) = (term404 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6136029 A B C a s x' g f op)). Qed.
Lemma lem6136031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6136088 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term270 A B C a s g f op) = (term405 A B C a s g f op).
Proof. exact (MK_COMB (@lem6136031 A) (@lem6136030 A B C a s g f op)). Qed.
Lemma lem6136089 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term405 A B C a s g f op.
Proof. exact (EQ_MP (@lem6136088 A B C a s g f op) (@lem6135811 A B C a s g f op h1)). Qed.
Lemma lem6136095 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term284 A B C op f s g) : term284 A B C op f s g.
Proof. exact (h1). Qed.
Lemma lem6136096 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term377 A B C x op s g f) : term377 A B C x op s g f.
Proof. exact (h1). Qed.
Lemma lem6136097 {A B C : Type'} (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term374 A B C x y op s g f) : term374 A B C x y op s g f.
Proof. exact (h1). Qed.
Lemma lem6136114 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6136115 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6136120 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6136121 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6136120 A B f x). Qed.
Lemma lem6136123 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6136121 A B f y). Qed.
Lemma lem6136124 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term406 A B C g f y).
Proof. exact (MK_COMB (@lem6136115 B C g) (@lem6136123 A B f y)). Qed.
Lemma lem6136126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6136127 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem6136126 B C f x). Qed.
Lemma lem6136128 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term406 A B C g f y) = (term407 A B C g f y).
Proof. exact (@lem6136127 B C g (@I (A -> B) f y)). Qed.
Lemma lem6136129 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term407 A B C g f y).
Proof. exact (TRANS (@lem6136124 A B C g f y) (@lem6136128 A B C g f y)). Qed.
Lemma lem6136132 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6136133 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term119 A B C g f y) = (term408 A B C g f y).
Proof. exact (MK_COMB (@lem6136114 C) (@lem6136129 A B C g f y)). Qed.
Lemma lem6136134 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term110 A B C g f y) = (@neutral C op)) = ((term407 A B C g f y) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6136133 A B C g f y) (@lem6136132 C op)). Qed.
Lemma lem6136135 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6136136 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6136141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6136142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6136141 A B f x). Qed.
Lemma lem6136144 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6136142 A B f x'). Qed.
Lemma lem6136149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6136150 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6136149 A B f x). Qed.
Lemma lem6136152 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6136150 A B f y). Qed.
Lemma lem6136153 {A B : Type'} (f : A -> B) (x' : A) : (term409 A B f x') = (term410 A B f x').
Proof. exact (MK_COMB (@lem6136136 B) (@lem6136144 A B f x')). Qed.
Lemma lem6136154 {A B : Type'} (x' : A) (f : A -> B) (y : A) : ((f x') = (f y)) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem6136153 A B f x') (@lem6136152 A B f y)). Qed.
Lemma lem6136155 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term383 A B x' f y) = (term411 A B x' f y).
Proof. exact (MK_COMB (@lem6136135) (@lem6136154 A B x' f y)). Qed.
Lemma lem6136162 {A : Type'} (x' : A) (y : A) : (term385 A x' y) = (term385 A x' y).
Proof. exact (eq_refl (term385 A x' y)). Qed.
Lemma lem6136163 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term387 A B x' f y) = (term412 A B x' f y).
Proof. exact (MK_COMB (@lem6136162 A x' y) (@lem6136155 A B x' f y)). Qed.
Lemma lem6136182 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term391 A a y s) = (term391 A a y s).
Proof. exact (eq_refl (term391 A a y s)). Qed.
Lemma lem6136183 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term393 A B a s x' f y) = (term413 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136182 A a y s) (@lem6136163 A B x' f y)). Qed.
Lemma lem6136202 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term391 A a x' s) = (term391 A a x' s).
Proof. exact (eq_refl (term391 A a x' s)). Qed.
Lemma lem6136203 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term396 A B a s x' f y) = (term414 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136202 A a x' s) (@lem6136183 A B a s x' f y)). Qed.
Lemma lem6136204 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6136205 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term399 A B a s x' f y) = (term415 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136204) (@lem6136203 A B a s x' f y)). Qed.
Lemma lem6136206 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term401 A B C a s x' g f y op) = (term416 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6136205 A B a s x' f y) (@lem6136134 A B C g f y op)). Qed.
Lemma lem6136207 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term402 A B C a s x' g f op) = (term417 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6136206 A B C a s x' g f y op)). Qed.
Lemma lem6136208 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6136209 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term403 A B C a s x' g f op) = (term418 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6136208 A) (@lem6136207 A B C a s x' g f op)). Qed.
Lemma lem6136210 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term404 A B C a s g f op) = (term419 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6136209 A B C a s x' g f op)). Qed.
Lemma lem6136211 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6136212 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term405 A B C a s g f op) = (term420 A B C a s g f op).
Proof. exact (MK_COMB (@lem6136211 A) (@lem6136210 A B C a s g f op)). Qed.
Lemma lem6136213 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term420 A B C a s g f op.
Proof. exact (EQ_MP (@lem6136212 A B C a s g f op) (@lem6136089 A B C a s g f op h1)). Qed.
Lemma lem6136241 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term284 A B C op f s g) : term284 A B C op f s g.
Proof. exact (h1). Qed.
Lemma lem6136266 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6136267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6136268 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6136269 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6136274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6136275 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6136274 A B f x). Qed.
Lemma lem6136277 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6136275 A B f y). Qed.
Lemma lem6136278 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term406 A B C g f y).
Proof. exact (MK_COMB (@lem6136269 B C g) (@lem6136277 A B f y)). Qed.
Lemma lem6136280 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6136281 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem6136280 B C f x). Qed.
Lemma lem6136282 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term406 A B C g f y) = (term407 A B C g f y).
Proof. exact (@lem6136281 B C g (@I (A -> B) f y)). Qed.
Lemma lem6136283 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term407 A B C g f y).
Proof. exact (TRANS (@lem6136278 A B C g f y) (@lem6136282 A B C g f y)). Qed.
Lemma lem6136286 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6136287 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term119 A B C g f y) = (term408 A B C g f y).
Proof. exact (MK_COMB (@lem6136268 C) (@lem6136283 A B C g f y)). Qed.
Lemma lem6136288 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term110 A B C g f y) = (@neutral C op)) = ((term407 A B C g f y) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6136287 A B C g f y) (@lem6136286 C op)). Qed.
Lemma lem6136289 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term421 A B C g f y op) = (term422 A B C g f y op).
Proof. exact (MK_COMB (@lem6136267) (@lem6136288 A B C g f y op)). Qed.
Lemma lem6136290 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6136295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6136297 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6136295 A B f x). Qed.
Lemma lem6136302 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6136303 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6136302 A B f x). Qed.
Lemma lem6136305 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6136303 A B f y). Qed.
Lemma lem6136306 {A B : Type'} (f : A -> B) (x : A) : (term409 A B f x) = (term410 A B f x).
Proof. exact (MK_COMB (@lem6136290 B) (@lem6136297 A B f x)). Qed.
Lemma lem6136307 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem6136306 A B f x) (@lem6136305 A B f y)). Qed.
Lemma lem6136316 {A : Type'} (x : A) (y : A) : (term423 A x y) = (term423 A x y).
Proof. exact (eq_refl (term423 A x y)). Qed.
Lemma lem6136317 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term118 A B x f y) = (term424 A B x f y).
Proof. exact (MK_COMB (@lem6136316 A x y) (@lem6136307 A B x f y)). Qed.
Lemma lem6136324 {A : Type'} (y : A) (s : A -> Prop) : (term425 A y s) = (term425 A y s).
Proof. exact (eq_refl (term425 A y s)). Qed.
Lemma lem6136325 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term159 A B s x f y) = (term426 A B s x f y).
Proof. exact (MK_COMB (@lem6136324 A y s) (@lem6136317 A B x f y)). Qed.
Lemma lem6136332 {A : Type'} (x : A) (s : A -> Prop) : (term425 A x s) = (term425 A x s).
Proof. exact (eq_refl (term425 A x s)). Qed.
Lemma lem6136333 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term152 A B s x f y) = (term427 A B s x f y).
Proof. exact (MK_COMB (@lem6136332 A x s) (@lem6136325 A B s x f y)). Qed.
Lemma lem6136334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6136335 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term428 A B s x f y) = (term429 A B s x f y).
Proof. exact (MK_COMB (@lem6136334) (@lem6136333 A B s x f y)). Qed.
Lemma lem6136336 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term325 A B C s x g f y op) = (term430 A B C s x g f y op).
Proof. exact (MK_COMB (@lem6136335 A B s x f y) (@lem6136289 A B C g f y op)). Qed.
Lemma lem6136337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6136338 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term372 A B C s x g f y op) = (term431 A B C s x g f y op).
Proof. exact (MK_COMB (@lem6136337) (@lem6136336 A B C s x g f y op)). Qed.
Lemma lem6136339 {A B C : Type'} (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term374 A B C x y op s g f) = (term432 A B C x y op s g f).
Proof. exact (MK_COMB (@lem6136338 A B C s x g f y op) (@lem6136266 A B C op s g f)). Qed.
Lemma lem6136340 {A B C : Type'} (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term374 A B C x y op s g f) : term432 A B C x y op s g f.
Proof. exact (EQ_MP (@lem6136339 A B C x y op s g f) (@lem6136097 A B C x y op s g f h1)). Qed.
Lemma lem6136341 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term430 A B C s x g f y op.
Proof. exact (h1). Qed.
Lemma lem6136344 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term427 A B s x f y.
Proof. exact (proj1 (@lem6136341 A B C s x g f y op h1)). Qed.
Lemma lem6136345 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term426 A B s x f y.
Proof. exact (proj2 (@lem6136344 A B C s x g f y op h1)). Qed.
Lemma lem6136347 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term424 A B x f y.
Proof. exact (proj2 (@lem6136345 A B C s x g f y op h1)). Qed.
Lemma lem6136364 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term407 A B C g f y) = (@neutral C op)) = ((term407 A B C g f y) = (@neutral C op)).
Proof. exact (eq_refl ((term407 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6136387 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term413 A B a s x' f y) = (term433 A B a s x' f y).
Proof. exact (@lem19699 (term389 A y a) (term180 A y s) (term412 A B x' f y)). Qed.
Lemma lem6136394 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term391 A a x' s) = (term391 A a x' s).
Proof. exact (eq_refl (term391 A a x' s)). Qed.
Lemma lem6136395 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term414 A B a s x' f y) = (term434 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136394 A a x' s) (@lem6136387 A B a s x' f y)). Qed.
Lemma lem6136396 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term434 A B a s x' f y) = (term435 A B a s x' f y).
Proof. exact (@lem19490 (term436 A B a x' f y) (term381 A a x' s) (term437 A B s x' f y)). Qed.
Lemma lem6136403 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term438 A B a s x' f y) = (term439 A B a s x' f y).
Proof. exact (@lem19699 (term389 A x' a) (term180 A x' s) (term437 A B s x' f y)). Qed.
Lemma lem6136410 {A B : Type'} (s : A -> Prop) (a : A) (x' : A) (f : A -> B) (y : A) : (term440 A B s a x' f y) = (term441 A B s a x' f y).
Proof. exact (@lem19699 (term389 A x' a) (term180 A x' s) (term436 A B a x' f y)). Qed.
Lemma lem6136411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6136412 {A B : Type'} (s : A -> Prop) (a : A) (x' : A) (f : A -> B) (y : A) : (term442 A B s a x' f y) = (term443 A B s a x' f y).
Proof. exact (MK_COMB (@lem6136411) (@lem6136410 A B s a x' f y)). Qed.
Lemma lem6136413 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term435 A B a s x' f y) = (term444 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136412 A B s a x' f y) (@lem6136403 A B a s x' f y)). Qed.
Lemma lem6136414 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term434 A B a s x' f y) = (term444 A B a s x' f y).
Proof. exact (TRANS (@lem6136396 A B a s x' f y) (@lem6136413 A B a s x' f y)). Qed.
Lemma lem6136415 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term414 A B a s x' f y) = (term444 A B a s x' f y).
Proof. exact (TRANS (@lem6136395 A B a s x' f y) (@lem6136414 A B a s x' f y)). Qed.
Lemma lem6136416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6136417 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term415 A B a s x' f y) = (term445 A B a s x' f y).
Proof. exact (MK_COMB (@lem6136416) (@lem6136415 A B a s x' f y)). Qed.
Lemma lem6136418 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term416 A B C a s x' g f y op) = (term446 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6136417 A B a s x' f y) (@lem6136364 A B C g f y op)). Qed.
Lemma lem6136419 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term446 A B C a s x' g f y op) = (term447 A B C a s x' g f y op).
Proof. exact (@lem19699 (term441 A B s a x' f y) (term439 A B a s x' f y) ((term407 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6136426 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term448 A B C a s x' g f y op) = (term449 A B C a s x' g f y op).
Proof. exact (@lem19699 (term450 A B a s x' f y) (term451 A B s x' f y) ((term407 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6136433 {A B C : Type'} (s : A -> Prop) (a : A) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term452 A B C s a x' g f y op) = (term453 A B C s a x' g f y op).
Proof. exact (@lem19699 (term454 A B a x' f y) (term455 A B s a x' f y) ((term407 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6136434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6136435 {A B C : Type'} (s : A -> Prop) (a : A) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term456 A B C s a x' g f y op) = (term457 A B C s a x' g f y op).
Proof. exact (MK_COMB (@lem6136434) (@lem6136433 A B C s a x' g f y op)). Qed.
Lemma lem6136436 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term447 A B C a s x' g f y op) = (term458 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6136435 A B C s a x' g f y op) (@lem6136426 A B C a s x' g f y op)). Qed.
Lemma lem6136437 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term446 A B C a s x' g f y op) = (term458 A B C a s x' g f y op).
Proof. exact (TRANS (@lem6136419 A B C a s x' g f y op) (@lem6136436 A B C a s x' g f y op)). Qed.
Lemma lem6136438 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term416 A B C a s x' g f y op) = (term458 A B C a s x' g f y op).
Proof. exact (TRANS (@lem6136418 A B C a s x' g f y op) (@lem6136437 A B C a s x' g f y op)). Qed.
Lemma lem6136439 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term417 A B C a s x' g f op) = (term459 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6136438 A B C a s x' g f y op)). Qed.
Lemma lem6136440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6136441 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term418 A B C a s x' g f op) = (term460 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6136440 A) (@lem6136439 A B C a s x' g f op)). Qed.
Lemma lem6136442 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term419 A B C a s g f op) = (term461 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6136441 A B C a s x' g f op)). Qed.
Lemma lem6136443 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6136445 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term420 A B C a s g f op) = (term462 A B C a s g f op).
Proof. exact (MK_COMB (@lem6136443 A) (@lem6136442 A B C a s g f op)). Qed.
Lemma lem6136446 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term462 A B C a s g f op.
Proof. exact (EQ_MP (@lem6136445 A B C a s g f op) (@lem6136213 A B C a s g f op h1)). Qed.
Lemma lem6136570 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term284 A B C op f s g) : term284 A B C op f s g.
Proof. exact (h1). Qed.
Lemma lem6136574 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term33 A B C op f s g) = (term34 A B C op s g f).
Proof. exact (h1). Qed.
Lemma lem6136575 {A B C : Type'} (_77113 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term463 A B C a s g f op _77113.
Proof. exact (@lem6136446 A B C a s g f op h1 _77113). Qed.
Lemma lem6136576 {A B C : Type'} (a : A) (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term463 A B C a s g f op _77113) = (term460 A B C a s _77113 g f op).
Proof. exact (eq_refl (term463 A B C a s g f op _77113)). Qed.
Lemma lem6136577 {A B C : Type'} (_77113 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term460 A B C a s _77113 g f op.
Proof. exact (EQ_MP (@lem6136576 A B C a s _77113 g f op) (@lem6136575 A B C _77113 a s g f op h1)). Qed.
Lemma lem6136578 {A B C : Type'} (_77113 : A) (_77114 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term464 A B C a s _77113 g f op _77114.
Proof. exact (@lem6136577 A B C _77113 a s g f op h1 _77114). Qed.
Lemma lem6136579 {A B C : Type'} (a : A) (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term464 A B C a s _77113 g f op _77114) = (term458 A B C a s _77113 g f _77114 op).
Proof. exact (eq_refl (term464 A B C a s _77113 g f op _77114)). Qed.
Lemma lem6136580 {A B C : Type'} (_77113 : A) (_77114 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term458 A B C a s _77113 g f _77114 op.
Proof. exact (EQ_MP (@lem6136579 A B C a s _77113 g f _77114 op) (@lem6136578 A B C _77113 _77114 a s g f op h1)). Qed.
Lemma lem6136587 {A B C : Type'} (_77113 : A) (_77114 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term449 A B C a s _77113 g f _77114 op.
Proof. exact (proj2 (@lem6136580 A B C _77113 _77114 a s g f op h1)). Qed.
Lemma lem6136589 {A B C : Type'} (_77113 : A) (_77114 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term465 A B C s _77113 g f _77114 op.
Proof. exact (proj2 (@lem6136587 A B C _77113 _77114 a s g f op h1)). Qed.
Lemma lem6136614 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term389 A x y.
Proof. exact (proj1 (@lem6136347 A B C s x g f y op h1)). Qed.
Lemma lem6136644 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term465 A B C s _77113 g f _77114 op) = (term466 A B C s _77113 g f _77114 op).
Proof. exact (@lem6113774 (term180 A _77113 s) (term437 A B s _77113 f _77114) ((term407 A B C g f _77114) = (@neutral C op))). Qed.
Lemma lem6136645 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term467 A B C s _77113 g f _77114 op) = (term468 A B C s _77113 g f _77114 op).
Proof. exact (@lem6113774 (term180 A _77114 s) (term412 A B _77113 f _77114) ((term407 A B C g f _77114) = (@neutral C op))). Qed.
Lemma lem6136652 {A B C : Type'} (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term469 A B C _77113 g f _77114 op) = (term470 A B C _77113 g f _77114 op).
Proof. exact (@lem6113774 (_77113 = _77114) (term411 A B _77113 f _77114) ((term407 A B C g f _77114) = (@neutral C op))). Qed.
Lemma lem6136653 {A : Type'} (_77114 : A) (s : A -> Prop) : (term471 A _77114 s) = (term471 A _77114 s).
Proof. exact (eq_refl (term471 A _77114 s)). Qed.
Lemma lem6136656 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term468 A B C s _77113 g f _77114 op) = (term472 A B C s _77113 g f _77114 op).
Proof. exact (MK_COMB (@lem6136653 A _77114 s) (@lem6136652 A B C _77113 g f _77114 op)). Qed.
Lemma lem6136657 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term467 A B C s _77113 g f _77114 op) = (term472 A B C s _77113 g f _77114 op).
Proof. exact (TRANS (@lem6136645 A B C s _77113 g f _77114 op) (@lem6136656 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6136658 {A : Type'} (_77113 : A) (s : A -> Prop) : (term471 A _77113 s) = (term471 A _77113 s).
Proof. exact (eq_refl (term471 A _77113 s)). Qed.
Lemma lem6136661 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term466 A B C s _77113 g f _77114 op) = (term473 A B C s _77113 g f _77114 op).
Proof. exact (MK_COMB (@lem6136658 A _77113 s) (@lem6136657 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6136663 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term465 A B C s _77113 g f _77114 op) = (term473 A B C s _77113 g f _77114 op).
Proof. exact (TRANS (@lem6136644 A B C s _77113 g f _77114 op) (@lem6136661 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6136664 {A B C : Type'} (_77113 : A) (_77114 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term473 A B C s _77113 g f _77114 op.
Proof. exact (EQ_MP (@lem6136663 A B C s _77113 g f _77114 op) (@lem6136589 A B C _77113 _77114 a s g f op h1)). Qed.
Lemma lem6136720 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term284 A B C op f s g) : term284 A B C op f s g.
Proof. exact (h1). Qed.
Lemma lem6136722 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term33 A B C op f s g) = (term34 A B C op s g f).
Proof. exact (h1). Qed.
Lemma lem6136993 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : @IN A x s.
Proof. exact (proj1 (@lem6136344 A B C s x g f y op h1)). Qed.
Lemma lem6136994 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term474 A x s.
Proof. exact (fun h0 : term180 A x s => @lem6136993 A B C s x g f y op h1). Qed.
Lemma lem6136996 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6136997 {A : Type'} (x : A) (s : A -> Prop) : (term474 A x s) = (@IN A x s).
Proof. exact (@lem6136996 (@IN A x s)). Qed.
Lemma lem6136998 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : @IN A x s.
Proof. exact (EQ_MP (@lem6136997 A x s) (@lem6136994 A B C s x g f y op h1)). Qed.
Lemma lem6137000 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : @IN A y s.
Proof. exact (proj1 (@lem6136345 A B C s x g f y op h1)). Qed.
Lemma lem6137001 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term474 A y s.
Proof. exact (fun h0 : term180 A y s => @lem6137000 A B C s x g f y op h1). Qed.
Lemma lem6137003 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6137004 {A : Type'} (y : A) (s : A -> Prop) : (term474 A y s) = (@IN A y s).
Proof. exact (@lem6137003 (@IN A y s)). Qed.
Lemma lem6137005 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : @IN A y s.
Proof. exact (EQ_MP (@lem6137004 A y s) (@lem6137001 A B C s x g f y op h1)). Qed.
Lemma lem6137007 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : (@I (A -> B) f x) = (@I (A -> B) f y).
Proof. exact (proj2 (@lem6136347 A B C s x g f y op h1)). Qed.
Lemma lem6137008 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term476 A B x f y.
Proof. exact (fun h0 : term411 A B x f y => @lem6137007 A B C s x g f y op h1). Qed.
Lemma lem6137010 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6137011 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term476 A B x f y) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (@lem6137010 ((@I (A -> B) f x) = (@I (A -> B) f y))). Qed.
Lemma lem6137012 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : (@I (A -> B) f x) = (@I (A -> B) f y).
Proof. exact (EQ_MP (@lem6137011 A B x f y) (@lem6137008 A B C s x g f y op h1)). Qed.
Lemma lem6137014 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term422 A B C g f y op.
Proof. exact (proj2 (@lem6136341 A B C s x g f y op h1)). Qed.
Lemma lem6137015 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term477 A B C g f y op.
Proof. exact (fun h0 : (term407 A B C g f y) = (@neutral C op) => @lem6137014 A B C s x g f y op h1). Qed.
Lemma lem6137017 (p : Prop) : (term478 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6137018 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term477 A B C g f y op) = (term422 A B C g f y op).
Proof. exact (@lem6137017 ((term407 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6137019 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term422 A B C g f y op.
Proof. exact (EQ_MP (@lem6137018 A B C g f y op) (@lem6137015 A B C s x g f y op h1)). Qed.
Lemma lem6137035 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137036 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term472 A B C s _77113 g f _77114 op) = (term479 A B C s _77113 g f _77114 op).
Proof. exact (@lem6137035 (_77113 = _77114) (term180 A _77114 s) (term480 A B C _77113 g f _77114 op)). Qed.
Lemma lem6137052 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137053 {A B C : Type'} (_77113 : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term481 A B C s _77113 g f _77114 op) = (term482 A B C _77113 s g f _77114 op).
Proof. exact (@lem6137052 (term411 A B _77113 f _77114) (term180 A _77114 s) ((term407 A B C g f _77114) = (@neutral C op))). Qed.
Lemma lem6137069 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6137070 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (_77114 : A) (s : A -> Prop) : (term483 A B C s g f _77114 op) = (term484 A B C g f op _77114 s).
Proof. exact (@lem6137069 ((term407 A B C g f _77114) = (@neutral C op)) (term180 A _77114 s)). Qed.
Lemma lem6137078 {A B : Type'} (_77113 : A) (f : A -> B) (_77114 : A) : (term485 A B _77113 f _77114) = (term485 A B _77113 f _77114).
Proof. exact (eq_refl (term485 A B _77113 f _77114)). Qed.
Lemma lem6137079 {A B C : Type'} (_77113 : A) (g : B -> C) (f : A -> B) (op : type1400 C) (_77114 : A) (s : A -> Prop) : (term482 A B C _77113 s g f _77114 op) = (term486 A B C _77113 g f op _77114 s).
Proof. exact (MK_COMB (@lem6137078 A B _77113 f _77114) (@lem6137070 A B C g f op _77114 s)). Qed.
Lemma lem6137083 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137084 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term486 A B C _77113 g f op _77114 s) = (term487 A B C g op _77113 f _77114 s).
Proof. exact (@lem6137083 ((term407 A B C g f _77114) = (@neutral C op)) (term411 A B _77113 f _77114) (term180 A _77114 s)). Qed.
Lemma lem6137104 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term482 A B C _77113 s g f _77114 op) = (term487 A B C g op _77113 f _77114 s).
Proof. exact (TRANS (@lem6137079 A B C _77113 g f op _77114 s) (@lem6137084 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137105 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term481 A B C s _77113 g f _77114 op) = (term487 A B C g op _77113 f _77114 s).
Proof. exact (TRANS (@lem6137053 A B C _77113 s g f _77114 op) (@lem6137104 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137106 {A : Type'} (_77113 : A) (_77114 : A) : (term385 A _77113 _77114) = (term385 A _77113 _77114).
Proof. exact (eq_refl (term385 A _77113 _77114)). Qed.
Lemma lem6137107 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term479 A B C s _77113 g f _77114 op) = (term488 A B C g op _77113 f _77114 s).
Proof. exact (MK_COMB (@lem6137106 A _77113 _77114) (@lem6137105 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137118 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term472 A B C s _77113 g f _77114 op) = (term488 A B C g op _77113 f _77114 s).
Proof. exact (TRANS (@lem6137036 A B C s _77113 g f _77114 op) (@lem6137107 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137119 {A : Type'} (_77113 : A) (s : A -> Prop) : (term471 A _77113 s) = (term471 A _77113 s).
Proof. exact (eq_refl (term471 A _77113 s)). Qed.
Lemma lem6137120 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term473 A B C s _77113 g f _77114 op) = (term489 A B C g op _77113 f _77114 s).
Proof. exact (MK_COMB (@lem6137119 A _77113 s) (@lem6137118 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137124 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137125 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term489 A B C g op _77113 f _77114 s) = (term490 A B C g op _77113 f _77114 s).
Proof. exact (@lem6137124 (_77113 = _77114) (term180 A _77113 s) (term487 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137141 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137142 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term491 A B C g op _77113 f _77114 s) = (term492 A B C g op _77113 f _77114 s).
Proof. exact (@lem6137141 ((term407 A B C g f _77114) = (@neutral C op)) (term180 A _77113 s) (term493 A B _77113 f _77114 s)). Qed.
Lemma lem6137158 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137159 {A B : Type'} (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term494 A B _77113 f _77114 s) = (term495 A B f _77113 _77114 s).
Proof. exact (@lem6137158 (term411 A B _77113 f _77114) (term180 A _77113 s) (term180 A _77114 s)). Qed.
Lemma lem6137177 {A B C : Type'} (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term496 A B C g f _77114 op) = (term496 A B C g f _77114 op).
Proof. exact (eq_refl (term496 A B C g f _77114 op)). Qed.
Lemma lem6137178 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term492 A B C g op _77113 f _77114 s) = (term497 A B C g op f _77113 _77114 s).
Proof. exact (MK_COMB (@lem6137177 A B C g f _77114 op) (@lem6137159 A B f _77113 _77114 s)). Qed.
Lemma lem6137189 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term491 A B C g op _77113 f _77114 s) = (term497 A B C g op f _77113 _77114 s).
Proof. exact (TRANS (@lem6137142 A B C g op _77113 f _77114 s) (@lem6137178 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137190 {A : Type'} (_77113 : A) (_77114 : A) : (term385 A _77113 _77114) = (term385 A _77113 _77114).
Proof. exact (eq_refl (term385 A _77113 _77114)). Qed.
Lemma lem6137191 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term490 A B C g op _77113 f _77114 s) = (term498 A B C g op f _77113 _77114 s).
Proof. exact (MK_COMB (@lem6137190 A _77113 _77114) (@lem6137189 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137202 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term489 A B C g op _77113 f _77114 s) = (term498 A B C g op f _77113 _77114 s).
Proof. exact (TRANS (@lem6137125 A B C g op _77113 f _77114 s) (@lem6137191 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137203 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term473 A B C s _77113 g f _77114 op) = (term498 A B C g op f _77113 _77114 s).
Proof. exact (TRANS (@lem6137120 A B C g op _77113 f _77114 s) (@lem6137202 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6137205 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term499 A B C s _77113 g f _77114 op) = (term500 A B C g op f _77113 _77114 s).
Proof. exact (MK_COMB (@lem6137204) (@lem6137203 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137231 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137232 {A B C : Type'} (_77113 : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term481 A B C s _77113 g f _77114 op) = (term482 A B C _77113 s g f _77114 op).
Proof. exact (@lem6137231 (term411 A B _77113 f _77114) (term180 A _77114 s) ((term407 A B C g f _77114) = (@neutral C op))). Qed.
Lemma lem6137248 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6137249 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (_77114 : A) (s : A -> Prop) : (term483 A B C s g f _77114 op) = (term484 A B C g f op _77114 s).
Proof. exact (@lem6137248 ((term407 A B C g f _77114) = (@neutral C op)) (term180 A _77114 s)). Qed.
Lemma lem6137257 {A B : Type'} (_77113 : A) (f : A -> B) (_77114 : A) : (term485 A B _77113 f _77114) = (term485 A B _77113 f _77114).
Proof. exact (eq_refl (term485 A B _77113 f _77114)). Qed.
Lemma lem6137258 {A B C : Type'} (_77113 : A) (g : B -> C) (f : A -> B) (op : type1400 C) (_77114 : A) (s : A -> Prop) : (term482 A B C _77113 s g f _77114 op) = (term486 A B C _77113 g f op _77114 s).
Proof. exact (MK_COMB (@lem6137257 A B _77113 f _77114) (@lem6137249 A B C g f op _77114 s)). Qed.
Lemma lem6137262 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137263 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term486 A B C _77113 g f op _77114 s) = (term487 A B C g op _77113 f _77114 s).
Proof. exact (@lem6137262 ((term407 A B C g f _77114) = (@neutral C op)) (term411 A B _77113 f _77114) (term180 A _77114 s)). Qed.
Lemma lem6137283 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term482 A B C _77113 s g f _77114 op) = (term487 A B C g op _77113 f _77114 s).
Proof. exact (TRANS (@lem6137258 A B C _77113 g f op _77114 s) (@lem6137263 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137284 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term481 A B C s _77113 g f _77114 op) = (term487 A B C g op _77113 f _77114 s).
Proof. exact (TRANS (@lem6137232 A B C _77113 s g f _77114 op) (@lem6137283 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137285 {A : Type'} (_77113 : A) (s : A -> Prop) : (term471 A _77113 s) = (term471 A _77113 s).
Proof. exact (eq_refl (term471 A _77113 s)). Qed.
Lemma lem6137286 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term501 A B C s _77113 g f _77114 op) = (term491 A B C g op _77113 f _77114 s).
Proof. exact (MK_COMB (@lem6137285 A _77113 s) (@lem6137284 A B C g op _77113 f _77114 s)). Qed.
Lemma lem6137290 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137291 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77113 : A) (f : A -> B) (_77114 : A) (s : A -> Prop) : (term491 A B C g op _77113 f _77114 s) = (term492 A B C g op _77113 f _77114 s).
Proof. exact (@lem6137290 ((term407 A B C g f _77114) = (@neutral C op)) (term180 A _77113 s) (term493 A B _77113 f _77114 s)). Qed.
Lemma lem6137307 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137308 {A B : Type'} (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term494 A B _77113 f _77114 s) = (term495 A B f _77113 _77114 s).
Proof. exact (@lem6137307 (term411 A B _77113 f _77114) (term180 A _77113 s) (term180 A _77114 s)). Qed.
Lemma lem6137326 {A B C : Type'} (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term496 A B C g f _77114 op) = (term496 A B C g f _77114 op).
Proof. exact (eq_refl (term496 A B C g f _77114 op)). Qed.
Lemma lem6137327 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term492 A B C g op _77113 f _77114 s) = (term497 A B C g op f _77113 _77114 s).
Proof. exact (MK_COMB (@lem6137326 A B C g f _77114 op) (@lem6137308 A B f _77113 _77114 s)). Qed.
Lemma lem6137338 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term491 A B C g op _77113 f _77114 s) = (term497 A B C g op f _77113 _77114 s).
Proof. exact (TRANS (@lem6137291 A B C g op _77113 f _77114 s) (@lem6137327 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137339 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term501 A B C s _77113 g f _77114 op) = (term497 A B C g op f _77113 _77114 s).
Proof. exact (TRANS (@lem6137286 A B C g op _77113 f _77114 s) (@lem6137338 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137340 {A : Type'} (_77113 : A) (_77114 : A) : (term385 A _77113 _77114) = (term385 A _77113 _77114).
Proof. exact (eq_refl (term385 A _77113 _77114)). Qed.
Lemma lem6137341 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : (term502 A B C s _77113 g f _77114 op) = (term498 A B C g op f _77113 _77114 s).
Proof. exact (MK_COMB (@lem6137340 A _77113 _77114) (@lem6137339 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137352 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : ((term473 A B C s _77113 g f _77114 op) = (term502 A B C s _77113 g f _77114 op)) = ((term498 A B C g op f _77113 _77114 s) = (term498 A B C g op f _77113 _77114 s)).
Proof. exact (MK_COMB (@lem6137205 A B C g op f _77113 _77114 s) (@lem6137341 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6137355 (x : Prop) : (x = x) = True.
Proof. exact (@lem6137354 Prop x). Qed.
Lemma lem6137356 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77113 : A) (_77114 : A) (s : A -> Prop) : ((term498 A B C g op f _77113 _77114 s) = (term498 A B C g op f _77113 _77114 s)) = True.
Proof. exact (@lem6137355 (term498 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137357 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : ((term473 A B C s _77113 g f _77114 op) = (term502 A B C s _77113 g f _77114 op)) = True.
Proof. exact (TRANS (@lem6137352 A B C g op f _77113 _77114 s) (@lem6137356 A B C g op f _77113 _77114 s)). Qed.
Lemma lem6137358 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : True = ((term473 A B C s _77113 g f _77114 op) = (term502 A B C s _77113 g f _77114 op)).
Proof. exact (SYM (@lem6137357 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6137359 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term473 A B C s _77113 g f _77114 op) = (term502 A B C s _77113 g f _77114 op).
Proof. exact (EQ_MP (@lem6137358 A B C s _77113 g f _77114 op) (@lem0)). Qed.
Lemma lem6137360 {A B C : Type'} (_77113 : A) (_77114 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term502 A B C s _77113 g f _77114 op.
Proof. exact (EQ_MP (@lem6137359 A B C s _77113 g f _77114 op) (@lem6136664 A B C _77113 _77114 a s g f op h1)). Qed.
Lemma lem6137362 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6137363 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (_77113 : A) (_77114 : A) : (term502 A B C s _77113 g f _77114 op) = (term504 A B C s g f op _77113 _77114).
Proof. exact (@lem6137362 (term501 A B C s _77113 g f _77114 op) (_77113 = _77114)). Qed.
Lemma lem6137365 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6137366 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term507 A B C s _77113 g f _77114 op) = (term508 A B C s _77113 g f _77114 op).
Proof. exact (@lem6137365 (term180 A _77113 s) (term481 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6137368 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6137369 {A : Type'} (_77113 : A) (s : A -> Prop) : (term509 A _77113 s) = (@IN A _77113 s).
Proof. exact (@lem6137368 (@IN A _77113 s)). Qed.
Lemma lem6137370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6137371 {A : Type'} (_77113 : A) (s : A -> Prop) : (term510 A _77113 s) = (term425 A _77113 s).
Proof. exact (MK_COMB (@lem6137370) (@lem6137369 A _77113 s)). Qed.
Lemma lem6137373 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6137374 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term511 A B C s _77113 g f _77114 op) = (term512 A B C s _77113 g f _77114 op).
Proof. exact (@lem6137373 (term180 A _77114 s) (term480 A B C _77113 g f _77114 op)). Qed.
Lemma lem6137376 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6137377 {A : Type'} (_77114 : A) (s : A -> Prop) : (term509 A _77114 s) = (@IN A _77114 s).
Proof. exact (@lem6137376 (@IN A _77114 s)). Qed.
Lemma lem6137378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6137379 {A : Type'} (_77114 : A) (s : A -> Prop) : (term510 A _77114 s) = (term425 A _77114 s).
Proof. exact (MK_COMB (@lem6137378) (@lem6137377 A _77114 s)). Qed.
Lemma lem6137381 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6137382 {A B C : Type'} (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term513 A B C _77113 g f _77114 op) = (term514 A B C _77113 g f _77114 op).
Proof. exact (@lem6137381 (term411 A B _77113 f _77114) ((term407 A B C g f _77114) = (@neutral C op))). Qed.
Lemma lem6137384 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6137385 {A B : Type'} (_77113 : A) (f : A -> B) (_77114 : A) : (term515 A B _77113 f _77114) = ((@I (A -> B) f _77113) = (@I (A -> B) f _77114)).
Proof. exact (@lem6137384 ((@I (A -> B) f _77113) = (@I (A -> B) f _77114))). Qed.
Lemma lem6137386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6137387 {A B : Type'} (_77113 : A) (f : A -> B) (_77114 : A) : (term516 A B _77113 f _77114) = (term517 A B _77113 f _77114).
Proof. exact (MK_COMB (@lem6137386) (@lem6137385 A B _77113 f _77114)). Qed.
Lemma lem6137388 {A B C : Type'} (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term422 A B C g f _77114 op) = (term422 A B C g f _77114 op).
Proof. exact (eq_refl (term422 A B C g f _77114 op)). Qed.
Lemma lem6137389 {A B C : Type'} (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term514 A B C _77113 g f _77114 op) = (term518 A B C _77113 g f _77114 op).
Proof. exact (MK_COMB (@lem6137387 A B _77113 f _77114) (@lem6137388 A B C g f _77114 op)). Qed.
Lemma lem6137390 {A B C : Type'} (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term513 A B C _77113 g f _77114 op) = (term518 A B C _77113 g f _77114 op).
Proof. exact (TRANS (@lem6137382 A B C _77113 g f _77114 op) (@lem6137389 A B C _77113 g f _77114 op)). Qed.
Lemma lem6137391 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term512 A B C s _77113 g f _77114 op) = (term519 A B C s _77113 g f _77114 op).
Proof. exact (MK_COMB (@lem6137379 A _77114 s) (@lem6137390 A B C _77113 g f _77114 op)). Qed.
Lemma lem6137392 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term511 A B C s _77113 g f _77114 op) = (term519 A B C s _77113 g f _77114 op).
Proof. exact (TRANS (@lem6137374 A B C s _77113 g f _77114 op) (@lem6137391 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6137393 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term508 A B C s _77113 g f _77114 op) = (term520 A B C s _77113 g f _77114 op).
Proof. exact (MK_COMB (@lem6137371 A _77113 s) (@lem6137392 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6137394 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term507 A B C s _77113 g f _77114 op) = (term520 A B C s _77113 g f _77114 op).
Proof. exact (TRANS (@lem6137366 A B C s _77113 g f _77114 op) (@lem6137393 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6137395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6137396 {A B C : Type'} (s : A -> Prop) (_77113 : A) (g : B -> C) (f : A -> B) (_77114 : A) (op : type1400 C) : (term521 A B C s _77113 g f _77114 op) = (term522 A B C s _77113 g f _77114 op).
Proof. exact (MK_COMB (@lem6137395) (@lem6137394 A B C s _77113 g f _77114 op)). Qed.
Lemma lem6137397 {A : Type'} (_77113 : A) (_77114 : A) : (_77113 = _77114) = (_77113 = _77114).
Proof. exact (eq_refl (_77113 = _77114)). Qed.
Lemma lem6137398 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (_77113 : A) (_77114 : A) : (term504 A B C s g f op _77113 _77114) = (term523 A B C s g f op _77113 _77114).
Proof. exact (MK_COMB (@lem6137396 A B C s _77113 g f _77114 op) (@lem6137397 A _77113 _77114)). Qed.
Lemma lem6137399 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (_77113 : A) (_77114 : A) : (term502 A B C s _77113 g f _77114 op) = (term523 A B C s g f op _77113 _77114).
Proof. exact (TRANS (@lem6137363 A B C s g f op _77113 _77114) (@lem6137398 A B C s g f op _77113 _77114)). Qed.
Lemma lem6137401 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term518 A B C x g f y op.
Proof. exact (conj (@lem6137012 A B C s x g f y op h1) (@lem6137019 A B C s x g f y op h1)). Qed.
Lemma lem6137402 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term519 A B C s x g f y op.
Proof. exact (conj (@lem6137005 A B C s x g f y op h1) (@lem6137401 A B C s x g f y op h1)). Qed.
Lemma lem6137403 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term520 A B C s x g f y op.
Proof. exact (conj (@lem6136998 A B C s x g f y op h1) (@lem6137402 A B C s x g f y op h1)). Qed.
Lemma lem6137405 {A B C : Type'} (_77113 : A) (_77114 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term523 A B C s g f op _77113 _77114.
Proof. exact (EQ_MP (@lem6137399 A B C s g f op _77113 _77114) (@lem6137360 A B C _77113 _77114 a s g f op h1)). Qed.
Lemma lem6137406 {A B C : Type'} (_77113 : A) (_77114 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term523 A B C s g f op _77113 _77114.
Proof. exact (@lem6137405 A B C _77113 _77114 a s g f op h1). Qed.
Lemma lem6137407 {A B C : Type'} (x : A) (y : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term523 A B C s g f op x y.
Proof. exact (@lem6137406 A B C x y a s g f op h1). Qed.
Lemma lem6137410 {A B C : Type'} (a : A) (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term430 A B C s x g f y op) : x = y.
Proof. exact (@lem6137407 A B C x y a s g f op h1 (@lem6137403 A B C s x g f y op h2)). Qed.
Lemma lem6137411 {A B C : Type'} (a : A) (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term430 A B C s x g f y op) : term524 A x y.
Proof. exact (fun h0 : term389 A x y => @lem6137410 A B C a s x g f y op h1 h2). Qed.
Lemma lem6137413 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6137414 {A : Type'} (x : A) (y : A) : (term524 A x y) = (x = y).
Proof. exact (@lem6137413 (x = y)). Qed.
Lemma lem6137415 {A B C : Type'} (a : A) (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term430 A B C s x g f y op) : x = y.
Proof. exact (EQ_MP (@lem6137414 A x y) (@lem6137411 A B C a s x g f y op h1 h2)). Qed.
Lemma lem6137418 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6137420 {A : Type'} (x : A) (y : A) : (term389 A x y) = (term525 A x y).
Proof. exact (@lem6137418 (x = y)). Qed.
Lemma lem6137423 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term430 A B C s x g f y op) : term525 A x y.
Proof. exact (EQ_MP (@lem6137420 A x y) (@lem6136614 A B C s x g f y op h1)). Qed.
Lemma lem6137426 {A B C : Type'} (a : A) (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term430 A B C s x g f y op) : False.
Proof. exact (@lem6137423 A B C s x g f y op h2 (@lem6137415 A B C a s x g f y op h1 h2)). Qed.
Lemma lem6137427 {A B C : Type'} (a : A) (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term430 A B C s x g f y op) : term526.
Proof. exact (fun h0 : ~ False => @lem6137426 A B C a s x g f y op h1 h2). Qed.
Lemma lem6137429 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6137430 : term526 = False.
Proof. exact (@lem6137429 False). Qed.
Lemma lem6137431 {A B C : Type'} (a : A) (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term430 A B C s x g f y op) : False.
Proof. exact (EQ_MP (@lem6137430) (@lem6137427 A B C a s x g f y op h1 h2)). Qed.
Lemma lem6137588 {C : Type'} (x : C) (y : C) (z : C) : term527 C x y z.
Proof. exact (@lem21385 C x y z). Qed.
Lemma lem6137606 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term33 A B C op f s g) = (term34 A B C op s g f).
Proof. exact (h1). Qed.
Lemma lem6137607 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : term528 A B C op s g f.
Proof. exact (fun h0 : term529 A B C op s g f => @lem6137606 A B C op s g f h1). Qed.
Lemma lem6137609 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6137610 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term528 A B C op s g f) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (@lem6137609 ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6137611 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term33 A B C op f s g) = (term34 A B C op s g f).
Proof. exact (EQ_MP (@lem6137610 A B C op s g f) (@lem6137607 A B C op s g f h1)). Qed.
Lemma lem6137613 {C : Type'} (x : C) : x = x.
Proof. exact (@lem21386 C x). Qed.
Lemma lem6137614 {C : Type'} (x : C) : x = x.
Proof. exact (@lem6137613 C x). Qed.
Lemma lem6137615 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term33 A B C op f s g).
Proof. exact (@lem6137614 C (term33 A B C op f s g)). Qed.
Lemma lem6137616 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term530 A B C op f s g.
Proof. exact (fun h0 : term531 A B C op f s g => @lem6137615 A B C op f s g). Qed.
Lemma lem6137618 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6137619 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term530 A B C op f s g) = ((term33 A B C op f s g) = (term33 A B C op f s g)).
Proof. exact (@lem6137618 ((term33 A B C op f s g) = (term33 A B C op f s g))). Qed.
Lemma lem6137620 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term33 A B C op f s g).
Proof. exact (EQ_MP (@lem6137619 A B C op f s g) (@lem6137616 A B C op f s g)). Qed.
Lemma lem6137638 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6137639 {C : Type'} (y : C) (x : C) (z : C) : (term532 C x y z) = (term533 C y x z).
Proof. exact (@lem6137638 (y = z) (term389 C x z)). Qed.
Lemma lem6137649 {C : Type'} (x : C) (y : C) : (term534 C x y) = (term534 C x y).
Proof. exact (eq_refl (term534 C x y)). Qed.
Lemma lem6137650 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term535 C y x z).
Proof. exact (MK_COMB (@lem6137649 C x y) (@lem6137639 C y x z)). Qed.
Lemma lem6137654 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6137655 {C : Type'} (y : C) (x : C) (z : C) : (term535 C y x z) = (term536 C y x z).
Proof. exact (@lem6137654 (y = z) (term389 C x y) (term389 C x z)). Qed.
Lemma lem6137677 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term536 C y x z).
Proof. exact (TRANS (@lem6137650 C y x z) (@lem6137655 C y x z)). Qed.
Lemma lem6137678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6137679 {C : Type'} (y : C) (x : C) (z : C) : (term537 C x y z) = (term538 C y x z).
Proof. exact (MK_COMB (@lem6137678) (@lem6137677 C y x z)). Qed.
Lemma lem6137701 {C : Type'} (y : C) (x : C) (z : C) : (term536 C y x z) = (term536 C y x z).
Proof. exact (eq_refl (term536 C y x z)). Qed.
Lemma lem6137702 {C : Type'} (y : C) (x : C) (z : C) : ((term527 C x y z) = (term536 C y x z)) = ((term536 C y x z) = (term536 C y x z)).
Proof. exact (MK_COMB (@lem6137679 C y x z) (@lem6137701 C y x z)). Qed.
Lemma lem6137704 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6137705 (x : Prop) : (x = x) = True.
Proof. exact (@lem6137704 Prop x). Qed.
Lemma lem6137706 {C : Type'} (y : C) (x : C) (z : C) : ((term536 C y x z) = (term536 C y x z)) = True.
Proof. exact (@lem6137705 (term536 C y x z)). Qed.
Lemma lem6137707 {C : Type'} (y : C) (x : C) (z : C) : ((term527 C x y z) = (term536 C y x z)) = True.
Proof. exact (TRANS (@lem6137702 C y x z) (@lem6137706 C y x z)). Qed.
Lemma lem6137708 {C : Type'} (y : C) (x : C) (z : C) : True = ((term527 C x y z) = (term536 C y x z)).
Proof. exact (SYM (@lem6137707 C y x z)). Qed.
Lemma lem6137709 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term536 C y x z).
Proof. exact (EQ_MP (@lem6137708 C y x z) (@lem0)). Qed.
Lemma lem6137710 {C : Type'} (y : C) (x : C) (z : C) : term536 C y x z.
Proof. exact (EQ_MP (@lem6137709 C y x z) (@lem6137588 C x y z)). Qed.
Lemma lem6137712 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6137713 {C : Type'} (x : C) (y : C) (z : C) : (term536 C y x z) = (term539 C x y z).
Proof. exact (@lem6137712 (term540 C y x z) (y = z)). Qed.
Lemma lem6137715 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6137716 {C : Type'} (y : C) (x : C) (z : C) : (term541 C y x z) = (term542 C y x z).
Proof. exact (@lem6137715 (term389 C x y) (term389 C x z)). Qed.
Lemma lem6137718 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6137719 {C : Type'} (x : C) (y : C) : (term382 C x y) = (x = y).
Proof. exact (@lem6137718 (x = y)). Qed.
Lemma lem6137720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6137721 {C : Type'} (x : C) (y : C) : (term543 C x y) = (term544 C x y).
Proof. exact (MK_COMB (@lem6137720) (@lem6137719 C x y)). Qed.
Lemma lem6137723 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6137724 {C : Type'} (x : C) (z : C) : (term382 C x z) = (x = z).
Proof. exact (@lem6137723 (x = z)). Qed.
Lemma lem6137725 {C : Type'} (y : C) (x : C) (z : C) : (term542 C y x z) = (term545 C y x z).
Proof. exact (MK_COMB (@lem6137721 C x y) (@lem6137724 C x z)). Qed.
Lemma lem6137726 {C : Type'} (y : C) (x : C) (z : C) : (term541 C y x z) = (term545 C y x z).
Proof. exact (TRANS (@lem6137716 C y x z) (@lem6137725 C y x z)). Qed.
Lemma lem6137727 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6137728 {C : Type'} (y : C) (x : C) (z : C) : (term546 C y x z) = (term547 C y x z).
Proof. exact (MK_COMB (@lem6137727) (@lem6137726 C y x z)). Qed.
Lemma lem6137729 {C : Type'} (y : C) (z : C) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6137730 {C : Type'} (x : C) (y : C) (z : C) : (term539 C x y z) = (term548 C x y z).
Proof. exact (MK_COMB (@lem6137728 C y x z) (@lem6137729 C y z)). Qed.
Lemma lem6137731 {C : Type'} (x : C) (y : C) (z : C) : (term536 C y x z) = (term548 C x y z).
Proof. exact (TRANS (@lem6137713 C x y z) (@lem6137730 C x y z)). Qed.
Lemma lem6137733 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : term549 A B C op f s g.
Proof. exact (conj (@lem6137611 A B C op s g f h1) (@lem6137620 A B C op f s g)). Qed.
Lemma lem6137735 {C : Type'} (x : C) (y : C) (z : C) : term548 C x y z.
Proof. exact (EQ_MP (@lem6137731 C x y z) (@lem6137710 C y x z)). Qed.
Lemma lem6137736 {C : Type'} (x : C) (y : C) (z : C) : term548 C x y z.
Proof. exact (@lem6137735 C x y z). Qed.
Lemma lem6137737 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term550 A B C op f s g.
Proof. exact (@lem6137736 C (term33 A B C op f s g) (term34 A B C op s g f) (term33 A B C op f s g)). Qed.
Lemma lem6137740 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term34 A B C op s g f) = (term33 A B C op f s g).
Proof. exact (@lem6137737 A B C op f s g (@lem6137733 A B C op s g f h1)). Qed.
Lemma lem6137741 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : term551 A B C op f s g.
Proof. exact (fun h0 : term284 A B C op f s g => @lem6137740 A B C op s g f h1). Qed.
Lemma lem6137743 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6137744 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term551 A B C op f s g) = ((term34 A B C op s g f) = (term33 A B C op f s g)).
Proof. exact (@lem6137743 ((term34 A B C op s g f) = (term33 A B C op f s g))). Qed.
Lemma lem6137745 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term34 A B C op s g f) = (term33 A B C op f s g).
Proof. exact (EQ_MP (@lem6137744 A B C op f s g) (@lem6137741 A B C op s g f h1)). Qed.
Lemma lem6137748 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6137750 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term284 A B C op f s g) = (term552 A B C op f s g).
Proof. exact (@lem6137748 ((term34 A B C op s g f) = (term33 A B C op f s g))). Qed.
Lemma lem6137753 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term284 A B C op f s g) : term552 A B C op f s g.
Proof. exact (EQ_MP (@lem6137750 A B C op f s g) (@lem6136720 A B C op f s g h1)). Qed.
Lemma lem6137756 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : False.
Proof. exact (@lem6137753 A B C op f s g h1 (@lem6137745 A B C op s g f h2)). Qed.
Lemma lem6137757 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : term526.
Proof. exact (fun h0 : ~ False => @lem6137756 A B C op s g f h1 h2). Qed.
Lemma lem6137759 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6137760 : term526 = False.
Proof. exact (@lem6137759 False). Qed.
Lemma lem6137761 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : False.
Proof. exact (EQ_MP (@lem6137760) (@lem6137757 A B C op s g f h1 h2)). Qed.
Lemma lem6137762 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = False.
Proof. exact (prop_ext (fun h3 : (term33 A B C op f s g) = (term34 A B C op s g f) => @lem6137761 A B C op s g f h1 h2) (fun h3 : False => @lem6136722 A B C op s g f h2)). Qed.
Lemma lem6137763 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : False.
Proof. exact (EQ_MP (@lem6137762 A B C op s g f h1 h2) (@lem6136722 A B C op s g f h2)). Qed.
Lemma lem6137764 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term284 A B C op f s g) = False.
Proof. exact (prop_ext (fun h3 : term284 A B C op f s g => @lem6137763 A B C op s g f h1 h2) (fun h3 : False => @lem6136720 A B C op f s g h1)). Qed.
Lemma lem6137765 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : False.
Proof. exact (EQ_MP (@lem6137764 A B C op s g f h1 h2) (@lem6136720 A B C op f s g h1)). Qed.
Lemma lem6137766 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = False.
Proof. exact (prop_ext (fun h3 : (term33 A B C op f s g) = (term34 A B C op s g f) => @lem6137765 A B C op s g f h1 h2) (fun h3 : False => @lem6136574 A B C op s g f h2)). Qed.
Lemma lem6137767 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : False.
Proof. exact (EQ_MP (@lem6137766 A B C op s g f h1 h2) (@lem6136574 A B C op s g f h2)). Qed.
Lemma lem6137768 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term284 A B C op f s g) = False.
Proof. exact (prop_ext (fun h3 : term284 A B C op f s g => @lem6137767 A B C op s g f h1 h2) (fun h3 : False => @lem6136570 A B C op f s g h1)). Qed.
Lemma lem6137769 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : False.
Proof. exact (EQ_MP (@lem6137768 A B C op s g f h1 h2) (@lem6136570 A B C op f s g h1)). Qed.
Lemma lem6137770 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = False.
Proof. exact (prop_ext (fun h3 : (term33 A B C op f s g) = (term34 A B C op s g f) => @lem6137769 A B C op s g f h1 h2) (fun h3 : False => @lem6136574 A B C op s g f h2)). Qed.
Lemma lem6137771 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : False.
Proof. exact (EQ_MP (@lem6137770 A B C op s g f h1 h2) (@lem6136574 A B C op s g f h2)). Qed.
Lemma lem6137772 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : (term284 A B C op f s g) = False.
Proof. exact (prop_ext (fun h3 : term284 A B C op f s g => @lem6137771 A B C op s g f h1 h2) (fun h3 : False => @lem6136570 A B C op f s g h1)). Qed.
Lemma lem6137773 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term284 A B C op f s g) (h2 : (term33 A B C op f s g) = (term34 A B C op s g f)) : False.
Proof. exact (EQ_MP (@lem6137772 A B C op s g f h1 h2) (@lem6136570 A B C op f s g h1)). Qed.
Lemma lem6137774 {A B C : Type'} (a : A) (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term284 A B C op f s g) (h3 : term374 A B C x y op s g f) : False.
Proof. exact (or_elim (@lem6136340 A B C x y op s g f h3) (fun h0 : term430 A B C s x g f y op => @lem6137431 A B C a s x g f y op h1 h0) (fun h0 : (term33 A B C op f s g) = (term34 A B C op s g f) => @lem6137773 A B C op s g f h2 h0)). Qed.
Lemma lem6137775 {A B C : Type'} (a : A) (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term284 A B C op f s g) (h3 : term374 A B C x y op s g f) : (term284 A B C op f s g) = False.
Proof. exact (prop_ext (fun h4 : term284 A B C op f s g => @lem6137774 A B C a x y op s g f h1 h2 h3) (fun h4 : False => @lem6136241 A B C op f s g h2)). Qed.
Lemma lem6137776 {A B C : Type'} (a : A) (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term284 A B C op f s g) (h3 : term374 A B C x y op s g f) : False.
Proof. exact (EQ_MP (@lem6137775 A B C a x y op s g f h1 h2 h3) (@lem6136241 A B C op f s g h2)). Qed.
Lemma lem6137777 {A B C : Type'} (a : A) (x : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term270 A B C a s g f op) (h2 : term377 A B C x op s g f) (h3 : term284 A B C op f s g) : False.
Proof. exact (ex_elim (@lem6136096 A B C x op s g f h2) (fun y : A => fun h0 : term376 A B C x op s g f y => @lem6137776 A B C a x y op s g f h1 h3 h0)). Qed.
Lemma lem6137778 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term284 A B C op f s g) (h3 : term175 A B C op s g f) : False.
Proof. exact (ex_elim (@lem6135975 A B C op s g f h3) (fun x : A => fun h0 : term378 A B C op s g f x => @lem6137777 A B C a x op f s g h1 h0 h2)). Qed.
Lemma lem6137779 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term284 A B C op f s g) (h3 : term175 A B C op s g f) : (term284 A B C op f s g) = False.
Proof. exact (prop_ext (fun h4 : term284 A B C op f s g => @lem6137778 A B C a op s g f h1 h2 h3) (fun h4 : False => @lem6136095 A B C op f s g h2)). Qed.
Lemma lem6137780 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term284 A B C op f s g) (h3 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6137779 A B C a op s g f h1 h2 h3) (@lem6136095 A B C op f s g h2)). Qed.
Lemma lem6137781 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term284 A B C op f s g) (h3 : term175 A B C op s g f) : (term284 A B C op f s g) = False.
Proof. exact (prop_ext (fun h4 : term284 A B C op f s g => @lem6137780 A B C a op s g f h1 h2 h3) (fun h4 : False => @lem6135816 A B C op f s g h2)). Qed.
Lemma lem6137782 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term284 A B C op f s g) (h3 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6137781 A B C a op s g f h1 h2 h3) (@lem6135816 A B C op f s g h2)). Qed.
Lemma lem6137783 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term175 A B C op s g f) : term283 A B C op f s g.
Proof. exact (fun h0 : term284 A B C op f s g => @lem6137782 A B C a op s g f h1 h0 h2). Qed.
Lemma lem6137784 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term175 A B C op s g f) : (term34 A B C op s g f) = (term33 A B C op f s g).
Proof. exact (EQ_MP (@lem6135815 A B C op f s g) (@lem6137783 A B C a op s g f h1 h2)). Qed.
Lemma lem6137785 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term292 A B C a op f s g.
Proof. exact (fun h0 : term270 A B C a s g f op => @lem6137784 A B C a op s g f h0 h1). Qed.
Lemma lem6137786 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term294 A B C a op f s g.
Proof. exact (fun h0 : @FINITE A s => @lem6137785 A B C a op s g f h1). Qed.
Lemma lem6137787 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term297 A B C a op f s g.
Proof. exact (fun h0 : term180 A a s => @lem6137786 A B C a op s g f h1). Qed.
Lemma lem6137788 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term300 A B C a op f s g.
Proof. exact (fun h0 : term175 A B C op s g f => @lem6137787 A B C a op s g f h0). Qed.
Lemma lem6137789 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term302 A B C a op f s g.
Proof. exact (fun h0 : @monoidal C op => @lem6137788 A B C a op f s g). Qed.
Lemma lem6137794 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term306 A B C op f s g.
Proof. exact (fun a : A => @lem6137789 A B C a op f s g). Qed.
Lemma lem6137799 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : term310 A B C f s g.
Proof. exact (fun op : type1400 C => @lem6137794 A B C op f s g). Qed.
Lemma lem6137804 {A B C : Type'} (s : A -> Prop) (g : B -> C) : term314 A B C s g.
Proof. exact (fun f : A -> B => @lem6137799 A B C f s g). Qed.
Lemma lem6137809 {A B C : Type'} (g : B -> C) : term318 A B C g.
Proof. exact (fun s : A -> Prop => @lem6137804 A B C s g). Qed.
Lemma lem6137814 {A B C : Type'} : term322 A B C.
Proof. exact (fun g : B -> C => @lem6137809 A B C g). Qed.
Lemma lem6137815 {A B C : Type'} : term321 A B C.
Proof. exact (EQ_MP (@lem6135806 A B C) (@lem6137814 A B C)). Qed.
Lemma lem6137816 {A B C : Type'} (g : B -> C) : term553 A B C g.
Proof. exact (@lem6137815 A B C g). Qed.
Lemma lem6137817 {A B C : Type'} (g : B -> C) : (term553 A B C g) = (term317 A B C g).
Proof. exact (eq_refl (term553 A B C g)). Qed.
Lemma lem6137818 {A B C : Type'} (g : B -> C) : term317 A B C g.
Proof. exact (EQ_MP (@lem6137817 A B C g) (@lem6137816 A B C g)). Qed.
Lemma lem6137819 {A B C : Type'} (g : B -> C) (s : A -> Prop) : term554 A B C g s.
Proof. exact (@lem6137818 A B C g s). Qed.
Lemma lem6137820 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term554 A B C g s) = (term313 A B C s g).
Proof. exact (eq_refl (term554 A B C g s)). Qed.
Lemma lem6137821 {A B C : Type'} (s : A -> Prop) (g : B -> C) : term313 A B C s g.
Proof. exact (EQ_MP (@lem6137820 A B C s g) (@lem6137819 A B C g s)). Qed.
Lemma lem6137822 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : term555 A B C s g f.
Proof. exact (@lem6137821 A B C s g f). Qed.
Lemma lem6137823 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term555 A B C s g f) = (term309 A B C f s g).
Proof. exact (eq_refl (term555 A B C s g f)). Qed.
Lemma lem6137824 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : term309 A B C f s g.
Proof. exact (EQ_MP (@lem6137823 A B C f s g) (@lem6137822 A B C s g f)). Qed.
Lemma lem6137825 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) : term556 A B C f s g op.
Proof. exact (@lem6137824 A B C f s g op). Qed.
Lemma lem6137826 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term556 A B C f s g op) = (term305 A B C op f s g).
Proof. exact (eq_refl (term556 A B C f s g op)). Qed.
Lemma lem6137827 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term305 A B C op f s g.
Proof. exact (EQ_MP (@lem6137826 A B C op f s g) (@lem6137825 A B C f s g op)). Qed.
Lemma lem6137828 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (a : A) : term557 A B C op f s g a.
Proof. exact (@lem6137827 A B C op f s g a). Qed.
Lemma lem6137829 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term557 A B C op f s g a) = (term285 A B C a op f s g).
Proof. exact (eq_refl (term557 A B C op f s g a)). Qed.
Lemma lem6137830 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term285 A B C a op f s g.
Proof. exact (EQ_MP (@lem6137829 A B C a op f s g) (@lem6137828 A B C op f s g a)). Qed.
Lemma lem6137832 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term285 A B C a op f s g.
Proof. exact (@lem6135484 A B C a op f s g (@lem6137830 A B C a op f s g)). Qed.
Lemma lem6137833 {A B C : Type'} (a : A) (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term299 A B C a op f s g.
Proof. exact (@lem6137832 A B C a op f s g (@lem6113800 C op h1)). Qed.
Lemma lem6137834 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term175 A B C op s g f) : term296 A B C a op f s g.
Proof. exact (@lem6137833 A B C a f s g op h1 (@lem6135446 A B C op s g f h2)). Qed.
Lemma lem6137835 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term180 A a s) (h3 : term175 A B C op s g f) : term293 A B C a op f s g.
Proof. exact (@lem6137834 A B C a op s g f h1 h3 (@lem6135448 A a s h2)). Qed.
Lemma lem6137836 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : term291 A B C a op f s g.
Proof. exact (@lem6137835 A B C a op s g f h2 h3 h4 (@lem6135447 A s h1)). Qed.
Lemma lem6137837 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term283 A B C op f s g.
Proof. exact (@lem6137836 A B C a op s g f h2 h3 h4 h5 (@lem6135449 A B C a s g f op h1)). Qed.
Lemma lem6137838 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term284 A B C op f s g) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : False.
Proof. exact (@lem6137837 A B C a op s g f h1 h2 h3 h5 h6 (@lem6135468 A B C op f s g h4)). Qed.
Lemma lem6137839 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term284 A B C op f s g) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : (term284 A B C op f s g) = False.
Proof. exact (prop_ext (fun h7 : term284 A B C op f s g => @lem6137838 A B C a op s g f h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem6135468 A B C op f s g h4)). Qed.
Lemma lem6137840 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term284 A B C op f s g) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6137839 A B C a op s g f h1 h2 h3 h4 h5 h6) (@lem6135468 A B C op f s g h4)). Qed.
Lemma lem6137841 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term283 A B C op f s g.
Proof. exact (fun h0 : term284 A B C op f s g => @lem6137840 A B C a op s g f h1 h2 h3 h0 h4 h5). Qed.
Lemma lem6137842 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term34 A B C op s g f) = (term33 A B C op f s g).
Proof. exact (EQ_MP (@lem6135467 A B C op f s g) (@lem6137841 A B C a op s g f h1 h2 h3 h4 h5)). Qed.
Lemma lem6137846 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem6113763 A B y f s) (@lem6113762 A B y s f)). Qed.
Lemma lem6137847 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (@lem6137846 A B y f s). Qed.
Lemma lem6137848 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term558 A B a f s) = (term559 A B a f s).
Proof. exact (@lem6137847 A B (f a) f s). Qed.
Lemma lem6137857 {C : Type'} : (@COND C) = (@COND C).
Proof. exact (eq_refl (@COND C)). Qed.
Lemma lem6137858 {A B C : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term560 A B C a f s) = (term561 A B C a f s).
Proof. exact (MK_COMB (@lem6137857 C) (@lem6137848 A B a f s)). Qed.
Lemma lem6137859 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term33 A B C op f s g).
Proof. exact (eq_refl (term33 A B C op f s g)). Qed.
Lemma lem6137860 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term562 A B C a op f s g) = (term563 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137858 A B C a f s) (@lem6137859 A B C op f s g)). Qed.
Lemma lem6137861 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term564 A B C a op f s g) = (term564 A B C a op f s g).
Proof. exact (eq_refl (term564 A B C a op f s g)). Qed.
Lemma lem6137862 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term222 A B C a op f s g) = (term565 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137860 A B C a op f s g) (@lem6137861 A B C a op f s g)). Qed.
Lemma lem6137863 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6137864 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term224 A B C a op f s g) = (term566 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137863 C) (@lem6137862 A B C a op f s g)). Qed.
Lemma lem6137865 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term279 A B C a op f s g) = (term279 A B C a op f s g).
Proof. exact (eq_refl (term279 A B C a op f s g)). Qed.
Lemma lem6137866 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term222 A B C a op f s g) = (term279 A B C a op f s g)) = ((term565 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (MK_COMB (@lem6137864 A B C a op f s g) (@lem6137865 A B C a op f s g)). Qed.
Lemma lem6137869 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term565 A B C a op f s g) = (term279 A B C a op f s g)) = ((term222 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (SYM (@lem6137866 A B C a op f s g)). Qed.
Lemma lem6137870 {C : Type'} (_474 : C) (_475 : Prop) (_476 : C -> Prop) (_477 : C) : (term567 C _476 _475 _474 _477) = (term568 C _474 _475 _476 _477).
Proof. exact (@lem13473 C _474 _475 _476 _477). Qed.
Lemma lem6137871 {A B C : Type'} (_474 : C) (_475 : Prop) (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (_477 : C) : (term569 A B C a op f s g _475 _474 _477) = (term570 A B C _474 _475 a op f s g _477).
Proof. exact (@lem6137870 C _474 _475 (term571 A B C a op f s g) _477). Qed.
Lemma lem6137872 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term572 A B C a op f s g) = (term573 A B C a op f s g).
Proof. exact (@lem6137871 A B C (term33 A B C op f s g) (term559 A B a f s) a op f s g (term564 A B C a op f s g)). Qed.
Lemma lem6137873 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term574 A B C a op f s g) = ((term564 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (eq_refl (term574 A B C a op f s g)). Qed.
Lemma lem6137874 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term575 A B a f s) = (term575 A B a f s).
Proof. exact (eq_refl (term575 A B a f s)). Qed.
Lemma lem6137875 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term576 A B C a op f s g) = (term577 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137874 A B a f s) (@lem6137873 A B C a op f s g)). Qed.
Lemma lem6137876 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term578 A B C a op f s g) = ((term33 A B C op f s g) = (term279 A B C a op f s g)).
Proof. exact (eq_refl (term578 A B C a op f s g)). Qed.
Lemma lem6137877 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term579 A B a f s) = (term579 A B a f s).
Proof. exact (eq_refl (term579 A B a f s)). Qed.
Lemma lem6137878 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term580 A B C a op f s g) = (term581 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137877 A B a f s) (@lem6137876 A B C a op f s g)). Qed.
Lemma lem6137879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6137880 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term582 A B C a op f s g) = (term583 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137879) (@lem6137878 A B C a op f s g)). Qed.
Lemma lem6137881 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term573 A B C a op f s g) = (term584 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137880 A B C a op f s g) (@lem6137875 A B C a op f s g)). Qed.
Lemma lem6137882 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term572 A B C a op f s g) = ((term565 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (eq_refl (term572 A B C a op f s g)). Qed.
Lemma lem6137883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6137884 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term585 A B C a op f s g) = (term586 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137883) (@lem6137882 A B C a op f s g)). Qed.
Lemma lem6137885 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term572 A B C a op f s g) = (term573 A B C a op f s g)) = (((term565 A B C a op f s g) = (term279 A B C a op f s g)) = (term584 A B C a op f s g)).
Proof. exact (MK_COMB (@lem6137884 A B C a op f s g) (@lem6137881 A B C a op f s g)). Qed.
Lemma lem6137886 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term565 A B C a op f s g) = (term279 A B C a op f s g)) = (term584 A B C a op f s g).
Proof. exact (EQ_MP (@lem6137885 A B C a op f s g) (@lem6137872 A B C a op f s g)). Qed.
Lemma lem6137887 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term584 A B C a op f s g) = ((term565 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (SYM (@lem6137886 A B C a op f s g)). Qed.
Lemma lem6137888 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) (h1 : term559 A B a f s) : term559 A B a f s.
Proof. exact (h1). Qed.
Lemma lem6137922 {A B C : Type'} (f : B -> C) : term587 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem6137923 {A B C : Type'} (f : B -> C) : (term587 A B C f) = (term588 A B C f).
Proof. exact (eq_refl (term587 A B C f)). Qed.
Lemma lem6137924 {A B C : Type'} (f : B -> C) : term588 A B C f.
Proof. exact (EQ_MP (@lem6137923 A B C f) (@lem6137922 A B C f)). Qed.
Lemma lem6137925 {A B C : Type'} (f : B -> C) (g : A -> B) : term589 A B C f g.
Proof. exact (@lem6137924 A B C f g). Qed.
Lemma lem6137926 {A B C : Type'} (f : B -> C) (g : A -> B) : (term589 A B C f g) = (term590 A B C f g).
Proof. exact (eq_refl (term589 A B C f g)). Qed.
Lemma lem6137927 {A B C : Type'} (f : B -> C) (g : A -> B) : term590 A B C f g.
Proof. exact (EQ_MP (@lem6137926 A B C f g) (@lem6137925 A B C f g)). Qed.
Lemma lem6137928 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term591 A B C f g x.
Proof. exact (@lem6137927 A B C f g x). Qed.
Lemma lem6137929 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term591 A B C f g x) = ((@o A B C f g x) = (term110 A B C f g x)).
Proof. exact (eq_refl (term591 A B C f g x)). Qed.
Lemma lem6137952 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term110 A B C f g x).
Proof. exact (EQ_MP (@lem6137929 A B C f g x) (@lem6137928 A B C f g x)). Qed.
Lemma lem6137953 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term110 A B C f g x).
Proof. exact (@lem6137952 A B C f g x). Qed.
Lemma lem6137954 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) : (@o A B C g f a) = (term110 A B C g f a).
Proof. exact (@lem6137953 A B C g f a). Qed.
Lemma lem6137955 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6137956 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) : (term592 A B C op g f a) = (term593 A B C op g f a).
Proof. exact (MK_COMB (@lem6137955 C op) (@lem6137954 A B C g f a)). Qed.
Lemma lem6137957 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term33 A B C op f s g).
Proof. exact (eq_refl (term33 A B C op f s g)). Qed.
Lemma lem6137958 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term279 A B C a op f s g) = (term564 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137956 A B C op g f a) (@lem6137957 A B C op f s g)). Qed.
Lemma lem6137959 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term594 A B C op f s g) = (term594 A B C op f s g).
Proof. exact (eq_refl (term594 A B C op f s g)). Qed.
Lemma lem6137960 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term33 A B C op f s g) = (term279 A B C a op f s g)) = ((term33 A B C op f s g) = (term564 A B C a op f s g)).
Proof. exact (MK_COMB (@lem6137959 A B C op f s g) (@lem6137958 A B C a op f s g)). Qed.
Lemma lem6137963 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term33 A B C op f s g) = (term564 A B C a op f s g)) = ((term33 A B C op f s g) = (term279 A B C a op f s g)).
Proof. exact (SYM (@lem6137960 A B C a op f s g)). Qed.
Lemma lem6137964 {A B C : Type'} (f : B -> C) : term587 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem6137965 {A B C : Type'} (f : B -> C) : (term587 A B C f) = (term588 A B C f).
Proof. exact (eq_refl (term587 A B C f)). Qed.
Lemma lem6137966 {A B C : Type'} (f : B -> C) : term588 A B C f.
Proof. exact (EQ_MP (@lem6137965 A B C f) (@lem6137964 A B C f)). Qed.
Lemma lem6137967 {A B C : Type'} (f : B -> C) (g : A -> B) : term589 A B C f g.
Proof. exact (@lem6137966 A B C f g). Qed.
Lemma lem6137968 {A B C : Type'} (f : B -> C) (g : A -> B) : (term589 A B C f g) = (term590 A B C f g).
Proof. exact (eq_refl (term589 A B C f g)). Qed.
Lemma lem6137969 {A B C : Type'} (f : B -> C) (g : A -> B) : term590 A B C f g.
Proof. exact (EQ_MP (@lem6137968 A B C f g) (@lem6137967 A B C f g)). Qed.
Lemma lem6137970 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term591 A B C f g x.
Proof. exact (@lem6137969 A B C f g x). Qed.
Lemma lem6137971 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term591 A B C f g x) = ((@o A B C f g x) = (term110 A B C f g x)).
Proof. exact (eq_refl (term591 A B C f g x)). Qed.
Lemma lem6137994 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term110 A B C f g x).
Proof. exact (EQ_MP (@lem6137971 A B C f g x) (@lem6137970 A B C f g x)). Qed.
Lemma lem6137995 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term110 A B C f g x).
Proof. exact (@lem6137994 A B C f g x). Qed.
Lemma lem6137996 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) : (@o A B C g f a) = (term110 A B C g f a).
Proof. exact (@lem6137995 A B C g f a). Qed.
Lemma lem6137997 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6137998 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) : (term592 A B C op g f a) = (term593 A B C op g f a).
Proof. exact (MK_COMB (@lem6137997 C op) (@lem6137996 A B C g f a)). Qed.
Lemma lem6137999 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term33 A B C op f s g).
Proof. exact (eq_refl (term33 A B C op f s g)). Qed.
Lemma lem6138000 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term279 A B C a op f s g) = (term564 A B C a op f s g).
Proof. exact (MK_COMB (@lem6137998 A B C op g f a) (@lem6137999 A B C op f s g)). Qed.
Lemma lem6138001 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term595 A B C a op f s g) = (term595 A B C a op f s g).
Proof. exact (eq_refl (term595 A B C a op f s g)). Qed.
Lemma lem6138002 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term564 A B C a op f s g) = (term279 A B C a op f s g)) = ((term564 A B C a op f s g) = (term564 A B C a op f s g)).
Proof. exact (MK_COMB (@lem6138001 A B C a op f s g) (@lem6138000 A B C a op f s g)). Qed.
Lemma lem6138004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6138005 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem6138004 C x). Qed.
Lemma lem6138006 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term564 A B C a op f s g) = (term564 A B C a op f s g)) = True.
Proof. exact (@lem6138005 C (term564 A B C a op f s g)). Qed.
Lemma lem6138007 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term564 A B C a op f s g) = (term279 A B C a op f s g)) = True.
Proof. exact (TRANS (@lem6138002 A B C a op f s g) (@lem6138006 A B C a op f s g)). Qed.
Lemma lem6138008 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : True = ((term564 A B C a op f s g) = (term279 A B C a op f s g)).
Proof. exact (SYM (@lem6138007 A B C a op f s g)). Qed.
Lemma lem6138010 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : (term110 A B C g f a) = (@neutral C op)) : (term110 A B C g f a) = (@neutral C op).
Proof. exact (h1). Qed.
Lemma lem6138011 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term596 A B C op f s g) = (term596 A B C op f s g).
Proof. exact (eq_refl (term596 A B C op f s g)). Qed.
Lemma lem6138012 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : (term110 A B C g f a) = (@neutral C op)) : (term597 A B C op s g f a) = (term598 A B C f s g op).
Proof. exact (MK_COMB (@lem6138011 A B C op f s g) (@lem6138010 A B C g f a op h1)). Qed.
Lemma lem6138013 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term598 A B C f s g op) = ((term33 A B C op f s g) = (term599 A B C op f s g)).
Proof. exact (eq_refl (term598 A B C f s g op)). Qed.
Lemma lem6138014 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) : (term600 A B C op s g f a) = (term600 A B C op s g f a).
Proof. exact (eq_refl (term600 A B C op s g f a)). Qed.
Lemma lem6138015 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term597 A B C op s g f a) = (term598 A B C f s g op)) = ((term597 A B C op s g f a) = ((term33 A B C op f s g) = (term599 A B C op f s g))).
Proof. exact (MK_COMB (@lem6138014 A B C op s g f a) (@lem6138013 A B C op f s g)). Qed.
Lemma lem6138016 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term597 A B C op s g f a) = ((term33 A B C op f s g) = (term564 A B C a op f s g)).
Proof. exact (eq_refl (term597 A B C op s g f a)). Qed.
Lemma lem6138017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6138018 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term600 A B C op s g f a) = (term601 A B C a op f s g).
Proof. exact (MK_COMB (@lem6138017) (@lem6138016 A B C a op f s g)). Qed.
Lemma lem6138019 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term33 A B C op f s g) = (term599 A B C op f s g)) = ((term33 A B C op f s g) = (term599 A B C op f s g)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term599 A B C op f s g))). Qed.
Lemma lem6138020 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term597 A B C op s g f a) = ((term33 A B C op f s g) = (term599 A B C op f s g))) = (((term33 A B C op f s g) = (term564 A B C a op f s g)) = ((term33 A B C op f s g) = (term599 A B C op f s g))).
Proof. exact (MK_COMB (@lem6138018 A B C a op f s g) (@lem6138019 A B C op f s g)). Qed.
Lemma lem6138021 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term597 A B C op s g f a) = (term598 A B C f s g op)) = (((term33 A B C op f s g) = (term564 A B C a op f s g)) = ((term33 A B C op f s g) = (term599 A B C op f s g))).
Proof. exact (TRANS (@lem6138015 A B C a op f s g) (@lem6138020 A B C a op f s g)). Qed.
Lemma lem6138022 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : (term110 A B C g f a) = (@neutral C op)) : ((term33 A B C op f s g) = (term564 A B C a op f s g)) = ((term33 A B C op f s g) = (term599 A B C op f s g)).
Proof. exact (EQ_MP (@lem6138021 A B C a op f s g) (@lem6138012 A B C s g f a op h1)). Qed.
Lemma lem6138023 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : (term110 A B C g f a) = (@neutral C op)) : ((term33 A B C op f s g) = (term599 A B C op f s g)) = ((term33 A B C op f s g) = (term564 A B C a op f s g)).
Proof. exact (SYM (@lem6138022 A B C s g f a op h1)). Qed.
Lemma lem6138025 (p : Prop) : p = (term282 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6138026 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : ((term110 A B C g f a) = (@neutral C op)) = (term602 A B C g f a op).
Proof. exact (@lem6138025 ((term110 A B C g f a) = (@neutral C op))). Qed.
Lemma lem6138027 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term602 A B C g f a op) = ((term110 A B C g f a) = (@neutral C op)).
Proof. exact (SYM (@lem6138026 A B C g f a op)). Qed.
Lemma lem6138028 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term421 A B C g f a op) : term421 A B C g f a op.
Proof. exact (h1). Qed.
Lemma lem6138029 {C : Type'} : term603 C.
Proof. exact (@lem5715484 C). Qed.
Lemma lem6138030 {A : Type'} : term603 A.
Proof. exact (@lem5715484 A). Qed.
Lemma lem6138031 {B : Type'} : term603 B.
Proof. exact (@lem5715484 B). Qed.
Lemma lem6138036 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term604 A B C s g f a op) : term604 A B C s g f a op.
Proof. exact (h1). Qed.
Lemma lem6138037 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term605 A B C s g f a op.
Proof. exact (fun h0 : term604 A B C s g f a op => @lem6138036 A B C s g f a op h0). Qed.
Lemma lem6138038 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term605 A B C s g f a op) : term605 A B C s g f a op.
Proof. exact (h1). Qed.
Lemma lem6138039 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term604 A B C s g f a op) : term604 A B C s g f a op.
Proof. exact (h1). Qed.
Lemma lem6138040 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term604 A B C s g f a op) (h2 : term605 A B C s g f a op) : term604 A B C s g f a op.
Proof. exact (@lem6138038 A B C s g f a op h2 (@lem6138039 A B C s g f a op h1)). Qed.
Lemma lem6138041 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term604 A B C s g f a op) : term606 A B C s g f a op.
Proof. exact (fun h0 : term605 A B C s g f a op => @lem6138040 A B C s g f a op h1 h0). Qed.
Lemma lem6138042 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term605 A B C s g f a op) : term605 A B C s g f a op.
Proof. exact (h1). Qed.
Lemma lem6138043 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term604 A B C s g f a op) (h2 : term605 A B C s g f a op) : term604 A B C s g f a op.
Proof. exact (@lem6138041 A B C s g f a op h1 (@lem6138042 A B C s g f a op h2)). Qed.
Lemma lem6138044 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term605 A B C s g f a op) : term605 A B C s g f a op.
Proof. exact (fun h0 : term604 A B C s g f a op => @lem6138043 A B C s g f a op h0 h1). Qed.
Lemma lem6138045 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term607 A B C s g f a op.
Proof. exact (fun h0 : term605 A B C s g f a op => @lem6138044 A B C s g f a op h0). Qed.
Lemma lem6138048 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term605 A B C s g f a op.
Proof. exact (@lem6138045 A B C s g f a op (@lem6138037 A B C s g f a op)). Qed.
Lemma lem6138049 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term605 A B C s g f a op.
Proof. exact (@lem6138048 A B C s g f a op). Qed.
Lemma lem6138285 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6138286 {C : Type'} : (term608 C) = (term609 C).
Proof. exact (@lem6138285 (term603 C)). Qed.
Lemma lem6138341 {B : Type'} : (term610 B) = (term610 B).
Proof. exact (eq_refl (term610 B)). Qed.
Lemma lem6138342 {B C : Type'} : (term611 B C) = (term612 B C).
Proof. exact (MK_COMB (@lem6138341 B) (@lem6138286 C)). Qed.
Lemma lem6138345 {A : Type'} : (term610 A) = (term610 A).
Proof. exact (eq_refl (term610 A)). Qed.
Lemma lem6138346 {A B C : Type'} : (term613 A B C) = (term614 A B C).
Proof. exact (MK_COMB (@lem6138345 A) (@lem6138342 B C)). Qed.
Lemma lem6138349 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term615 A B C g f a op) = (term615 A B C g f a op).
Proof. exact (eq_refl (term615 A B C g f a op)). Qed.
Lemma lem6138350 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term616 A B C g f a op) = (term617 A B C g f a op).
Proof. exact (MK_COMB (@lem6138349 A B C g f a op) (@lem6138346 A B C)). Qed.
Lemma lem6138353 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term579 A B a f s) = (term579 A B a f s).
Proof. exact (eq_refl (term579 A B a f s)). Qed.
Lemma lem6138354 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term618 A B C s g f a op) = (term619 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138353 A B a f s) (@lem6138350 A B C g f a op)). Qed.
Lemma lem6138357 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term272 A B C a s g f op) = (term272 A B C a s g f op).
Proof. exact (eq_refl (term272 A B C a s g f op)). Qed.
Lemma lem6138358 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term620 A B C s g f a op) = (term621 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138357 A B C a s g f op) (@lem6138354 A B C s g f a op)). Qed.
Lemma lem6138361 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem6138362 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term622 A B C s g f a op) = (term623 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138361 A s) (@lem6138358 A B C s g f a op)). Qed.
Lemma lem6138365 {A : Type'} (a : A) (s : A -> Prop) : (term295 A a s) = (term295 A a s).
Proof. exact (eq_refl (term295 A a s)). Qed.
Lemma lem6138366 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term624 A B C s g f a op) = (term625 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138365 A a s) (@lem6138362 A B C s g f a op)). Qed.
Lemma lem6138369 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term298 A B C op s g f) = (term298 A B C op s g f).
Proof. exact (eq_refl (term298 A B C op s g f)). Qed.
Lemma lem6138370 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term626 A B C s g f a op) = (term627 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138369 A B C op s g f) (@lem6138366 A B C s g f a op)). Qed.
Lemma lem6138373 {C : Type'} (op : type1400 C) : (term301 C op) = (term301 C op).
Proof. exact (eq_refl (term301 C op)). Qed.
Lemma lem6138374 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term604 A B C s g f a op) = (term628 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138373 C op) (@lem6138370 A B C s g f a op)). Qed.
Lemma lem6138377 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term629 A B C g f a op) = (term630 A B C g f a op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6138374 A B C s g f a op)). Qed.
Lemma lem6138378 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6138379 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term631 A B C g f a op) = (term632 A B C g f a op).
Proof. exact (MK_COMB (@lem6138378 A) (@lem6138377 A B C g f a op)). Qed.
Lemma lem6138384 {A B C : Type'} (f : A -> B) (a : A) (op : type1400 C) : (term633 A B C f a op) = (term634 A B C f a op).
Proof. exact (fun_ext (fun g : B -> C => @lem6138379 A B C g f a op)). Qed.
Lemma lem6138385 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem6138386 {A B C : Type'} (f : A -> B) (a : A) (op : type1400 C) : (term635 A B C f a op) = (term636 A B C f a op).
Proof. exact (MK_COMB (@lem6138385 B C) (@lem6138384 A B C f a op)). Qed.
Lemma lem6138391 {A B C : Type'} (a : A) (op : type1400 C) : (term637 A B C a op) = (term638 A B C a op).
Proof. exact (fun_ext (fun f : A -> B => @lem6138386 A B C f a op)). Qed.
Lemma lem6138392 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6138393 {A B C : Type'} (a : A) (op : type1400 C) : (term639 A B C a op) = (term640 A B C a op).
Proof. exact (MK_COMB (@lem6138392 A B) (@lem6138391 A B C a op)). Qed.
Lemma lem6138398 {A B C : Type'} (op : type1400 C) : (term641 A B C op) = (term642 A B C op).
Proof. exact (fun_ext (fun a : A => @lem6138393 A B C a op)). Qed.
Lemma lem6138399 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138400 {A B C : Type'} (op : type1400 C) : (term643 A B C op) = (term644 A B C op).
Proof. exact (MK_COMB (@lem6138399 A) (@lem6138398 A B C op)). Qed.
Lemma lem6138405 {A B C : Type'} : (term645 A B C) = (term646 A B C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6138400 A B C op)). Qed.
Lemma lem6138406 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6138415 {A B C : Type'} : (term647 A B C) = (term648 A B C).
Proof. exact (MK_COMB (@lem6138406 C) (@lem6138405 A B C)). Qed.
Lemma lem6138416 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : ((term649 C a op b c) = (term649 C b op a c)) = ((term649 C a op b c) = (term649 C b op a c)).
Proof. exact (eq_refl ((term649 C a op b c) = (term649 C b op a c))). Qed.
Lemma lem6138417 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term650 C b op a) = (term650 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6138416 C b op a c)). Qed.
Lemma lem6138418 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138419 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term651 C b op a) = (term651 C b op a).
Proof. exact (MK_COMB (@lem6138418 C) (@lem6138417 C b op a)). Qed.
Lemma lem6138420 {C : Type'} (op : type1400 C) (a : C) : (term652 C op a) = (term652 C op a).
Proof. exact (fun_ext (fun b : C => @lem6138419 C b op a)). Qed.
Lemma lem6138421 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138422 {C : Type'} (op : type1400 C) (a : C) : (term653 C op a) = (term653 C op a).
Proof. exact (MK_COMB (@lem6138421 C) (@lem6138420 C op a)). Qed.
Lemma lem6138423 {C : Type'} (op : type1400 C) : (term654 C op) = (term654 C op).
Proof. exact (fun_ext (fun a : C => @lem6138422 C op a)). Qed.
Lemma lem6138424 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138425 {C : Type'} (op : type1400 C) : (term655 C op) = (term655 C op).
Proof. exact (MK_COMB (@lem6138424 C) (@lem6138423 C op)). Qed.
Lemma lem6138426 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : ((term656 C op a b c) = (term649 C a op b c)) = ((term656 C op a b c) = (term649 C a op b c)).
Proof. exact (eq_refl ((term656 C op a b c) = (term649 C a op b c))). Qed.
Lemma lem6138427 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term657 C a op b) = (term657 C a op b).
Proof. exact (fun_ext (fun c : C => @lem6138426 C a op b c)). Qed.
Lemma lem6138428 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138429 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term658 C a op b) = (term658 C a op b).
Proof. exact (MK_COMB (@lem6138428 C) (@lem6138427 C a op b)). Qed.
Lemma lem6138430 {C : Type'} (a : C) (op : type1400 C) : (term659 C a op) = (term659 C a op).
Proof. exact (fun_ext (fun b : C => @lem6138429 C a op b)). Qed.
Lemma lem6138431 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138432 {C : Type'} (a : C) (op : type1400 C) : (term660 C a op) = (term660 C a op).
Proof. exact (MK_COMB (@lem6138431 C) (@lem6138430 C a op)). Qed.
Lemma lem6138433 {C : Type'} (op : type1400 C) : (term661 C op) = (term661 C op).
Proof. exact (fun_ext (fun a : C => @lem6138432 C a op)). Qed.
Lemma lem6138434 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138435 {C : Type'} (op : type1400 C) : (term662 C op) = (term662 C op).
Proof. exact (MK_COMB (@lem6138434 C) (@lem6138433 C op)). Qed.
Lemma lem6138436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138437 {C : Type'} (op : type1400 C) : (term663 C op) = (term663 C op).
Proof. exact (MK_COMB (@lem6138436) (@lem6138435 C op)). Qed.
Lemma lem6138438 {C : Type'} (op : type1400 C) : (term664 C op) = (term664 C op).
Proof. exact (MK_COMB (@lem6138437 C op) (@lem6138425 C op)). Qed.
Lemma lem6138439 {C : Type'} (op : type1400 C) (b : C) (a : C) : ((op a b) = (op b a)) = ((op a b) = (op b a)).
Proof. exact (eq_refl ((op a b) = (op b a))). Qed.
Lemma lem6138440 {C : Type'} (op : type1400 C) (a : C) : (term665 C op a) = (term665 C op a).
Proof. exact (fun_ext (fun b : C => @lem6138439 C op b a)). Qed.
Lemma lem6138441 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138442 {C : Type'} (op : type1400 C) (a : C) : (term666 C op a) = (term666 C op a).
Proof. exact (MK_COMB (@lem6138441 C) (@lem6138440 C op a)). Qed.
Lemma lem6138443 {C : Type'} (op : type1400 C) : (term667 C op) = (term667 C op).
Proof. exact (fun_ext (fun a : C => @lem6138442 C op a)). Qed.
Lemma lem6138444 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138445 {C : Type'} (op : type1400 C) : (term668 C op) = (term668 C op).
Proof. exact (MK_COMB (@lem6138444 C) (@lem6138443 C op)). Qed.
Lemma lem6138446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138447 {C : Type'} (op : type1400 C) : (term669 C op) = (term669 C op).
Proof. exact (MK_COMB (@lem6138446) (@lem6138445 C op)). Qed.
Lemma lem6138448 {C : Type'} (op : type1400 C) : (term670 C op) = (term670 C op).
Proof. exact (MK_COMB (@lem6138447 C op) (@lem6138438 C op)). Qed.
Lemma lem6138449 {C : Type'} (op : type1400 C) (a : C) : ((term671 C a op) = a) = ((term671 C a op) = a).
Proof. exact (eq_refl ((term671 C a op) = a)). Qed.
Lemma lem6138450 {C : Type'} (op : type1400 C) : (term672 C op) = (term672 C op).
Proof. exact (fun_ext (fun a : C => @lem6138449 C op a)). Qed.
Lemma lem6138451 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138452 {C : Type'} (op : type1400 C) : (term673 C op) = (term673 C op).
Proof. exact (MK_COMB (@lem6138451 C) (@lem6138450 C op)). Qed.
Lemma lem6138453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138454 {C : Type'} (op : type1400 C) : (term674 C op) = (term674 C op).
Proof. exact (MK_COMB (@lem6138453) (@lem6138452 C op)). Qed.
Lemma lem6138455 {C : Type'} (op : type1400 C) : (term675 C op) = (term675 C op).
Proof. exact (MK_COMB (@lem6138454 C op) (@lem6138448 C op)). Qed.
Lemma lem6138456 {C : Type'} (op : type1400 C) (a : C) : ((term676 C op a) = a) = ((term676 C op a) = a).
Proof. exact (eq_refl ((term676 C op a) = a)). Qed.
Lemma lem6138457 {C : Type'} (op : type1400 C) : (term677 C op) = (term677 C op).
Proof. exact (fun_ext (fun a : C => @lem6138456 C op a)). Qed.
Lemma lem6138458 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6138459 {C : Type'} (op : type1400 C) : (term678 C op) = (term678 C op).
Proof. exact (MK_COMB (@lem6138458 C) (@lem6138457 C op)). Qed.
Lemma lem6138460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138461 {C : Type'} (op : type1400 C) : (term679 C op) = (term679 C op).
Proof. exact (MK_COMB (@lem6138460) (@lem6138459 C op)). Qed.
Lemma lem6138462 {C : Type'} (op : type1400 C) : (term680 C op) = (term680 C op).
Proof. exact (MK_COMB (@lem6138461 C op) (@lem6138455 C op)). Qed.
Lemma lem6138465 {C : Type'} (op : type1400 C) : (term301 C op) = (term301 C op).
Proof. exact (eq_refl (term301 C op)). Qed.
Lemma lem6138466 {C : Type'} (op : type1400 C) : (term681 C op) = (term681 C op).
Proof. exact (MK_COMB (@lem6138465 C op) (@lem6138462 C op)). Qed.
Lemma lem6138467 {C : Type'} : (term682 C) = (term682 C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6138466 C op)). Qed.
Lemma lem6138468 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6138469 {C : Type'} : (term603 C) = (term603 C).
Proof. exact (MK_COMB (@lem6138468 C) (@lem6138467 C)). Qed.
Lemma lem6138470 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6138471 {C : Type'} : (term609 C) = (term609 C).
Proof. exact (MK_COMB (@lem6138470) (@lem6138469 C)). Qed.
Lemma lem6138472 {B : Type'} (b : B) (op : type1400 B) (a : B) (c : B) : ((term649 B a op b c) = (term649 B b op a c)) = ((term649 B a op b c) = (term649 B b op a c)).
Proof. exact (eq_refl ((term649 B a op b c) = (term649 B b op a c))). Qed.
Lemma lem6138473 {B : Type'} (b : B) (op : type1400 B) (a : B) : (term650 B b op a) = (term650 B b op a).
Proof. exact (fun_ext (fun c : B => @lem6138472 B b op a c)). Qed.
Lemma lem6138474 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138475 {B : Type'} (b : B) (op : type1400 B) (a : B) : (term651 B b op a) = (term651 B b op a).
Proof. exact (MK_COMB (@lem6138474 B) (@lem6138473 B b op a)). Qed.
Lemma lem6138476 {B : Type'} (op : type1400 B) (a : B) : (term652 B op a) = (term652 B op a).
Proof. exact (fun_ext (fun b : B => @lem6138475 B b op a)). Qed.
Lemma lem6138477 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138478 {B : Type'} (op : type1400 B) (a : B) : (term653 B op a) = (term653 B op a).
Proof. exact (MK_COMB (@lem6138477 B) (@lem6138476 B op a)). Qed.
Lemma lem6138479 {B : Type'} (op : type1400 B) : (term654 B op) = (term654 B op).
Proof. exact (fun_ext (fun a : B => @lem6138478 B op a)). Qed.
Lemma lem6138480 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138481 {B : Type'} (op : type1400 B) : (term655 B op) = (term655 B op).
Proof. exact (MK_COMB (@lem6138480 B) (@lem6138479 B op)). Qed.
Lemma lem6138482 {B : Type'} (a : B) (op : type1400 B) (b : B) (c : B) : ((term656 B op a b c) = (term649 B a op b c)) = ((term656 B op a b c) = (term649 B a op b c)).
Proof. exact (eq_refl ((term656 B op a b c) = (term649 B a op b c))). Qed.
Lemma lem6138483 {B : Type'} (a : B) (op : type1400 B) (b : B) : (term657 B a op b) = (term657 B a op b).
Proof. exact (fun_ext (fun c : B => @lem6138482 B a op b c)). Qed.
Lemma lem6138484 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138485 {B : Type'} (a : B) (op : type1400 B) (b : B) : (term658 B a op b) = (term658 B a op b).
Proof. exact (MK_COMB (@lem6138484 B) (@lem6138483 B a op b)). Qed.
Lemma lem6138486 {B : Type'} (a : B) (op : type1400 B) : (term659 B a op) = (term659 B a op).
Proof. exact (fun_ext (fun b : B => @lem6138485 B a op b)). Qed.
Lemma lem6138487 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138488 {B : Type'} (a : B) (op : type1400 B) : (term660 B a op) = (term660 B a op).
Proof. exact (MK_COMB (@lem6138487 B) (@lem6138486 B a op)). Qed.
Lemma lem6138489 {B : Type'} (op : type1400 B) : (term661 B op) = (term661 B op).
Proof. exact (fun_ext (fun a : B => @lem6138488 B a op)). Qed.
Lemma lem6138490 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138491 {B : Type'} (op : type1400 B) : (term662 B op) = (term662 B op).
Proof. exact (MK_COMB (@lem6138490 B) (@lem6138489 B op)). Qed.
Lemma lem6138492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138493 {B : Type'} (op : type1400 B) : (term663 B op) = (term663 B op).
Proof. exact (MK_COMB (@lem6138492) (@lem6138491 B op)). Qed.
Lemma lem6138494 {B : Type'} (op : type1400 B) : (term664 B op) = (term664 B op).
Proof. exact (MK_COMB (@lem6138493 B op) (@lem6138481 B op)). Qed.
Lemma lem6138495 {B : Type'} (op : type1400 B) (b : B) (a : B) : ((op a b) = (op b a)) = ((op a b) = (op b a)).
Proof. exact (eq_refl ((op a b) = (op b a))). Qed.
Lemma lem6138496 {B : Type'} (op : type1400 B) (a : B) : (term665 B op a) = (term665 B op a).
Proof. exact (fun_ext (fun b : B => @lem6138495 B op b a)). Qed.
Lemma lem6138497 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138498 {B : Type'} (op : type1400 B) (a : B) : (term666 B op a) = (term666 B op a).
Proof. exact (MK_COMB (@lem6138497 B) (@lem6138496 B op a)). Qed.
Lemma lem6138499 {B : Type'} (op : type1400 B) : (term667 B op) = (term667 B op).
Proof. exact (fun_ext (fun a : B => @lem6138498 B op a)). Qed.
Lemma lem6138500 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138501 {B : Type'} (op : type1400 B) : (term668 B op) = (term668 B op).
Proof. exact (MK_COMB (@lem6138500 B) (@lem6138499 B op)). Qed.
Lemma lem6138502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138503 {B : Type'} (op : type1400 B) : (term669 B op) = (term669 B op).
Proof. exact (MK_COMB (@lem6138502) (@lem6138501 B op)). Qed.
Lemma lem6138504 {B : Type'} (op : type1400 B) : (term670 B op) = (term670 B op).
Proof. exact (MK_COMB (@lem6138503 B op) (@lem6138494 B op)). Qed.
Lemma lem6138505 {B : Type'} (op : type1400 B) (a : B) : ((term671 B a op) = a) = ((term671 B a op) = a).
Proof. exact (eq_refl ((term671 B a op) = a)). Qed.
Lemma lem6138506 {B : Type'} (op : type1400 B) : (term672 B op) = (term672 B op).
Proof. exact (fun_ext (fun a : B => @lem6138505 B op a)). Qed.
Lemma lem6138507 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138508 {B : Type'} (op : type1400 B) : (term673 B op) = (term673 B op).
Proof. exact (MK_COMB (@lem6138507 B) (@lem6138506 B op)). Qed.
Lemma lem6138509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138510 {B : Type'} (op : type1400 B) : (term674 B op) = (term674 B op).
Proof. exact (MK_COMB (@lem6138509) (@lem6138508 B op)). Qed.
Lemma lem6138511 {B : Type'} (op : type1400 B) : (term675 B op) = (term675 B op).
Proof. exact (MK_COMB (@lem6138510 B op) (@lem6138504 B op)). Qed.
Lemma lem6138512 {B : Type'} (op : type1400 B) (a : B) : ((term676 B op a) = a) = ((term676 B op a) = a).
Proof. exact (eq_refl ((term676 B op a) = a)). Qed.
Lemma lem6138513 {B : Type'} (op : type1400 B) : (term677 B op) = (term677 B op).
Proof. exact (fun_ext (fun a : B => @lem6138512 B op a)). Qed.
Lemma lem6138514 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6138515 {B : Type'} (op : type1400 B) : (term678 B op) = (term678 B op).
Proof. exact (MK_COMB (@lem6138514 B) (@lem6138513 B op)). Qed.
Lemma lem6138516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138517 {B : Type'} (op : type1400 B) : (term679 B op) = (term679 B op).
Proof. exact (MK_COMB (@lem6138516) (@lem6138515 B op)). Qed.
Lemma lem6138518 {B : Type'} (op : type1400 B) : (term680 B op) = (term680 B op).
Proof. exact (MK_COMB (@lem6138517 B op) (@lem6138511 B op)). Qed.
Lemma lem6138521 {B : Type'} (op : type1400 B) : (term301 B op) = (term301 B op).
Proof. exact (eq_refl (term301 B op)). Qed.
Lemma lem6138522 {B : Type'} (op : type1400 B) : (term681 B op) = (term681 B op).
Proof. exact (MK_COMB (@lem6138521 B op) (@lem6138518 B op)). Qed.
Lemma lem6138523 {B : Type'} : (term682 B) = (term682 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6138522 B op)). Qed.
Lemma lem6138524 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6138525 {B : Type'} : (term603 B) = (term603 B).
Proof. exact (MK_COMB (@lem6138524 B) (@lem6138523 B)). Qed.
Lemma lem6138526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6138527 {B : Type'} : (term610 B) = (term610 B).
Proof. exact (MK_COMB (@lem6138526) (@lem6138525 B)). Qed.
Lemma lem6138528 {B C : Type'} : (term612 B C) = (term612 B C).
Proof. exact (MK_COMB (@lem6138527 B) (@lem6138471 C)). Qed.
Lemma lem6138529 {A : Type'} (b : A) (op : type1400 A) (a : A) (c : A) : ((term649 A a op b c) = (term649 A b op a c)) = ((term649 A a op b c) = (term649 A b op a c)).
Proof. exact (eq_refl ((term649 A a op b c) = (term649 A b op a c))). Qed.
Lemma lem6138530 {A : Type'} (b : A) (op : type1400 A) (a : A) : (term650 A b op a) = (term650 A b op a).
Proof. exact (fun_ext (fun c : A => @lem6138529 A b op a c)). Qed.
Lemma lem6138531 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138532 {A : Type'} (b : A) (op : type1400 A) (a : A) : (term651 A b op a) = (term651 A b op a).
Proof. exact (MK_COMB (@lem6138531 A) (@lem6138530 A b op a)). Qed.
Lemma lem6138533 {A : Type'} (op : type1400 A) (a : A) : (term652 A op a) = (term652 A op a).
Proof. exact (fun_ext (fun b : A => @lem6138532 A b op a)). Qed.
Lemma lem6138534 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138535 {A : Type'} (op : type1400 A) (a : A) : (term653 A op a) = (term653 A op a).
Proof. exact (MK_COMB (@lem6138534 A) (@lem6138533 A op a)). Qed.
Lemma lem6138536 {A : Type'} (op : type1400 A) : (term654 A op) = (term654 A op).
Proof. exact (fun_ext (fun a : A => @lem6138535 A op a)). Qed.
Lemma lem6138537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138538 {A : Type'} (op : type1400 A) : (term655 A op) = (term655 A op).
Proof. exact (MK_COMB (@lem6138537 A) (@lem6138536 A op)). Qed.
Lemma lem6138539 {A : Type'} (a : A) (op : type1400 A) (b : A) (c : A) : ((term656 A op a b c) = (term649 A a op b c)) = ((term656 A op a b c) = (term649 A a op b c)).
Proof. exact (eq_refl ((term656 A op a b c) = (term649 A a op b c))). Qed.
Lemma lem6138540 {A : Type'} (a : A) (op : type1400 A) (b : A) : (term657 A a op b) = (term657 A a op b).
Proof. exact (fun_ext (fun c : A => @lem6138539 A a op b c)). Qed.
Lemma lem6138541 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138542 {A : Type'} (a : A) (op : type1400 A) (b : A) : (term658 A a op b) = (term658 A a op b).
Proof. exact (MK_COMB (@lem6138541 A) (@lem6138540 A a op b)). Qed.
Lemma lem6138543 {A : Type'} (a : A) (op : type1400 A) : (term659 A a op) = (term659 A a op).
Proof. exact (fun_ext (fun b : A => @lem6138542 A a op b)). Qed.
Lemma lem6138544 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138545 {A : Type'} (a : A) (op : type1400 A) : (term660 A a op) = (term660 A a op).
Proof. exact (MK_COMB (@lem6138544 A) (@lem6138543 A a op)). Qed.
Lemma lem6138546 {A : Type'} (op : type1400 A) : (term661 A op) = (term661 A op).
Proof. exact (fun_ext (fun a : A => @lem6138545 A a op)). Qed.
Lemma lem6138547 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138548 {A : Type'} (op : type1400 A) : (term662 A op) = (term662 A op).
Proof. exact (MK_COMB (@lem6138547 A) (@lem6138546 A op)). Qed.
Lemma lem6138549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138550 {A : Type'} (op : type1400 A) : (term663 A op) = (term663 A op).
Proof. exact (MK_COMB (@lem6138549) (@lem6138548 A op)). Qed.
Lemma lem6138551 {A : Type'} (op : type1400 A) : (term664 A op) = (term664 A op).
Proof. exact (MK_COMB (@lem6138550 A op) (@lem6138538 A op)). Qed.
Lemma lem6138552 {A : Type'} (op : type1400 A) (b : A) (a : A) : ((op a b) = (op b a)) = ((op a b) = (op b a)).
Proof. exact (eq_refl ((op a b) = (op b a))). Qed.
Lemma lem6138553 {A : Type'} (op : type1400 A) (a : A) : (term665 A op a) = (term665 A op a).
Proof. exact (fun_ext (fun b : A => @lem6138552 A op b a)). Qed.
Lemma lem6138554 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138555 {A : Type'} (op : type1400 A) (a : A) : (term666 A op a) = (term666 A op a).
Proof. exact (MK_COMB (@lem6138554 A) (@lem6138553 A op a)). Qed.
Lemma lem6138556 {A : Type'} (op : type1400 A) : (term667 A op) = (term667 A op).
Proof. exact (fun_ext (fun a : A => @lem6138555 A op a)). Qed.
Lemma lem6138557 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138558 {A : Type'} (op : type1400 A) : (term668 A op) = (term668 A op).
Proof. exact (MK_COMB (@lem6138557 A) (@lem6138556 A op)). Qed.
Lemma lem6138559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138560 {A : Type'} (op : type1400 A) : (term669 A op) = (term669 A op).
Proof. exact (MK_COMB (@lem6138559) (@lem6138558 A op)). Qed.
Lemma lem6138561 {A : Type'} (op : type1400 A) : (term670 A op) = (term670 A op).
Proof. exact (MK_COMB (@lem6138560 A op) (@lem6138551 A op)). Qed.
Lemma lem6138562 {A : Type'} (op : type1400 A) (a : A) : ((term671 A a op) = a) = ((term671 A a op) = a).
Proof. exact (eq_refl ((term671 A a op) = a)). Qed.
Lemma lem6138563 {A : Type'} (op : type1400 A) : (term672 A op) = (term672 A op).
Proof. exact (fun_ext (fun a : A => @lem6138562 A op a)). Qed.
Lemma lem6138564 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138565 {A : Type'} (op : type1400 A) : (term673 A op) = (term673 A op).
Proof. exact (MK_COMB (@lem6138564 A) (@lem6138563 A op)). Qed.
Lemma lem6138566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138567 {A : Type'} (op : type1400 A) : (term674 A op) = (term674 A op).
Proof. exact (MK_COMB (@lem6138566) (@lem6138565 A op)). Qed.
Lemma lem6138568 {A : Type'} (op : type1400 A) : (term675 A op) = (term675 A op).
Proof. exact (MK_COMB (@lem6138567 A op) (@lem6138561 A op)). Qed.
Lemma lem6138569 {A : Type'} (op : type1400 A) (a : A) : ((term676 A op a) = a) = ((term676 A op a) = a).
Proof. exact (eq_refl ((term676 A op a) = a)). Qed.
Lemma lem6138570 {A : Type'} (op : type1400 A) : (term677 A op) = (term677 A op).
Proof. exact (fun_ext (fun a : A => @lem6138569 A op a)). Qed.
Lemma lem6138571 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138572 {A : Type'} (op : type1400 A) : (term678 A op) = (term678 A op).
Proof. exact (MK_COMB (@lem6138571 A) (@lem6138570 A op)). Qed.
Lemma lem6138573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6138574 {A : Type'} (op : type1400 A) : (term679 A op) = (term679 A op).
Proof. exact (MK_COMB (@lem6138573) (@lem6138572 A op)). Qed.
Lemma lem6138575 {A : Type'} (op : type1400 A) : (term680 A op) = (term680 A op).
Proof. exact (MK_COMB (@lem6138574 A op) (@lem6138568 A op)). Qed.
Lemma lem6138578 {A : Type'} (op : type1400 A) : (term301 A op) = (term301 A op).
Proof. exact (eq_refl (term301 A op)). Qed.
Lemma lem6138579 {A : Type'} (op : type1400 A) : (term681 A op) = (term681 A op).
Proof. exact (MK_COMB (@lem6138578 A op) (@lem6138575 A op)). Qed.
Lemma lem6138580 {A : Type'} : (term682 A) = (term682 A).
Proof. exact (fun_ext (fun op : type1400 A => @lem6138579 A op)). Qed.
Lemma lem6138581 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6138582 {A : Type'} : (term603 A) = (term603 A).
Proof. exact (MK_COMB (@lem6138581 A) (@lem6138580 A)). Qed.
Lemma lem6138583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6138584 {A : Type'} : (term610 A) = (term610 A).
Proof. exact (MK_COMB (@lem6138583) (@lem6138582 A)). Qed.
Lemma lem6138585 {A B C : Type'} : (term614 A B C) = (term614 A B C).
Proof. exact (MK_COMB (@lem6138584 A) (@lem6138528 B C)). Qed.
Lemma lem6138590 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term615 A B C g f a op) = (term615 A B C g f a op).
Proof. exact (eq_refl (term615 A B C g f a op)). Qed.
Lemma lem6138591 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term617 A B C g f a op) = (term617 A B C g f a op).
Proof. exact (MK_COMB (@lem6138590 A B C g f a op) (@lem6138585 A B C)). Qed.
Lemma lem6138596 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) : (term683 A B a f x s) = (term683 A B a f x s).
Proof. exact (eq_refl (term683 A B a f x s)). Qed.
Lemma lem6138597 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term684 A B a f s) = (term684 A B a f s).
Proof. exact (fun_ext (fun x : A => @lem6138596 A B a f x s)). Qed.
Lemma lem6138598 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6138599 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term559 A B a f s) = (term559 A B a f s).
Proof. exact (MK_COMB (@lem6138598 A) (@lem6138597 A B a f s)). Qed.
Lemma lem6138600 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6138601 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term579 A B a f s) = (term579 A B a f s).
Proof. exact (MK_COMB (@lem6138600) (@lem6138599 A B a f s)). Qed.
Lemma lem6138602 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term619 A B C s g f a op) = (term619 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138601 A B a f s) (@lem6138591 A B C g f a op)). Qed.
Lemma lem6138629 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term266 A B C a s x' g f y op) = (term266 A B C a s x' g f y op).
Proof. exact (eq_refl (term266 A B C a s x' g f y op)). Qed.
Lemma lem6138630 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term267 A B C a s x' g f op) = (term267 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6138629 A B C a s x' g f y op)). Qed.
Lemma lem6138631 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138632 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term268 A B C a s x' g f op) = (term268 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6138631 A) (@lem6138630 A B C a s x' g f op)). Qed.
Lemma lem6138633 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term269 A B C a s g f op) = (term269 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6138632 A B C a s x' g f op)). Qed.
Lemma lem6138634 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138635 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term270 A B C a s g f op) = (term270 A B C a s g f op).
Proof. exact (MK_COMB (@lem6138634 A) (@lem6138633 A B C a s g f op)). Qed.
Lemma lem6138636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6138637 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term272 A B C a s g f op) = (term272 A B C a s g f op).
Proof. exact (MK_COMB (@lem6138636) (@lem6138635 A B C a s g f op)). Qed.
Lemma lem6138638 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term621 A B C s g f a op) = (term621 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138637 A B C a s g f op) (@lem6138602 A B C s g f a op)). Qed.
Lemma lem6138641 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem6138642 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term623 A B C s g f a op) = (term623 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138641 A s) (@lem6138638 A B C s g f a op)). Qed.
Lemma lem6138647 {A : Type'} (a : A) (s : A -> Prop) : (term295 A a s) = (term295 A a s).
Proof. exact (eq_refl (term295 A a s)). Qed.
Lemma lem6138648 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term625 A B C s g f a op) = (term625 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138647 A a s) (@lem6138642 A B C s g f a op)). Qed.
Lemma lem6138649 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6138668 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term163 A B C s x g f y op) = (term163 A B C s x g f y op).
Proof. exact (eq_refl (term163 A B C s x g f y op)). Qed.
Lemma lem6138669 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term165 A B C s x g f op) = (term165 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6138668 A B C s x g f y op)). Qed.
Lemma lem6138670 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138671 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term167 A B C s x g f op) = (term167 A B C s x g f op).
Proof. exact (MK_COMB (@lem6138670 A) (@lem6138669 A B C s x g f op)). Qed.
Lemma lem6138672 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term169 A B C s g f op) = (term169 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6138671 A B C s x g f op)). Qed.
Lemma lem6138673 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138674 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term170 A B C s g f op) = (term170 A B C s g f op).
Proof. exact (MK_COMB (@lem6138673 A) (@lem6138672 A B C s g f op)). Qed.
Lemma lem6138675 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6138676 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term323 A B C s g f op) = (term323 A B C s g f op).
Proof. exact (MK_COMB (@lem6138675) (@lem6138674 A B C s g f op)). Qed.
Lemma lem6138677 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term175 A B C op s g f).
Proof. exact (MK_COMB (@lem6138676 A B C s g f op) (@lem6138649 A B C op s g f)). Qed.
Lemma lem6138678 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6138679 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term298 A B C op s g f) = (term298 A B C op s g f).
Proof. exact (MK_COMB (@lem6138678) (@lem6138677 A B C op s g f)). Qed.
Lemma lem6138680 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term627 A B C s g f a op) = (term627 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138679 A B C op s g f) (@lem6138648 A B C s g f a op)). Qed.
Lemma lem6138683 {C : Type'} (op : type1400 C) : (term301 C op) = (term301 C op).
Proof. exact (eq_refl (term301 C op)). Qed.
Lemma lem6138684 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term628 A B C s g f a op) = (term628 A B C s g f a op).
Proof. exact (MK_COMB (@lem6138683 C op) (@lem6138680 A B C s g f a op)). Qed.
Lemma lem6138685 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term630 A B C g f a op) = (term630 A B C g f a op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6138684 A B C s g f a op)). Qed.
Lemma lem6138686 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6138687 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term632 A B C g f a op) = (term632 A B C g f a op).
Proof. exact (MK_COMB (@lem6138686 A) (@lem6138685 A B C g f a op)). Qed.
Lemma lem6138688 {A B C : Type'} (f : A -> B) (a : A) (op : type1400 C) : (term634 A B C f a op) = (term634 A B C f a op).
Proof. exact (fun_ext (fun g : B -> C => @lem6138687 A B C g f a op)). Qed.
Lemma lem6138689 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem6138690 {A B C : Type'} (f : A -> B) (a : A) (op : type1400 C) : (term636 A B C f a op) = (term636 A B C f a op).
Proof. exact (MK_COMB (@lem6138689 B C) (@lem6138688 A B C f a op)). Qed.
Lemma lem6138691 {A B C : Type'} (a : A) (op : type1400 C) : (term638 A B C a op) = (term638 A B C a op).
Proof. exact (fun_ext (fun f : A -> B => @lem6138690 A B C f a op)). Qed.
Lemma lem6138692 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6138693 {A B C : Type'} (a : A) (op : type1400 C) : (term640 A B C a op) = (term640 A B C a op).
Proof. exact (MK_COMB (@lem6138692 A B) (@lem6138691 A B C a op)). Qed.
Lemma lem6138694 {A B C : Type'} (op : type1400 C) : (term642 A B C op) = (term642 A B C op).
Proof. exact (fun_ext (fun a : A => @lem6138693 A B C a op)). Qed.
Lemma lem6138695 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6138696 {A B C : Type'} (op : type1400 C) : (term644 A B C op) = (term644 A B C op).
Proof. exact (MK_COMB (@lem6138695 A) (@lem6138694 A B C op)). Qed.
Lemma lem6138697 {A B C : Type'} : (term646 A B C) = (term646 A B C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6138696 A B C op)). Qed.
Lemma lem6138698 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6138699 {A B C : Type'} : (term648 A B C) = (term648 A B C).
Proof. exact (MK_COMB (@lem6138698 C) (@lem6138697 A B C)). Qed.
Lemma lem6139032 {A B C : Type'} : (term647 A B C) = (term648 A B C).
Proof. exact (TRANS (@lem6138415 A B C) (@lem6138699 A B C)). Qed.
Lemma lem6139033 {A B C : Type'} : (term648 A B C) = (term647 A B C).
Proof. exact (SYM (@lem6139032 A B C)). Qed.
Lemma lem6139035 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term175 A B C op s g f.
Proof. exact (h1). Qed.
Lemma lem6139038 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term270 A B C a s g f op.
Proof. exact (h1). Qed.
Lemma lem6139039 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) (h1 : term559 A B a f s) : term559 A B a f s.
Proof. exact (h1). Qed.
Lemma lem6139068 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term324 A B C s x g f y op) = (term325 A B C s x g f y op).
Proof. exact (@lem17362 (term152 A B s x f y) ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6139069 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6139070 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term328 A B C s x g f op) = (term329 A B C s x g f op).
Proof. exact (@lem6139069 A (term165 A B C s x g f op)). Qed.
Lemma lem6139071 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term330 A B C s x g f op y) = (term163 A B C s x g f y op).
Proof. exact (eq_refl (term330 A B C s x g f op y)). Qed.
Lemma lem6139072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6139073 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term331 A B C s x g f op y) = (term324 A B C s x g f y op).
Proof. exact (MK_COMB (@lem6139072) (@lem6139071 A B C s x g f y op)). Qed.
Lemma lem6139074 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term331 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (TRANS (@lem6139073 A B C s x g f y op) (@lem6139068 A B C s x g f y op)). Qed.
Lemma lem6139075 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term332 A B C s x g f op) = (term333 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6139074 A B C s x g f y op)). Qed.
Lemma lem6139076 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6139077 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term329 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (MK_COMB (@lem6139076 A) (@lem6139075 A B C s x g f op)). Qed.
Lemma lem6139078 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term328 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (TRANS (@lem6139070 A B C s x g f op) (@lem6139077 A B C s x g f op)). Qed.
Lemma lem6139079 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6139080 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term335 A B C s g f op) = (term336 A B C s g f op).
Proof. exact (@lem6139079 A (term169 A B C s g f op)). Qed.
Lemma lem6139081 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term337 A B C s g f op x) = (term167 A B C s x g f op).
Proof. exact (eq_refl (term337 A B C s g f op x)). Qed.
Lemma lem6139082 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6139083 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term338 A B C s g f op x) = (term328 A B C s x g f op).
Proof. exact (MK_COMB (@lem6139082) (@lem6139081 A B C s x g f op)). Qed.
Lemma lem6139084 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term338 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (TRANS (@lem6139083 A B C s x g f op) (@lem6139078 A B C s x g f op)). Qed.
Lemma lem6139085 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term339 A B C s g f op) = (term340 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6139084 A B C s x g f op)). Qed.
Lemma lem6139086 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6139087 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term336 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (MK_COMB (@lem6139086 A) (@lem6139085 A B C s g f op)). Qed.
Lemma lem6139088 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term335 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (TRANS (@lem6139080 A B C s g f op) (@lem6139087 A B C s g f op)). Qed.
Lemma lem6139089 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6139090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139091 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term342 A B C s g f op) = (term343 A B C s g f op).
Proof. exact (MK_COMB (@lem6139090) (@lem6139088 A B C s g f op)). Qed.
Lemma lem6139092 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term344 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (MK_COMB (@lem6139091 A B C s g f op) (@lem6139089 A B C op s g f)). Qed.
Lemma lem6139093 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term344 A B C op s g f).
Proof. exact (@lem17265 (term170 A B C s g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6139094 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (TRANS (@lem6139093 A B C op s g f) (@lem6139092 A B C op s g f)). Qed.
Lemma lem6139149 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6139150 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem6139149 A P Q). Qed.
Lemma lem6139151 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term348 A B C op s g f) = (term349 A B C op s g f).
Proof. exact (@lem6139150 A (term340 A B C s g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6139152 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term350 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (eq_refl (term350 A B C s g f op x)). Qed.
Lemma lem6139153 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term351 A B C s g f op) = (term340 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6139152 A B C s x g f op)). Qed.
Lemma lem6139154 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6139155 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term352 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (MK_COMB (@lem6139154 A) (@lem6139153 A B C s g f op)). Qed.
Lemma lem6139156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139157 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term353 A B C s g f op) = (term343 A B C s g f op).
Proof. exact (MK_COMB (@lem6139156) (@lem6139155 A B C s g f op)). Qed.
Lemma lem6139158 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6139159 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term348 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (MK_COMB (@lem6139157 A B C s g f op) (@lem6139158 A B C op s g f)). Qed.
Lemma lem6139160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6139161 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term354 A B C op s g f) = (term355 A B C op s g f).
Proof. exact (MK_COMB (@lem6139160) (@lem6139159 A B C op s g f)). Qed.
Lemma lem6139162 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term350 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (eq_refl (term350 A B C s g f op x)). Qed.
Lemma lem6139163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139164 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term356 A B C s g f op x) = (term357 A B C s x g f op).
Proof. exact (MK_COMB (@lem6139163) (@lem6139162 A B C s x g f op)). Qed.
Lemma lem6139165 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6139166 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term358 A B C x op s g f) = (term359 A B C x op s g f).
Proof. exact (MK_COMB (@lem6139164 A B C s x g f op) (@lem6139165 A B C op s g f)). Qed.
Lemma lem6139167 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term360 A B C op s g f) = (term361 A B C op s g f).
Proof. exact (fun_ext (fun x : A => @lem6139166 A B C x op s g f)). Qed.
Lemma lem6139168 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6139169 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term349 A B C op s g f) = (term362 A B C op s g f).
Proof. exact (MK_COMB (@lem6139168 A) (@lem6139167 A B C op s g f)). Qed.
Lemma lem6139170 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term348 A B C op s g f) = (term349 A B C op s g f)) = ((term345 A B C op s g f) = (term362 A B C op s g f)).
Proof. exact (MK_COMB (@lem6139161 A B C op s g f) (@lem6139169 A B C op s g f)). Qed.
Lemma lem6139171 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term345 A B C op s g f) = (term362 A B C op s g f).
Proof. exact (EQ_MP (@lem6139170 A B C op s g f) (@lem6139151 A B C op s g f)). Qed.
Lemma lem6139173 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6139174 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem6139173 A P Q). Qed.
Lemma lem6139175 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term363 A B C x op s g f) = (term364 A B C x op s g f).
Proof. exact (@lem6139174 A (term333 A B C s x g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6139176 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term365 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (eq_refl (term365 A B C s x g f op y)). Qed.
Lemma lem6139177 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term366 A B C s x g f op) = (term333 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6139176 A B C s x g f y op)). Qed.
Lemma lem6139178 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6139179 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term367 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (MK_COMB (@lem6139178 A) (@lem6139177 A B C s x g f op)). Qed.
Lemma lem6139180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139181 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term368 A B C s x g f op) = (term357 A B C s x g f op).
Proof. exact (MK_COMB (@lem6139180) (@lem6139179 A B C s x g f op)). Qed.
Lemma lem6139182 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6139183 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term363 A B C x op s g f) = (term359 A B C x op s g f).
Proof. exact (MK_COMB (@lem6139181 A B C s x g f op) (@lem6139182 A B C op s g f)). Qed.
Lemma lem6139184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6139185 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term369 A B C x op s g f) = (term370 A B C x op s g f).
Proof. exact (MK_COMB (@lem6139184) (@lem6139183 A B C x op s g f)). Qed.
Lemma lem6139186 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term365 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (eq_refl (term365 A B C s x g f op y)). Qed.
Lemma lem6139187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139188 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term371 A B C s x g f op y) = (term372 A B C s x g f y op).
Proof. exact (MK_COMB (@lem6139187) (@lem6139186 A B C s x g f y op)). Qed.
Lemma lem6139189 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6139190 {A B C : Type'} (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term373 A B C x y op s g f) = (term374 A B C x y op s g f).
Proof. exact (MK_COMB (@lem6139188 A B C s x g f y op) (@lem6139189 A B C op s g f)). Qed.
Lemma lem6139191 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term375 A B C x op s g f) = (term376 A B C x op s g f).
Proof. exact (fun_ext (fun y : A => @lem6139190 A B C x y op s g f)). Qed.
Lemma lem6139192 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6139193 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term364 A B C x op s g f) = (term377 A B C x op s g f).
Proof. exact (MK_COMB (@lem6139192 A) (@lem6139191 A B C x op s g f)). Qed.
Lemma lem6139194 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term363 A B C x op s g f) = (term364 A B C x op s g f)) = ((term359 A B C x op s g f) = (term377 A B C x op s g f)).
Proof. exact (MK_COMB (@lem6139185 A B C x op s g f) (@lem6139193 A B C x op s g f)). Qed.
Lemma lem6139195 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term359 A B C x op s g f) = (term377 A B C x op s g f).
Proof. exact (EQ_MP (@lem6139194 A B C x op s g f) (@lem6139175 A B C x op s g f)). Qed.
Lemma lem6139196 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term361 A B C op s g f) = (term378 A B C op s g f).
Proof. exact (fun_ext (fun x : A => @lem6139195 A B C x op s g f)). Qed.
Lemma lem6139197 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6139198 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term362 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (MK_COMB (@lem6139197 A) (@lem6139196 A B C op s g f)). Qed.
Lemma lem6139200 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term345 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (TRANS (@lem6139171 A B C op s g f) (@lem6139198 A B C op s g f)). Qed.
Lemma lem6139201 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (TRANS (@lem6139094 A B C op s g f) (@lem6139200 A B C op s g f)). Qed.
Lemma lem6139202 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term379 A B C op s g f.
Proof. exact (EQ_MP (@lem6139201 A B C op s g f) (@lem6139035 A B C op s g f h1)). Qed.
Lemma lem6139208 {A : Type'} (a : A) (s : A -> Prop) (h1 : term180 A a s) : term180 A a s.
Proof. exact (h1). Qed.
Lemma lem6139221 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term380 A a x' s) = (term381 A a x' s).
Proof. exact (@lem17160 (x' = a) (@IN A x' s)). Qed.
Lemma lem6139228 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term380 A a y s) = (term381 A a y s).
Proof. exact (@lem17160 (y = a) (@IN A y s)). Qed.
Lemma lem6139231 {A : Type'} (x' : A) (y : A) : (term382 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem6139232 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term383 A B x' f y) = (term383 A B x' f y).
Proof. exact (eq_refl (term383 A B x' f y)). Qed.
Lemma lem6139233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139234 {A : Type'} (x' : A) (y : A) : (term384 A x' y) = (term385 A x' y).
Proof. exact (MK_COMB (@lem6139233) (@lem6139231 A x' y)). Qed.
Lemma lem6139235 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term386 A B x' f y) = (term387 A B x' f y).
Proof. exact (MK_COMB (@lem6139234 A x' y) (@lem6139232 A B x' f y)). Qed.
Lemma lem6139236 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term388 A B x' f y) = (term386 A B x' f y).
Proof. exact (@lem17045 (term389 A x' y) ((f x') = (f y))). Qed.
Lemma lem6139237 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term388 A B x' f y) = (term387 A B x' f y).
Proof. exact (TRANS (@lem6139236 A B x' f y) (@lem6139235 A B x' f y)). Qed.
Lemma lem6139238 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139239 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term390 A a y s) = (term391 A a y s).
Proof. exact (MK_COMB (@lem6139238) (@lem6139228 A a y s)). Qed.
Lemma lem6139240 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term392 A B a s x' f y) = (term393 A B a s x' f y).
Proof. exact (MK_COMB (@lem6139239 A a y s) (@lem6139237 A B x' f y)). Qed.
Lemma lem6139241 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term394 A B a s x' f y) = (term392 A B a s x' f y).
Proof. exact (@lem17045 (term20 A a y s) (term118 A B x' f y)). Qed.
Lemma lem6139242 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term394 A B a s x' f y) = (term393 A B a s x' f y).
Proof. exact (TRANS (@lem6139241 A B a s x' f y) (@lem6139240 A B a s x' f y)). Qed.
Lemma lem6139243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139244 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term390 A a x' s) = (term391 A a x' s).
Proof. exact (MK_COMB (@lem6139243) (@lem6139221 A a x' s)). Qed.
Lemma lem6139245 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term395 A B a s x' f y) = (term396 A B a s x' f y).
Proof. exact (MK_COMB (@lem6139244 A a x' s) (@lem6139242 A B a s x' f y)). Qed.
Lemma lem6139246 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term397 A B a s x' f y) = (term395 A B a s x' f y).
Proof. exact (@lem17045 (term20 A a x' s) (term262 A B a s x' f y)). Qed.
Lemma lem6139247 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term397 A B a s x' f y) = (term396 A B a s x' f y).
Proof. exact (TRANS (@lem6139246 A B a s x' f y) (@lem6139245 A B a s x' f y)). Qed.
Lemma lem6139248 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term110 A B C g f y) = (@neutral C op)) = ((term110 A B C g f y) = (@neutral C op)).
Proof. exact (eq_refl ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6139249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139250 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term398 A B a s x' f y) = (term399 A B a s x' f y).
Proof. exact (MK_COMB (@lem6139249) (@lem6139247 A B a s x' f y)). Qed.
Lemma lem6139251 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term400 A B C a s x' g f y op) = (term401 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6139250 A B a s x' f y) (@lem6139248 A B C g f y op)). Qed.
Lemma lem6139252 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term266 A B C a s x' g f y op) = (term400 A B C a s x' g f y op).
Proof. exact (@lem17265 (term263 A B a s x' f y) ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6139253 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term266 A B C a s x' g f y op) = (term401 A B C a s x' g f y op).
Proof. exact (TRANS (@lem6139252 A B C a s x' g f y op) (@lem6139251 A B C a s x' g f y op)). Qed.
Lemma lem6139254 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term267 A B C a s x' g f op) = (term402 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6139253 A B C a s x' g f y op)). Qed.
Lemma lem6139255 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6139256 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term268 A B C a s x' g f op) = (term403 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6139255 A) (@lem6139254 A B C a s x' g f op)). Qed.
Lemma lem6139257 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term269 A B C a s g f op) = (term404 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6139256 A B C a s x' g f op)). Qed.
Lemma lem6139258 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6139315 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term270 A B C a s g f op) = (term405 A B C a s g f op).
Proof. exact (MK_COMB (@lem6139258 A) (@lem6139257 A B C a s g f op)). Qed.
Lemma lem6139316 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term405 A B C a s g f op.
Proof. exact (EQ_MP (@lem6139315 A B C a s g f op) (@lem6139038 A B C a s g f op h1)). Qed.
Lemma lem6139321 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) : (term683 A B a f x s) = (term683 A B a f x s).
Proof. exact (eq_refl (term683 A B a f x s)). Qed.
Lemma lem6139322 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term684 A B a f s) = (term684 A B a f s).
Proof. exact (fun_ext (fun x : A => @lem6139321 A B a f x s)). Qed.
Lemma lem6139323 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6139376 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term559 A B a f s) = (term559 A B a f s).
Proof. exact (MK_COMB (@lem6139323 A) (@lem6139322 A B a f s)). Qed.
Lemma lem6139377 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) (h1 : term559 A B a f s) : term559 A B a f s.
Proof. exact (EQ_MP (@lem6139376 A B a f s) (@lem6139039 A B a f s h1)). Qed.
Lemma lem6139383 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term421 A B C g f a op) : term421 A B C g f a op.
Proof. exact (h1). Qed.
Lemma lem6139831 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term683 A B a f x s.
Proof. exact (h1). Qed.
Lemma lem6139832 {A B C : Type'} (x' : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term377 A B C x' op s g f) : term377 A B C x' op s g f.
Proof. exact (h1). Qed.
Lemma lem6139833 {A B C : Type'} (x' : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term374 A B C x' y op s g f) : term374 A B C x' y op s g f.
Proof. exact (h1). Qed.
Lemma lem6139843 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6139850 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139851 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6139850 A (type686 A) f x). Qed.
Lemma lem6139852 {A : Type'} (a : A) : (@IN A a) = (@I (A -> (A -> Prop) -> Prop) (@IN A) a).
Proof. exact (@lem6139851 A (@IN A) a). Qed.
Lemma lem6139853 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6139854 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) a s).
Proof. exact (MK_COMB (@lem6139852 A a) (@lem6139853 A s)). Qed.
Lemma lem6139856 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139857 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6139856 (A -> Prop) Prop f x). Qed.
Lemma lem6139858 {A : Type'} (a : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) a s) = (term685 A a s).
Proof. exact (@lem6139857 A (@I (A -> (A -> Prop) -> Prop) (@IN A) a) s). Qed.
Lemma lem6139860 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = (term685 A a s).
Proof. exact (TRANS (@lem6139854 A a s) (@lem6139858 A a s)). Qed.
Lemma lem6139861 {A : Type'} (a : A) (s : A -> Prop) : (term180 A a s) = (term686 A a s).
Proof. exact (MK_COMB (@lem6139843) (@lem6139860 A a s)). Qed.
Lemma lem6139872 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6139873 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6139878 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6139878 A B f x). Qed.
Lemma lem6139881 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6139879 A B f y). Qed.
Lemma lem6139882 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term406 A B C g f y).
Proof. exact (MK_COMB (@lem6139873 B C g) (@lem6139881 A B f y)). Qed.
Lemma lem6139884 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139885 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem6139884 B C f x). Qed.
Lemma lem6139886 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term406 A B C g f y) = (term407 A B C g f y).
Proof. exact (@lem6139885 B C g (@I (A -> B) f y)). Qed.
Lemma lem6139887 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term407 A B C g f y).
Proof. exact (TRANS (@lem6139882 A B C g f y) (@lem6139886 A B C g f y)). Qed.
Lemma lem6139892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139893 {C : Type'} (f : type402 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> C) f x).
Proof. exact (@lem6139892 (type1400 C) C f x). Qed.
Lemma lem6139895 {C : Type'} (op : type1400 C) : (@neutral C op) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (@lem6139893 C (@neutral C) op). Qed.
Lemma lem6139896 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term119 A B C g f y) = (term408 A B C g f y).
Proof. exact (MK_COMB (@lem6139872 C) (@lem6139887 A B C g f y)). Qed.
Lemma lem6139897 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term110 A B C g f y) = (@neutral C op)) = ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op)).
Proof. exact (MK_COMB (@lem6139896 A B C g f y) (@lem6139895 C op)). Qed.
Lemma lem6139898 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6139899 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6139904 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6139904 A B f x). Qed.
Lemma lem6139907 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6139905 A B f x'). Qed.
Lemma lem6139912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139913 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6139912 A B f x). Qed.
Lemma lem6139915 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6139913 A B f y). Qed.
Lemma lem6139916 {A B : Type'} (f : A -> B) (x' : A) : (term409 A B f x') = (term410 A B f x').
Proof. exact (MK_COMB (@lem6139899 B) (@lem6139907 A B f x')). Qed.
Lemma lem6139917 {A B : Type'} (x' : A) (f : A -> B) (y : A) : ((f x') = (f y)) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem6139916 A B f x') (@lem6139915 A B f y)). Qed.
Lemma lem6139918 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term383 A B x' f y) = (term411 A B x' f y).
Proof. exact (MK_COMB (@lem6139898) (@lem6139917 A B x' f y)). Qed.
Lemma lem6139925 {A : Type'} (x' : A) (y : A) : (term385 A x' y) = (term385 A x' y).
Proof. exact (eq_refl (term385 A x' y)). Qed.
Lemma lem6139926 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term387 A B x' f y) = (term412 A B x' f y).
Proof. exact (MK_COMB (@lem6139925 A x' y) (@lem6139918 A B x' f y)). Qed.
Lemma lem6139927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6139934 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139935 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6139934 A (type686 A) f x). Qed.
Lemma lem6139936 {A : Type'} (y : A) : (@IN A y) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y).
Proof. exact (@lem6139935 A (@IN A) y). Qed.
Lemma lem6139937 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6139938 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y s).
Proof. exact (MK_COMB (@lem6139936 A y) (@lem6139937 A s)). Qed.
Lemma lem6139940 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139941 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6139940 (A -> Prop) Prop f x). Qed.
Lemma lem6139942 {A : Type'} (y : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y s) = (term685 A y s).
Proof. exact (@lem6139941 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y) s). Qed.
Lemma lem6139944 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (term685 A y s).
Proof. exact (TRANS (@lem6139938 A y s) (@lem6139942 A y s)). Qed.
Lemma lem6139945 {A : Type'} (y : A) (s : A -> Prop) : (term180 A y s) = (term686 A y s).
Proof. exact (MK_COMB (@lem6139927) (@lem6139944 A y s)). Qed.
Lemma lem6139954 {A : Type'} (y : A) (a : A) : (term423 A y a) = (term423 A y a).
Proof. exact (eq_refl (term423 A y a)). Qed.
Lemma lem6139955 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term381 A a y s) = (term687 A a y s).
Proof. exact (MK_COMB (@lem6139954 A y a) (@lem6139945 A y s)). Qed.
Lemma lem6139956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139957 {A : Type'} (a : A) (y : A) (s : A -> Prop) : (term391 A a y s) = (term688 A a y s).
Proof. exact (MK_COMB (@lem6139956) (@lem6139955 A a y s)). Qed.
Lemma lem6139958 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term393 A B a s x' f y) = (term689 A B a s x' f y).
Proof. exact (MK_COMB (@lem6139957 A a y s) (@lem6139926 A B x' f y)). Qed.
Lemma lem6139959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6139966 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139967 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6139966 A (type686 A) f x). Qed.
Lemma lem6139968 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6139967 A (@IN A) x'). Qed.
Lemma lem6139969 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6139970 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6139968 A x') (@lem6139969 A s)). Qed.
Lemma lem6139972 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6139973 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6139972 (A -> Prop) Prop f x). Qed.
Lemma lem6139974 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term685 A x' s).
Proof. exact (@lem6139973 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6139976 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term685 A x' s).
Proof. exact (TRANS (@lem6139970 A x' s) (@lem6139974 A x' s)). Qed.
Lemma lem6139977 {A : Type'} (x' : A) (s : A -> Prop) : (term180 A x' s) = (term686 A x' s).
Proof. exact (MK_COMB (@lem6139959) (@lem6139976 A x' s)). Qed.
Lemma lem6139986 {A : Type'} (x' : A) (a : A) : (term423 A x' a) = (term423 A x' a).
Proof. exact (eq_refl (term423 A x' a)). Qed.
Lemma lem6139987 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term381 A a x' s) = (term687 A a x' s).
Proof. exact (MK_COMB (@lem6139986 A x' a) (@lem6139977 A x' s)). Qed.
Lemma lem6139988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139989 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term391 A a x' s) = (term688 A a x' s).
Proof. exact (MK_COMB (@lem6139988) (@lem6139987 A a x' s)). Qed.
Lemma lem6139990 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term396 A B a s x' f y) = (term690 A B a s x' f y).
Proof. exact (MK_COMB (@lem6139989 A a x' s) (@lem6139958 A B a s x' f y)). Qed.
Lemma lem6139991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6139992 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term399 A B a s x' f y) = (term691 A B a s x' f y).
Proof. exact (MK_COMB (@lem6139991) (@lem6139990 A B a s x' f y)). Qed.
Lemma lem6139993 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term401 A B C a s x' g f y op) = (term692 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6139992 A B a s x' f y) (@lem6139897 A B C g f y op)). Qed.
Lemma lem6139994 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term402 A B C a s x' g f op) = (term693 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6139993 A B C a s x' g f y op)). Qed.
Lemma lem6139995 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6139996 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term403 A B C a s x' g f op) = (term694 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6139995 A) (@lem6139994 A B C a s x' g f op)). Qed.
Lemma lem6139997 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term404 A B C a s g f op) = (term695 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6139996 A B C a s x' g f op)). Qed.
Lemma lem6139998 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6139999 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term405 A B C a s g f op) = (term696 A B C a s g f op).
Proof. exact (MK_COMB (@lem6139998 A) (@lem6139997 A B C a s g f op)). Qed.
Lemma lem6140000 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term696 A B C a s g f op.
Proof. exact (EQ_MP (@lem6139999 A B C a s g f op) (@lem6139316 A B C a s g f op h1)). Qed.
Lemma lem6140001 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6140002 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6140003 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6140008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140009 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6140008 A B f x). Qed.
Lemma lem6140011 {A B : Type'} (f : A -> B) (a : A) : (f a) = (@I (A -> B) f a).
Proof. exact (@lem6140009 A B f a). Qed.
Lemma lem6140012 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) : (term110 A B C g f a) = (term406 A B C g f a).
Proof. exact (MK_COMB (@lem6140003 B C g) (@lem6140011 A B f a)). Qed.
Lemma lem6140014 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140015 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem6140014 B C f x). Qed.
Lemma lem6140016 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) : (term406 A B C g f a) = (term407 A B C g f a).
Proof. exact (@lem6140015 B C g (@I (A -> B) f a)). Qed.
Lemma lem6140017 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) : (term110 A B C g f a) = (term407 A B C g f a).
Proof. exact (TRANS (@lem6140012 A B C g f a) (@lem6140016 A B C g f a)). Qed.
Lemma lem6140022 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140023 {C : Type'} (f : type402 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> C) f x).
Proof. exact (@lem6140022 (type1400 C) C f x). Qed.
Lemma lem6140025 {C : Type'} (op : type1400 C) : (@neutral C op) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (@lem6140023 C (@neutral C) op). Qed.
Lemma lem6140026 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) : (term119 A B C g f a) = (term408 A B C g f a).
Proof. exact (MK_COMB (@lem6140002 C) (@lem6140017 A B C g f a)). Qed.
Lemma lem6140027 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : ((term110 A B C g f a) = (@neutral C op)) = ((term407 A B C g f a) = (@I ((C -> C -> C) -> C) (@neutral C) op)).
Proof. exact (MK_COMB (@lem6140026 A B C g f a) (@lem6140025 C op)). Qed.
Lemma lem6140028 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term421 A B C g f a op) = (term697 A B C g f a op).
Proof. exact (MK_COMB (@lem6140001) (@lem6140027 A B C g f a op)). Qed.
Lemma lem6140906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140907 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6140906 A (type686 A) f x). Qed.
Lemma lem6140908 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem6140907 A (@IN A) x). Qed.
Lemma lem6140909 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6140910 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem6140908 A x) (@lem6140909 A s)). Qed.
Lemma lem6140912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140913 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6140912 (A -> Prop) Prop f x). Qed.
Lemma lem6140914 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term685 A x s).
Proof. exact (@lem6140913 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem6140916 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term685 A x s).
Proof. exact (TRANS (@lem6140910 A x s) (@lem6140914 A x s)). Qed.
Lemma lem6140917 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6140922 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140923 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6140922 A B f x). Qed.
Lemma lem6140925 {A B : Type'} (f : A -> B) (a : A) : (f a) = (@I (A -> B) f a).
Proof. exact (@lem6140923 A B f a). Qed.
Lemma lem6140930 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140932 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6140930 A B f x). Qed.
Lemma lem6140933 {A B : Type'} (f : A -> B) (a : A) : (term409 A B f a) = (term410 A B f a).
Proof. exact (MK_COMB (@lem6140917 B) (@lem6140925 A B f a)). Qed.
Lemma lem6140934 {A B : Type'} (a : A) (f : A -> B) (x : A) : ((f a) = (f x)) = ((@I (A -> B) f a) = (@I (A -> B) f x)).
Proof. exact (MK_COMB (@lem6140933 A B f a) (@lem6140932 A B f x)). Qed.
Lemma lem6140935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6140936 {A B : Type'} (a : A) (f : A -> B) (x : A) : (term698 A B a f x) = (term517 A B a f x).
Proof. exact (MK_COMB (@lem6140935) (@lem6140934 A B a f x)). Qed.
Lemma lem6140937 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) : (term683 A B a f x s) = (term699 A B a f x s).
Proof. exact (MK_COMB (@lem6140936 A B a f x) (@lem6140916 A x s)). Qed.
Lemma lem6140938 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term699 A B a f x s.
Proof. exact (EQ_MP (@lem6140937 A B a f x s) (@lem6139831 A B a f x s h1)). Qed.
Lemma lem6140939 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6140948 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140949 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem6140948 (A -> B) (type678 A B) f x). Qed.
Lemma lem6140950 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem6140949 A B (@IMAGE A B) f). Qed.
Lemma lem6140951 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6140952 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem6140950 A B f) (@lem6140951 A s)). Qed.
Lemma lem6140954 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140955 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem6140954 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem6140956 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term700 A B f s).
Proof. exact (@lem6140955 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem6140958 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term700 A B f s).
Proof. exact (TRANS (@lem6140952 A B f s) (@lem6140956 A B f s)). Qed.
Lemma lem6140959 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6140960 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@iterate C B op).
Proof. exact (eq_refl (@iterate C B op)). Qed.
Lemma lem6140961 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term701 A B C op f s) = (term702 A B C op f s).
Proof. exact (MK_COMB (@lem6140960 B C op) (@lem6140958 A B f s)). Qed.
Lemma lem6140962 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term703 A B C op f s g).
Proof. exact (MK_COMB (@lem6140961 A B C op f s) (@lem6140959 B C g)). Qed.
Lemma lem6140964 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140965 {B C : Type'} (f : type750 B C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) f x).
Proof. exact (@lem6140964 (type1400 C) (type632 B C) f x). Qed.
Lemma lem6140966 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) (@iterate C B) op).
Proof. exact (@lem6140965 B C (@iterate C B) op). Qed.
Lemma lem6140967 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term700 A B f s) = (term700 A B f s).
Proof. exact (eq_refl (term700 A B f s)). Qed.
Lemma lem6140968 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term702 A B C op f s) = (term704 A B C op f s).
Proof. exact (MK_COMB (@lem6140966 B C op) (@lem6140967 A B f s)). Qed.
Lemma lem6140970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140971 {B C : Type'} (f : type632 B C) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> C) -> C) f x).
Proof. exact (@lem6140970 (B -> Prop) (type570 B C) f x). Qed.
Lemma lem6140972 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term704 A B C op f s) = (term705 A B C op f s).
Proof. exact (@lem6140971 B C (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) (@iterate C B) op) (term700 A B f s)). Qed.
Lemma lem6140973 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term702 A B C op f s) = (term705 A B C op f s).
Proof. exact (TRANS (@lem6140968 A B C op f s) (@lem6140972 A B C op f s)). Qed.
Lemma lem6140974 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6140975 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term703 A B C op f s g) = (term706 A B C op f s g).
Proof. exact (MK_COMB (@lem6140973 A B C op f s) (@lem6140974 B C g)). Qed.
Lemma lem6140977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140978 {B C : Type'} (f : type570 B C) (x : B -> C) : (f x) = (@I ((B -> C) -> C) f x).
Proof. exact (@lem6140977 (B -> C) C f x). Qed.
Lemma lem6140979 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term706 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (@lem6140978 B C (term705 A B C op f s) g). Qed.
Lemma lem6140980 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term703 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (TRANS (@lem6140975 A B C op f s g) (@lem6140979 A B C op f s g)). Qed.
Lemma lem6140981 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (TRANS (@lem6140962 A B C op f s g) (@lem6140980 A B C op f s g)). Qed.
Lemma lem6140991 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140992 {A B C : Type'} (f : type808 A B C) (x : B -> C) : (f x) = (@I ((B -> C) -> (A -> B) -> A -> C) f x).
Proof. exact (@lem6140991 (B -> C) (type550 A B C) f x). Qed.
Lemma lem6140993 {A B C : Type'} (g : B -> C) : (@o A B C g) = (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g).
Proof. exact (@lem6140992 A B C (@o A B C) g). Qed.
Lemma lem6140994 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6140995 {A B C : Type'} (g : B -> C) (f : A -> B) : (@o A B C g f) = (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g f).
Proof. exact (MK_COMB (@lem6140993 A B C g) (@lem6140994 A B f)). Qed.
Lemma lem6140997 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6140998 {A B C : Type'} (f : type550 A B C) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> C) f x).
Proof. exact (@lem6140997 (A -> B) (A -> C) f x). Qed.
Lemma lem6140999 {A B C : Type'} (g : B -> C) (f : A -> B) : (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g f) = (term708 A B C g f).
Proof. exact (@lem6140998 A B C (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g) f). Qed.
Lemma lem6141001 {A B C : Type'} (g : B -> C) (f : A -> B) : (@o A B C g f) = (term708 A B C g f).
Proof. exact (TRANS (@lem6140995 A B C g f) (@lem6140999 A B C g f)). Qed.
Lemma lem6141003 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem6141004 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term34 A B C op s g f) = (term709 A B C op s g f).
Proof. exact (MK_COMB (@lem6141003 A C op s) (@lem6141001 A B C g f)). Qed.
Lemma lem6141006 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141007 {A C : Type'} (f : type750 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem6141006 (type1400 C) (type632 A C) f x). Qed.
Lemma lem6141008 {A C : Type'} (op : type1400 C) : (@iterate C A op) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op).
Proof. exact (@lem6141007 A C (@iterate C A) op). Qed.
Lemma lem6141009 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6141010 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s).
Proof. exact (MK_COMB (@lem6141008 A C op) (@lem6141009 A s)). Qed.
Lemma lem6141012 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141013 {A C : Type'} (f : type632 A C) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem6141012 (A -> Prop) (type570 A C) f x). Qed.
Lemma lem6141014 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s) = (term710 A C op s).
Proof. exact (@lem6141013 A C (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op) s). Qed.
Lemma lem6141015 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (term710 A C op s).
Proof. exact (TRANS (@lem6141010 A C op s) (@lem6141014 A C op s)). Qed.
Lemma lem6141016 {A B C : Type'} (g : B -> C) (f : A -> B) : (term708 A B C g f) = (term708 A B C g f).
Proof. exact (eq_refl (term708 A B C g f)). Qed.
Lemma lem6141017 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term709 A B C op s g f) = (term711 A B C op s g f).
Proof. exact (MK_COMB (@lem6141015 A C op s) (@lem6141016 A B C g f)). Qed.
Lemma lem6141019 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141020 {A C : Type'} (f : type570 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> C) f x).
Proof. exact (@lem6141019 (A -> C) C f x). Qed.
Lemma lem6141021 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term711 A B C op s g f) = (term712 A B C op s g f).
Proof. exact (@lem6141020 A C (term710 A C op s) (term708 A B C g f)). Qed.
Lemma lem6141022 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term709 A B C op s g f) = (term712 A B C op s g f).
Proof. exact (TRANS (@lem6141017 A B C op s g f) (@lem6141021 A B C op s g f)). Qed.
Lemma lem6141023 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term34 A B C op s g f) = (term712 A B C op s g f).
Proof. exact (TRANS (@lem6141004 A B C op s g f) (@lem6141022 A B C op s g f)). Qed.
Lemma lem6141024 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term594 A B C op f s g) = (term713 A B C op f s g).
Proof. exact (MK_COMB (@lem6140939 C) (@lem6140981 A B C op f s g)). Qed.
Lemma lem6141025 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term707 A B C op f s g) = (term712 A B C op s g f)).
Proof. exact (MK_COMB (@lem6141024 A B C op f s g) (@lem6141023 A B C op s g f)). Qed.
Lemma lem6141026 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6141027 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6141028 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6141033 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141034 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6141033 A B f x). Qed.
Lemma lem6141036 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6141034 A B f y). Qed.
Lemma lem6141037 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term406 A B C g f y).
Proof. exact (MK_COMB (@lem6141028 B C g) (@lem6141036 A B f y)). Qed.
Lemma lem6141039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141040 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem6141039 B C f x). Qed.
Lemma lem6141041 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term406 A B C g f y) = (term407 A B C g f y).
Proof. exact (@lem6141040 B C g (@I (A -> B) f y)). Qed.
Lemma lem6141042 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term407 A B C g f y).
Proof. exact (TRANS (@lem6141037 A B C g f y) (@lem6141041 A B C g f y)). Qed.
Lemma lem6141047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141048 {C : Type'} (f : type402 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> C) f x).
Proof. exact (@lem6141047 (type1400 C) C f x). Qed.
Lemma lem6141050 {C : Type'} (op : type1400 C) : (@neutral C op) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (@lem6141048 C (@neutral C) op). Qed.
Lemma lem6141051 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term119 A B C g f y) = (term408 A B C g f y).
Proof. exact (MK_COMB (@lem6141027 C) (@lem6141042 A B C g f y)). Qed.
Lemma lem6141052 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term110 A B C g f y) = (@neutral C op)) = ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op)).
Proof. exact (MK_COMB (@lem6141051 A B C g f y) (@lem6141050 C op)). Qed.
Lemma lem6141053 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term421 A B C g f y op) = (term697 A B C g f y op).
Proof. exact (MK_COMB (@lem6141026) (@lem6141052 A B C g f y op)). Qed.
Lemma lem6141054 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6141059 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6141059 A B f x). Qed.
Lemma lem6141062 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6141060 A B f x'). Qed.
Lemma lem6141067 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141068 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6141067 A B f x). Qed.
Lemma lem6141070 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6141068 A B f y). Qed.
Lemma lem6141071 {A B : Type'} (f : A -> B) (x' : A) : (term409 A B f x') = (term410 A B f x').
Proof. exact (MK_COMB (@lem6141054 B) (@lem6141062 A B f x')). Qed.
Lemma lem6141072 {A B : Type'} (x' : A) (f : A -> B) (y : A) : ((f x') = (f y)) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem6141071 A B f x') (@lem6141070 A B f y)). Qed.
Lemma lem6141081 {A : Type'} (x' : A) (y : A) : (term423 A x' y) = (term423 A x' y).
Proof. exact (eq_refl (term423 A x' y)). Qed.
Lemma lem6141082 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term118 A B x' f y) = (term424 A B x' f y).
Proof. exact (MK_COMB (@lem6141081 A x' y) (@lem6141072 A B x' f y)). Qed.
Lemma lem6141089 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141090 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6141089 A (type686 A) f x). Qed.
Lemma lem6141091 {A : Type'} (y : A) : (@IN A y) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y).
Proof. exact (@lem6141090 A (@IN A) y). Qed.
Lemma lem6141092 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6141093 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y s).
Proof. exact (MK_COMB (@lem6141091 A y) (@lem6141092 A s)). Qed.
Lemma lem6141095 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141096 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6141095 (A -> Prop) Prop f x). Qed.
Lemma lem6141097 {A : Type'} (y : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y s) = (term685 A y s).
Proof. exact (@lem6141096 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y) s). Qed.
Lemma lem6141099 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (term685 A y s).
Proof. exact (TRANS (@lem6141093 A y s) (@lem6141097 A y s)). Qed.
Lemma lem6141100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6141101 {A : Type'} (y : A) (s : A -> Prop) : (term425 A y s) = (term714 A y s).
Proof. exact (MK_COMB (@lem6141100) (@lem6141099 A y s)). Qed.
Lemma lem6141102 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term159 A B s x' f y) = (term715 A B s x' f y).
Proof. exact (MK_COMB (@lem6141101 A y s) (@lem6141082 A B x' f y)). Qed.
Lemma lem6141109 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141110 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6141109 A (type686 A) f x). Qed.
Lemma lem6141111 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6141110 A (@IN A) x'). Qed.
Lemma lem6141112 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6141113 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6141111 A x') (@lem6141112 A s)). Qed.
Lemma lem6141115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6141116 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6141115 (A -> Prop) Prop f x). Qed.
Lemma lem6141117 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term685 A x' s).
Proof. exact (@lem6141116 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6141119 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term685 A x' s).
Proof. exact (TRANS (@lem6141113 A x' s) (@lem6141117 A x' s)). Qed.
Lemma lem6141120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6141121 {A : Type'} (x' : A) (s : A -> Prop) : (term425 A x' s) = (term714 A x' s).
Proof. exact (MK_COMB (@lem6141120) (@lem6141119 A x' s)). Qed.
Lemma lem6141122 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term152 A B s x' f y) = (term716 A B s x' f y).
Proof. exact (MK_COMB (@lem6141121 A x' s) (@lem6141102 A B s x' f y)). Qed.
Lemma lem6141123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6141124 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term428 A B s x' f y) = (term717 A B s x' f y).
Proof. exact (MK_COMB (@lem6141123) (@lem6141122 A B s x' f y)). Qed.
Lemma lem6141125 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term325 A B C s x' g f y op) = (term718 A B C s x' g f y op).
Proof. exact (MK_COMB (@lem6141124 A B s x' f y) (@lem6141053 A B C g f y op)). Qed.
Lemma lem6141126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6141127 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term372 A B C s x' g f y op) = (term719 A B C s x' g f y op).
Proof. exact (MK_COMB (@lem6141126) (@lem6141125 A B C s x' g f y op)). Qed.
Lemma lem6141128 {A B C : Type'} (x' : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term374 A B C x' y op s g f) = (term720 A B C x' y op s g f).
Proof. exact (MK_COMB (@lem6141127 A B C s x' g f y op) (@lem6141025 A B C op s g f)). Qed.
Lemma lem6141129 {A B C : Type'} (x' : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term374 A B C x' y op s g f) : term720 A B C x' y op s g f.
Proof. exact (EQ_MP (@lem6141128 A B C x' y op s g f) (@lem6139833 A B C x' y op s g f h1)). Qed.
Lemma lem6141132 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term718 A B C s x' g f y op.
Proof. exact (h1). Qed.
Lemma lem6141135 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term716 A B s x' f y.
Proof. exact (proj1 (@lem6141132 A B C s x' g f y op h1)). Qed.
Lemma lem6141136 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term715 A B s x' f y.
Proof. exact (proj2 (@lem6141135 A B C s x' g f y op h1)). Qed.
Lemma lem6141138 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term424 A B x' f y.
Proof. exact (proj2 (@lem6141136 A B C s x' g f y op h1)). Qed.
Lemma lem6141155 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op)) = ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op)).
Proof. exact (eq_refl ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6141178 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term689 A B a s x' f y) = (term721 A B a s x' f y).
Proof. exact (@lem19699 (term389 A y a) (term686 A y s) (term412 A B x' f y)). Qed.
Lemma lem6141185 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term688 A a x' s) = (term688 A a x' s).
Proof. exact (eq_refl (term688 A a x' s)). Qed.
Lemma lem6141186 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term690 A B a s x' f y) = (term722 A B a s x' f y).
Proof. exact (MK_COMB (@lem6141185 A a x' s) (@lem6141178 A B a s x' f y)). Qed.
Lemma lem6141187 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term722 A B a s x' f y) = (term723 A B a s x' f y).
Proof. exact (@lem19490 (term436 A B a x' f y) (term687 A a x' s) (term724 A B s x' f y)). Qed.
Lemma lem6141194 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term725 A B a s x' f y) = (term726 A B a s x' f y).
Proof. exact (@lem19699 (term389 A x' a) (term686 A x' s) (term724 A B s x' f y)). Qed.
Lemma lem6141201 {A B : Type'} (s : A -> Prop) (a : A) (x' : A) (f : A -> B) (y : A) : (term727 A B s a x' f y) = (term728 A B s a x' f y).
Proof. exact (@lem19699 (term389 A x' a) (term686 A x' s) (term436 A B a x' f y)). Qed.
Lemma lem6141202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6141203 {A B : Type'} (s : A -> Prop) (a : A) (x' : A) (f : A -> B) (y : A) : (term729 A B s a x' f y) = (term730 A B s a x' f y).
Proof. exact (MK_COMB (@lem6141202) (@lem6141201 A B s a x' f y)). Qed.
Lemma lem6141204 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term723 A B a s x' f y) = (term731 A B a s x' f y).
Proof. exact (MK_COMB (@lem6141203 A B s a x' f y) (@lem6141194 A B a s x' f y)). Qed.
Lemma lem6141205 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term722 A B a s x' f y) = (term731 A B a s x' f y).
Proof. exact (TRANS (@lem6141187 A B a s x' f y) (@lem6141204 A B a s x' f y)). Qed.
Lemma lem6141206 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term690 A B a s x' f y) = (term731 A B a s x' f y).
Proof. exact (TRANS (@lem6141186 A B a s x' f y) (@lem6141205 A B a s x' f y)). Qed.
Lemma lem6141207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6141208 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term691 A B a s x' f y) = (term732 A B a s x' f y).
Proof. exact (MK_COMB (@lem6141207) (@lem6141206 A B a s x' f y)). Qed.
Lemma lem6141209 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term692 A B C a s x' g f y op) = (term733 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6141208 A B a s x' f y) (@lem6141155 A B C g f y op)). Qed.
Lemma lem6141210 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term733 A B C a s x' g f y op) = (term734 A B C a s x' g f y op).
Proof. exact (@lem19699 (term728 A B s a x' f y) (term726 A B a s x' f y) ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6141217 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term735 A B C a s x' g f y op) = (term736 A B C a s x' g f y op).
Proof. exact (@lem19699 (term737 A B a s x' f y) (term738 A B s x' f y) ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6141224 {A B C : Type'} (s : A -> Prop) (a : A) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term739 A B C s a x' g f y op) = (term740 A B C s a x' g f y op).
Proof. exact (@lem19699 (term454 A B a x' f y) (term741 A B s a x' f y) ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6141225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6141226 {A B C : Type'} (s : A -> Prop) (a : A) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term742 A B C s a x' g f y op) = (term743 A B C s a x' g f y op).
Proof. exact (MK_COMB (@lem6141225) (@lem6141224 A B C s a x' g f y op)). Qed.
Lemma lem6141227 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term734 A B C a s x' g f y op) = (term744 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6141226 A B C s a x' g f y op) (@lem6141217 A B C a s x' g f y op)). Qed.
Lemma lem6141228 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term733 A B C a s x' g f y op) = (term744 A B C a s x' g f y op).
Proof. exact (TRANS (@lem6141210 A B C a s x' g f y op) (@lem6141227 A B C a s x' g f y op)). Qed.
Lemma lem6141229 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term692 A B C a s x' g f y op) = (term744 A B C a s x' g f y op).
Proof. exact (TRANS (@lem6141209 A B C a s x' g f y op) (@lem6141228 A B C a s x' g f y op)). Qed.
Lemma lem6141230 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term693 A B C a s x' g f op) = (term745 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6141229 A B C a s x' g f y op)). Qed.
Lemma lem6141231 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6141232 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term694 A B C a s x' g f op) = (term746 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6141231 A) (@lem6141230 A B C a s x' g f op)). Qed.
Lemma lem6141233 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term695 A B C a s g f op) = (term747 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6141232 A B C a s x' g f op)). Qed.
Lemma lem6141234 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6141236 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term696 A B C a s g f op) = (term748 A B C a s g f op).
Proof. exact (MK_COMB (@lem6141234 A) (@lem6141233 A B C a s g f op)). Qed.
Lemma lem6141237 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term748 A B C a s g f op.
Proof. exact (EQ_MP (@lem6141236 A B C a s g f op) (@lem6140000 A B C a s g f op h1)). Qed.
Lemma lem6142678 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op)) = ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op)).
Proof. exact (eq_refl ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6142701 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term689 A B a s x' f y) = (term721 A B a s x' f y).
Proof. exact (@lem19699 (term389 A y a) (term686 A y s) (term412 A B x' f y)). Qed.
Lemma lem6142708 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term688 A a x' s) = (term688 A a x' s).
Proof. exact (eq_refl (term688 A a x' s)). Qed.
Lemma lem6142709 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term690 A B a s x' f y) = (term722 A B a s x' f y).
Proof. exact (MK_COMB (@lem6142708 A a x' s) (@lem6142701 A B a s x' f y)). Qed.
Lemma lem6142710 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term722 A B a s x' f y) = (term723 A B a s x' f y).
Proof. exact (@lem19490 (term436 A B a x' f y) (term687 A a x' s) (term724 A B s x' f y)). Qed.
Lemma lem6142717 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term725 A B a s x' f y) = (term726 A B a s x' f y).
Proof. exact (@lem19699 (term389 A x' a) (term686 A x' s) (term724 A B s x' f y)). Qed.
Lemma lem6142724 {A B : Type'} (s : A -> Prop) (a : A) (x' : A) (f : A -> B) (y : A) : (term727 A B s a x' f y) = (term728 A B s a x' f y).
Proof. exact (@lem19699 (term389 A x' a) (term686 A x' s) (term436 A B a x' f y)). Qed.
Lemma lem6142725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6142726 {A B : Type'} (s : A -> Prop) (a : A) (x' : A) (f : A -> B) (y : A) : (term729 A B s a x' f y) = (term730 A B s a x' f y).
Proof. exact (MK_COMB (@lem6142725) (@lem6142724 A B s a x' f y)). Qed.
Lemma lem6142727 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term723 A B a s x' f y) = (term731 A B a s x' f y).
Proof. exact (MK_COMB (@lem6142726 A B s a x' f y) (@lem6142717 A B a s x' f y)). Qed.
Lemma lem6142728 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term722 A B a s x' f y) = (term731 A B a s x' f y).
Proof. exact (TRANS (@lem6142710 A B a s x' f y) (@lem6142727 A B a s x' f y)). Qed.
Lemma lem6142729 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term690 A B a s x' f y) = (term731 A B a s x' f y).
Proof. exact (TRANS (@lem6142709 A B a s x' f y) (@lem6142728 A B a s x' f y)). Qed.
Lemma lem6142730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6142731 {A B : Type'} (a : A) (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term691 A B a s x' f y) = (term732 A B a s x' f y).
Proof. exact (MK_COMB (@lem6142730) (@lem6142729 A B a s x' f y)). Qed.
Lemma lem6142732 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term692 A B C a s x' g f y op) = (term733 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6142731 A B a s x' f y) (@lem6142678 A B C g f y op)). Qed.
Lemma lem6142733 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term733 A B C a s x' g f y op) = (term734 A B C a s x' g f y op).
Proof. exact (@lem19699 (term728 A B s a x' f y) (term726 A B a s x' f y) ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6142740 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term735 A B C a s x' g f y op) = (term736 A B C a s x' g f y op).
Proof. exact (@lem19699 (term737 A B a s x' f y) (term738 A B s x' f y) ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6142747 {A B C : Type'} (s : A -> Prop) (a : A) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term739 A B C s a x' g f y op) = (term740 A B C s a x' g f y op).
Proof. exact (@lem19699 (term454 A B a x' f y) (term741 A B s a x' f y) ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6142748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6142749 {A B C : Type'} (s : A -> Prop) (a : A) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term742 A B C s a x' g f y op) = (term743 A B C s a x' g f y op).
Proof. exact (MK_COMB (@lem6142748) (@lem6142747 A B C s a x' g f y op)). Qed.
Lemma lem6142750 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term734 A B C a s x' g f y op) = (term744 A B C a s x' g f y op).
Proof. exact (MK_COMB (@lem6142749 A B C s a x' g f y op) (@lem6142740 A B C a s x' g f y op)). Qed.
Lemma lem6142751 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term733 A B C a s x' g f y op) = (term744 A B C a s x' g f y op).
Proof. exact (TRANS (@lem6142733 A B C a s x' g f y op) (@lem6142750 A B C a s x' g f y op)). Qed.
Lemma lem6142752 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term692 A B C a s x' g f y op) = (term744 A B C a s x' g f y op).
Proof. exact (TRANS (@lem6142732 A B C a s x' g f y op) (@lem6142751 A B C a s x' g f y op)). Qed.
Lemma lem6142753 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term693 A B C a s x' g f op) = (term745 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6142752 A B C a s x' g f y op)). Qed.
Lemma lem6142754 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6142755 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term694 A B C a s x' g f op) = (term746 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6142754 A) (@lem6142753 A B C a s x' g f op)). Qed.
Lemma lem6142756 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term695 A B C a s g f op) = (term747 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6142755 A B C a s x' g f op)). Qed.
Lemma lem6142757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6142759 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term696 A B C a s g f op) = (term748 A B C a s g f op).
Proof. exact (MK_COMB (@lem6142757 A) (@lem6142756 A B C a s g f op)). Qed.
Lemma lem6142760 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term748 A B C a s g f op.
Proof. exact (EQ_MP (@lem6142759 A B C a s g f op) (@lem6140000 A B C a s g f op h1)). Qed.
Lemma lem6144172 {A B C : Type'} (_77201 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term749 A B C a s g f op _77201.
Proof. exact (@lem6141237 A B C a s g f op h1 _77201). Qed.
Lemma lem6144173 {A B C : Type'} (a : A) (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term749 A B C a s g f op _77201) = (term746 A B C a s _77201 g f op).
Proof. exact (eq_refl (term749 A B C a s g f op _77201)). Qed.
Lemma lem6144174 {A B C : Type'} (_77201 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term746 A B C a s _77201 g f op.
Proof. exact (EQ_MP (@lem6144173 A B C a s _77201 g f op) (@lem6144172 A B C _77201 a s g f op h1)). Qed.
Lemma lem6144175 {A B C : Type'} (_77201 : A) (_77202 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term750 A B C a s _77201 g f op _77202.
Proof. exact (@lem6144174 A B C _77201 a s g f op h1 _77202). Qed.
Lemma lem6144176 {A B C : Type'} (a : A) (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term750 A B C a s _77201 g f op _77202) = (term744 A B C a s _77201 g f _77202 op).
Proof. exact (eq_refl (term750 A B C a s _77201 g f op _77202)). Qed.
Lemma lem6144177 {A B C : Type'} (_77201 : A) (_77202 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term744 A B C a s _77201 g f _77202 op.
Proof. exact (EQ_MP (@lem6144176 A B C a s _77201 g f _77202 op) (@lem6144175 A B C _77201 _77202 a s g f op h1)). Qed.
Lemma lem6144214 {A B C : Type'} (_77215 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term749 A B C a s g f op _77215.
Proof. exact (@lem6142760 A B C a s g f op h1 _77215). Qed.
Lemma lem6144215 {A B C : Type'} (a : A) (s : A -> Prop) (_77215 : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term749 A B C a s g f op _77215) = (term746 A B C a s _77215 g f op).
Proof. exact (eq_refl (term749 A B C a s g f op _77215)). Qed.
Lemma lem6144216 {A B C : Type'} (_77215 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term746 A B C a s _77215 g f op.
Proof. exact (EQ_MP (@lem6144215 A B C a s _77215 g f op) (@lem6144214 A B C _77215 a s g f op h1)). Qed.
Lemma lem6144217 {A B C : Type'} (_77215 : A) (_77216 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term750 A B C a s _77215 g f op _77216.
Proof. exact (@lem6144216 A B C _77215 a s g f op h1 _77216). Qed.
Lemma lem6144218 {A B C : Type'} (a : A) (s : A -> Prop) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term750 A B C a s _77215 g f op _77216) = (term744 A B C a s _77215 g f _77216 op).
Proof. exact (eq_refl (term750 A B C a s _77215 g f op _77216)). Qed.
Lemma lem6144219 {A B C : Type'} (_77215 : A) (_77216 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term744 A B C a s _77215 g f _77216 op.
Proof. exact (EQ_MP (@lem6144218 A B C a s _77215 g f _77216 op) (@lem6144217 A B C _77215 _77216 a s g f op h1)). Qed.
Lemma lem6144280 {A B C : Type'} (_77201 : A) (_77202 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term736 A B C a s _77201 g f _77202 op.
Proof. exact (proj2 (@lem6144177 A B C _77201 _77202 a s g f op h1)). Qed.
Lemma lem6144282 {A B C : Type'} (_77201 : A) (_77202 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term751 A B C s _77201 g f _77202 op.
Proof. exact (proj2 (@lem6144280 A B C _77201 _77202 a s g f op h1)). Qed.
Lemma lem6144311 {A B C : Type'} (_77215 : A) (_77216 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term740 A B C s a _77215 g f _77216 op.
Proof. exact (proj1 (@lem6144219 A B C _77215 _77216 a s g f op h1)). Qed.
Lemma lem6144314 {A B C : Type'} (_77215 : A) (_77216 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term752 A B C s a _77215 g f _77216 op.
Proof. exact (proj2 (@lem6144311 A B C _77215 _77216 a s g f op h1)). Qed.
Lemma lem6144335 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term389 A x' y.
Proof. exact (proj1 (@lem6141138 A B C s x' g f y op h1)). Qed.
Lemma lem6144455 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term751 A B C s _77201 g f _77202 op) = (term753 A B C s _77201 g f _77202 op).
Proof. exact (@lem6113755 (term686 A _77201 s) (term724 A B s _77201 f _77202) ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6144456 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term754 A B C s _77201 g f _77202 op) = (term755 A B C s _77201 g f _77202 op).
Proof. exact (@lem6113755 (term686 A _77202 s) (term412 A B _77201 f _77202) ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6144463 {A B C : Type'} (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term756 A B C _77201 g f _77202 op) = (term757 A B C _77201 g f _77202 op).
Proof. exact (@lem6113755 (_77201 = _77202) (term411 A B _77201 f _77202) ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6144464 {A : Type'} (_77202 : A) (s : A -> Prop) : (term758 A _77202 s) = (term758 A _77202 s).
Proof. exact (eq_refl (term758 A _77202 s)). Qed.
Lemma lem6144467 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term755 A B C s _77201 g f _77202 op) = (term759 A B C s _77201 g f _77202 op).
Proof. exact (MK_COMB (@lem6144464 A _77202 s) (@lem6144463 A B C _77201 g f _77202 op)). Qed.
Lemma lem6144468 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term754 A B C s _77201 g f _77202 op) = (term759 A B C s _77201 g f _77202 op).
Proof. exact (TRANS (@lem6144456 A B C s _77201 g f _77202 op) (@lem6144467 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6144469 {A : Type'} (_77201 : A) (s : A -> Prop) : (term758 A _77201 s) = (term758 A _77201 s).
Proof. exact (eq_refl (term758 A _77201 s)). Qed.
Lemma lem6144472 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term753 A B C s _77201 g f _77202 op) = (term760 A B C s _77201 g f _77202 op).
Proof. exact (MK_COMB (@lem6144469 A _77201 s) (@lem6144468 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6144474 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term751 A B C s _77201 g f _77202 op) = (term760 A B C s _77201 g f _77202 op).
Proof. exact (TRANS (@lem6144455 A B C s _77201 g f _77202 op) (@lem6144472 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6144475 {A B C : Type'} (_77201 : A) (_77202 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term760 A B C s _77201 g f _77202 op.
Proof. exact (EQ_MP (@lem6144474 A B C s _77201 g f _77202 op) (@lem6144282 A B C _77201 _77202 a s g f op h1)). Qed.
Lemma lem6144531 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term421 A B C g f a op) : term697 A B C g f a op.
Proof. exact (EQ_MP (@lem6140028 A B C g f a op) (@lem6139383 A B C g f a op h1)). Qed.
Lemma lem6144703 {A B C : Type'} (s : A -> Prop) (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term752 A B C s a _77215 g f _77216 op) = (term761 A B C s a _77215 g f _77216 op).
Proof. exact (@lem6113755 (term686 A _77215 s) (term436 A B a _77215 f _77216) ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6144704 {A B C : Type'} (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term762 A B C a _77215 g f _77216 op) = (term763 A B C a _77215 g f _77216 op).
Proof. exact (@lem6113755 (term389 A _77216 a) (term412 A B _77215 f _77216) ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6144711 {A B C : Type'} (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term756 A B C _77215 g f _77216 op) = (term757 A B C _77215 g f _77216 op).
Proof. exact (@lem6113755 (_77215 = _77216) (term411 A B _77215 f _77216) ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6144712 {A : Type'} (_77216 : A) (a : A) : (term534 A _77216 a) = (term534 A _77216 a).
Proof. exact (eq_refl (term534 A _77216 a)). Qed.
Lemma lem6144715 {A B C : Type'} (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term763 A B C a _77215 g f _77216 op) = (term764 A B C a _77215 g f _77216 op).
Proof. exact (MK_COMB (@lem6144712 A _77216 a) (@lem6144711 A B C _77215 g f _77216 op)). Qed.
Lemma lem6144716 {A B C : Type'} (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term762 A B C a _77215 g f _77216 op) = (term764 A B C a _77215 g f _77216 op).
Proof. exact (TRANS (@lem6144704 A B C a _77215 g f _77216 op) (@lem6144715 A B C a _77215 g f _77216 op)). Qed.
Lemma lem6144717 {A : Type'} (_77215 : A) (s : A -> Prop) : (term758 A _77215 s) = (term758 A _77215 s).
Proof. exact (eq_refl (term758 A _77215 s)). Qed.
Lemma lem6144720 {A B C : Type'} (s : A -> Prop) (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term761 A B C s a _77215 g f _77216 op) = (term765 A B C s a _77215 g f _77216 op).
Proof. exact (MK_COMB (@lem6144717 A _77215 s) (@lem6144716 A B C a _77215 g f _77216 op)). Qed.
Lemma lem6144722 {A B C : Type'} (s : A -> Prop) (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term752 A B C s a _77215 g f _77216 op) = (term765 A B C s a _77215 g f _77216 op).
Proof. exact (TRANS (@lem6144703 A B C s a _77215 g f _77216 op) (@lem6144720 A B C s a _77215 g f _77216 op)). Qed.
Lemma lem6144723 {A B C : Type'} (_77215 : A) (_77216 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term765 A B C s a _77215 g f _77216 op.
Proof. exact (EQ_MP (@lem6144722 A B C s a _77215 g f _77216 op) (@lem6144314 A B C _77215 _77216 a s g f op h1)). Qed.
Lemma lem6145021 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term685 A x' s.
Proof. exact (proj1 (@lem6141135 A B C s x' g f y op h1)). Qed.
Lemma lem6145022 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term766 A x' s.
Proof. exact (fun h0 : term686 A x' s => @lem6145021 A B C s x' g f y op h1). Qed.
Lemma lem6145024 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145025 {A : Type'} (x' : A) (s : A -> Prop) : (term766 A x' s) = (term685 A x' s).
Proof. exact (@lem6145024 (term685 A x' s)). Qed.
Lemma lem6145026 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term685 A x' s.
Proof. exact (EQ_MP (@lem6145025 A x' s) (@lem6145022 A B C s x' g f y op h1)). Qed.
Lemma lem6145028 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term685 A y s.
Proof. exact (proj1 (@lem6141136 A B C s x' g f y op h1)). Qed.
Lemma lem6145029 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term766 A y s.
Proof. exact (fun h0 : term686 A y s => @lem6145028 A B C s x' g f y op h1). Qed.
Lemma lem6145031 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145032 {A : Type'} (y : A) (s : A -> Prop) : (term766 A y s) = (term685 A y s).
Proof. exact (@lem6145031 (term685 A y s)). Qed.
Lemma lem6145033 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term685 A y s.
Proof. exact (EQ_MP (@lem6145032 A y s) (@lem6145029 A B C s x' g f y op h1)). Qed.
Lemma lem6145035 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : (@I (A -> B) f x') = (@I (A -> B) f y).
Proof. exact (proj2 (@lem6141138 A B C s x' g f y op h1)). Qed.
Lemma lem6145036 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term476 A B x' f y.
Proof. exact (fun h0 : term411 A B x' f y => @lem6145035 A B C s x' g f y op h1). Qed.
Lemma lem6145038 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145039 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term476 A B x' f y) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (@lem6145038 ((@I (A -> B) f x') = (@I (A -> B) f y))). Qed.
Lemma lem6145040 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : (@I (A -> B) f x') = (@I (A -> B) f y).
Proof. exact (EQ_MP (@lem6145039 A B x' f y) (@lem6145036 A B C s x' g f y op h1)). Qed.
Lemma lem6145042 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term697 A B C g f y op.
Proof. exact (proj2 (@lem6141132 A B C s x' g f y op h1)). Qed.
Lemma lem6145043 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term767 A B C g f y op.
Proof. exact (fun h0 : (term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op) => @lem6145042 A B C s x' g f y op h1). Qed.
Lemma lem6145045 (p : Prop) : (term478 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6145046 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term767 A B C g f y op) = (term697 A B C g f y op).
Proof. exact (@lem6145045 ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6145047 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term697 A B C g f y op.
Proof. exact (EQ_MP (@lem6145046 A B C g f y op) (@lem6145043 A B C s x' g f y op h1)). Qed.
Lemma lem6145063 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145064 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term759 A B C s _77201 g f _77202 op) = (term768 A B C s _77201 g f _77202 op).
Proof. exact (@lem6145063 (_77201 = _77202) (term686 A _77202 s) (term769 A B C _77201 g f _77202 op)). Qed.
Lemma lem6145080 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145081 {A B C : Type'} (_77201 : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term770 A B C s _77201 g f _77202 op) = (term771 A B C _77201 s g f _77202 op).
Proof. exact (@lem6145080 (term411 A B _77201 f _77202) (term686 A _77202 s) ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6145097 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6145098 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (_77202 : A) (s : A -> Prop) : (term772 A B C s g f _77202 op) = (term773 A B C g f op _77202 s).
Proof. exact (@lem6145097 ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term686 A _77202 s)). Qed.
Lemma lem6145106 {A B : Type'} (_77201 : A) (f : A -> B) (_77202 : A) : (term485 A B _77201 f _77202) = (term485 A B _77201 f _77202).
Proof. exact (eq_refl (term485 A B _77201 f _77202)). Qed.
Lemma lem6145107 {A B C : Type'} (_77201 : A) (g : B -> C) (f : A -> B) (op : type1400 C) (_77202 : A) (s : A -> Prop) : (term771 A B C _77201 s g f _77202 op) = (term774 A B C _77201 g f op _77202 s).
Proof. exact (MK_COMB (@lem6145106 A B _77201 f _77202) (@lem6145098 A B C g f op _77202 s)). Qed.
Lemma lem6145111 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145112 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term774 A B C _77201 g f op _77202 s) = (term775 A B C g op _77201 f _77202 s).
Proof. exact (@lem6145111 ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term411 A B _77201 f _77202) (term686 A _77202 s)). Qed.
Lemma lem6145132 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term771 A B C _77201 s g f _77202 op) = (term775 A B C g op _77201 f _77202 s).
Proof. exact (TRANS (@lem6145107 A B C _77201 g f op _77202 s) (@lem6145112 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145133 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term770 A B C s _77201 g f _77202 op) = (term775 A B C g op _77201 f _77202 s).
Proof. exact (TRANS (@lem6145081 A B C _77201 s g f _77202 op) (@lem6145132 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145134 {A : Type'} (_77201 : A) (_77202 : A) : (term385 A _77201 _77202) = (term385 A _77201 _77202).
Proof. exact (eq_refl (term385 A _77201 _77202)). Qed.
Lemma lem6145135 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term768 A B C s _77201 g f _77202 op) = (term776 A B C g op _77201 f _77202 s).
Proof. exact (MK_COMB (@lem6145134 A _77201 _77202) (@lem6145133 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145146 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term759 A B C s _77201 g f _77202 op) = (term776 A B C g op _77201 f _77202 s).
Proof. exact (TRANS (@lem6145064 A B C s _77201 g f _77202 op) (@lem6145135 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145147 {A : Type'} (_77201 : A) (s : A -> Prop) : (term758 A _77201 s) = (term758 A _77201 s).
Proof. exact (eq_refl (term758 A _77201 s)). Qed.
Lemma lem6145148 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term760 A B C s _77201 g f _77202 op) = (term777 A B C g op _77201 f _77202 s).
Proof. exact (MK_COMB (@lem6145147 A _77201 s) (@lem6145146 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145152 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145153 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term777 A B C g op _77201 f _77202 s) = (term778 A B C g op _77201 f _77202 s).
Proof. exact (@lem6145152 (_77201 = _77202) (term686 A _77201 s) (term775 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145169 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145170 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term779 A B C g op _77201 f _77202 s) = (term780 A B C g op _77201 f _77202 s).
Proof. exact (@lem6145169 ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term686 A _77201 s) (term781 A B _77201 f _77202 s)). Qed.
Lemma lem6145186 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145187 {A B : Type'} (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term782 A B _77201 f _77202 s) = (term783 A B f _77201 _77202 s).
Proof. exact (@lem6145186 (term411 A B _77201 f _77202) (term686 A _77201 s) (term686 A _77202 s)). Qed.
Lemma lem6145205 {A B C : Type'} (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term784 A B C g f _77202 op) = (term784 A B C g f _77202 op).
Proof. exact (eq_refl (term784 A B C g f _77202 op)). Qed.
Lemma lem6145206 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term780 A B C g op _77201 f _77202 s) = (term785 A B C g op f _77201 _77202 s).
Proof. exact (MK_COMB (@lem6145205 A B C g f _77202 op) (@lem6145187 A B f _77201 _77202 s)). Qed.
Lemma lem6145217 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term779 A B C g op _77201 f _77202 s) = (term785 A B C g op f _77201 _77202 s).
Proof. exact (TRANS (@lem6145170 A B C g op _77201 f _77202 s) (@lem6145206 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145218 {A : Type'} (_77201 : A) (_77202 : A) : (term385 A _77201 _77202) = (term385 A _77201 _77202).
Proof. exact (eq_refl (term385 A _77201 _77202)). Qed.
Lemma lem6145219 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term778 A B C g op _77201 f _77202 s) = (term786 A B C g op f _77201 _77202 s).
Proof. exact (MK_COMB (@lem6145218 A _77201 _77202) (@lem6145217 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145230 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term777 A B C g op _77201 f _77202 s) = (term786 A B C g op f _77201 _77202 s).
Proof. exact (TRANS (@lem6145153 A B C g op _77201 f _77202 s) (@lem6145219 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145231 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term760 A B C s _77201 g f _77202 op) = (term786 A B C g op f _77201 _77202 s).
Proof. exact (TRANS (@lem6145148 A B C g op _77201 f _77202 s) (@lem6145230 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6145233 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term787 A B C s _77201 g f _77202 op) = (term788 A B C g op f _77201 _77202 s).
Proof. exact (MK_COMB (@lem6145232) (@lem6145231 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145259 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145260 {A B C : Type'} (_77201 : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term770 A B C s _77201 g f _77202 op) = (term771 A B C _77201 s g f _77202 op).
Proof. exact (@lem6145259 (term411 A B _77201 f _77202) (term686 A _77202 s) ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6145276 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6145277 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (_77202 : A) (s : A -> Prop) : (term772 A B C s g f _77202 op) = (term773 A B C g f op _77202 s).
Proof. exact (@lem6145276 ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term686 A _77202 s)). Qed.
Lemma lem6145285 {A B : Type'} (_77201 : A) (f : A -> B) (_77202 : A) : (term485 A B _77201 f _77202) = (term485 A B _77201 f _77202).
Proof. exact (eq_refl (term485 A B _77201 f _77202)). Qed.
Lemma lem6145286 {A B C : Type'} (_77201 : A) (g : B -> C) (f : A -> B) (op : type1400 C) (_77202 : A) (s : A -> Prop) : (term771 A B C _77201 s g f _77202 op) = (term774 A B C _77201 g f op _77202 s).
Proof. exact (MK_COMB (@lem6145285 A B _77201 f _77202) (@lem6145277 A B C g f op _77202 s)). Qed.
Lemma lem6145290 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145291 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term774 A B C _77201 g f op _77202 s) = (term775 A B C g op _77201 f _77202 s).
Proof. exact (@lem6145290 ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term411 A B _77201 f _77202) (term686 A _77202 s)). Qed.
Lemma lem6145311 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term771 A B C _77201 s g f _77202 op) = (term775 A B C g op _77201 f _77202 s).
Proof. exact (TRANS (@lem6145286 A B C _77201 g f op _77202 s) (@lem6145291 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145312 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term770 A B C s _77201 g f _77202 op) = (term775 A B C g op _77201 f _77202 s).
Proof. exact (TRANS (@lem6145260 A B C _77201 s g f _77202 op) (@lem6145311 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145313 {A : Type'} (_77201 : A) (s : A -> Prop) : (term758 A _77201 s) = (term758 A _77201 s).
Proof. exact (eq_refl (term758 A _77201 s)). Qed.
Lemma lem6145314 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term789 A B C s _77201 g f _77202 op) = (term779 A B C g op _77201 f _77202 s).
Proof. exact (MK_COMB (@lem6145313 A _77201 s) (@lem6145312 A B C g op _77201 f _77202 s)). Qed.
Lemma lem6145318 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145319 {A B C : Type'} (g : B -> C) (op : type1400 C) (_77201 : A) (f : A -> B) (_77202 : A) (s : A -> Prop) : (term779 A B C g op _77201 f _77202 s) = (term780 A B C g op _77201 f _77202 s).
Proof. exact (@lem6145318 ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term686 A _77201 s) (term781 A B _77201 f _77202 s)). Qed.
Lemma lem6145335 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145336 {A B : Type'} (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term782 A B _77201 f _77202 s) = (term783 A B f _77201 _77202 s).
Proof. exact (@lem6145335 (term411 A B _77201 f _77202) (term686 A _77201 s) (term686 A _77202 s)). Qed.
Lemma lem6145354 {A B C : Type'} (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term784 A B C g f _77202 op) = (term784 A B C g f _77202 op).
Proof. exact (eq_refl (term784 A B C g f _77202 op)). Qed.
Lemma lem6145355 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term780 A B C g op _77201 f _77202 s) = (term785 A B C g op f _77201 _77202 s).
Proof. exact (MK_COMB (@lem6145354 A B C g f _77202 op) (@lem6145336 A B f _77201 _77202 s)). Qed.
Lemma lem6145366 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term779 A B C g op _77201 f _77202 s) = (term785 A B C g op f _77201 _77202 s).
Proof. exact (TRANS (@lem6145319 A B C g op _77201 f _77202 s) (@lem6145355 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145367 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term789 A B C s _77201 g f _77202 op) = (term785 A B C g op f _77201 _77202 s).
Proof. exact (TRANS (@lem6145314 A B C g op _77201 f _77202 s) (@lem6145366 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145368 {A : Type'} (_77201 : A) (_77202 : A) : (term385 A _77201 _77202) = (term385 A _77201 _77202).
Proof. exact (eq_refl (term385 A _77201 _77202)). Qed.
Lemma lem6145369 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : (term790 A B C s _77201 g f _77202 op) = (term786 A B C g op f _77201 _77202 s).
Proof. exact (MK_COMB (@lem6145368 A _77201 _77202) (@lem6145367 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145380 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : ((term760 A B C s _77201 g f _77202 op) = (term790 A B C s _77201 g f _77202 op)) = ((term786 A B C g op f _77201 _77202 s) = (term786 A B C g op f _77201 _77202 s)).
Proof. exact (MK_COMB (@lem6145233 A B C g op f _77201 _77202 s) (@lem6145369 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145382 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6145383 (x : Prop) : (x = x) = True.
Proof. exact (@lem6145382 Prop x). Qed.
Lemma lem6145384 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77201 : A) (_77202 : A) (s : A -> Prop) : ((term786 A B C g op f _77201 _77202 s) = (term786 A B C g op f _77201 _77202 s)) = True.
Proof. exact (@lem6145383 (term786 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145385 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : ((term760 A B C s _77201 g f _77202 op) = (term790 A B C s _77201 g f _77202 op)) = True.
Proof. exact (TRANS (@lem6145380 A B C g op f _77201 _77202 s) (@lem6145384 A B C g op f _77201 _77202 s)). Qed.
Lemma lem6145386 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : True = ((term760 A B C s _77201 g f _77202 op) = (term790 A B C s _77201 g f _77202 op)).
Proof. exact (SYM (@lem6145385 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6145387 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term760 A B C s _77201 g f _77202 op) = (term790 A B C s _77201 g f _77202 op).
Proof. exact (EQ_MP (@lem6145386 A B C s _77201 g f _77202 op) (@lem0)). Qed.
Lemma lem6145388 {A B C : Type'} (_77201 : A) (_77202 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term790 A B C s _77201 g f _77202 op.
Proof. exact (EQ_MP (@lem6145387 A B C s _77201 g f _77202 op) (@lem6144475 A B C _77201 _77202 a s g f op h1)). Qed.
Lemma lem6145390 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6145391 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (_77201 : A) (_77202 : A) : (term790 A B C s _77201 g f _77202 op) = (term791 A B C s g f op _77201 _77202).
Proof. exact (@lem6145390 (term789 A B C s _77201 g f _77202 op) (_77201 = _77202)). Qed.
Lemma lem6145393 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6145394 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term792 A B C s _77201 g f _77202 op) = (term793 A B C s _77201 g f _77202 op).
Proof. exact (@lem6145393 (term686 A _77201 s) (term770 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6145396 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6145397 {A : Type'} (_77201 : A) (s : A -> Prop) : (term794 A _77201 s) = (term685 A _77201 s).
Proof. exact (@lem6145396 (term685 A _77201 s)). Qed.
Lemma lem6145398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6145399 {A : Type'} (_77201 : A) (s : A -> Prop) : (term795 A _77201 s) = (term714 A _77201 s).
Proof. exact (MK_COMB (@lem6145398) (@lem6145397 A _77201 s)). Qed.
Lemma lem6145401 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6145402 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term796 A B C s _77201 g f _77202 op) = (term797 A B C s _77201 g f _77202 op).
Proof. exact (@lem6145401 (term686 A _77202 s) (term769 A B C _77201 g f _77202 op)). Qed.
Lemma lem6145404 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6145405 {A : Type'} (_77202 : A) (s : A -> Prop) : (term794 A _77202 s) = (term685 A _77202 s).
Proof. exact (@lem6145404 (term685 A _77202 s)). Qed.
Lemma lem6145406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6145407 {A : Type'} (_77202 : A) (s : A -> Prop) : (term795 A _77202 s) = (term714 A _77202 s).
Proof. exact (MK_COMB (@lem6145406) (@lem6145405 A _77202 s)). Qed.
Lemma lem6145409 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6145410 {A B C : Type'} (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term798 A B C _77201 g f _77202 op) = (term799 A B C _77201 g f _77202 op).
Proof. exact (@lem6145409 (term411 A B _77201 f _77202) ((term407 A B C g f _77202) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6145412 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6145413 {A B : Type'} (_77201 : A) (f : A -> B) (_77202 : A) : (term515 A B _77201 f _77202) = ((@I (A -> B) f _77201) = (@I (A -> B) f _77202)).
Proof. exact (@lem6145412 ((@I (A -> B) f _77201) = (@I (A -> B) f _77202))). Qed.
Lemma lem6145414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6145415 {A B : Type'} (_77201 : A) (f : A -> B) (_77202 : A) : (term516 A B _77201 f _77202) = (term517 A B _77201 f _77202).
Proof. exact (MK_COMB (@lem6145414) (@lem6145413 A B _77201 f _77202)). Qed.
Lemma lem6145416 {A B C : Type'} (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term697 A B C g f _77202 op) = (term697 A B C g f _77202 op).
Proof. exact (eq_refl (term697 A B C g f _77202 op)). Qed.
Lemma lem6145417 {A B C : Type'} (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term799 A B C _77201 g f _77202 op) = (term800 A B C _77201 g f _77202 op).
Proof. exact (MK_COMB (@lem6145415 A B _77201 f _77202) (@lem6145416 A B C g f _77202 op)). Qed.
Lemma lem6145418 {A B C : Type'} (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term798 A B C _77201 g f _77202 op) = (term800 A B C _77201 g f _77202 op).
Proof. exact (TRANS (@lem6145410 A B C _77201 g f _77202 op) (@lem6145417 A B C _77201 g f _77202 op)). Qed.
Lemma lem6145419 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term797 A B C s _77201 g f _77202 op) = (term801 A B C s _77201 g f _77202 op).
Proof. exact (MK_COMB (@lem6145407 A _77202 s) (@lem6145418 A B C _77201 g f _77202 op)). Qed.
Lemma lem6145420 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term796 A B C s _77201 g f _77202 op) = (term801 A B C s _77201 g f _77202 op).
Proof. exact (TRANS (@lem6145402 A B C s _77201 g f _77202 op) (@lem6145419 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6145421 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term793 A B C s _77201 g f _77202 op) = (term802 A B C s _77201 g f _77202 op).
Proof. exact (MK_COMB (@lem6145399 A _77201 s) (@lem6145420 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6145422 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term792 A B C s _77201 g f _77202 op) = (term802 A B C s _77201 g f _77202 op).
Proof. exact (TRANS (@lem6145394 A B C s _77201 g f _77202 op) (@lem6145421 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6145423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6145424 {A B C : Type'} (s : A -> Prop) (_77201 : A) (g : B -> C) (f : A -> B) (_77202 : A) (op : type1400 C) : (term803 A B C s _77201 g f _77202 op) = (term804 A B C s _77201 g f _77202 op).
Proof. exact (MK_COMB (@lem6145423) (@lem6145422 A B C s _77201 g f _77202 op)). Qed.
Lemma lem6145425 {A : Type'} (_77201 : A) (_77202 : A) : (_77201 = _77202) = (_77201 = _77202).
Proof. exact (eq_refl (_77201 = _77202)). Qed.
Lemma lem6145426 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (_77201 : A) (_77202 : A) : (term791 A B C s g f op _77201 _77202) = (term805 A B C s g f op _77201 _77202).
Proof. exact (MK_COMB (@lem6145424 A B C s _77201 g f _77202 op) (@lem6145425 A _77201 _77202)). Qed.
Lemma lem6145427 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (_77201 : A) (_77202 : A) : (term790 A B C s _77201 g f _77202 op) = (term805 A B C s g f op _77201 _77202).
Proof. exact (TRANS (@lem6145391 A B C s g f op _77201 _77202) (@lem6145426 A B C s g f op _77201 _77202)). Qed.
Lemma lem6145429 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term800 A B C x' g f y op.
Proof. exact (conj (@lem6145040 A B C s x' g f y op h1) (@lem6145047 A B C s x' g f y op h1)). Qed.
Lemma lem6145430 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term801 A B C s x' g f y op.
Proof. exact (conj (@lem6145033 A B C s x' g f y op h1) (@lem6145429 A B C s x' g f y op h1)). Qed.
Lemma lem6145431 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term802 A B C s x' g f y op.
Proof. exact (conj (@lem6145026 A B C s x' g f y op h1) (@lem6145430 A B C s x' g f y op h1)). Qed.
Lemma lem6145433 {A B C : Type'} (_77201 : A) (_77202 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term805 A B C s g f op _77201 _77202.
Proof. exact (EQ_MP (@lem6145427 A B C s g f op _77201 _77202) (@lem6145388 A B C _77201 _77202 a s g f op h1)). Qed.
Lemma lem6145434 {A B C : Type'} (_77201 : A) (_77202 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term805 A B C s g f op _77201 _77202.
Proof. exact (@lem6145433 A B C _77201 _77202 a s g f op h1). Qed.
Lemma lem6145435 {A B C : Type'} (x' : A) (y : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term805 A B C s g f op x' y.
Proof. exact (@lem6145434 A B C x' y a s g f op h1). Qed.
Lemma lem6145438 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term718 A B C s x' g f y op) : x' = y.
Proof. exact (@lem6145435 A B C x' y a s g f op h1 (@lem6145431 A B C s x' g f y op h2)). Qed.
Lemma lem6145439 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term718 A B C s x' g f y op) : term524 A x' y.
Proof. exact (fun h0 : term389 A x' y => @lem6145438 A B C a s x' g f y op h1 h2). Qed.
Lemma lem6145441 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145442 {A : Type'} (x' : A) (y : A) : (term524 A x' y) = (x' = y).
Proof. exact (@lem6145441 (x' = y)). Qed.
Lemma lem6145443 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term718 A B C s x' g f y op) : x' = y.
Proof. exact (EQ_MP (@lem6145442 A x' y) (@lem6145439 A B C a s x' g f y op h1 h2)). Qed.
Lemma lem6145446 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6145448 {A : Type'} (x' : A) (y : A) : (term389 A x' y) = (term525 A x' y).
Proof. exact (@lem6145446 (x' = y)). Qed.
Lemma lem6145451 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term718 A B C s x' g f y op) : term525 A x' y.
Proof. exact (EQ_MP (@lem6145448 A x' y) (@lem6144335 A B C s x' g f y op h1)). Qed.
Lemma lem6145454 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term718 A B C s x' g f y op) : False.
Proof. exact (@lem6145451 A B C s x' g f y op h2 (@lem6145443 A B C a s x' g f y op h1 h2)). Qed.
Lemma lem6145455 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term718 A B C s x' g f y op) : term526.
Proof. exact (fun h0 : ~ False => @lem6145454 A B C a s x' g f y op h1 h2). Qed.
Lemma lem6145457 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145458 : term526 = False.
Proof. exact (@lem6145457 False). Qed.
Lemma lem6145459 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) (h1 : term270 A B C a s g f op) (h2 : term718 A B C s x' g f y op) : False.
Proof. exact (EQ_MP (@lem6145458) (@lem6145455 A B C a s x' g f y op h1 h2)). Qed.
Lemma lem6145498 {A : Type'} : (@I ((A -> Prop) -> Prop)) = (@I ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop))). Qed.
Lemma lem6145499 {A : Type'} (_77301 : type686 A) (_77303 : type686 A) (h1 : _77301 = _77303) : _77301 = _77303.
Proof. exact (h1). Qed.
Lemma lem6145500 {A : Type'} (_77302 : A -> Prop) (_77304 : A -> Prop) (h1 : _77302 = _77304) : _77302 = _77304.
Proof. exact (h1). Qed.
Lemma lem6145501 {A : Type'} (_77301 : type686 A) (_77303 : type686 A) (h1 : _77301 = _77303) : (@I ((A -> Prop) -> Prop) _77301) = (@I ((A -> Prop) -> Prop) _77303).
Proof. exact (MK_COMB (@lem6145498 A) (@lem6145499 A _77301 _77303 h1)). Qed.
Lemma lem6145502 {A : Type'} (_77302 : A -> Prop) (_77304 : A -> Prop) (_77301 : type686 A) (_77303 : type686 A) (h1 : _77302 = _77304) (h2 : _77301 = _77303) : (@I ((A -> Prop) -> Prop) _77301 _77302) = (@I ((A -> Prop) -> Prop) _77303 _77304).
Proof. exact (MK_COMB (@lem6145501 A _77301 _77303 h2) (@lem6145500 A _77302 _77304 h1)). Qed.
Lemma lem6145504 (b : Prop) (a : Prop) : term806 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem6145505 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : term807 A _77303 _77304 _77301 _77302.
Proof. exact (@lem6145504 (@I ((A -> Prop) -> Prop) _77303 _77304) (@I ((A -> Prop) -> Prop) _77301 _77302)). Qed.
Lemma lem6145506 {A : Type'} (_77302 : A -> Prop) (_77304 : A -> Prop) (_77301 : type686 A) (_77303 : type686 A) (h1 : _77302 = _77304) (h2 : _77301 = _77303) : term808 A _77303 _77304 _77301 _77302.
Proof. exact (@lem6145505 A _77303 _77304 _77301 _77302 (@lem6145502 A _77302 _77304 _77301 _77303 h1 h2)). Qed.
Lemma lem6145507 {A : Type'} (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) (_77304 : A -> Prop) (h1 : _77302 = _77304) : term809 A _77303 _77304 _77301 _77302.
Proof. exact (fun h0 : _77301 = _77303 => @lem6145506 A _77302 _77304 _77301 _77303 h1 h0). Qed.
Lemma lem6145509 (a : Prop) (b : Prop) : (a -> b) = (term810 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6145510 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term809 A _77303 _77304 _77301 _77302) = (term811 A _77303 _77304 _77301 _77302).
Proof. exact (@lem6145509 (_77301 = _77303) (term808 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6145511 {A : Type'} (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) (_77304 : A -> Prop) (h1 : _77302 = _77304) : term811 A _77303 _77304 _77301 _77302.
Proof. exact (EQ_MP (@lem6145510 A _77303 _77304 _77301 _77302) (@lem6145507 A _77303 _77301 _77302 _77304 h1)). Qed.
Lemma lem6145512 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : term812 A _77303 _77304 _77301 _77302.
Proof. exact (fun h0 : _77302 = _77304 => @lem6145511 A _77303 _77301 _77302 _77304 h0). Qed.
Lemma lem6145514 (a : Prop) (b : Prop) : (a -> b) = (term810 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6145515 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term812 A _77303 _77304 _77301 _77302) = (term813 A _77303 _77304 _77301 _77302).
Proof. exact (@lem6145514 (_77302 = _77304) (term811 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6145516 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : term813 A _77303 _77304 _77301 _77302.
Proof. exact (EQ_MP (@lem6145515 A _77303 _77304 _77301 _77302) (@lem6145512 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6145851 {A : Type'} : (@I (A -> (A -> Prop) -> Prop)) = (@I (A -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@I (A -> (A -> Prop) -> Prop))). Qed.
Lemma lem6145852 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (h1 : _77393 = _77395) : _77393 = _77395.
Proof. exact (h1). Qed.
Lemma lem6145853 {A : Type'} (_77394 : A) (_77396 : A) (h1 : _77394 = _77396) : _77394 = _77396.
Proof. exact (h1). Qed.
Lemma lem6145854 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (h1 : _77393 = _77395) : (@I (A -> (A -> Prop) -> Prop) _77393) = (@I (A -> (A -> Prop) -> Prop) _77395).
Proof. exact (MK_COMB (@lem6145851 A) (@lem6145852 A _77393 _77395 h1)). Qed.
Lemma lem6145855 {A : Type'} (_77394 : A) (_77396 : A) (_77393 : type1364 A) (_77395 : type1364 A) (h1 : _77394 = _77396) (h2 : _77393 = _77395) : (@I (A -> (A -> Prop) -> Prop) _77393 _77394) = (@I (A -> (A -> Prop) -> Prop) _77395 _77396).
Proof. exact (MK_COMB (@lem6145854 A _77393 _77395 h2) (@lem6145853 A _77394 _77396 h1)). Qed.
Lemma lem6145856 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (_77394 : A) (_77396 : A) (h1 : _77394 = _77396) : term814 A _77393 _77394 _77395 _77396.
Proof. exact (fun h0 : _77393 = _77395 => @lem6145855 A _77394 _77396 _77393 _77395 h1 h0). Qed.
Lemma lem6145858 (a : Prop) (b : Prop) : (a -> b) = (term810 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6145859 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : (term814 A _77393 _77394 _77395 _77396) = (term815 A _77393 _77394 _77395 _77396).
Proof. exact (@lem6145858 (_77393 = _77395) ((@I (A -> (A -> Prop) -> Prop) _77393 _77394) = (@I (A -> (A -> Prop) -> Prop) _77395 _77396))). Qed.
Lemma lem6145860 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (_77394 : A) (_77396 : A) (h1 : _77394 = _77396) : term815 A _77393 _77394 _77395 _77396.
Proof. exact (EQ_MP (@lem6145859 A _77393 _77394 _77395 _77396) (@lem6145856 A _77393 _77395 _77394 _77396 h1)). Qed.
Lemma lem6145861 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : term816 A _77393 _77394 _77395 _77396.
Proof. exact (fun h0 : _77394 = _77396 => @lem6145860 A _77393 _77395 _77394 _77396 h0). Qed.
Lemma lem6145863 (a : Prop) (b : Prop) : (a -> b) = (term810 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6145864 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : (term816 A _77393 _77394 _77395 _77396) = (term817 A _77393 _77394 _77395 _77396).
Proof. exact (@lem6145863 (_77394 = _77396) (term815 A _77393 _77394 _77395 _77396)). Qed.
Lemma lem6145865 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : term817 A _77393 _77394 _77395 _77396.
Proof. exact (EQ_MP (@lem6145864 A _77393 _77394 _77395 _77396) (@lem6145861 A _77393 _77394 _77395 _77396)). Qed.
Lemma lem6145881 {B : Type'} (x : B) (y : B) (z : B) : term527 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem6145931 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term685 A x s.
Proof. exact (proj2 (@lem6140938 A B a f x s h1)). Qed.
Lemma lem6145932 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term766 A x s.
Proof. exact (fun h0 : term686 A x s => @lem6145931 A B a f x s h1). Qed.
Lemma lem6145934 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145935 {A : Type'} (x : A) (s : A -> Prop) : (term766 A x s) = (term685 A x s).
Proof. exact (@lem6145934 (term685 A x s)). Qed.
Lemma lem6145936 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term685 A x s.
Proof. exact (EQ_MP (@lem6145935 A x s) (@lem6145932 A B a f x s h1)). Qed.
Lemma lem6145938 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem6145939 {A : Type'} (x : A) : x = x.
Proof. exact (@lem6145938 A x). Qed.
Lemma lem6145940 {A : Type'} (a : A) : a = a.
Proof. exact (@lem6145939 A a). Qed.
Lemma lem6145941 {A : Type'} (a : A) : term818 A a.
Proof. exact (fun h0 : term819 A a => @lem6145940 A a). Qed.
Lemma lem6145943 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145944 {A : Type'} (a : A) : (term818 A a) = (a = a).
Proof. exact (@lem6145943 (a = a)). Qed.
Lemma lem6145945 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem6145944 A a) (@lem6145941 A a)). Qed.
Lemma lem6145947 {A : Type'} (x : type1364 A) : x = x.
Proof. exact (@lem21386 (type1364 A) x). Qed.
Lemma lem6145948 {A : Type'} (x : type1364 A) : x = x.
Proof. exact (@lem6145947 A x). Qed.
Lemma lem6145949 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (@lem6145948 A (@IN A)). Qed.
Lemma lem6145950 {A : Type'} : term820 A.
Proof. exact (fun h0 : term821 A => @lem6145949 A). Qed.
Lemma lem6145952 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145953 {A : Type'} : (term820 A) = ((@IN A) = (@IN A)).
Proof. exact (@lem6145952 ((@IN A) = (@IN A))). Qed.
Lemma lem6145954 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (EQ_MP (@lem6145953 A) (@lem6145950 A)). Qed.
Lemma lem6145956 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem6145957 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem6145956 A x). Qed.
Lemma lem6145958 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem6145957 A s). Qed.
Lemma lem6145959 {A : Type'} (s : A -> Prop) : term822 A s.
Proof. exact (fun h0 : term823 A s => @lem6145958 A s). Qed.
Lemma lem6145961 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145962 {A : Type'} (s : A -> Prop) : (term822 A s) = (s = s).
Proof. exact (@lem6145961 (s = s)). Qed.
Lemma lem6145963 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem6145962 A s) (@lem6145959 A s)). Qed.
Lemma lem6145965 {A : Type'} (a : A) (s : A -> Prop) (h1 : term180 A a s) : term686 A a s.
Proof. exact (EQ_MP (@lem6139861 A a s) (@lem6139208 A a s h1)). Qed.
Lemma lem6145966 {A : Type'} (a : A) (s : A -> Prop) (h1 : term180 A a s) : term824 A a s.
Proof. exact (fun h0 : term685 A a s => @lem6145965 A a s h1). Qed.
Lemma lem6145968 (p : Prop) : (term478 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6145969 {A : Type'} (a : A) (s : A -> Prop) : (term824 A a s) = (term686 A a s).
Proof. exact (@lem6145968 (term685 A a s)). Qed.
Lemma lem6145970 {A : Type'} (a : A) (s : A -> Prop) (h1 : term180 A a s) : term686 A a s.
Proof. exact (EQ_MP (@lem6145969 A a s) (@lem6145966 A a s h1)). Qed.
Lemma lem6145972 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term685 A x s.
Proof. exact (proj2 (@lem6140938 A B a f x s h1)). Qed.
Lemma lem6145973 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term766 A x s.
Proof. exact (fun h0 : term686 A x s => @lem6145972 A B a f x s h1). Qed.
Lemma lem6145975 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6145976 {A : Type'} (x : A) (s : A -> Prop) : (term766 A x s) = (term685 A x s).
Proof. exact (@lem6145975 (term685 A x s)). Qed.
Lemma lem6145977 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term685 A x s.
Proof. exact (EQ_MP (@lem6145976 A x s) (@lem6145973 A B a f x s h1)). Qed.
Lemma lem6145995 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6145996 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term811 A _77303 _77304 _77301 _77302) = (term825 A _77304 _77303 _77301 _77302).
Proof. exact (@lem6145995 (@I ((A -> Prop) -> Prop) _77303 _77304) (term826 A _77301 _77303) (term827 A _77301 _77302)). Qed.
Lemma lem6146014 {A : Type'} (_77302 : A -> Prop) (_77304 : A -> Prop) : (term828 A _77302 _77304) = (term828 A _77302 _77304).
Proof. exact (eq_refl (term828 A _77302 _77304)). Qed.
Lemma lem6146015 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term813 A _77303 _77304 _77301 _77302) = (term829 A _77304 _77303 _77301 _77302).
Proof. exact (MK_COMB (@lem6146014 A _77302 _77304) (@lem6145996 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146019 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146020 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term829 A _77304 _77303 _77301 _77302) = (term830 A _77304 _77303 _77301 _77302).
Proof. exact (@lem6146019 (@I ((A -> Prop) -> Prop) _77303 _77304) (term831 A _77302 _77304) (term832 A _77303 _77301 _77302)). Qed.
Lemma lem6146050 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term813 A _77303 _77304 _77301 _77302) = (term830 A _77304 _77303 _77301 _77302).
Proof. exact (TRANS (@lem6146015 A _77304 _77303 _77301 _77302) (@lem6146020 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6146052 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term833 A _77303 _77304 _77301 _77302) = (term834 A _77304 _77303 _77301 _77302).
Proof. exact (MK_COMB (@lem6146051) (@lem6146050 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146056 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146057 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term835 A _77303 _77304 _77301 _77302) = (term813 A _77303 _77304 _77301 _77302).
Proof. exact (@lem6146056 (term831 A _77302 _77304) (term826 A _77301 _77303) (term808 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146073 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146074 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term811 A _77303 _77304 _77301 _77302) = (term825 A _77304 _77303 _77301 _77302).
Proof. exact (@lem6146073 (@I ((A -> Prop) -> Prop) _77303 _77304) (term826 A _77301 _77303) (term827 A _77301 _77302)). Qed.
Lemma lem6146092 {A : Type'} (_77302 : A -> Prop) (_77304 : A -> Prop) : (term828 A _77302 _77304) = (term828 A _77302 _77304).
Proof. exact (eq_refl (term828 A _77302 _77304)). Qed.
Lemma lem6146093 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term813 A _77303 _77304 _77301 _77302) = (term829 A _77304 _77303 _77301 _77302).
Proof. exact (MK_COMB (@lem6146092 A _77302 _77304) (@lem6146074 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146097 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146098 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term829 A _77304 _77303 _77301 _77302) = (term830 A _77304 _77303 _77301 _77302).
Proof. exact (@lem6146097 (@I ((A -> Prop) -> Prop) _77303 _77304) (term831 A _77302 _77304) (term832 A _77303 _77301 _77302)). Qed.
Lemma lem6146128 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term813 A _77303 _77304 _77301 _77302) = (term830 A _77304 _77303 _77301 _77302).
Proof. exact (TRANS (@lem6146093 A _77304 _77303 _77301 _77302) (@lem6146098 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146129 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : (term835 A _77303 _77304 _77301 _77302) = (term830 A _77304 _77303 _77301 _77302).
Proof. exact (TRANS (@lem6146057 A _77303 _77304 _77301 _77302) (@lem6146128 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146130 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : ((term813 A _77303 _77304 _77301 _77302) = (term835 A _77303 _77304 _77301 _77302)) = ((term830 A _77304 _77303 _77301 _77302) = (term830 A _77304 _77303 _77301 _77302)).
Proof. exact (MK_COMB (@lem6146052 A _77304 _77303 _77301 _77302) (@lem6146129 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146132 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6146133 (x : Prop) : (x = x) = True.
Proof. exact (@lem6146132 Prop x). Qed.
Lemma lem6146134 {A : Type'} (_77304 : A -> Prop) (_77303 : type686 A) (_77301 : type686 A) (_77302 : A -> Prop) : ((term830 A _77304 _77303 _77301 _77302) = (term830 A _77304 _77303 _77301 _77302)) = True.
Proof. exact (@lem6146133 (term830 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146135 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : ((term813 A _77303 _77304 _77301 _77302) = (term835 A _77303 _77304 _77301 _77302)) = True.
Proof. exact (TRANS (@lem6146130 A _77304 _77303 _77301 _77302) (@lem6146134 A _77304 _77303 _77301 _77302)). Qed.
Lemma lem6146136 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : True = ((term813 A _77303 _77304 _77301 _77302) = (term835 A _77303 _77304 _77301 _77302)).
Proof. exact (SYM (@lem6146135 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146137 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term813 A _77303 _77304 _77301 _77302) = (term835 A _77303 _77304 _77301 _77302).
Proof. exact (EQ_MP (@lem6146136 A _77303 _77304 _77301 _77302) (@lem0)). Qed.
Lemma lem6146138 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : term835 A _77303 _77304 _77301 _77302.
Proof. exact (EQ_MP (@lem6146137 A _77303 _77304 _77301 _77302) (@lem6145516 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146140 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6146141 {A : Type'} (_77304 : A -> Prop) (_77302 : A -> Prop) (_77301 : type686 A) (_77303 : type686 A) : (term835 A _77303 _77304 _77301 _77302) = (term836 A _77304 _77302 _77301 _77303).
Proof. exact (@lem6146140 (term837 A _77303 _77304 _77301 _77302) (term826 A _77301 _77303)). Qed.
Lemma lem6146143 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6146144 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term838 A _77303 _77304 _77301 _77302) = (term839 A _77303 _77304 _77301 _77302).
Proof. exact (@lem6146143 (term831 A _77302 _77304) (term808 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146146 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6146147 {A : Type'} (_77302 : A -> Prop) (_77304 : A -> Prop) : (term840 A _77302 _77304) = (_77302 = _77304).
Proof. exact (@lem6146146 (_77302 = _77304)). Qed.
Lemma lem6146148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6146149 {A : Type'} (_77302 : A -> Prop) (_77304 : A -> Prop) : (term841 A _77302 _77304) = (term842 A _77302 _77304).
Proof. exact (MK_COMB (@lem6146148) (@lem6146147 A _77302 _77304)). Qed.
Lemma lem6146151 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6146152 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term843 A _77303 _77304 _77301 _77302) = (term844 A _77303 _77304 _77301 _77302).
Proof. exact (@lem6146151 (@I ((A -> Prop) -> Prop) _77303 _77304) (term827 A _77301 _77302)). Qed.
Lemma lem6146154 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6146155 {A : Type'} (_77301 : type686 A) (_77302 : A -> Prop) : (term845 A _77301 _77302) = (@I ((A -> Prop) -> Prop) _77301 _77302).
Proof. exact (@lem6146154 (@I ((A -> Prop) -> Prop) _77301 _77302)). Qed.
Lemma lem6146156 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) : (term846 A _77303 _77304) = (term846 A _77303 _77304).
Proof. exact (eq_refl (term846 A _77303 _77304)). Qed.
Lemma lem6146157 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term844 A _77303 _77304 _77301 _77302) = (term847 A _77303 _77304 _77301 _77302).
Proof. exact (MK_COMB (@lem6146156 A _77303 _77304) (@lem6146155 A _77301 _77302)). Qed.
Lemma lem6146158 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term843 A _77303 _77304 _77301 _77302) = (term847 A _77303 _77304 _77301 _77302).
Proof. exact (TRANS (@lem6146152 A _77303 _77304 _77301 _77302) (@lem6146157 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146159 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term839 A _77303 _77304 _77301 _77302) = (term848 A _77303 _77304 _77301 _77302).
Proof. exact (MK_COMB (@lem6146149 A _77302 _77304) (@lem6146158 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146160 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term838 A _77303 _77304 _77301 _77302) = (term848 A _77303 _77304 _77301 _77302).
Proof. exact (TRANS (@lem6146144 A _77303 _77304 _77301 _77302) (@lem6146159 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146161 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6146162 {A : Type'} (_77303 : type686 A) (_77304 : A -> Prop) (_77301 : type686 A) (_77302 : A -> Prop) : (term849 A _77303 _77304 _77301 _77302) = (term850 A _77303 _77304 _77301 _77302).
Proof. exact (MK_COMB (@lem6146161) (@lem6146160 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146163 {A : Type'} (_77301 : type686 A) (_77303 : type686 A) : (term826 A _77301 _77303) = (term826 A _77301 _77303).
Proof. exact (eq_refl (term826 A _77301 _77303)). Qed.
Lemma lem6146164 {A : Type'} (_77304 : A -> Prop) (_77302 : A -> Prop) (_77301 : type686 A) (_77303 : type686 A) : (term836 A _77304 _77302 _77301 _77303) = (term851 A _77304 _77302 _77301 _77303).
Proof. exact (MK_COMB (@lem6146162 A _77303 _77304 _77301 _77302) (@lem6146163 A _77301 _77303)). Qed.
Lemma lem6146165 {A : Type'} (_77304 : A -> Prop) (_77302 : A -> Prop) (_77301 : type686 A) (_77303 : type686 A) : (term835 A _77303 _77304 _77301 _77302) = (term851 A _77304 _77302 _77301 _77303).
Proof. exact (TRANS (@lem6146141 A _77304 _77302 _77301 _77303) (@lem6146164 A _77304 _77302 _77301 _77303)). Qed.
Lemma lem6146167 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term852 A a x s.
Proof. exact (conj (@lem6145970 A a s h1) (@lem6145977 A B a f x s h2)). Qed.
Lemma lem6146168 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term853 A a x s.
Proof. exact (conj (@lem6145963 A s) (@lem6146167 A B a f x s h1 h2)). Qed.
Lemma lem6146170 {A : Type'} (_77304 : A -> Prop) (_77302 : A -> Prop) (_77301 : type686 A) (_77303 : type686 A) : term851 A _77304 _77302 _77301 _77303.
Proof. exact (EQ_MP (@lem6146165 A _77304 _77302 _77301 _77303) (@lem6146138 A _77303 _77304 _77301 _77302)). Qed.
Lemma lem6146171 {A : Type'} (_77304 : A -> Prop) (_77302 : A -> Prop) (_77301 : type686 A) (_77303 : type686 A) : term851 A _77304 _77302 _77301 _77303.
Proof. exact (@lem6146170 A _77304 _77302 _77301 _77303). Qed.
Lemma lem6146172 {A : Type'} (s : A -> Prop) (x : A) (a : A) : term854 A s x a.
Proof. exact (@lem6146171 A s s (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (@I (A -> (A -> Prop) -> Prop) (@IN A) a)). Qed.
Lemma lem6146175 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term855 A x a.
Proof. exact (@lem6146172 A s x a (@lem6146168 A B a f x s h1 h2)). Qed.
Lemma lem6146176 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term856 A x a.
Proof. exact (fun h0 : (@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) a) => @lem6146175 A B a f x s h1 h2). Qed.
Lemma lem6146178 (p : Prop) : (term478 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6146179 {A : Type'} (x : A) (a : A) : (term856 A x a) = (term855 A x a).
Proof. exact (@lem6146178 ((@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) a))). Qed.
Lemma lem6146180 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term855 A x a.
Proof. exact (EQ_MP (@lem6146179 A x a) (@lem6146176 A B a f x s h1 h2)). Qed.
Lemma lem6146182 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6146183 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (_77394 : A) (_77396 : A) : (term817 A _77393 _77394 _77395 _77396) = (term857 A _77393 _77395 _77394 _77396).
Proof. exact (@lem6146182 (term815 A _77393 _77394 _77395 _77396) (term389 A _77394 _77396)). Qed.
Lemma lem6146185 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6146186 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : (term858 A _77393 _77394 _77395 _77396) = (term859 A _77393 _77394 _77395 _77396).
Proof. exact (@lem6146185 (term860 A _77393 _77395) ((@I (A -> (A -> Prop) -> Prop) _77393 _77394) = (@I (A -> (A -> Prop) -> Prop) _77395 _77396))). Qed.
Lemma lem6146188 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6146189 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) : (term861 A _77393 _77395) = (_77393 = _77395).
Proof. exact (@lem6146188 (_77393 = _77395)). Qed.
Lemma lem6146190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6146191 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) : (term862 A _77393 _77395) = (term863 A _77393 _77395).
Proof. exact (MK_COMB (@lem6146190) (@lem6146189 A _77393 _77395)). Qed.
Lemma lem6146192 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : (term864 A _77393 _77394 _77395 _77396) = (term864 A _77393 _77394 _77395 _77396).
Proof. exact (eq_refl (term864 A _77393 _77394 _77395 _77396)). Qed.
Lemma lem6146193 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : (term859 A _77393 _77394 _77395 _77396) = (term865 A _77393 _77394 _77395 _77396).
Proof. exact (MK_COMB (@lem6146191 A _77393 _77395) (@lem6146192 A _77393 _77394 _77395 _77396)). Qed.
Lemma lem6146194 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : (term858 A _77393 _77394 _77395 _77396) = (term865 A _77393 _77394 _77395 _77396).
Proof. exact (TRANS (@lem6146186 A _77393 _77394 _77395 _77396) (@lem6146193 A _77393 _77394 _77395 _77396)). Qed.
Lemma lem6146195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6146196 {A : Type'} (_77393 : type1364 A) (_77394 : A) (_77395 : type1364 A) (_77396 : A) : (term866 A _77393 _77394 _77395 _77396) = (term867 A _77393 _77394 _77395 _77396).
Proof. exact (MK_COMB (@lem6146195) (@lem6146194 A _77393 _77394 _77395 _77396)). Qed.
Lemma lem6146197 {A : Type'} (_77394 : A) (_77396 : A) : (term389 A _77394 _77396) = (term389 A _77394 _77396).
Proof. exact (eq_refl (term389 A _77394 _77396)). Qed.
Lemma lem6146198 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (_77394 : A) (_77396 : A) : (term857 A _77393 _77395 _77394 _77396) = (term868 A _77393 _77395 _77394 _77396).
Proof. exact (MK_COMB (@lem6146196 A _77393 _77394 _77395 _77396) (@lem6146197 A _77394 _77396)). Qed.
Lemma lem6146199 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (_77394 : A) (_77396 : A) : (term817 A _77393 _77394 _77395 _77396) = (term868 A _77393 _77395 _77394 _77396).
Proof. exact (TRANS (@lem6146183 A _77393 _77395 _77394 _77396) (@lem6146198 A _77393 _77395 _77394 _77396)). Qed.
Lemma lem6146201 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term869 A x a.
Proof. exact (conj (@lem6145954 A) (@lem6146180 A B a f x s h1 h2)). Qed.
Lemma lem6146203 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (_77394 : A) (_77396 : A) : term868 A _77393 _77395 _77394 _77396.
Proof. exact (EQ_MP (@lem6146199 A _77393 _77395 _77394 _77396) (@lem6145865 A _77393 _77394 _77395 _77396)). Qed.
Lemma lem6146204 {A : Type'} (_77393 : type1364 A) (_77395 : type1364 A) (_77394 : A) (_77396 : A) : term868 A _77393 _77395 _77394 _77396.
Proof. exact (@lem6146203 A _77393 _77395 _77394 _77396). Qed.
Lemma lem6146205 {A : Type'} (x : A) (a : A) : term870 A x a.
Proof. exact (@lem6146204 A (@IN A) (@IN A) x a). Qed.
Lemma lem6146208 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term389 A x a.
Proof. exact (@lem6146205 A x a (@lem6146201 A B a f x s h1 h2)). Qed.
Lemma lem6146209 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term871 A x a.
Proof. exact (fun h0 : x = a => @lem6146208 A B a f x s h1 h2). Qed.
Lemma lem6146211 (p : Prop) : (term478 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6146212 {A : Type'} (x : A) (a : A) : (term871 A x a) = (term389 A x a).
Proof. exact (@lem6146211 (x = a)). Qed.
Lemma lem6146213 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term389 A x a.
Proof. exact (EQ_MP (@lem6146212 A x a) (@lem6146209 A B a f x s h1 h2)). Qed.
Lemma lem6146215 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : (@I (A -> B) f a) = (@I (A -> B) f x).
Proof. exact (proj1 (@lem6140938 A B a f x s h1)). Qed.
Lemma lem6146216 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term476 A B a f x.
Proof. exact (fun h0 : term411 A B a f x => @lem6146215 A B a f x s h1). Qed.
Lemma lem6146218 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6146219 {A B : Type'} (a : A) (f : A -> B) (x : A) : (term476 A B a f x) = ((@I (A -> B) f a) = (@I (A -> B) f x)).
Proof. exact (@lem6146218 ((@I (A -> B) f a) = (@I (A -> B) f x))). Qed.
Lemma lem6146220 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : (@I (A -> B) f a) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem6146219 A B a f x) (@lem6146216 A B a f x s h1)). Qed.
Lemma lem6146222 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem6146223 {B : Type'} (x : B) : x = x.
Proof. exact (@lem6146222 B x). Qed.
Lemma lem6146224 {A B : Type'} (f : A -> B) (a : A) : (@I (A -> B) f a) = (@I (A -> B) f a).
Proof. exact (@lem6146223 B (@I (A -> B) f a)). Qed.
Lemma lem6146225 {A B : Type'} (f : A -> B) (a : A) : term872 A B f a.
Proof. exact (fun h0 : term873 A B f a => @lem6146224 A B f a). Qed.
Lemma lem6146227 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6146228 {A B : Type'} (f : A -> B) (a : A) : (term872 A B f a) = ((@I (A -> B) f a) = (@I (A -> B) f a)).
Proof. exact (@lem6146227 ((@I (A -> B) f a) = (@I (A -> B) f a))). Qed.
Lemma lem6146229 {A B : Type'} (f : A -> B) (a : A) : (@I (A -> B) f a) = (@I (A -> B) f a).
Proof. exact (EQ_MP (@lem6146228 A B f a) (@lem6146225 A B f a)). Qed.
Lemma lem6146247 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6146248 {B : Type'} (y : B) (x : B) (z : B) : (term532 B x y z) = (term533 B y x z).
Proof. exact (@lem6146247 (y = z) (term389 B x z)). Qed.
Lemma lem6146258 {B : Type'} (x : B) (y : B) : (term534 B x y) = (term534 B x y).
Proof. exact (eq_refl (term534 B x y)). Qed.
Lemma lem6146259 {B : Type'} (y : B) (x : B) (z : B) : (term527 B x y z) = (term535 B y x z).
Proof. exact (MK_COMB (@lem6146258 B x y) (@lem6146248 B y x z)). Qed.
Lemma lem6146263 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146264 {B : Type'} (y : B) (x : B) (z : B) : (term535 B y x z) = (term536 B y x z).
Proof. exact (@lem6146263 (y = z) (term389 B x y) (term389 B x z)). Qed.
Lemma lem6146286 {B : Type'} (y : B) (x : B) (z : B) : (term527 B x y z) = (term536 B y x z).
Proof. exact (TRANS (@lem6146259 B y x z) (@lem6146264 B y x z)). Qed.
Lemma lem6146287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6146288 {B : Type'} (y : B) (x : B) (z : B) : (term537 B x y z) = (term538 B y x z).
Proof. exact (MK_COMB (@lem6146287) (@lem6146286 B y x z)). Qed.
Lemma lem6146310 {B : Type'} (y : B) (x : B) (z : B) : (term536 B y x z) = (term536 B y x z).
Proof. exact (eq_refl (term536 B y x z)). Qed.
Lemma lem6146311 {B : Type'} (y : B) (x : B) (z : B) : ((term527 B x y z) = (term536 B y x z)) = ((term536 B y x z) = (term536 B y x z)).
Proof. exact (MK_COMB (@lem6146288 B y x z) (@lem6146310 B y x z)). Qed.
Lemma lem6146313 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6146314 (x : Prop) : (x = x) = True.
Proof. exact (@lem6146313 Prop x). Qed.
Lemma lem6146315 {B : Type'} (y : B) (x : B) (z : B) : ((term536 B y x z) = (term536 B y x z)) = True.
Proof. exact (@lem6146314 (term536 B y x z)). Qed.
Lemma lem6146316 {B : Type'} (y : B) (x : B) (z : B) : ((term527 B x y z) = (term536 B y x z)) = True.
Proof. exact (TRANS (@lem6146311 B y x z) (@lem6146315 B y x z)). Qed.
Lemma lem6146317 {B : Type'} (y : B) (x : B) (z : B) : True = ((term527 B x y z) = (term536 B y x z)).
Proof. exact (SYM (@lem6146316 B y x z)). Qed.
Lemma lem6146318 {B : Type'} (y : B) (x : B) (z : B) : (term527 B x y z) = (term536 B y x z).
Proof. exact (EQ_MP (@lem6146317 B y x z) (@lem0)). Qed.
Lemma lem6146319 {B : Type'} (y : B) (x : B) (z : B) : term536 B y x z.
Proof. exact (EQ_MP (@lem6146318 B y x z) (@lem6145881 B x y z)). Qed.
Lemma lem6146321 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6146322 {B : Type'} (x : B) (y : B) (z : B) : (term536 B y x z) = (term539 B x y z).
Proof. exact (@lem6146321 (term540 B y x z) (y = z)). Qed.
Lemma lem6146324 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6146325 {B : Type'} (y : B) (x : B) (z : B) : (term541 B y x z) = (term542 B y x z).
Proof. exact (@lem6146324 (term389 B x y) (term389 B x z)). Qed.
Lemma lem6146327 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6146328 {B : Type'} (x : B) (y : B) : (term382 B x y) = (x = y).
Proof. exact (@lem6146327 (x = y)). Qed.
Lemma lem6146329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6146330 {B : Type'} (x : B) (y : B) : (term543 B x y) = (term544 B x y).
Proof. exact (MK_COMB (@lem6146329) (@lem6146328 B x y)). Qed.
Lemma lem6146332 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6146333 {B : Type'} (x : B) (z : B) : (term382 B x z) = (x = z).
Proof. exact (@lem6146332 (x = z)). Qed.
Lemma lem6146334 {B : Type'} (y : B) (x : B) (z : B) : (term542 B y x z) = (term545 B y x z).
Proof. exact (MK_COMB (@lem6146330 B x y) (@lem6146333 B x z)). Qed.
Lemma lem6146335 {B : Type'} (y : B) (x : B) (z : B) : (term541 B y x z) = (term545 B y x z).
Proof. exact (TRANS (@lem6146325 B y x z) (@lem6146334 B y x z)). Qed.
Lemma lem6146336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6146337 {B : Type'} (y : B) (x : B) (z : B) : (term546 B y x z) = (term547 B y x z).
Proof. exact (MK_COMB (@lem6146336) (@lem6146335 B y x z)). Qed.
Lemma lem6146338 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6146339 {B : Type'} (x : B) (y : B) (z : B) : (term539 B x y z) = (term548 B x y z).
Proof. exact (MK_COMB (@lem6146337 B y x z) (@lem6146338 B y z)). Qed.
Lemma lem6146340 {B : Type'} (x : B) (y : B) (z : B) : (term536 B y x z) = (term548 B x y z).
Proof. exact (TRANS (@lem6146322 B x y z) (@lem6146339 B x y z)). Qed.
Lemma lem6146342 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term874 A B x f a.
Proof. exact (conj (@lem6146220 A B a f x s h1) (@lem6146229 A B f a)). Qed.
Lemma lem6146344 {B : Type'} (x : B) (y : B) (z : B) : term548 B x y z.
Proof. exact (EQ_MP (@lem6146340 B x y z) (@lem6146319 B y x z)). Qed.
Lemma lem6146345 {B : Type'} (x : B) (y : B) (z : B) : term548 B x y z.
Proof. exact (@lem6146344 B x y z). Qed.
Lemma lem6146346 {A B : Type'} (x : A) (f : A -> B) (a : A) : term875 A B x f a.
Proof. exact (@lem6146345 B (@I (A -> B) f a) (@I (A -> B) f x) (@I (A -> B) f a)). Qed.
Lemma lem6146349 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : (@I (A -> B) f x) = (@I (A -> B) f a).
Proof. exact (@lem6146346 A B x f a (@lem6146342 A B a f x s h1)). Qed.
Lemma lem6146350 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : term476 A B x f a.
Proof. exact (fun h0 : term411 A B x f a => @lem6146349 A B a f x s h1). Qed.
Lemma lem6146352 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6146353 {A B : Type'} (x : A) (f : A -> B) (a : A) : (term476 A B x f a) = ((@I (A -> B) f x) = (@I (A -> B) f a)).
Proof. exact (@lem6146352 ((@I (A -> B) f x) = (@I (A -> B) f a))). Qed.
Lemma lem6146354 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term683 A B a f x s) : (@I (A -> B) f x) = (@I (A -> B) f a).
Proof. exact (EQ_MP (@lem6146353 A B x f a) (@lem6146350 A B a f x s h1)). Qed.
Lemma lem6146360 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146361 {A B C : Type'} (a : A) (s : A -> Prop) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term765 A B C s a _77215 g f _77216 op) = (term876 A B C a s _77215 g f _77216 op).
Proof. exact (@lem6146360 (term389 A _77216 a) (term686 A _77215 s) (term757 A B C _77215 g f _77216 op)). Qed.
Lemma lem6146377 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146378 {A B C : Type'} (s : A -> Prop) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term877 A B C s _77215 g f _77216 op) = (term878 A B C s _77215 g f _77216 op).
Proof. exact (@lem6146377 (_77215 = _77216) (term686 A _77215 s) (term769 A B C _77215 g f _77216 op)). Qed.
Lemma lem6146394 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146395 {A B C : Type'} (_77215 : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term879 A B C s _77215 g f _77216 op) = (term880 A B C _77215 s g f _77216 op).
Proof. exact (@lem6146394 (term411 A B _77215 f _77216) (term686 A _77215 s) ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6146411 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6146412 {A B C : Type'} (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) (_77215 : A) (s : A -> Prop) : (term881 A B C _77215 s g f _77216 op) = (term882 A B C g f _77216 op _77215 s).
Proof. exact (@lem6146411 ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term686 A _77215 s)). Qed.
Lemma lem6146420 {A B : Type'} (_77215 : A) (f : A -> B) (_77216 : A) : (term485 A B _77215 f _77216) = (term485 A B _77215 f _77216).
Proof. exact (eq_refl (term485 A B _77215 f _77216)). Qed.
Lemma lem6146421 {A B C : Type'} (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) (_77215 : A) (s : A -> Prop) : (term880 A B C _77215 s g f _77216 op) = (term883 A B C g f _77216 op _77215 s).
Proof. exact (MK_COMB (@lem6146420 A B _77215 f _77216) (@lem6146412 A B C g f _77216 op _77215 s)). Qed.
Lemma lem6146425 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146426 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term883 A B C g f _77216 op _77215 s) = (term884 A B C g op f _77216 _77215 s).
Proof. exact (@lem6146425 ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term411 A B _77215 f _77216) (term686 A _77215 s)). Qed.
Lemma lem6146446 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term880 A B C _77215 s g f _77216 op) = (term884 A B C g op f _77216 _77215 s).
Proof. exact (TRANS (@lem6146421 A B C g f _77216 op _77215 s) (@lem6146426 A B C g op f _77216 _77215 s)). Qed.
Lemma lem6146447 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term879 A B C s _77215 g f _77216 op) = (term884 A B C g op f _77216 _77215 s).
Proof. exact (TRANS (@lem6146395 A B C _77215 s g f _77216 op) (@lem6146446 A B C g op f _77216 _77215 s)). Qed.
Lemma lem6146448 {A : Type'} (_77215 : A) (_77216 : A) : (term385 A _77215 _77216) = (term385 A _77215 _77216).
Proof. exact (eq_refl (term385 A _77215 _77216)). Qed.
Lemma lem6146449 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term878 A B C s _77215 g f _77216 op) = (term885 A B C g op f _77216 _77215 s).
Proof. exact (MK_COMB (@lem6146448 A _77215 _77216) (@lem6146447 A B C g op f _77216 _77215 s)). Qed.
Lemma lem6146460 {A B C : Type'} (g : B -> C) (op : type1400 C) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term877 A B C s _77215 g f _77216 op) = (term885 A B C g op f _77216 _77215 s).
Proof. exact (TRANS (@lem6146378 A B C s _77215 g f _77216 op) (@lem6146449 A B C g op f _77216 _77215 s)). Qed.
Lemma lem6146461 {A : Type'} (_77216 : A) (a : A) : (term534 A _77216 a) = (term534 A _77216 a).
Proof. exact (eq_refl (term534 A _77216 a)). Qed.
Lemma lem6146462 {A B C : Type'} (a : A) (g : B -> C) (op : type1400 C) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term876 A B C a s _77215 g f _77216 op) = (term886 A B C a g op f _77216 _77215 s).
Proof. exact (MK_COMB (@lem6146461 A _77216 a) (@lem6146460 A B C g op f _77216 _77215 s)). Qed.
Lemma lem6146466 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146467 {A B C : Type'} (a : A) (g : B -> C) (op : type1400 C) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term886 A B C a g op f _77216 _77215 s) = (term887 A B C a g op f _77216 _77215 s).
Proof. exact (@lem6146466 (_77215 = _77216) (term389 A _77216 a) (term884 A B C g op f _77216 _77215 s)). Qed.
Lemma lem6146483 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146484 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term888 A B C a g op f _77216 _77215 s) = (term889 A B C g op a f _77216 _77215 s).
Proof. exact (@lem6146483 ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term389 A _77216 a) (term890 A B f _77216 _77215 s)). Qed.
Lemma lem6146516 {A : Type'} (_77215 : A) (_77216 : A) : (term385 A _77215 _77216) = (term385 A _77215 _77216).
Proof. exact (eq_refl (term385 A _77215 _77216)). Qed.
Lemma lem6146517 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term887 A B C a g op f _77216 _77215 s) = (term891 A B C g op a f _77216 _77215 s).
Proof. exact (MK_COMB (@lem6146516 A _77215 _77216) (@lem6146484 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146528 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term886 A B C a g op f _77216 _77215 s) = (term891 A B C g op a f _77216 _77215 s).
Proof. exact (TRANS (@lem6146467 A B C a g op f _77216 _77215 s) (@lem6146517 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146529 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term876 A B C a s _77215 g f _77216 op) = (term891 A B C g op a f _77216 _77215 s).
Proof. exact (TRANS (@lem6146462 A B C a g op f _77216 _77215 s) (@lem6146528 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146530 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term765 A B C s a _77215 g f _77216 op) = (term891 A B C g op a f _77216 _77215 s).
Proof. exact (TRANS (@lem6146361 A B C a s _77215 g f _77216 op) (@lem6146529 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6146532 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term892 A B C s a _77215 g f _77216 op) = (term893 A B C g op a f _77216 _77215 s).
Proof. exact (MK_COMB (@lem6146531) (@lem6146530 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146548 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146549 {A B : Type'} (a : A) (s : A -> Prop) (_77215 : A) (f : A -> B) (_77216 : A) : (term741 A B s a _77215 f _77216) = (term894 A B a s _77215 f _77216).
Proof. exact (@lem6146548 (term389 A _77216 a) (term686 A _77215 s) (term412 A B _77215 f _77216)). Qed.
Lemma lem6146565 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146566 {A B : Type'} (s : A -> Prop) (_77215 : A) (f : A -> B) (_77216 : A) : (term895 A B s _77215 f _77216) = (term896 A B s _77215 f _77216).
Proof. exact (@lem6146565 (_77215 = _77216) (term686 A _77215 s) (term411 A B _77215 f _77216)). Qed.
Lemma lem6146582 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6146583 {A B : Type'} (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term897 A B s _77215 f _77216) = (term890 A B f _77216 _77215 s).
Proof. exact (@lem6146582 (term411 A B _77215 f _77216) (term686 A _77215 s)). Qed.
Lemma lem6146591 {A : Type'} (_77215 : A) (_77216 : A) : (term385 A _77215 _77216) = (term385 A _77215 _77216).
Proof. exact (eq_refl (term385 A _77215 _77216)). Qed.
Lemma lem6146592 {A B : Type'} (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term896 A B s _77215 f _77216) = (term898 A B f _77216 _77215 s).
Proof. exact (MK_COMB (@lem6146591 A _77215 _77216) (@lem6146583 A B f _77216 _77215 s)). Qed.
Lemma lem6146603 {A B : Type'} (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term895 A B s _77215 f _77216) = (term898 A B f _77216 _77215 s).
Proof. exact (TRANS (@lem6146566 A B s _77215 f _77216) (@lem6146592 A B f _77216 _77215 s)). Qed.
Lemma lem6146604 {A : Type'} (_77216 : A) (a : A) : (term534 A _77216 a) = (term534 A _77216 a).
Proof. exact (eq_refl (term534 A _77216 a)). Qed.
Lemma lem6146605 {A B : Type'} (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term894 A B a s _77215 f _77216) = (term899 A B a f _77216 _77215 s).
Proof. exact (MK_COMB (@lem6146604 A _77216 a) (@lem6146603 A B f _77216 _77215 s)). Qed.
Lemma lem6146609 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146610 {A B : Type'} (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term899 A B a f _77216 _77215 s) = (term900 A B a f _77216 _77215 s).
Proof. exact (@lem6146609 (_77215 = _77216) (term389 A _77216 a) (term890 A B f _77216 _77215 s)). Qed.
Lemma lem6146642 {A B : Type'} (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term894 A B a s _77215 f _77216) = (term900 A B a f _77216 _77215 s).
Proof. exact (TRANS (@lem6146605 A B a f _77216 _77215 s) (@lem6146610 A B a f _77216 _77215 s)). Qed.
Lemma lem6146643 {A B : Type'} (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term741 A B s a _77215 f _77216) = (term900 A B a f _77216 _77215 s).
Proof. exact (TRANS (@lem6146549 A B a s _77215 f _77216) (@lem6146642 A B a f _77216 _77215 s)). Qed.
Lemma lem6146644 {A B C : Type'} (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term784 A B C g f _77216 op) = (term784 A B C g f _77216 op).
Proof. exact (eq_refl (term784 A B C g f _77216 op)). Qed.
Lemma lem6146645 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term901 A B C g op s a _77215 f _77216) = (term902 A B C g op a f _77216 _77215 s).
Proof. exact (MK_COMB (@lem6146644 A B C g f _77216 op) (@lem6146643 A B a f _77216 _77215 s)). Qed.
Lemma lem6146649 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6146650 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term902 A B C g op a f _77216 _77215 s) = (term891 A B C g op a f _77216 _77215 s).
Proof. exact (@lem6146649 (_77215 = _77216) ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op)) (term903 A B a f _77216 _77215 s)). Qed.
Lemma lem6146694 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : (term901 A B C g op s a _77215 f _77216) = (term891 A B C g op a f _77216 _77215 s).
Proof. exact (TRANS (@lem6146645 A B C g op a f _77216 _77215 s) (@lem6146650 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146695 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : ((term765 A B C s a _77215 g f _77216 op) = (term901 A B C g op s a _77215 f _77216)) = ((term891 A B C g op a f _77216 _77215 s) = (term891 A B C g op a f _77216 _77215 s)).
Proof. exact (MK_COMB (@lem6146532 A B C g op a f _77216 _77215 s) (@lem6146694 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146697 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6146698 (x : Prop) : (x = x) = True.
Proof. exact (@lem6146697 Prop x). Qed.
Lemma lem6146699 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (_77216 : A) (_77215 : A) (s : A -> Prop) : ((term891 A B C g op a f _77216 _77215 s) = (term891 A B C g op a f _77216 _77215 s)) = True.
Proof. exact (@lem6146698 (term891 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146700 {A B C : Type'} (g : B -> C) (op : type1400 C) (s : A -> Prop) (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : ((term765 A B C s a _77215 g f _77216 op) = (term901 A B C g op s a _77215 f _77216)) = True.
Proof. exact (TRANS (@lem6146695 A B C g op a f _77216 _77215 s) (@lem6146699 A B C g op a f _77216 _77215 s)). Qed.
Lemma lem6146701 {A B C : Type'} (g : B -> C) (op : type1400 C) (s : A -> Prop) (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : True = ((term765 A B C s a _77215 g f _77216 op) = (term901 A B C g op s a _77215 f _77216)).
Proof. exact (SYM (@lem6146700 A B C g op s a _77215 f _77216)). Qed.
Lemma lem6146702 {A B C : Type'} (g : B -> C) (op : type1400 C) (s : A -> Prop) (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : (term765 A B C s a _77215 g f _77216 op) = (term901 A B C g op s a _77215 f _77216).
Proof. exact (EQ_MP (@lem6146701 A B C g op s a _77215 f _77216) (@lem0)). Qed.
Lemma lem6146703 {A B C : Type'} (_77215 : A) (_77216 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term901 A B C g op s a _77215 f _77216.
Proof. exact (EQ_MP (@lem6146702 A B C g op s a _77215 f _77216) (@lem6144723 A B C _77215 _77216 a s g f op h1)). Qed.
Lemma lem6146705 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6146706 {A B C : Type'} (s : A -> Prop) (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term901 A B C g op s a _77215 f _77216) = (term904 A B C s a _77215 g f _77216 op).
Proof. exact (@lem6146705 (term741 A B s a _77215 f _77216) ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6146708 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6146709 {A B : Type'} (s : A -> Prop) (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : (term905 A B s a _77215 f _77216) = (term906 A B s a _77215 f _77216).
Proof. exact (@lem6146708 (term686 A _77215 s) (term436 A B a _77215 f _77216)). Qed.
Lemma lem6146711 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6146712 {A : Type'} (_77215 : A) (s : A -> Prop) : (term794 A _77215 s) = (term685 A _77215 s).
Proof. exact (@lem6146711 (term685 A _77215 s)). Qed.
Lemma lem6146713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6146714 {A : Type'} (_77215 : A) (s : A -> Prop) : (term795 A _77215 s) = (term714 A _77215 s).
Proof. exact (MK_COMB (@lem6146713) (@lem6146712 A _77215 s)). Qed.
Lemma lem6146716 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6146717 {A B : Type'} (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : (term907 A B a _77215 f _77216) = (term908 A B a _77215 f _77216).
Proof. exact (@lem6146716 (term389 A _77216 a) (term412 A B _77215 f _77216)). Qed.
Lemma lem6146719 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6146720 {A : Type'} (_77216 : A) (a : A) : (term382 A _77216 a) = (_77216 = a).
Proof. exact (@lem6146719 (_77216 = a)). Qed.
Lemma lem6146721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6146722 {A : Type'} (_77216 : A) (a : A) : (term543 A _77216 a) = (term544 A _77216 a).
Proof. exact (MK_COMB (@lem6146721) (@lem6146720 A _77216 a)). Qed.
Lemma lem6146724 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6146725 {A B : Type'} (_77215 : A) (f : A -> B) (_77216 : A) : (term909 A B _77215 f _77216) = (term910 A B _77215 f _77216).
Proof. exact (@lem6146724 (_77215 = _77216) (term411 A B _77215 f _77216)). Qed.
Lemma lem6146727 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6146728 {A B : Type'} (_77215 : A) (f : A -> B) (_77216 : A) : (term515 A B _77215 f _77216) = ((@I (A -> B) f _77215) = (@I (A -> B) f _77216)).
Proof. exact (@lem6146727 ((@I (A -> B) f _77215) = (@I (A -> B) f _77216))). Qed.
Lemma lem6146729 {A : Type'} (_77215 : A) (_77216 : A) : (term423 A _77215 _77216) = (term423 A _77215 _77216).
Proof. exact (eq_refl (term423 A _77215 _77216)). Qed.
Lemma lem6146730 {A B : Type'} (_77215 : A) (f : A -> B) (_77216 : A) : (term910 A B _77215 f _77216) = (term424 A B _77215 f _77216).
Proof. exact (MK_COMB (@lem6146729 A _77215 _77216) (@lem6146728 A B _77215 f _77216)). Qed.
Lemma lem6146731 {A B : Type'} (_77215 : A) (f : A -> B) (_77216 : A) : (term909 A B _77215 f _77216) = (term424 A B _77215 f _77216).
Proof. exact (TRANS (@lem6146725 A B _77215 f _77216) (@lem6146730 A B _77215 f _77216)). Qed.
Lemma lem6146732 {A B : Type'} (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : (term908 A B a _77215 f _77216) = (term911 A B a _77215 f _77216).
Proof. exact (MK_COMB (@lem6146722 A _77216 a) (@lem6146731 A B _77215 f _77216)). Qed.
Lemma lem6146733 {A B : Type'} (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : (term907 A B a _77215 f _77216) = (term911 A B a _77215 f _77216).
Proof. exact (TRANS (@lem6146717 A B a _77215 f _77216) (@lem6146732 A B a _77215 f _77216)). Qed.
Lemma lem6146734 {A B : Type'} (s : A -> Prop) (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : (term906 A B s a _77215 f _77216) = (term912 A B s a _77215 f _77216).
Proof. exact (MK_COMB (@lem6146714 A _77215 s) (@lem6146733 A B a _77215 f _77216)). Qed.
Lemma lem6146735 {A B : Type'} (s : A -> Prop) (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : (term905 A B s a _77215 f _77216) = (term912 A B s a _77215 f _77216).
Proof. exact (TRANS (@lem6146709 A B s a _77215 f _77216) (@lem6146734 A B s a _77215 f _77216)). Qed.
Lemma lem6146736 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6146737 {A B : Type'} (s : A -> Prop) (a : A) (_77215 : A) (f : A -> B) (_77216 : A) : (term913 A B s a _77215 f _77216) = (term914 A B s a _77215 f _77216).
Proof. exact (MK_COMB (@lem6146736) (@lem6146735 A B s a _77215 f _77216)). Qed.
Lemma lem6146738 {A B C : Type'} (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op)) = ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op)).
Proof. exact (eq_refl ((term407 A B C g f _77216) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6146739 {A B C : Type'} (s : A -> Prop) (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term904 A B C s a _77215 g f _77216 op) = (term915 A B C s a _77215 g f _77216 op).
Proof. exact (MK_COMB (@lem6146737 A B s a _77215 f _77216) (@lem6146738 A B C g f _77216 op)). Qed.
Lemma lem6146740 {A B C : Type'} (s : A -> Prop) (a : A) (_77215 : A) (g : B -> C) (f : A -> B) (_77216 : A) (op : type1400 C) : (term901 A B C g op s a _77215 f _77216) = (term915 A B C s a _77215 g f _77216 op).
Proof. exact (TRANS (@lem6146706 A B C s a _77215 g f _77216 op) (@lem6146739 A B C s a _77215 g f _77216 op)). Qed.
Lemma lem6146742 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term424 A B x f a.
Proof. exact (conj (@lem6146213 A B a f x s h1 h2) (@lem6146354 A B a f x s h2)). Qed.
Lemma lem6146743 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term916 A B x f a.
Proof. exact (conj (@lem6145945 A a) (@lem6146742 A B a f x s h1 h2)). Qed.
Lemma lem6146744 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term180 A a s) (h2 : term683 A B a f x s) : term917 A B s x f a.
Proof. exact (conj (@lem6145936 A B a f x s h2) (@lem6146743 A B a f x s h1 h2)). Qed.
Lemma lem6146746 {A B C : Type'} (_77215 : A) (_77216 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term915 A B C s a _77215 g f _77216 op.
Proof. exact (EQ_MP (@lem6146740 A B C s a _77215 g f _77216 op) (@lem6146703 A B C _77215 _77216 a s g f op h1)). Qed.
Lemma lem6146747 {A B C : Type'} (_77215 : A) (_77216 : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term915 A B C s a _77215 g f _77216 op.
Proof. exact (@lem6146746 A B C _77215 _77216 a s g f op h1). Qed.
Lemma lem6146748 {A B C : Type'} (x : A) (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : term270 A B C a s g f op) : term918 A B C s x g f a op.
Proof. exact (@lem6146747 A B C x a a s g f op h1). Qed.
Lemma lem6146751 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term270 A B C a s g f op) (h2 : term180 A a s) (h3 : term683 A B a f x s) : (term407 A B C g f a) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (@lem6146748 A B C x a s g f op h1 (@lem6146744 A B a f x s h2 h3)). Qed.
Lemma lem6146752 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term270 A B C a s g f op) (h2 : term180 A a s) (h3 : term683 A B a f x s) : term919 A B C g f a op.
Proof. exact (fun h0 : term697 A B C g f a op => @lem6146751 A B C g op a f x s h1 h2 h3). Qed.
Lemma lem6146754 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6146755 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term919 A B C g f a op) = ((term407 A B C g f a) = (@I ((C -> C -> C) -> C) (@neutral C) op)).
Proof. exact (@lem6146754 ((term407 A B C g f a) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6146756 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term270 A B C a s g f op) (h2 : term180 A a s) (h3 : term683 A B a f x s) : (term407 A B C g f a) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (EQ_MP (@lem6146755 A B C g f a op) (@lem6146752 A B C g op a f x s h1 h2 h3)). Qed.
Lemma lem6146759 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6146761 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term697 A B C g f a op) = (term920 A B C g f a op).
Proof. exact (@lem6146759 ((term407 A B C g f a) = (@I ((C -> C -> C) -> C) (@neutral C) op))). Qed.
Lemma lem6146764 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : term421 A B C g f a op) : term920 A B C g f a op.
Proof. exact (EQ_MP (@lem6146761 A B C g f a op) (@lem6144531 A B C g f a op h1)). Qed.
Lemma lem6146767 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term270 A B C a s g f op) (h2 : term421 A B C g f a op) (h3 : term180 A a s) (h4 : term683 A B a f x s) : False.
Proof. exact (@lem6146764 A B C g f a op h2 (@lem6146756 A B C g op a f x s h1 h3 h4)). Qed.
Lemma lem6146768 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term270 A B C a s g f op) (h2 : term421 A B C g f a op) (h3 : term180 A a s) (h4 : term683 A B a f x s) : term526.
Proof. exact (fun h0 : ~ False => @lem6146767 A B C g op a f x s h1 h2 h3 h4). Qed.
Lemma lem6146770 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6146771 : term526 = False.
Proof. exact (@lem6146770 False). Qed.
Lemma lem6146772 {A B C : Type'} (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term270 A B C a s g f op) (h2 : term421 A B C g f a op) (h3 : term180 A a s) (h4 : term683 A B a f x s) : False.
Proof. exact (EQ_MP (@lem6146771) (@lem6146768 A B C g op a f x s h1 h2 h3 h4)). Qed.
Lemma lem6146773 {A B C : Type'} (a : A) (x : A) (x' : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term421 A B C g f a op) (h3 : term180 A a s) (h4 : term683 A B a f x s) (h5 : term374 A B C x' y op s g f) : False.
Proof. exact (or_elim (@lem6141129 A B C x' y op s g f h5) (fun h0 : term718 A B C s x' g f y op => @lem6145459 A B C a s x' g f y op h1 h0) (fun h0 : (term707 A B C op f s g) = (term712 A B C op s g f) => @lem6146772 A B C g op a f x s h1 h2 h3 h4)). Qed.
Lemma lem6146774 {A B C : Type'} (x' : A) (g : B -> C) (op : type1400 C) (a : A) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term270 A B C a s g f op) (h2 : term377 A B C x' op s g f) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term683 A B a f x s) : False.
Proof. exact (ex_elim (@lem6139832 A B C x' op s g f h2) (fun y : A => fun h0 : term376 A B C x' op s g f y => @lem6146773 A B C a x x' y op s g f h1 h3 h4 h5 h0)). Qed.
Lemma lem6146775 {A B C : Type'} (a : A) (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term421 A B C g f a op) (h3 : term180 A a s) (h4 : term683 A B a f x s) (h5 : term175 A B C op s g f) : False.
Proof. exact (ex_elim (@lem6139202 A B C op s g f h5) (fun x' : A => fun h0 : term378 A B C op s g f x' => @lem6146774 A B C x' g op a f x s h1 h0 h2 h3 h4)). Qed.
Lemma lem6146776 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : False.
Proof. exact (ex_elim (@lem6139377 A B a f s h2) (fun x : A => fun h0 : term684 A B a f s x => @lem6146775 A B C a x op s g f h1 h3 h4 h0 h5)). Qed.
Lemma lem6146777 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term421 A B C g f a op) = False.
Proof. exact (prop_ext (fun h6 : term421 A B C g f a op => @lem6146776 A B C a op s g f h1 h2 h3 h4 h5) (fun h6 : False => @lem6139383 A B C g f a op h3)). Qed.
Lemma lem6146778 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6146777 A B C a op s g f h1 h2 h3 h4 h5) (@lem6139383 A B C g f a op h3)). Qed.
Lemma lem6146779 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term559 A B a f s) = False.
Proof. exact (prop_ext (fun h6 : term559 A B a f s => @lem6146778 A B C a op s g f h1 h2 h3 h4 h5) (fun h6 : False => @lem6139377 A B a f s h2)). Qed.
Lemma lem6146780 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6146779 A B C a op s g f h1 h2 h3 h4 h5) (@lem6139377 A B a f s h2)). Qed.
Lemma lem6146781 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term180 A a s) = False.
Proof. exact (prop_ext (fun h6 : term180 A a s => @lem6146780 A B C a op s g f h1 h2 h3 h4 h5) (fun h6 : False => @lem6139208 A a s h4)). Qed.
Lemma lem6146782 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6146781 A B C a op s g f h1 h2 h3 h4 h5) (@lem6139208 A a s h4)). Qed.
Lemma lem6146783 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term608 C.
Proof. exact (fun h0 : term603 C => @lem6146782 A B C a op s g f h1 h2 h3 h4 h5). Qed.
Lemma lem6146784 {C : Type'} : (term608 C) = (term609 C).
Proof. exact (@lem69 (term603 C)). Qed.
Lemma lem6146785 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term609 C.
Proof. exact (EQ_MP (@lem6146784 C) (@lem6146783 A B C a op s g f h1 h2 h3 h4 h5)). Qed.
Lemma lem6146786 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term612 B C.
Proof. exact (fun h0 : term603 B => @lem6146785 A B C a op s g f h1 h2 h3 h4 h5). Qed.
Lemma lem6146787 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term421 A B C g f a op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term614 A B C.
Proof. exact (fun h0 : term603 A => @lem6146786 A B C a op s g f h1 h2 h3 h4 h5). Qed.
Lemma lem6146788 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : term617 A B C g f a op.
Proof. exact (fun h0 : term421 A B C g f a op => @lem6146787 A B C a op s g f h1 h2 h0 h3 h4). Qed.
Lemma lem6146789 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term180 A a s) (h3 : term175 A B C op s g f) : term619 A B C s g f a op.
Proof. exact (fun h0 : term559 A B a f s => @lem6146788 A B C a op s g f h1 h0 h2 h3). Qed.
Lemma lem6146790 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term180 A a s) (h2 : term175 A B C op s g f) : term621 A B C s g f a op.
Proof. exact (fun h0 : term270 A B C a s g f op => @lem6146789 A B C a op s g f h0 h1 h2). Qed.
Lemma lem6146791 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term180 A a s) (h2 : term175 A B C op s g f) : term623 A B C s g f a op.
Proof. exact (fun h0 : @FINITE A s => @lem6146790 A B C a op s g f h1 h2). Qed.
Lemma lem6146792 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term625 A B C s g f a op.
Proof. exact (fun h0 : term180 A a s => @lem6146791 A B C a op s g f h0 h1). Qed.
Lemma lem6146793 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term627 A B C s g f a op.
Proof. exact (fun h0 : term175 A B C op s g f => @lem6146792 A B C a op s g f h0). Qed.
Lemma lem6146794 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term628 A B C s g f a op.
Proof. exact (fun h0 : @monoidal C op => @lem6146793 A B C s g f a op). Qed.
Lemma lem6146799 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term632 A B C g f a op.
Proof. exact (fun s : A -> Prop => @lem6146794 A B C s g f a op). Qed.
Lemma lem6146804 {A B C : Type'} (f : A -> B) (a : A) (op : type1400 C) : term636 A B C f a op.
Proof. exact (fun g : B -> C => @lem6146799 A B C g f a op). Qed.
Lemma lem6146809 {A B C : Type'} (a : A) (op : type1400 C) : term640 A B C a op.
Proof. exact (fun f : A -> B => @lem6146804 A B C f a op). Qed.
Lemma lem6146814 {A B C : Type'} (op : type1400 C) : term644 A B C op.
Proof. exact (fun a : A => @lem6146809 A B C a op). Qed.
Lemma lem6146819 {A B C : Type'} : term648 A B C.
Proof. exact (fun op : type1400 C => @lem6146814 A B C op). Qed.
Lemma lem6146820 {A B C : Type'} : term647 A B C.
Proof. exact (EQ_MP (@lem6139033 A B C) (@lem6146819 A B C)). Qed.
Lemma lem6146821 {A B C : Type'} (op : type1400 C) : term921 A B C op.
Proof. exact (@lem6146820 A B C op). Qed.
Lemma lem6146822 {A B C : Type'} (op : type1400 C) : (term921 A B C op) = (term643 A B C op).
Proof. exact (eq_refl (term921 A B C op)). Qed.
Lemma lem6146823 {A B C : Type'} (op : type1400 C) : term643 A B C op.
Proof. exact (EQ_MP (@lem6146822 A B C op) (@lem6146821 A B C op)). Qed.
Lemma lem6146824 {A B C : Type'} (op : type1400 C) (a : A) : term922 A B C op a.
Proof. exact (@lem6146823 A B C op a). Qed.
Lemma lem6146825 {A B C : Type'} (a : A) (op : type1400 C) : (term922 A B C op a) = (term639 A B C a op).
Proof. exact (eq_refl (term922 A B C op a)). Qed.
Lemma lem6146826 {A B C : Type'} (a : A) (op : type1400 C) : term639 A B C a op.
Proof. exact (EQ_MP (@lem6146825 A B C a op) (@lem6146824 A B C op a)). Qed.
Lemma lem6146827 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) : term923 A B C a op f.
Proof. exact (@lem6146826 A B C a op f). Qed.
Lemma lem6146828 {A B C : Type'} (f : A -> B) (a : A) (op : type1400 C) : (term923 A B C a op f) = (term635 A B C f a op).
Proof. exact (eq_refl (term923 A B C a op f)). Qed.
Lemma lem6146829 {A B C : Type'} (f : A -> B) (a : A) (op : type1400 C) : term635 A B C f a op.
Proof. exact (EQ_MP (@lem6146828 A B C f a op) (@lem6146827 A B C a op f)). Qed.
Lemma lem6146830 {A B C : Type'} (f : A -> B) (a : A) (op : type1400 C) (g : B -> C) : term924 A B C f a op g.
Proof. exact (@lem6146829 A B C f a op g). Qed.
Lemma lem6146831 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term924 A B C f a op g) = (term631 A B C g f a op).
Proof. exact (eq_refl (term924 A B C f a op g)). Qed.
Lemma lem6146832 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term631 A B C g f a op.
Proof. exact (EQ_MP (@lem6146831 A B C g f a op) (@lem6146830 A B C f a op g)). Qed.
Lemma lem6146833 {A B C : Type'} (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (s : A -> Prop) : term925 A B C g f a op s.
Proof. exact (@lem6146832 A B C g f a op s). Qed.
Lemma lem6146834 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : (term925 A B C g f a op s) = (term604 A B C s g f a op).
Proof. exact (eq_refl (term925 A B C g f a op s)). Qed.
Lemma lem6146835 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term604 A B C s g f a op.
Proof. exact (EQ_MP (@lem6146834 A B C s g f a op) (@lem6146833 A B C g f a op s)). Qed.
Lemma lem6146837 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) : term604 A B C s g f a op.
Proof. exact (@lem6138049 A B C s g f a op (@lem6146835 A B C s g f a op)). Qed.
Lemma lem6146838 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (a : A) (op : type1400 C) (h1 : @monoidal C op) : term626 A B C s g f a op.
Proof. exact (@lem6146837 A B C s g f a op (@lem6113800 C op h1)). Qed.
Lemma lem6146839 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term175 A B C op s g f) : term624 A B C s g f a op.
Proof. exact (@lem6146838 A B C s g f a op h1 (@lem6135446 A B C op s g f h2)). Qed.
Lemma lem6146840 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term180 A a s) (h3 : term175 A B C op s g f) : term622 A B C s g f a op.
Proof. exact (@lem6146839 A B C a op s g f h1 h3 (@lem6135448 A a s h2)). Qed.
Lemma lem6146841 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : term620 A B C s g f a op.
Proof. exact (@lem6146840 A B C a op s g f h2 h3 h4 (@lem6135447 A s h1)). Qed.
Lemma lem6146842 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term618 A B C s g f a op.
Proof. exact (@lem6146841 A B C a op s g f h2 h3 h4 h5 (@lem6135449 A B C a s g f op h1)). Qed.
Lemma lem6146843 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : term616 A B C g f a op.
Proof. exact (@lem6146842 A B C a op s g f h1 h3 h4 h5 h6 (@lem6137888 A B a f s h2)). Qed.
Lemma lem6146844 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term421 A B C g f a op) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : term613 A B C.
Proof. exact (@lem6146843 A B C a op s g f h1 h2 h3 h4 h6 h7 (@lem6138028 A B C g f a op h5)). Qed.
Lemma lem6146845 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term421 A B C g f a op) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : term611 B C.
Proof. exact (@lem6146844 A B C a op s g f h1 h2 h3 h4 h5 h6 h7 (@lem6138030 A)). Qed.
Lemma lem6146846 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term421 A B C g f a op) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : term608 C.
Proof. exact (@lem6146845 A B C a op s g f h1 h2 h3 h4 h5 h6 h7 (@lem6138031 B)). Qed.
Lemma lem6146847 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term421 A B C g f a op) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : False.
Proof. exact (@lem6146846 A B C a op s g f h1 h2 h3 h4 h5 h6 h7 (@lem6138029 C)). Qed.
Lemma lem6146848 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term421 A B C g f a op) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : (term421 A B C g f a op) = False.
Proof. exact (prop_ext (fun h8 : term421 A B C g f a op => @lem6146847 A B C a op s g f h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem6138028 A B C g f a op h5)). Qed.
Lemma lem6146849 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term421 A B C g f a op) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6146848 A B C a op s g f h1 h2 h3 h4 h5 h6 h7) (@lem6138028 A B C g f a op h5)). Qed.
Lemma lem6146850 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : term602 A B C g f a op.
Proof. exact (fun h0 : term421 A B C g f a op => @lem6146849 A B C a op s g f h1 h2 h3 h4 h0 h5 h6). Qed.
Lemma lem6146851 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : (term110 A B C g f a) = (@neutral C op).
Proof. exact (EQ_MP (@lem6138027 A B C g f a op) (@lem6146850 A B C a op s g f h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem6146853 (p : Prop) : p = (term282 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6146854 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term33 A B C op f s g) = (term599 A B C op f s g)) = (term926 A B C op f s g).
Proof. exact (@lem6146853 ((term33 A B C op f s g) = (term599 A B C op f s g))). Qed.
Lemma lem6146855 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term926 A B C op f s g) = ((term33 A B C op f s g) = (term599 A B C op f s g)).
Proof. exact (SYM (@lem6146854 A B C op f s g)). Qed.
Lemma lem6146856 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term927 A B C op f s g) : term927 A B C op f s g.
Proof. exact (h1). Qed.
Lemma lem6146857 {C : Type'} : term603 C.
Proof. exact (@lem5715484 C). Qed.
Lemma lem6146858 {A : Type'} : term603 A.
Proof. exact (@lem5715484 A). Qed.
Lemma lem6146859 {B : Type'} : term603 B.
Proof. exact (@lem5715484 B). Qed.
Lemma lem6146864 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term928 A B C a op f s g) : term928 A B C a op f s g.
Proof. exact (h1). Qed.
Lemma lem6146865 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term929 A B C a op f s g.
Proof. exact (fun h0 : term928 A B C a op f s g => @lem6146864 A B C a op f s g h0). Qed.
Lemma lem6146866 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term929 A B C a op f s g) : term929 A B C a op f s g.
Proof. exact (h1). Qed.
Lemma lem6146867 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term928 A B C a op f s g) : term928 A B C a op f s g.
Proof. exact (h1). Qed.
Lemma lem6146868 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term928 A B C a op f s g) (h2 : term929 A B C a op f s g) : term928 A B C a op f s g.
Proof. exact (@lem6146866 A B C a op f s g h2 (@lem6146867 A B C a op f s g h1)). Qed.
Lemma lem6146869 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term928 A B C a op f s g) : term930 A B C a op f s g.
Proof. exact (fun h0 : term929 A B C a op f s g => @lem6146868 A B C a op f s g h1 h0). Qed.
Lemma lem6146870 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term929 A B C a op f s g) : term929 A B C a op f s g.
Proof. exact (h1). Qed.
Lemma lem6146871 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term928 A B C a op f s g) (h2 : term929 A B C a op f s g) : term928 A B C a op f s g.
Proof. exact (@lem6146869 A B C a op f s g h1 (@lem6146870 A B C a op f s g h2)). Qed.
Lemma lem6146872 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term929 A B C a op f s g) : term929 A B C a op f s g.
Proof. exact (fun h0 : term928 A B C a op f s g => @lem6146871 A B C a op f s g h0 h1). Qed.
Lemma lem6146873 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term931 A B C a op f s g.
Proof. exact (fun h0 : term929 A B C a op f s g => @lem6146872 A B C a op f s g h0). Qed.
Lemma lem6146876 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term929 A B C a op f s g.
Proof. exact (@lem6146873 A B C a op f s g (@lem6146865 A B C a op f s g)). Qed.
Lemma lem6146877 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term929 A B C a op f s g.
Proof. exact (@lem6146876 A B C a op f s g). Qed.
Lemma lem6147113 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6147114 {C : Type'} : (term608 C) = (term609 C).
Proof. exact (@lem6147113 (term603 C)). Qed.
Lemma lem6147169 {B : Type'} : (term610 B) = (term610 B).
Proof. exact (eq_refl (term610 B)). Qed.
Lemma lem6147170 {B C : Type'} : (term611 B C) = (term612 B C).
Proof. exact (MK_COMB (@lem6147169 B) (@lem6147114 C)). Qed.
Lemma lem6147173 {A : Type'} : (term610 A) = (term610 A).
Proof. exact (eq_refl (term610 A)). Qed.
Lemma lem6147174 {A B C : Type'} : (term613 A B C) = (term614 A B C).
Proof. exact (MK_COMB (@lem6147173 A) (@lem6147170 B C)). Qed.
Lemma lem6147177 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term932 A B C op f s g) = (term932 A B C op f s g).
Proof. exact (eq_refl (term932 A B C op f s g)). Qed.
Lemma lem6147178 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term933 A B C op f s g) = (term934 A B C op f s g).
Proof. exact (MK_COMB (@lem6147177 A B C op f s g) (@lem6147174 A B C)). Qed.
Lemma lem6147181 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term579 A B a f s) = (term579 A B a f s).
Proof. exact (eq_refl (term579 A B a f s)). Qed.
Lemma lem6147182 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term935 A B C a op f s g) = (term936 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147181 A B a f s) (@lem6147178 A B C op f s g)). Qed.
Lemma lem6147185 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term272 A B C a s g f op) = (term272 A B C a s g f op).
Proof. exact (eq_refl (term272 A B C a s g f op)). Qed.
Lemma lem6147186 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term937 A B C a op f s g) = (term938 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147185 A B C a s g f op) (@lem6147182 A B C a op f s g)). Qed.
Lemma lem6147189 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem6147190 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term939 A B C a op f s g) = (term940 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147189 A s) (@lem6147186 A B C a op f s g)). Qed.
Lemma lem6147193 {A : Type'} (a : A) (s : A -> Prop) : (term295 A a s) = (term295 A a s).
Proof. exact (eq_refl (term295 A a s)). Qed.
Lemma lem6147194 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term941 A B C a op f s g) = (term942 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147193 A a s) (@lem6147190 A B C a op f s g)). Qed.
Lemma lem6147197 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term298 A B C op s g f) = (term298 A B C op s g f).
Proof. exact (eq_refl (term298 A B C op s g f)). Qed.
Lemma lem6147198 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term943 A B C a op f s g) = (term944 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147197 A B C op s g f) (@lem6147194 A B C a op f s g)). Qed.
Lemma lem6147201 {C : Type'} (op : type1400 C) : (term301 C op) = (term301 C op).
Proof. exact (eq_refl (term301 C op)). Qed.
Lemma lem6147202 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term928 A B C a op f s g) = (term945 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147201 C op) (@lem6147198 A B C a op f s g)). Qed.
Lemma lem6147205 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term946 A B C op f s g) = (term947 A B C op f s g).
Proof. exact (fun_ext (fun a : A => @lem6147202 A B C a op f s g)). Qed.
Lemma lem6147206 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147207 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term948 A B C op f s g) = (term949 A B C op f s g).
Proof. exact (MK_COMB (@lem6147206 A) (@lem6147205 A B C op f s g)). Qed.
Lemma lem6147212 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term950 A B C f s g) = (term951 A B C f s g).
Proof. exact (fun_ext (fun op : type1400 C => @lem6147207 A B C op f s g)). Qed.
Lemma lem6147213 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6147214 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term952 A B C f s g) = (term953 A B C f s g).
Proof. exact (MK_COMB (@lem6147213 C) (@lem6147212 A B C f s g)). Qed.
Lemma lem6147219 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term954 A B C s g) = (term955 A B C s g).
Proof. exact (fun_ext (fun f : A -> B => @lem6147214 A B C f s g)). Qed.
Lemma lem6147220 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6147221 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term956 A B C s g) = (term957 A B C s g).
Proof. exact (MK_COMB (@lem6147220 A B) (@lem6147219 A B C s g)). Qed.
Lemma lem6147226 {A B C : Type'} (g : B -> C) : (term958 A B C g) = (term959 A B C g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6147221 A B C s g)). Qed.
Lemma lem6147227 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6147228 {A B C : Type'} (g : B -> C) : (term960 A B C g) = (term961 A B C g).
Proof. exact (MK_COMB (@lem6147227 A) (@lem6147226 A B C g)). Qed.
Lemma lem6147233 {A B C : Type'} : (term962 A B C) = (term963 A B C).
Proof. exact (fun_ext (fun g : B -> C => @lem6147228 A B C g)). Qed.
Lemma lem6147234 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem6147243 {A B C : Type'} : (term964 A B C) = (term965 A B C).
Proof. exact (MK_COMB (@lem6147234 B C) (@lem6147233 A B C)). Qed.
Lemma lem6147244 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : ((term649 C a op b c) = (term649 C b op a c)) = ((term649 C a op b c) = (term649 C b op a c)).
Proof. exact (eq_refl ((term649 C a op b c) = (term649 C b op a c))). Qed.
Lemma lem6147245 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term650 C b op a) = (term650 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6147244 C b op a c)). Qed.
Lemma lem6147246 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147247 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term651 C b op a) = (term651 C b op a).
Proof. exact (MK_COMB (@lem6147246 C) (@lem6147245 C b op a)). Qed.
Lemma lem6147248 {C : Type'} (op : type1400 C) (a : C) : (term652 C op a) = (term652 C op a).
Proof. exact (fun_ext (fun b : C => @lem6147247 C b op a)). Qed.
Lemma lem6147249 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147250 {C : Type'} (op : type1400 C) (a : C) : (term653 C op a) = (term653 C op a).
Proof. exact (MK_COMB (@lem6147249 C) (@lem6147248 C op a)). Qed.
Lemma lem6147251 {C : Type'} (op : type1400 C) : (term654 C op) = (term654 C op).
Proof. exact (fun_ext (fun a : C => @lem6147250 C op a)). Qed.
Lemma lem6147252 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147253 {C : Type'} (op : type1400 C) : (term655 C op) = (term655 C op).
Proof. exact (MK_COMB (@lem6147252 C) (@lem6147251 C op)). Qed.
Lemma lem6147254 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : ((term656 C op a b c) = (term649 C a op b c)) = ((term656 C op a b c) = (term649 C a op b c)).
Proof. exact (eq_refl ((term656 C op a b c) = (term649 C a op b c))). Qed.
Lemma lem6147255 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term657 C a op b) = (term657 C a op b).
Proof. exact (fun_ext (fun c : C => @lem6147254 C a op b c)). Qed.
Lemma lem6147256 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147257 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term658 C a op b) = (term658 C a op b).
Proof. exact (MK_COMB (@lem6147256 C) (@lem6147255 C a op b)). Qed.
Lemma lem6147258 {C : Type'} (a : C) (op : type1400 C) : (term659 C a op) = (term659 C a op).
Proof. exact (fun_ext (fun b : C => @lem6147257 C a op b)). Qed.
Lemma lem6147259 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147260 {C : Type'} (a : C) (op : type1400 C) : (term660 C a op) = (term660 C a op).
Proof. exact (MK_COMB (@lem6147259 C) (@lem6147258 C a op)). Qed.
Lemma lem6147261 {C : Type'} (op : type1400 C) : (term661 C op) = (term661 C op).
Proof. exact (fun_ext (fun a : C => @lem6147260 C a op)). Qed.
Lemma lem6147262 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147263 {C : Type'} (op : type1400 C) : (term662 C op) = (term662 C op).
Proof. exact (MK_COMB (@lem6147262 C) (@lem6147261 C op)). Qed.
Lemma lem6147264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147265 {C : Type'} (op : type1400 C) : (term663 C op) = (term663 C op).
Proof. exact (MK_COMB (@lem6147264) (@lem6147263 C op)). Qed.
Lemma lem6147266 {C : Type'} (op : type1400 C) : (term664 C op) = (term664 C op).
Proof. exact (MK_COMB (@lem6147265 C op) (@lem6147253 C op)). Qed.
Lemma lem6147267 {C : Type'} (op : type1400 C) (b : C) (a : C) : ((op a b) = (op b a)) = ((op a b) = (op b a)).
Proof. exact (eq_refl ((op a b) = (op b a))). Qed.
Lemma lem6147268 {C : Type'} (op : type1400 C) (a : C) : (term665 C op a) = (term665 C op a).
Proof. exact (fun_ext (fun b : C => @lem6147267 C op b a)). Qed.
Lemma lem6147269 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147270 {C : Type'} (op : type1400 C) (a : C) : (term666 C op a) = (term666 C op a).
Proof. exact (MK_COMB (@lem6147269 C) (@lem6147268 C op a)). Qed.
Lemma lem6147271 {C : Type'} (op : type1400 C) : (term667 C op) = (term667 C op).
Proof. exact (fun_ext (fun a : C => @lem6147270 C op a)). Qed.
Lemma lem6147272 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147273 {C : Type'} (op : type1400 C) : (term668 C op) = (term668 C op).
Proof. exact (MK_COMB (@lem6147272 C) (@lem6147271 C op)). Qed.
Lemma lem6147274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147275 {C : Type'} (op : type1400 C) : (term669 C op) = (term669 C op).
Proof. exact (MK_COMB (@lem6147274) (@lem6147273 C op)). Qed.
Lemma lem6147276 {C : Type'} (op : type1400 C) : (term670 C op) = (term670 C op).
Proof. exact (MK_COMB (@lem6147275 C op) (@lem6147266 C op)). Qed.
Lemma lem6147277 {C : Type'} (op : type1400 C) (a : C) : ((term671 C a op) = a) = ((term671 C a op) = a).
Proof. exact (eq_refl ((term671 C a op) = a)). Qed.
Lemma lem6147278 {C : Type'} (op : type1400 C) : (term672 C op) = (term672 C op).
Proof. exact (fun_ext (fun a : C => @lem6147277 C op a)). Qed.
Lemma lem6147279 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147280 {C : Type'} (op : type1400 C) : (term673 C op) = (term673 C op).
Proof. exact (MK_COMB (@lem6147279 C) (@lem6147278 C op)). Qed.
Lemma lem6147281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147282 {C : Type'} (op : type1400 C) : (term674 C op) = (term674 C op).
Proof. exact (MK_COMB (@lem6147281) (@lem6147280 C op)). Qed.
Lemma lem6147283 {C : Type'} (op : type1400 C) : (term675 C op) = (term675 C op).
Proof. exact (MK_COMB (@lem6147282 C op) (@lem6147276 C op)). Qed.
Lemma lem6147284 {C : Type'} (op : type1400 C) (a : C) : ((term676 C op a) = a) = ((term676 C op a) = a).
Proof. exact (eq_refl ((term676 C op a) = a)). Qed.
Lemma lem6147285 {C : Type'} (op : type1400 C) : (term677 C op) = (term677 C op).
Proof. exact (fun_ext (fun a : C => @lem6147284 C op a)). Qed.
Lemma lem6147286 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6147287 {C : Type'} (op : type1400 C) : (term678 C op) = (term678 C op).
Proof. exact (MK_COMB (@lem6147286 C) (@lem6147285 C op)). Qed.
Lemma lem6147288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147289 {C : Type'} (op : type1400 C) : (term679 C op) = (term679 C op).
Proof. exact (MK_COMB (@lem6147288) (@lem6147287 C op)). Qed.
Lemma lem6147290 {C : Type'} (op : type1400 C) : (term680 C op) = (term680 C op).
Proof. exact (MK_COMB (@lem6147289 C op) (@lem6147283 C op)). Qed.
Lemma lem6147293 {C : Type'} (op : type1400 C) : (term301 C op) = (term301 C op).
Proof. exact (eq_refl (term301 C op)). Qed.
Lemma lem6147294 {C : Type'} (op : type1400 C) : (term681 C op) = (term681 C op).
Proof. exact (MK_COMB (@lem6147293 C op) (@lem6147290 C op)). Qed.
Lemma lem6147295 {C : Type'} : (term682 C) = (term682 C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6147294 C op)). Qed.
Lemma lem6147296 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6147297 {C : Type'} : (term603 C) = (term603 C).
Proof. exact (MK_COMB (@lem6147296 C) (@lem6147295 C)). Qed.
Lemma lem6147298 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6147299 {C : Type'} : (term609 C) = (term609 C).
Proof. exact (MK_COMB (@lem6147298) (@lem6147297 C)). Qed.
Lemma lem6147300 {B : Type'} (b : B) (op : type1400 B) (a : B) (c : B) : ((term649 B a op b c) = (term649 B b op a c)) = ((term649 B a op b c) = (term649 B b op a c)).
Proof. exact (eq_refl ((term649 B a op b c) = (term649 B b op a c))). Qed.
Lemma lem6147301 {B : Type'} (b : B) (op : type1400 B) (a : B) : (term650 B b op a) = (term650 B b op a).
Proof. exact (fun_ext (fun c : B => @lem6147300 B b op a c)). Qed.
Lemma lem6147302 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147303 {B : Type'} (b : B) (op : type1400 B) (a : B) : (term651 B b op a) = (term651 B b op a).
Proof. exact (MK_COMB (@lem6147302 B) (@lem6147301 B b op a)). Qed.
Lemma lem6147304 {B : Type'} (op : type1400 B) (a : B) : (term652 B op a) = (term652 B op a).
Proof. exact (fun_ext (fun b : B => @lem6147303 B b op a)). Qed.
Lemma lem6147305 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147306 {B : Type'} (op : type1400 B) (a : B) : (term653 B op a) = (term653 B op a).
Proof. exact (MK_COMB (@lem6147305 B) (@lem6147304 B op a)). Qed.
Lemma lem6147307 {B : Type'} (op : type1400 B) : (term654 B op) = (term654 B op).
Proof. exact (fun_ext (fun a : B => @lem6147306 B op a)). Qed.
Lemma lem6147308 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147309 {B : Type'} (op : type1400 B) : (term655 B op) = (term655 B op).
Proof. exact (MK_COMB (@lem6147308 B) (@lem6147307 B op)). Qed.
Lemma lem6147310 {B : Type'} (a : B) (op : type1400 B) (b : B) (c : B) : ((term656 B op a b c) = (term649 B a op b c)) = ((term656 B op a b c) = (term649 B a op b c)).
Proof. exact (eq_refl ((term656 B op a b c) = (term649 B a op b c))). Qed.
Lemma lem6147311 {B : Type'} (a : B) (op : type1400 B) (b : B) : (term657 B a op b) = (term657 B a op b).
Proof. exact (fun_ext (fun c : B => @lem6147310 B a op b c)). Qed.
Lemma lem6147312 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147313 {B : Type'} (a : B) (op : type1400 B) (b : B) : (term658 B a op b) = (term658 B a op b).
Proof. exact (MK_COMB (@lem6147312 B) (@lem6147311 B a op b)). Qed.
Lemma lem6147314 {B : Type'} (a : B) (op : type1400 B) : (term659 B a op) = (term659 B a op).
Proof. exact (fun_ext (fun b : B => @lem6147313 B a op b)). Qed.
Lemma lem6147315 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147316 {B : Type'} (a : B) (op : type1400 B) : (term660 B a op) = (term660 B a op).
Proof. exact (MK_COMB (@lem6147315 B) (@lem6147314 B a op)). Qed.
Lemma lem6147317 {B : Type'} (op : type1400 B) : (term661 B op) = (term661 B op).
Proof. exact (fun_ext (fun a : B => @lem6147316 B a op)). Qed.
Lemma lem6147318 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147319 {B : Type'} (op : type1400 B) : (term662 B op) = (term662 B op).
Proof. exact (MK_COMB (@lem6147318 B) (@lem6147317 B op)). Qed.
Lemma lem6147320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147321 {B : Type'} (op : type1400 B) : (term663 B op) = (term663 B op).
Proof. exact (MK_COMB (@lem6147320) (@lem6147319 B op)). Qed.
Lemma lem6147322 {B : Type'} (op : type1400 B) : (term664 B op) = (term664 B op).
Proof. exact (MK_COMB (@lem6147321 B op) (@lem6147309 B op)). Qed.
Lemma lem6147323 {B : Type'} (op : type1400 B) (b : B) (a : B) : ((op a b) = (op b a)) = ((op a b) = (op b a)).
Proof. exact (eq_refl ((op a b) = (op b a))). Qed.
Lemma lem6147324 {B : Type'} (op : type1400 B) (a : B) : (term665 B op a) = (term665 B op a).
Proof. exact (fun_ext (fun b : B => @lem6147323 B op b a)). Qed.
Lemma lem6147325 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147326 {B : Type'} (op : type1400 B) (a : B) : (term666 B op a) = (term666 B op a).
Proof. exact (MK_COMB (@lem6147325 B) (@lem6147324 B op a)). Qed.
Lemma lem6147327 {B : Type'} (op : type1400 B) : (term667 B op) = (term667 B op).
Proof. exact (fun_ext (fun a : B => @lem6147326 B op a)). Qed.
Lemma lem6147328 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147329 {B : Type'} (op : type1400 B) : (term668 B op) = (term668 B op).
Proof. exact (MK_COMB (@lem6147328 B) (@lem6147327 B op)). Qed.
Lemma lem6147330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147331 {B : Type'} (op : type1400 B) : (term669 B op) = (term669 B op).
Proof. exact (MK_COMB (@lem6147330) (@lem6147329 B op)). Qed.
Lemma lem6147332 {B : Type'} (op : type1400 B) : (term670 B op) = (term670 B op).
Proof. exact (MK_COMB (@lem6147331 B op) (@lem6147322 B op)). Qed.
Lemma lem6147333 {B : Type'} (op : type1400 B) (a : B) : ((term671 B a op) = a) = ((term671 B a op) = a).
Proof. exact (eq_refl ((term671 B a op) = a)). Qed.
Lemma lem6147334 {B : Type'} (op : type1400 B) : (term672 B op) = (term672 B op).
Proof. exact (fun_ext (fun a : B => @lem6147333 B op a)). Qed.
Lemma lem6147335 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147336 {B : Type'} (op : type1400 B) : (term673 B op) = (term673 B op).
Proof. exact (MK_COMB (@lem6147335 B) (@lem6147334 B op)). Qed.
Lemma lem6147337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147338 {B : Type'} (op : type1400 B) : (term674 B op) = (term674 B op).
Proof. exact (MK_COMB (@lem6147337) (@lem6147336 B op)). Qed.
Lemma lem6147339 {B : Type'} (op : type1400 B) : (term675 B op) = (term675 B op).
Proof. exact (MK_COMB (@lem6147338 B op) (@lem6147332 B op)). Qed.
Lemma lem6147340 {B : Type'} (op : type1400 B) (a : B) : ((term676 B op a) = a) = ((term676 B op a) = a).
Proof. exact (eq_refl ((term676 B op a) = a)). Qed.
Lemma lem6147341 {B : Type'} (op : type1400 B) : (term677 B op) = (term677 B op).
Proof. exact (fun_ext (fun a : B => @lem6147340 B op a)). Qed.
Lemma lem6147342 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6147343 {B : Type'} (op : type1400 B) : (term678 B op) = (term678 B op).
Proof. exact (MK_COMB (@lem6147342 B) (@lem6147341 B op)). Qed.
Lemma lem6147344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147345 {B : Type'} (op : type1400 B) : (term679 B op) = (term679 B op).
Proof. exact (MK_COMB (@lem6147344) (@lem6147343 B op)). Qed.
Lemma lem6147346 {B : Type'} (op : type1400 B) : (term680 B op) = (term680 B op).
Proof. exact (MK_COMB (@lem6147345 B op) (@lem6147339 B op)). Qed.
Lemma lem6147349 {B : Type'} (op : type1400 B) : (term301 B op) = (term301 B op).
Proof. exact (eq_refl (term301 B op)). Qed.
Lemma lem6147350 {B : Type'} (op : type1400 B) : (term681 B op) = (term681 B op).
Proof. exact (MK_COMB (@lem6147349 B op) (@lem6147346 B op)). Qed.
Lemma lem6147351 {B : Type'} : (term682 B) = (term682 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6147350 B op)). Qed.
Lemma lem6147352 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6147353 {B : Type'} : (term603 B) = (term603 B).
Proof. exact (MK_COMB (@lem6147352 B) (@lem6147351 B)). Qed.
Lemma lem6147354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6147355 {B : Type'} : (term610 B) = (term610 B).
Proof. exact (MK_COMB (@lem6147354) (@lem6147353 B)). Qed.
Lemma lem6147356 {B C : Type'} : (term612 B C) = (term612 B C).
Proof. exact (MK_COMB (@lem6147355 B) (@lem6147299 C)). Qed.
Lemma lem6147357 {A : Type'} (b : A) (op : type1400 A) (a : A) (c : A) : ((term649 A a op b c) = (term649 A b op a c)) = ((term649 A a op b c) = (term649 A b op a c)).
Proof. exact (eq_refl ((term649 A a op b c) = (term649 A b op a c))). Qed.
Lemma lem6147358 {A : Type'} (b : A) (op : type1400 A) (a : A) : (term650 A b op a) = (term650 A b op a).
Proof. exact (fun_ext (fun c : A => @lem6147357 A b op a c)). Qed.
Lemma lem6147359 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147360 {A : Type'} (b : A) (op : type1400 A) (a : A) : (term651 A b op a) = (term651 A b op a).
Proof. exact (MK_COMB (@lem6147359 A) (@lem6147358 A b op a)). Qed.
Lemma lem6147361 {A : Type'} (op : type1400 A) (a : A) : (term652 A op a) = (term652 A op a).
Proof. exact (fun_ext (fun b : A => @lem6147360 A b op a)). Qed.
Lemma lem6147362 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147363 {A : Type'} (op : type1400 A) (a : A) : (term653 A op a) = (term653 A op a).
Proof. exact (MK_COMB (@lem6147362 A) (@lem6147361 A op a)). Qed.
Lemma lem6147364 {A : Type'} (op : type1400 A) : (term654 A op) = (term654 A op).
Proof. exact (fun_ext (fun a : A => @lem6147363 A op a)). Qed.
Lemma lem6147365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147366 {A : Type'} (op : type1400 A) : (term655 A op) = (term655 A op).
Proof. exact (MK_COMB (@lem6147365 A) (@lem6147364 A op)). Qed.
Lemma lem6147367 {A : Type'} (a : A) (op : type1400 A) (b : A) (c : A) : ((term656 A op a b c) = (term649 A a op b c)) = ((term656 A op a b c) = (term649 A a op b c)).
Proof. exact (eq_refl ((term656 A op a b c) = (term649 A a op b c))). Qed.
Lemma lem6147368 {A : Type'} (a : A) (op : type1400 A) (b : A) : (term657 A a op b) = (term657 A a op b).
Proof. exact (fun_ext (fun c : A => @lem6147367 A a op b c)). Qed.
Lemma lem6147369 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147370 {A : Type'} (a : A) (op : type1400 A) (b : A) : (term658 A a op b) = (term658 A a op b).
Proof. exact (MK_COMB (@lem6147369 A) (@lem6147368 A a op b)). Qed.
Lemma lem6147371 {A : Type'} (a : A) (op : type1400 A) : (term659 A a op) = (term659 A a op).
Proof. exact (fun_ext (fun b : A => @lem6147370 A a op b)). Qed.
Lemma lem6147372 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147373 {A : Type'} (a : A) (op : type1400 A) : (term660 A a op) = (term660 A a op).
Proof. exact (MK_COMB (@lem6147372 A) (@lem6147371 A a op)). Qed.
Lemma lem6147374 {A : Type'} (op : type1400 A) : (term661 A op) = (term661 A op).
Proof. exact (fun_ext (fun a : A => @lem6147373 A a op)). Qed.
Lemma lem6147375 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147376 {A : Type'} (op : type1400 A) : (term662 A op) = (term662 A op).
Proof. exact (MK_COMB (@lem6147375 A) (@lem6147374 A op)). Qed.
Lemma lem6147377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147378 {A : Type'} (op : type1400 A) : (term663 A op) = (term663 A op).
Proof. exact (MK_COMB (@lem6147377) (@lem6147376 A op)). Qed.
Lemma lem6147379 {A : Type'} (op : type1400 A) : (term664 A op) = (term664 A op).
Proof. exact (MK_COMB (@lem6147378 A op) (@lem6147366 A op)). Qed.
Lemma lem6147380 {A : Type'} (op : type1400 A) (b : A) (a : A) : ((op a b) = (op b a)) = ((op a b) = (op b a)).
Proof. exact (eq_refl ((op a b) = (op b a))). Qed.
Lemma lem6147381 {A : Type'} (op : type1400 A) (a : A) : (term665 A op a) = (term665 A op a).
Proof. exact (fun_ext (fun b : A => @lem6147380 A op b a)). Qed.
Lemma lem6147382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147383 {A : Type'} (op : type1400 A) (a : A) : (term666 A op a) = (term666 A op a).
Proof. exact (MK_COMB (@lem6147382 A) (@lem6147381 A op a)). Qed.
Lemma lem6147384 {A : Type'} (op : type1400 A) : (term667 A op) = (term667 A op).
Proof. exact (fun_ext (fun a : A => @lem6147383 A op a)). Qed.
Lemma lem6147385 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147386 {A : Type'} (op : type1400 A) : (term668 A op) = (term668 A op).
Proof. exact (MK_COMB (@lem6147385 A) (@lem6147384 A op)). Qed.
Lemma lem6147387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147388 {A : Type'} (op : type1400 A) : (term669 A op) = (term669 A op).
Proof. exact (MK_COMB (@lem6147387) (@lem6147386 A op)). Qed.
Lemma lem6147389 {A : Type'} (op : type1400 A) : (term670 A op) = (term670 A op).
Proof. exact (MK_COMB (@lem6147388 A op) (@lem6147379 A op)). Qed.
Lemma lem6147390 {A : Type'} (op : type1400 A) (a : A) : ((term671 A a op) = a) = ((term671 A a op) = a).
Proof. exact (eq_refl ((term671 A a op) = a)). Qed.
Lemma lem6147391 {A : Type'} (op : type1400 A) : (term672 A op) = (term672 A op).
Proof. exact (fun_ext (fun a : A => @lem6147390 A op a)). Qed.
Lemma lem6147392 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147393 {A : Type'} (op : type1400 A) : (term673 A op) = (term673 A op).
Proof. exact (MK_COMB (@lem6147392 A) (@lem6147391 A op)). Qed.
Lemma lem6147394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147395 {A : Type'} (op : type1400 A) : (term674 A op) = (term674 A op).
Proof. exact (MK_COMB (@lem6147394) (@lem6147393 A op)). Qed.
Lemma lem6147396 {A : Type'} (op : type1400 A) : (term675 A op) = (term675 A op).
Proof. exact (MK_COMB (@lem6147395 A op) (@lem6147389 A op)). Qed.
Lemma lem6147397 {A : Type'} (op : type1400 A) (a : A) : ((term676 A op a) = a) = ((term676 A op a) = a).
Proof. exact (eq_refl ((term676 A op a) = a)). Qed.
Lemma lem6147398 {A : Type'} (op : type1400 A) : (term677 A op) = (term677 A op).
Proof. exact (fun_ext (fun a : A => @lem6147397 A op a)). Qed.
Lemma lem6147399 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147400 {A : Type'} (op : type1400 A) : (term678 A op) = (term678 A op).
Proof. exact (MK_COMB (@lem6147399 A) (@lem6147398 A op)). Qed.
Lemma lem6147401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6147402 {A : Type'} (op : type1400 A) : (term679 A op) = (term679 A op).
Proof. exact (MK_COMB (@lem6147401) (@lem6147400 A op)). Qed.
Lemma lem6147403 {A : Type'} (op : type1400 A) : (term680 A op) = (term680 A op).
Proof. exact (MK_COMB (@lem6147402 A op) (@lem6147396 A op)). Qed.
Lemma lem6147406 {A : Type'} (op : type1400 A) : (term301 A op) = (term301 A op).
Proof. exact (eq_refl (term301 A op)). Qed.
Lemma lem6147407 {A : Type'} (op : type1400 A) : (term681 A op) = (term681 A op).
Proof. exact (MK_COMB (@lem6147406 A op) (@lem6147403 A op)). Qed.
Lemma lem6147408 {A : Type'} : (term682 A) = (term682 A).
Proof. exact (fun_ext (fun op : type1400 A => @lem6147407 A op)). Qed.
Lemma lem6147409 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6147410 {A : Type'} : (term603 A) = (term603 A).
Proof. exact (MK_COMB (@lem6147409 A) (@lem6147408 A)). Qed.
Lemma lem6147411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6147412 {A : Type'} : (term610 A) = (term610 A).
Proof. exact (MK_COMB (@lem6147411) (@lem6147410 A)). Qed.
Lemma lem6147413 {A B C : Type'} : (term614 A B C) = (term614 A B C).
Proof. exact (MK_COMB (@lem6147412 A) (@lem6147356 B C)). Qed.
Lemma lem6147418 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term932 A B C op f s g) = (term932 A B C op f s g).
Proof. exact (eq_refl (term932 A B C op f s g)). Qed.
Lemma lem6147419 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term934 A B C op f s g) = (term934 A B C op f s g).
Proof. exact (MK_COMB (@lem6147418 A B C op f s g) (@lem6147413 A B C)). Qed.
Lemma lem6147424 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) : (term683 A B a f x s) = (term683 A B a f x s).
Proof. exact (eq_refl (term683 A B a f x s)). Qed.
Lemma lem6147425 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term684 A B a f s) = (term684 A B a f s).
Proof. exact (fun_ext (fun x : A => @lem6147424 A B a f x s)). Qed.
Lemma lem6147426 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6147427 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term559 A B a f s) = (term559 A B a f s).
Proof. exact (MK_COMB (@lem6147426 A) (@lem6147425 A B a f s)). Qed.
Lemma lem6147428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6147429 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term579 A B a f s) = (term579 A B a f s).
Proof. exact (MK_COMB (@lem6147428) (@lem6147427 A B a f s)). Qed.
Lemma lem6147430 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term936 A B C a op f s g) = (term936 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147429 A B a f s) (@lem6147419 A B C op f s g)). Qed.
Lemma lem6147457 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term266 A B C a s x' g f y op) = (term266 A B C a s x' g f y op).
Proof. exact (eq_refl (term266 A B C a s x' g f y op)). Qed.
Lemma lem6147458 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term267 A B C a s x' g f op) = (term267 A B C a s x' g f op).
Proof. exact (fun_ext (fun y : A => @lem6147457 A B C a s x' g f y op)). Qed.
Lemma lem6147459 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147460 {A B C : Type'} (a : A) (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term268 A B C a s x' g f op) = (term268 A B C a s x' g f op).
Proof. exact (MK_COMB (@lem6147459 A) (@lem6147458 A B C a s x' g f op)). Qed.
Lemma lem6147461 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term269 A B C a s g f op) = (term269 A B C a s g f op).
Proof. exact (fun_ext (fun x' : A => @lem6147460 A B C a s x' g f op)). Qed.
Lemma lem6147462 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147463 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term270 A B C a s g f op) = (term270 A B C a s g f op).
Proof. exact (MK_COMB (@lem6147462 A) (@lem6147461 A B C a s g f op)). Qed.
Lemma lem6147464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6147465 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term272 A B C a s g f op) = (term272 A B C a s g f op).
Proof. exact (MK_COMB (@lem6147464) (@lem6147463 A B C a s g f op)). Qed.
Lemma lem6147466 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term938 A B C a op f s g) = (term938 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147465 A B C a s g f op) (@lem6147430 A B C a op f s g)). Qed.
Lemma lem6147469 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (eq_refl (term70 A s)). Qed.
Lemma lem6147470 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term940 A B C a op f s g) = (term940 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147469 A s) (@lem6147466 A B C a op f s g)). Qed.
Lemma lem6147475 {A : Type'} (a : A) (s : A -> Prop) : (term295 A a s) = (term295 A a s).
Proof. exact (eq_refl (term295 A a s)). Qed.
Lemma lem6147476 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term942 A B C a op f s g) = (term942 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147475 A a s) (@lem6147470 A B C a op f s g)). Qed.
Lemma lem6147477 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6147496 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term163 A B C s x g f y op) = (term163 A B C s x g f y op).
Proof. exact (eq_refl (term163 A B C s x g f y op)). Qed.
Lemma lem6147497 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term165 A B C s x g f op) = (term165 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6147496 A B C s x g f y op)). Qed.
Lemma lem6147498 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147499 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term167 A B C s x g f op) = (term167 A B C s x g f op).
Proof. exact (MK_COMB (@lem6147498 A) (@lem6147497 A B C s x g f op)). Qed.
Lemma lem6147500 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term169 A B C s g f op) = (term169 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6147499 A B C s x g f op)). Qed.
Lemma lem6147501 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147502 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term170 A B C s g f op) = (term170 A B C s g f op).
Proof. exact (MK_COMB (@lem6147501 A) (@lem6147500 A B C s g f op)). Qed.
Lemma lem6147503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6147504 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term323 A B C s g f op) = (term323 A B C s g f op).
Proof. exact (MK_COMB (@lem6147503) (@lem6147502 A B C s g f op)). Qed.
Lemma lem6147505 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term175 A B C op s g f).
Proof. exact (MK_COMB (@lem6147504 A B C s g f op) (@lem6147477 A B C op s g f)). Qed.
Lemma lem6147506 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6147507 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term298 A B C op s g f) = (term298 A B C op s g f).
Proof. exact (MK_COMB (@lem6147506) (@lem6147505 A B C op s g f)). Qed.
Lemma lem6147508 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term944 A B C a op f s g) = (term944 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147507 A B C op s g f) (@lem6147476 A B C a op f s g)). Qed.
Lemma lem6147511 {C : Type'} (op : type1400 C) : (term301 C op) = (term301 C op).
Proof. exact (eq_refl (term301 C op)). Qed.
Lemma lem6147512 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term945 A B C a op f s g) = (term945 A B C a op f s g).
Proof. exact (MK_COMB (@lem6147511 C op) (@lem6147508 A B C a op f s g)). Qed.
Lemma lem6147513 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term947 A B C op f s g) = (term947 A B C op f s g).
Proof. exact (fun_ext (fun a : A => @lem6147512 A B C a op f s g)). Qed.
Lemma lem6147514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6147515 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term949 A B C op f s g) = (term949 A B C op f s g).
Proof. exact (MK_COMB (@lem6147514 A) (@lem6147513 A B C op f s g)). Qed.
Lemma lem6147516 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term951 A B C f s g) = (term951 A B C f s g).
Proof. exact (fun_ext (fun op : type1400 C => @lem6147515 A B C op f s g)). Qed.
Lemma lem6147517 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6147518 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term953 A B C f s g) = (term953 A B C f s g).
Proof. exact (MK_COMB (@lem6147517 C) (@lem6147516 A B C f s g)). Qed.
Lemma lem6147519 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term955 A B C s g) = (term955 A B C s g).
Proof. exact (fun_ext (fun f : A -> B => @lem6147518 A B C f s g)). Qed.
Lemma lem6147520 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6147521 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term957 A B C s g) = (term957 A B C s g).
Proof. exact (MK_COMB (@lem6147520 A B) (@lem6147519 A B C s g)). Qed.
Lemma lem6147522 {A B C : Type'} (g : B -> C) : (term959 A B C g) = (term959 A B C g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6147521 A B C s g)). Qed.
Lemma lem6147523 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6147524 {A B C : Type'} (g : B -> C) : (term961 A B C g) = (term961 A B C g).
Proof. exact (MK_COMB (@lem6147523 A) (@lem6147522 A B C g)). Qed.
Lemma lem6147525 {A B C : Type'} : (term963 A B C) = (term963 A B C).
Proof. exact (fun_ext (fun g : B -> C => @lem6147524 A B C g)). Qed.
Lemma lem6147526 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem6147527 {A B C : Type'} : (term965 A B C) = (term965 A B C).
Proof. exact (MK_COMB (@lem6147526 B C) (@lem6147525 A B C)). Qed.
Lemma lem6147860 {A B C : Type'} : (term964 A B C) = (term965 A B C).
Proof. exact (TRANS (@lem6147243 A B C) (@lem6147527 A B C)). Qed.
Lemma lem6147861 {A B C : Type'} : (term965 A B C) = (term964 A B C).
Proof. exact (SYM (@lem6147860 A B C)). Qed.
Lemma lem6147863 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term175 A B C op s g f.
Proof. exact (h1). Qed.
Lemma lem6147867 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) (h1 : term559 A B a f s) : term559 A B a f s.
Proof. exact (h1). Qed.
Lemma lem6147871 {C : Type'} (h1 : term603 C) : term603 C.
Proof. exact (h1). Qed.
Lemma lem6147877 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem6147896 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term324 A B C s x g f y op) = (term325 A B C s x g f y op).
Proof. exact (@lem17362 (term152 A B s x f y) ((term110 A B C g f y) = (@neutral C op))). Qed.
Lemma lem6147897 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6147898 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term328 A B C s x g f op) = (term329 A B C s x g f op).
Proof. exact (@lem6147897 A (term165 A B C s x g f op)). Qed.
Lemma lem6147899 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term330 A B C s x g f op y) = (term163 A B C s x g f y op).
Proof. exact (eq_refl (term330 A B C s x g f op y)). Qed.
Lemma lem6147900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6147901 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term331 A B C s x g f op y) = (term324 A B C s x g f y op).
Proof. exact (MK_COMB (@lem6147900) (@lem6147899 A B C s x g f y op)). Qed.
Lemma lem6147902 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term331 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (TRANS (@lem6147901 A B C s x g f y op) (@lem6147896 A B C s x g f y op)). Qed.
Lemma lem6147903 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term332 A B C s x g f op) = (term333 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6147902 A B C s x g f y op)). Qed.
Lemma lem6147904 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6147905 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term329 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (MK_COMB (@lem6147904 A) (@lem6147903 A B C s x g f op)). Qed.
Lemma lem6147906 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term328 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (TRANS (@lem6147898 A B C s x g f op) (@lem6147905 A B C s x g f op)). Qed.
Lemma lem6147907 {A : Type'} (P : A -> Prop) : (term326 A P) = (term327 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6147908 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term335 A B C s g f op) = (term336 A B C s g f op).
Proof. exact (@lem6147907 A (term169 A B C s g f op)). Qed.
Lemma lem6147909 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term337 A B C s g f op x) = (term167 A B C s x g f op).
Proof. exact (eq_refl (term337 A B C s g f op x)). Qed.
Lemma lem6147910 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6147911 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term338 A B C s g f op x) = (term328 A B C s x g f op).
Proof. exact (MK_COMB (@lem6147910) (@lem6147909 A B C s x g f op)). Qed.
Lemma lem6147912 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term338 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (TRANS (@lem6147911 A B C s x g f op) (@lem6147906 A B C s x g f op)). Qed.
Lemma lem6147913 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term339 A B C s g f op) = (term340 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6147912 A B C s x g f op)). Qed.
Lemma lem6147914 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6147915 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term336 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (MK_COMB (@lem6147914 A) (@lem6147913 A B C s g f op)). Qed.
Lemma lem6147916 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term335 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (TRANS (@lem6147908 A B C s g f op) (@lem6147915 A B C s g f op)). Qed.
Lemma lem6147917 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6147918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6147919 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term342 A B C s g f op) = (term343 A B C s g f op).
Proof. exact (MK_COMB (@lem6147918) (@lem6147916 A B C s g f op)). Qed.
Lemma lem6147920 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term344 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (MK_COMB (@lem6147919 A B C s g f op) (@lem6147917 A B C op s g f)). Qed.
Lemma lem6147921 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term344 A B C op s g f).
Proof. exact (@lem17265 (term170 A B C s g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6147922 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (TRANS (@lem6147921 A B C op s g f) (@lem6147920 A B C op s g f)). Qed.
Lemma lem6147977 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6147978 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem6147977 A P Q). Qed.
Lemma lem6147979 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term348 A B C op s g f) = (term349 A B C op s g f).
Proof. exact (@lem6147978 A (term340 A B C s g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6147980 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term350 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (eq_refl (term350 A B C s g f op x)). Qed.
Lemma lem6147981 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term351 A B C s g f op) = (term340 A B C s g f op).
Proof. exact (fun_ext (fun x : A => @lem6147980 A B C s x g f op)). Qed.
Lemma lem6147982 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6147983 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term352 A B C s g f op) = (term341 A B C s g f op).
Proof. exact (MK_COMB (@lem6147982 A) (@lem6147981 A B C s g f op)). Qed.
Lemma lem6147984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6147985 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) : (term353 A B C s g f op) = (term343 A B C s g f op).
Proof. exact (MK_COMB (@lem6147984) (@lem6147983 A B C s g f op)). Qed.
Lemma lem6147986 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6147987 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term348 A B C op s g f) = (term345 A B C op s g f).
Proof. exact (MK_COMB (@lem6147985 A B C s g f op) (@lem6147986 A B C op s g f)). Qed.
Lemma lem6147988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6147989 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term354 A B C op s g f) = (term355 A B C op s g f).
Proof. exact (MK_COMB (@lem6147988) (@lem6147987 A B C op s g f)). Qed.
Lemma lem6147990 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term350 A B C s g f op x) = (term334 A B C s x g f op).
Proof. exact (eq_refl (term350 A B C s g f op x)). Qed.
Lemma lem6147991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6147992 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term356 A B C s g f op x) = (term357 A B C s x g f op).
Proof. exact (MK_COMB (@lem6147991) (@lem6147990 A B C s x g f op)). Qed.
Lemma lem6147993 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6147994 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term358 A B C x op s g f) = (term359 A B C x op s g f).
Proof. exact (MK_COMB (@lem6147992 A B C s x g f op) (@lem6147993 A B C op s g f)). Qed.
Lemma lem6147995 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term360 A B C op s g f) = (term361 A B C op s g f).
Proof. exact (fun_ext (fun x : A => @lem6147994 A B C x op s g f)). Qed.
Lemma lem6147996 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6147997 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term349 A B C op s g f) = (term362 A B C op s g f).
Proof. exact (MK_COMB (@lem6147996 A) (@lem6147995 A B C op s g f)). Qed.
Lemma lem6147998 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term348 A B C op s g f) = (term349 A B C op s g f)) = ((term345 A B C op s g f) = (term362 A B C op s g f)).
Proof. exact (MK_COMB (@lem6147989 A B C op s g f) (@lem6147997 A B C op s g f)). Qed.
Lemma lem6147999 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term345 A B C op s g f) = (term362 A B C op s g f).
Proof. exact (EQ_MP (@lem6147998 A B C op s g f) (@lem6147979 A B C op s g f)). Qed.
Lemma lem6148001 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6148002 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem6148001 A P Q). Qed.
Lemma lem6148003 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term363 A B C x op s g f) = (term364 A B C x op s g f).
Proof. exact (@lem6148002 A (term333 A B C s x g f op) ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6148004 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term365 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (eq_refl (term365 A B C s x g f op y)). Qed.
Lemma lem6148005 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term366 A B C s x g f op) = (term333 A B C s x g f op).
Proof. exact (fun_ext (fun y : A => @lem6148004 A B C s x g f y op)). Qed.
Lemma lem6148006 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6148007 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term367 A B C s x g f op) = (term334 A B C s x g f op).
Proof. exact (MK_COMB (@lem6148006 A) (@lem6148005 A B C s x g f op)). Qed.
Lemma lem6148008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6148009 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (op : type1400 C) : (term368 A B C s x g f op) = (term357 A B C s x g f op).
Proof. exact (MK_COMB (@lem6148008) (@lem6148007 A B C s x g f op)). Qed.
Lemma lem6148010 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6148011 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term363 A B C x op s g f) = (term359 A B C x op s g f).
Proof. exact (MK_COMB (@lem6148009 A B C s x g f op) (@lem6148010 A B C op s g f)). Qed.
Lemma lem6148012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6148013 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term369 A B C x op s g f) = (term370 A B C x op s g f).
Proof. exact (MK_COMB (@lem6148012) (@lem6148011 A B C x op s g f)). Qed.
Lemma lem6148014 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term365 A B C s x g f op y) = (term325 A B C s x g f y op).
Proof. exact (eq_refl (term365 A B C s x g f op y)). Qed.
Lemma lem6148015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6148016 {A B C : Type'} (s : A -> Prop) (x : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term371 A B C s x g f op y) = (term372 A B C s x g f y op).
Proof. exact (MK_COMB (@lem6148015) (@lem6148014 A B C s x g f y op)). Qed.
Lemma lem6148017 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term33 A B C op f s g) = (term34 A B C op s g f)).
Proof. exact (eq_refl ((term33 A B C op f s g) = (term34 A B C op s g f))). Qed.
Lemma lem6148018 {A B C : Type'} (x : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term373 A B C x y op s g f) = (term374 A B C x y op s g f).
Proof. exact (MK_COMB (@lem6148016 A B C s x g f y op) (@lem6148017 A B C op s g f)). Qed.
Lemma lem6148019 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term375 A B C x op s g f) = (term376 A B C x op s g f).
Proof. exact (fun_ext (fun y : A => @lem6148018 A B C x y op s g f)). Qed.
Lemma lem6148020 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6148021 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term364 A B C x op s g f) = (term377 A B C x op s g f).
Proof. exact (MK_COMB (@lem6148020 A) (@lem6148019 A B C x op s g f)). Qed.
Lemma lem6148022 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term363 A B C x op s g f) = (term364 A B C x op s g f)) = ((term359 A B C x op s g f) = (term377 A B C x op s g f)).
Proof. exact (MK_COMB (@lem6148013 A B C x op s g f) (@lem6148021 A B C x op s g f)). Qed.
Lemma lem6148023 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term359 A B C x op s g f) = (term377 A B C x op s g f).
Proof. exact (EQ_MP (@lem6148022 A B C x op s g f) (@lem6148003 A B C x op s g f)). Qed.
Lemma lem6148024 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term361 A B C op s g f) = (term378 A B C op s g f).
Proof. exact (fun_ext (fun x : A => @lem6148023 A B C x op s g f)). Qed.
Lemma lem6148025 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6148026 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term362 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (MK_COMB (@lem6148025 A) (@lem6148024 A B C op s g f)). Qed.
Lemma lem6148028 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term345 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (TRANS (@lem6147999 A B C op s g f) (@lem6148026 A B C op s g f)). Qed.
Lemma lem6148029 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term175 A B C op s g f) = (term379 A B C op s g f).
Proof. exact (TRANS (@lem6147922 A B C op s g f) (@lem6148028 A B C op s g f)). Qed.
Lemma lem6148030 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term175 A B C op s g f) : term379 A B C op s g f.
Proof. exact (EQ_MP (@lem6148029 A B C op s g f) (@lem6147863 A B C op s g f h1)). Qed.
Lemma lem6148149 {A B : Type'} (a : A) (f : A -> B) (x : A) (s : A -> Prop) : (term683 A B a f x s) = (term683 A B a f x s).
Proof. exact (eq_refl (term683 A B a f x s)). Qed.
Lemma lem6148150 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term684 A B a f s) = (term684 A B a f s).
Proof. exact (fun_ext (fun x : A => @lem6148149 A B a f x s)). Qed.
Lemma lem6148151 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6148204 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) : (term559 A B a f s) = (term559 A B a f s).
Proof. exact (MK_COMB (@lem6148151 A) (@lem6148150 A B a f s)). Qed.
Lemma lem6148205 {A B : Type'} (a : A) (f : A -> B) (s : A -> Prop) (h1 : term559 A B a f s) : term559 A B a f s.
Proof. exact (EQ_MP (@lem6148204 A B a f s) (@lem6147867 A B a f s h1)). Qed.
Lemma lem6148211 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term927 A B C op f s g) : term927 A B C op f s g.
Proof. exact (h1). Qed.
Lemma lem6148511 {C : Type'} (op : type1400 C) (a : C) : ((term676 C op a) = a) = ((term676 C op a) = a).
Proof. exact (eq_refl ((term676 C op a) = a)). Qed.
Lemma lem6148512 {C : Type'} (op : type1400 C) : (term677 C op) = (term677 C op).
Proof. exact (fun_ext (fun a : C => @lem6148511 C op a)). Qed.
Lemma lem6148513 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148514 {C : Type'} (op : type1400 C) : (term678 C op) = (term678 C op).
Proof. exact (MK_COMB (@lem6148513 C) (@lem6148512 C op)). Qed.
Lemma lem6148515 {C : Type'} (op : type1400 C) (a : C) : ((term671 C a op) = a) = ((term671 C a op) = a).
Proof. exact (eq_refl ((term671 C a op) = a)). Qed.
Lemma lem6148516 {C : Type'} (op : type1400 C) : (term672 C op) = (term672 C op).
Proof. exact (fun_ext (fun a : C => @lem6148515 C op a)). Qed.
Lemma lem6148517 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148518 {C : Type'} (op : type1400 C) : (term673 C op) = (term673 C op).
Proof. exact (MK_COMB (@lem6148517 C) (@lem6148516 C op)). Qed.
Lemma lem6148519 {C : Type'} (op : type1400 C) (b : C) (a : C) : ((op a b) = (op b a)) = ((op a b) = (op b a)).
Proof. exact (eq_refl ((op a b) = (op b a))). Qed.
Lemma lem6148520 {C : Type'} (op : type1400 C) (a : C) : (term665 C op a) = (term665 C op a).
Proof. exact (fun_ext (fun b : C => @lem6148519 C op b a)). Qed.
Lemma lem6148521 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148522 {C : Type'} (op : type1400 C) (a : C) : (term666 C op a) = (term666 C op a).
Proof. exact (MK_COMB (@lem6148521 C) (@lem6148520 C op a)). Qed.
Lemma lem6148523 {C : Type'} (op : type1400 C) : (term667 C op) = (term667 C op).
Proof. exact (fun_ext (fun a : C => @lem6148522 C op a)). Qed.
Lemma lem6148524 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148525 {C : Type'} (op : type1400 C) : (term668 C op) = (term668 C op).
Proof. exact (MK_COMB (@lem6148524 C) (@lem6148523 C op)). Qed.
Lemma lem6148526 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : ((term656 C op a b c) = (term649 C a op b c)) = ((term656 C op a b c) = (term649 C a op b c)).
Proof. exact (eq_refl ((term656 C op a b c) = (term649 C a op b c))). Qed.
Lemma lem6148527 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term657 C a op b) = (term657 C a op b).
Proof. exact (fun_ext (fun c : C => @lem6148526 C a op b c)). Qed.
Lemma lem6148528 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148529 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term658 C a op b) = (term658 C a op b).
Proof. exact (MK_COMB (@lem6148528 C) (@lem6148527 C a op b)). Qed.
Lemma lem6148530 {C : Type'} (a : C) (op : type1400 C) : (term659 C a op) = (term659 C a op).
Proof. exact (fun_ext (fun b : C => @lem6148529 C a op b)). Qed.
Lemma lem6148531 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148532 {C : Type'} (a : C) (op : type1400 C) : (term660 C a op) = (term660 C a op).
Proof. exact (MK_COMB (@lem6148531 C) (@lem6148530 C a op)). Qed.
Lemma lem6148533 {C : Type'} (op : type1400 C) : (term661 C op) = (term661 C op).
Proof. exact (fun_ext (fun a : C => @lem6148532 C a op)). Qed.
Lemma lem6148534 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148535 {C : Type'} (op : type1400 C) : (term662 C op) = (term662 C op).
Proof. exact (MK_COMB (@lem6148534 C) (@lem6148533 C op)). Qed.
Lemma lem6148536 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : ((term649 C a op b c) = (term649 C b op a c)) = ((term649 C a op b c) = (term649 C b op a c)).
Proof. exact (eq_refl ((term649 C a op b c) = (term649 C b op a c))). Qed.
Lemma lem6148537 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term650 C b op a) = (term650 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6148536 C b op a c)). Qed.
Lemma lem6148538 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148539 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term651 C b op a) = (term651 C b op a).
Proof. exact (MK_COMB (@lem6148538 C) (@lem6148537 C b op a)). Qed.
Lemma lem6148540 {C : Type'} (op : type1400 C) (a : C) : (term652 C op a) = (term652 C op a).
Proof. exact (fun_ext (fun b : C => @lem6148539 C b op a)). Qed.
Lemma lem6148541 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148542 {C : Type'} (op : type1400 C) (a : C) : (term653 C op a) = (term653 C op a).
Proof. exact (MK_COMB (@lem6148541 C) (@lem6148540 C op a)). Qed.
Lemma lem6148543 {C : Type'} (op : type1400 C) : (term654 C op) = (term654 C op).
Proof. exact (fun_ext (fun a : C => @lem6148542 C op a)). Qed.
Lemma lem6148544 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6148545 {C : Type'} (op : type1400 C) : (term655 C op) = (term655 C op).
Proof. exact (MK_COMB (@lem6148544 C) (@lem6148543 C op)). Qed.
Lemma lem6148546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6148547 {C : Type'} (op : type1400 C) : (term663 C op) = (term663 C op).
Proof. exact (MK_COMB (@lem6148546) (@lem6148535 C op)). Qed.
Lemma lem6148548 {C : Type'} (op : type1400 C) : (term664 C op) = (term664 C op).
Proof. exact (MK_COMB (@lem6148547 C op) (@lem6148545 C op)). Qed.
Lemma lem6148549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6148550 {C : Type'} (op : type1400 C) : (term669 C op) = (term669 C op).
Proof. exact (MK_COMB (@lem6148549) (@lem6148525 C op)). Qed.
Lemma lem6148551 {C : Type'} (op : type1400 C) : (term670 C op) = (term670 C op).
Proof. exact (MK_COMB (@lem6148550 C op) (@lem6148548 C op)). Qed.
Lemma lem6148552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6148553 {C : Type'} (op : type1400 C) : (term674 C op) = (term674 C op).
Proof. exact (MK_COMB (@lem6148552) (@lem6148518 C op)). Qed.
Lemma lem6148554 {C : Type'} (op : type1400 C) : (term675 C op) = (term675 C op).
Proof. exact (MK_COMB (@lem6148553 C op) (@lem6148551 C op)). Qed.
Lemma lem6148555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6148556 {C : Type'} (op : type1400 C) : (term679 C op) = (term679 C op).
Proof. exact (MK_COMB (@lem6148555) (@lem6148514 C op)). Qed.
Lemma lem6148557 {C : Type'} (op : type1400 C) : (term680 C op) = (term680 C op).
Proof. exact (MK_COMB (@lem6148556 C op) (@lem6148554 C op)). Qed.
Lemma lem6148559 {C : Type'} (op : type1400 C) : (term966 C op) = (term966 C op).
Proof. exact (eq_refl (term966 C op)). Qed.
Lemma lem6148560 {C : Type'} (op : type1400 C) : (term967 C op) = (term967 C op).
Proof. exact (MK_COMB (@lem6148559 C op) (@lem6148557 C op)). Qed.
Lemma lem6148561 {C : Type'} (op : type1400 C) : (term681 C op) = (term967 C op).
Proof. exact (@lem17265 (@monoidal C op) (term680 C op)). Qed.
Lemma lem6148562 {C : Type'} (op : type1400 C) : (term681 C op) = (term967 C op).
Proof. exact (TRANS (@lem6148561 C op) (@lem6148560 C op)). Qed.
Lemma lem6148563 {C : Type'} : (term682 C) = (term968 C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6148562 C op)). Qed.
Lemma lem6148564 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6148657 {C : Type'} : (term603 C) = (term969 C).
Proof. exact (MK_COMB (@lem6148564 C) (@lem6148563 C)). Qed.
Lemma lem6148658 {C : Type'} (h1 : term603 C) : term969 C.
Proof. exact (EQ_MP (@lem6148657 C) (@lem6147871 C h1)). Qed.
Lemma lem6148660 {A B C : Type'} (x' : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term377 A B C x' op s g f) : term377 A B C x' op s g f.
Proof. exact (h1). Qed.
Lemma lem6148661 {A B C : Type'} (x' : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term374 A B C x' y op s g f) : term374 A B C x' y op s g f.
Proof. exact (h1). Qed.
Lemma lem6148666 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148667 {C : Type'} (f : type403 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> Prop) f x).
Proof. exact (@lem6148666 (type1400 C) Prop f x). Qed.
Lemma lem6148669 {C : Type'} (op : type1400 C) : (@monoidal C op) = (@I ((C -> C -> C) -> Prop) (@monoidal C) op).
Proof. exact (@lem6148667 C (@monoidal C) op). Qed.
Lemma lem6148829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6148830 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6148839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148840 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem6148839 (A -> B) (type678 A B) f x). Qed.
Lemma lem6148841 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem6148840 A B (@IMAGE A B) f). Qed.
Lemma lem6148842 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6148843 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem6148841 A B f) (@lem6148842 A s)). Qed.
Lemma lem6148845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148846 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem6148845 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem6148847 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term700 A B f s).
Proof. exact (@lem6148846 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem6148849 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term700 A B f s).
Proof. exact (TRANS (@lem6148843 A B f s) (@lem6148847 A B f s)). Qed.
Lemma lem6148850 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6148851 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@iterate C B op).
Proof. exact (eq_refl (@iterate C B op)). Qed.
Lemma lem6148852 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term701 A B C op f s) = (term702 A B C op f s).
Proof. exact (MK_COMB (@lem6148851 B C op) (@lem6148849 A B f s)). Qed.
Lemma lem6148853 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term703 A B C op f s g).
Proof. exact (MK_COMB (@lem6148852 A B C op f s) (@lem6148850 B C g)). Qed.
Lemma lem6148855 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148856 {B C : Type'} (f : type750 B C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) f x).
Proof. exact (@lem6148855 (type1400 C) (type632 B C) f x). Qed.
Lemma lem6148857 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) (@iterate C B) op).
Proof. exact (@lem6148856 B C (@iterate C B) op). Qed.
Lemma lem6148858 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term700 A B f s) = (term700 A B f s).
Proof. exact (eq_refl (term700 A B f s)). Qed.
Lemma lem6148859 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term702 A B C op f s) = (term704 A B C op f s).
Proof. exact (MK_COMB (@lem6148857 B C op) (@lem6148858 A B f s)). Qed.
Lemma lem6148861 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148862 {B C : Type'} (f : type632 B C) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> C) -> C) f x).
Proof. exact (@lem6148861 (B -> Prop) (type570 B C) f x). Qed.
Lemma lem6148863 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term704 A B C op f s) = (term705 A B C op f s).
Proof. exact (@lem6148862 B C (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) (@iterate C B) op) (term700 A B f s)). Qed.
Lemma lem6148864 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term702 A B C op f s) = (term705 A B C op f s).
Proof. exact (TRANS (@lem6148859 A B C op f s) (@lem6148863 A B C op f s)). Qed.
Lemma lem6148865 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6148866 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term703 A B C op f s g) = (term706 A B C op f s g).
Proof. exact (MK_COMB (@lem6148864 A B C op f s) (@lem6148865 B C g)). Qed.
Lemma lem6148868 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148869 {B C : Type'} (f : type570 B C) (x : B -> C) : (f x) = (@I ((B -> C) -> C) f x).
Proof. exact (@lem6148868 (B -> C) C f x). Qed.
Lemma lem6148870 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term706 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (@lem6148869 B C (term705 A B C op f s) g). Qed.
Lemma lem6148871 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term703 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (TRANS (@lem6148866 A B C op f s g) (@lem6148870 A B C op f s g)). Qed.
Lemma lem6148872 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (TRANS (@lem6148853 A B C op f s g) (@lem6148871 A B C op f s g)). Qed.
Lemma lem6148873 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6148878 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148879 {C : Type'} (f : type402 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> C) f x).
Proof. exact (@lem6148878 (type1400 C) C f x). Qed.
Lemma lem6148881 {C : Type'} (op : type1400 C) : (@neutral C op) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (@lem6148879 C (@neutral C) op). Qed.
Lemma lem6148890 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148891 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem6148890 (A -> B) (type678 A B) f x). Qed.
Lemma lem6148892 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem6148891 A B (@IMAGE A B) f). Qed.
Lemma lem6148893 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6148894 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem6148892 A B f) (@lem6148893 A s)). Qed.
Lemma lem6148896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148897 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem6148896 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem6148898 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term700 A B f s).
Proof. exact (@lem6148897 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem6148900 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term700 A B f s).
Proof. exact (TRANS (@lem6148894 A B f s) (@lem6148898 A B f s)). Qed.
Lemma lem6148901 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6148902 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@iterate C B op).
Proof. exact (eq_refl (@iterate C B op)). Qed.
Lemma lem6148903 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term701 A B C op f s) = (term702 A B C op f s).
Proof. exact (MK_COMB (@lem6148902 B C op) (@lem6148900 A B f s)). Qed.
Lemma lem6148904 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term703 A B C op f s g).
Proof. exact (MK_COMB (@lem6148903 A B C op f s) (@lem6148901 B C g)). Qed.
Lemma lem6148906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148907 {B C : Type'} (f : type750 B C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) f x).
Proof. exact (@lem6148906 (type1400 C) (type632 B C) f x). Qed.
Lemma lem6148908 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) (@iterate C B) op).
Proof. exact (@lem6148907 B C (@iterate C B) op). Qed.
Lemma lem6148909 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term700 A B f s) = (term700 A B f s).
Proof. exact (eq_refl (term700 A B f s)). Qed.
Lemma lem6148910 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term702 A B C op f s) = (term704 A B C op f s).
Proof. exact (MK_COMB (@lem6148908 B C op) (@lem6148909 A B f s)). Qed.
Lemma lem6148912 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148913 {B C : Type'} (f : type632 B C) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> C) -> C) f x).
Proof. exact (@lem6148912 (B -> Prop) (type570 B C) f x). Qed.
Lemma lem6148914 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term704 A B C op f s) = (term705 A B C op f s).
Proof. exact (@lem6148913 B C (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) (@iterate C B) op) (term700 A B f s)). Qed.
Lemma lem6148915 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term702 A B C op f s) = (term705 A B C op f s).
Proof. exact (TRANS (@lem6148910 A B C op f s) (@lem6148914 A B C op f s)). Qed.
Lemma lem6148916 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6148917 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term703 A B C op f s g) = (term706 A B C op f s g).
Proof. exact (MK_COMB (@lem6148915 A B C op f s) (@lem6148916 B C g)). Qed.
Lemma lem6148919 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148920 {B C : Type'} (f : type570 B C) (x : B -> C) : (f x) = (@I ((B -> C) -> C) f x).
Proof. exact (@lem6148919 (B -> C) C f x). Qed.
Lemma lem6148921 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term706 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (@lem6148920 B C (term705 A B C op f s) g). Qed.
Lemma lem6148922 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term703 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (TRANS (@lem6148917 A B C op f s g) (@lem6148921 A B C op f s g)). Qed.
Lemma lem6148923 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (TRANS (@lem6148904 A B C op f s g) (@lem6148922 A B C op f s g)). Qed.
Lemma lem6148924 {C : Type'} (op : type1400 C) : (term970 C op) = (term971 C op).
Proof. exact (MK_COMB (@lem6148873 C op) (@lem6148881 C op)). Qed.
Lemma lem6148925 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term599 A B C op f s g) = (term972 A B C op f s g).
Proof. exact (MK_COMB (@lem6148924 C op) (@lem6148923 A B C op f s g)). Qed.
Lemma lem6148927 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148928 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6148927 C (C -> C) f x). Qed.
Lemma lem6148929 {C : Type'} (op : type1400 C) : (term971 C op) = (term973 C op).
Proof. exact (@lem6148928 C op (@I ((C -> C -> C) -> C) (@neutral C) op)). Qed.
Lemma lem6148930 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term707 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (eq_refl (term707 A B C op f s g)). Qed.
Lemma lem6148931 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term972 A B C op f s g) = (term974 A B C op f s g).
Proof. exact (MK_COMB (@lem6148929 C op) (@lem6148930 A B C op f s g)). Qed.
Lemma lem6148933 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6148934 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6148933 C C f x). Qed.
Lemma lem6148935 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term974 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (@lem6148934 C (term973 C op) (term707 A B C op f s g)). Qed.
Lemma lem6148936 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term972 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (TRANS (@lem6148931 A B C op f s g) (@lem6148935 A B C op f s g)). Qed.
Lemma lem6148937 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term599 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (TRANS (@lem6148925 A B C op f s g) (@lem6148936 A B C op f s g)). Qed.
Lemma lem6148938 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term594 A B C op f s g) = (term713 A B C op f s g).
Proof. exact (MK_COMB (@lem6148830 C) (@lem6148872 A B C op f s g)). Qed.
Lemma lem6148939 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : ((term33 A B C op f s g) = (term599 A B C op f s g)) = ((term707 A B C op f s g) = (term975 A B C op f s g)).
Proof. exact (MK_COMB (@lem6148938 A B C op f s g) (@lem6148937 A B C op f s g)). Qed.
Lemma lem6148940 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term927 A B C op f s g) = (term976 A B C op f s g).
Proof. exact (MK_COMB (@lem6148829) (@lem6148939 A B C op f s g)). Qed.
Lemma lem6149522 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6149531 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149532 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149531 C (C -> C) f x). Qed.
Lemma lem6149533 {C : Type'} (op : type1400 C) (b : C) : (op b) = (@I (C -> C -> C) op b).
Proof. exact (@lem6149532 C op b). Qed.
Lemma lem6149534 {C : Type'} (c : C) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem6149535 {C : Type'} (op : type1400 C) (b : C) (c : C) : (op b c) = (@I (C -> C -> C) op b c).
Proof. exact (MK_COMB (@lem6149533 C op b) (@lem6149534 C c)). Qed.
Lemma lem6149537 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149538 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149537 C C f x). Qed.
Lemma lem6149539 {C : Type'} (op : type1400 C) (b : C) (c : C) : (@I (C -> C -> C) op b c) = (term977 C op b c).
Proof. exact (@lem6149538 C (@I (C -> C -> C) op b) c). Qed.
Lemma lem6149541 {C : Type'} (op : type1400 C) (b : C) (c : C) : (op b c) = (term977 C op b c).
Proof. exact (TRANS (@lem6149535 C op b c) (@lem6149539 C op b c)). Qed.
Lemma lem6149542 {C : Type'} (op : type1400 C) (a : C) : (op a) = (op a).
Proof. exact (eq_refl (op a)). Qed.
Lemma lem6149543 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term649 C a op b c) = (term978 C a op b c).
Proof. exact (MK_COMB (@lem6149542 C op a) (@lem6149541 C op b c)). Qed.
Lemma lem6149545 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149546 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149545 C (C -> C) f x). Qed.
Lemma lem6149547 {C : Type'} (op : type1400 C) (a : C) : (op a) = (@I (C -> C -> C) op a).
Proof. exact (@lem6149546 C op a). Qed.
Lemma lem6149548 {C : Type'} (op : type1400 C) (b : C) (c : C) : (term977 C op b c) = (term977 C op b c).
Proof. exact (eq_refl (term977 C op b c)). Qed.
Lemma lem6149549 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term978 C a op b c) = (term979 C a op b c).
Proof. exact (MK_COMB (@lem6149547 C op a) (@lem6149548 C op b c)). Qed.
Lemma lem6149551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149552 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149551 C C f x). Qed.
Lemma lem6149553 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term979 C a op b c) = (term980 C a op b c).
Proof. exact (@lem6149552 C (@I (C -> C -> C) op a) (term977 C op b c)). Qed.
Lemma lem6149554 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term978 C a op b c) = (term980 C a op b c).
Proof. exact (TRANS (@lem6149549 C a op b c) (@lem6149553 C a op b c)). Qed.
Lemma lem6149555 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term649 C a op b c) = (term980 C a op b c).
Proof. exact (TRANS (@lem6149543 C a op b c) (@lem6149554 C a op b c)). Qed.
Lemma lem6149564 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149565 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149564 C (C -> C) f x). Qed.
Lemma lem6149566 {C : Type'} (op : type1400 C) (a : C) : (op a) = (@I (C -> C -> C) op a).
Proof. exact (@lem6149565 C op a). Qed.
Lemma lem6149567 {C : Type'} (c : C) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem6149568 {C : Type'} (op : type1400 C) (a : C) (c : C) : (op a c) = (@I (C -> C -> C) op a c).
Proof. exact (MK_COMB (@lem6149566 C op a) (@lem6149567 C c)). Qed.
Lemma lem6149570 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149571 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149570 C C f x). Qed.
Lemma lem6149572 {C : Type'} (op : type1400 C) (a : C) (c : C) : (@I (C -> C -> C) op a c) = (term977 C op a c).
Proof. exact (@lem6149571 C (@I (C -> C -> C) op a) c). Qed.
Lemma lem6149574 {C : Type'} (op : type1400 C) (a : C) (c : C) : (op a c) = (term977 C op a c).
Proof. exact (TRANS (@lem6149568 C op a c) (@lem6149572 C op a c)). Qed.
Lemma lem6149575 {C : Type'} (op : type1400 C) (b : C) : (op b) = (op b).
Proof. exact (eq_refl (op b)). Qed.
Lemma lem6149576 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term649 C b op a c) = (term978 C b op a c).
Proof. exact (MK_COMB (@lem6149575 C op b) (@lem6149574 C op a c)). Qed.
Lemma lem6149578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149579 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149578 C (C -> C) f x). Qed.
Lemma lem6149580 {C : Type'} (op : type1400 C) (b : C) : (op b) = (@I (C -> C -> C) op b).
Proof. exact (@lem6149579 C op b). Qed.
Lemma lem6149581 {C : Type'} (op : type1400 C) (a : C) (c : C) : (term977 C op a c) = (term977 C op a c).
Proof. exact (eq_refl (term977 C op a c)). Qed.
Lemma lem6149582 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term978 C b op a c) = (term979 C b op a c).
Proof. exact (MK_COMB (@lem6149580 C op b) (@lem6149581 C op a c)). Qed.
Lemma lem6149584 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149585 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149584 C C f x). Qed.
Lemma lem6149586 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term979 C b op a c) = (term980 C b op a c).
Proof. exact (@lem6149585 C (@I (C -> C -> C) op b) (term977 C op a c)). Qed.
Lemma lem6149587 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term978 C b op a c) = (term980 C b op a c).
Proof. exact (TRANS (@lem6149582 C b op a c) (@lem6149586 C b op a c)). Qed.
Lemma lem6149588 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term649 C b op a c) = (term980 C b op a c).
Proof. exact (TRANS (@lem6149576 C b op a c) (@lem6149587 C b op a c)). Qed.
Lemma lem6149589 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term981 C a op b c) = (term982 C a op b c).
Proof. exact (MK_COMB (@lem6149522 C) (@lem6149555 C a op b c)). Qed.
Lemma lem6149590 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : ((term649 C a op b c) = (term649 C b op a c)) = ((term980 C a op b c) = (term980 C b op a c)).
Proof. exact (MK_COMB (@lem6149589 C a op b c) (@lem6149588 C b op a c)). Qed.
Lemma lem6149591 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term650 C b op a) = (term983 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6149590 C b op a c)). Qed.
Lemma lem6149592 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149593 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term651 C b op a) = (term984 C b op a).
Proof. exact (MK_COMB (@lem6149592 C) (@lem6149591 C b op a)). Qed.
Lemma lem6149594 {C : Type'} (op : type1400 C) (a : C) : (term652 C op a) = (term985 C op a).
Proof. exact (fun_ext (fun b : C => @lem6149593 C b op a)). Qed.
Lemma lem6149595 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149596 {C : Type'} (op : type1400 C) (a : C) : (term653 C op a) = (term986 C op a).
Proof. exact (MK_COMB (@lem6149595 C) (@lem6149594 C op a)). Qed.
Lemma lem6149597 {C : Type'} (op : type1400 C) : (term654 C op) = (term987 C op).
Proof. exact (fun_ext (fun a : C => @lem6149596 C op a)). Qed.
Lemma lem6149598 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149599 {C : Type'} (op : type1400 C) : (term655 C op) = (term988 C op).
Proof. exact (MK_COMB (@lem6149598 C) (@lem6149597 C op)). Qed.
Lemma lem6149600 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6149601 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6149608 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149609 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149608 C (C -> C) f x). Qed.
Lemma lem6149610 {C : Type'} (op : type1400 C) (a : C) : (op a) = (@I (C -> C -> C) op a).
Proof. exact (@lem6149609 C op a). Qed.
Lemma lem6149611 {C : Type'} (b : C) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6149612 {C : Type'} (op : type1400 C) (a : C) (b : C) : (op a b) = (@I (C -> C -> C) op a b).
Proof. exact (MK_COMB (@lem6149610 C op a) (@lem6149611 C b)). Qed.
Lemma lem6149614 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149615 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149614 C C f x). Qed.
Lemma lem6149616 {C : Type'} (op : type1400 C) (a : C) (b : C) : (@I (C -> C -> C) op a b) = (term977 C op a b).
Proof. exact (@lem6149615 C (@I (C -> C -> C) op a) b). Qed.
Lemma lem6149618 {C : Type'} (op : type1400 C) (a : C) (b : C) : (op a b) = (term977 C op a b).
Proof. exact (TRANS (@lem6149612 C op a b) (@lem6149616 C op a b)). Qed.
Lemma lem6149619 {C : Type'} (c : C) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem6149620 {C : Type'} (op : type1400 C) (a : C) (b : C) : (term989 C op a b) = (term990 C op a b).
Proof. exact (MK_COMB (@lem6149601 C op) (@lem6149618 C op a b)). Qed.
Lemma lem6149621 {C : Type'} (op : type1400 C) (a : C) (b : C) (c : C) : (term656 C op a b c) = (term991 C op a b c).
Proof. exact (MK_COMB (@lem6149620 C op a b) (@lem6149619 C c)). Qed.
Lemma lem6149623 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149624 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149623 C (C -> C) f x). Qed.
Lemma lem6149625 {C : Type'} (op : type1400 C) (a : C) (b : C) : (term990 C op a b) = (term992 C op a b).
Proof. exact (@lem6149624 C op (term977 C op a b)). Qed.
Lemma lem6149626 {C : Type'} (c : C) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem6149627 {C : Type'} (op : type1400 C) (a : C) (b : C) (c : C) : (term991 C op a b c) = (term993 C op a b c).
Proof. exact (MK_COMB (@lem6149625 C op a b) (@lem6149626 C c)). Qed.
Lemma lem6149629 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149630 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149629 C C f x). Qed.
Lemma lem6149631 {C : Type'} (op : type1400 C) (a : C) (b : C) (c : C) : (term993 C op a b c) = (term994 C op a b c).
Proof. exact (@lem6149630 C (term992 C op a b) c). Qed.
Lemma lem6149632 {C : Type'} (op : type1400 C) (a : C) (b : C) (c : C) : (term991 C op a b c) = (term994 C op a b c).
Proof. exact (TRANS (@lem6149627 C op a b c) (@lem6149631 C op a b c)). Qed.
Lemma lem6149633 {C : Type'} (op : type1400 C) (a : C) (b : C) (c : C) : (term656 C op a b c) = (term994 C op a b c).
Proof. exact (TRANS (@lem6149621 C op a b c) (@lem6149632 C op a b c)). Qed.
Lemma lem6149642 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149643 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149642 C (C -> C) f x). Qed.
Lemma lem6149644 {C : Type'} (op : type1400 C) (b : C) : (op b) = (@I (C -> C -> C) op b).
Proof. exact (@lem6149643 C op b). Qed.
Lemma lem6149645 {C : Type'} (c : C) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem6149646 {C : Type'} (op : type1400 C) (b : C) (c : C) : (op b c) = (@I (C -> C -> C) op b c).
Proof. exact (MK_COMB (@lem6149644 C op b) (@lem6149645 C c)). Qed.
Lemma lem6149648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149649 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149648 C C f x). Qed.
Lemma lem6149650 {C : Type'} (op : type1400 C) (b : C) (c : C) : (@I (C -> C -> C) op b c) = (term977 C op b c).
Proof. exact (@lem6149649 C (@I (C -> C -> C) op b) c). Qed.
Lemma lem6149652 {C : Type'} (op : type1400 C) (b : C) (c : C) : (op b c) = (term977 C op b c).
Proof. exact (TRANS (@lem6149646 C op b c) (@lem6149650 C op b c)). Qed.
Lemma lem6149653 {C : Type'} (op : type1400 C) (a : C) : (op a) = (op a).
Proof. exact (eq_refl (op a)). Qed.
Lemma lem6149654 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term649 C a op b c) = (term978 C a op b c).
Proof. exact (MK_COMB (@lem6149653 C op a) (@lem6149652 C op b c)). Qed.
Lemma lem6149656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149657 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149656 C (C -> C) f x). Qed.
Lemma lem6149658 {C : Type'} (op : type1400 C) (a : C) : (op a) = (@I (C -> C -> C) op a).
Proof. exact (@lem6149657 C op a). Qed.
Lemma lem6149659 {C : Type'} (op : type1400 C) (b : C) (c : C) : (term977 C op b c) = (term977 C op b c).
Proof. exact (eq_refl (term977 C op b c)). Qed.
Lemma lem6149660 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term978 C a op b c) = (term979 C a op b c).
Proof. exact (MK_COMB (@lem6149658 C op a) (@lem6149659 C op b c)). Qed.
Lemma lem6149662 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149663 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149662 C C f x). Qed.
Lemma lem6149664 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term979 C a op b c) = (term980 C a op b c).
Proof. exact (@lem6149663 C (@I (C -> C -> C) op a) (term977 C op b c)). Qed.
Lemma lem6149665 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term978 C a op b c) = (term980 C a op b c).
Proof. exact (TRANS (@lem6149660 C a op b c) (@lem6149664 C a op b c)). Qed.
Lemma lem6149666 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term649 C a op b c) = (term980 C a op b c).
Proof. exact (TRANS (@lem6149654 C a op b c) (@lem6149665 C a op b c)). Qed.
Lemma lem6149667 {C : Type'} (op : type1400 C) (a : C) (b : C) (c : C) : (term995 C op a b c) = (term996 C op a b c).
Proof. exact (MK_COMB (@lem6149600 C) (@lem6149633 C op a b c)). Qed.
Lemma lem6149668 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : ((term656 C op a b c) = (term649 C a op b c)) = ((term994 C op a b c) = (term980 C a op b c)).
Proof. exact (MK_COMB (@lem6149667 C op a b c) (@lem6149666 C a op b c)). Qed.
Lemma lem6149669 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term657 C a op b) = (term997 C a op b).
Proof. exact (fun_ext (fun c : C => @lem6149668 C a op b c)). Qed.
Lemma lem6149670 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149671 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term658 C a op b) = (term998 C a op b).
Proof. exact (MK_COMB (@lem6149670 C) (@lem6149669 C a op b)). Qed.
Lemma lem6149672 {C : Type'} (a : C) (op : type1400 C) : (term659 C a op) = (term999 C a op).
Proof. exact (fun_ext (fun b : C => @lem6149671 C a op b)). Qed.
Lemma lem6149673 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149674 {C : Type'} (a : C) (op : type1400 C) : (term660 C a op) = (term1000 C a op).
Proof. exact (MK_COMB (@lem6149673 C) (@lem6149672 C a op)). Qed.
Lemma lem6149675 {C : Type'} (op : type1400 C) : (term661 C op) = (term1001 C op).
Proof. exact (fun_ext (fun a : C => @lem6149674 C a op)). Qed.
Lemma lem6149676 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149677 {C : Type'} (op : type1400 C) : (term662 C op) = (term1002 C op).
Proof. exact (MK_COMB (@lem6149676 C) (@lem6149675 C op)). Qed.
Lemma lem6149678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6149679 {C : Type'} (op : type1400 C) : (term663 C op) = (term1003 C op).
Proof. exact (MK_COMB (@lem6149678) (@lem6149677 C op)). Qed.
Lemma lem6149680 {C : Type'} (op : type1400 C) : (term664 C op) = (term1004 C op).
Proof. exact (MK_COMB (@lem6149679 C op) (@lem6149599 C op)). Qed.
Lemma lem6149681 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6149688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149689 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149688 C (C -> C) f x). Qed.
Lemma lem6149690 {C : Type'} (op : type1400 C) (a : C) : (op a) = (@I (C -> C -> C) op a).
Proof. exact (@lem6149689 C op a). Qed.
Lemma lem6149691 {C : Type'} (b : C) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6149692 {C : Type'} (op : type1400 C) (a : C) (b : C) : (op a b) = (@I (C -> C -> C) op a b).
Proof. exact (MK_COMB (@lem6149690 C op a) (@lem6149691 C b)). Qed.
Lemma lem6149694 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149695 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149694 C C f x). Qed.
Lemma lem6149696 {C : Type'} (op : type1400 C) (a : C) (b : C) : (@I (C -> C -> C) op a b) = (term977 C op a b).
Proof. exact (@lem6149695 C (@I (C -> C -> C) op a) b). Qed.
Lemma lem6149698 {C : Type'} (op : type1400 C) (a : C) (b : C) : (op a b) = (term977 C op a b).
Proof. exact (TRANS (@lem6149692 C op a b) (@lem6149696 C op a b)). Qed.
Lemma lem6149705 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149706 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149705 C (C -> C) f x). Qed.
Lemma lem6149707 {C : Type'} (op : type1400 C) (b : C) : (op b) = (@I (C -> C -> C) op b).
Proof. exact (@lem6149706 C op b). Qed.
Lemma lem6149708 {C : Type'} (a : C) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem6149709 {C : Type'} (op : type1400 C) (b : C) (a : C) : (op b a) = (@I (C -> C -> C) op b a).
Proof. exact (MK_COMB (@lem6149707 C op b) (@lem6149708 C a)). Qed.
Lemma lem6149711 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149712 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149711 C C f x). Qed.
Lemma lem6149713 {C : Type'} (op : type1400 C) (b : C) (a : C) : (@I (C -> C -> C) op b a) = (term977 C op b a).
Proof. exact (@lem6149712 C (@I (C -> C -> C) op b) a). Qed.
Lemma lem6149715 {C : Type'} (op : type1400 C) (b : C) (a : C) : (op b a) = (term977 C op b a).
Proof. exact (TRANS (@lem6149709 C op b a) (@lem6149713 C op b a)). Qed.
Lemma lem6149716 {C : Type'} (op : type1400 C) (a : C) (b : C) : (term1005 C op a b) = (term1006 C op a b).
Proof. exact (MK_COMB (@lem6149681 C) (@lem6149698 C op a b)). Qed.
Lemma lem6149717 {C : Type'} (op : type1400 C) (b : C) (a : C) : ((op a b) = (op b a)) = ((term977 C op a b) = (term977 C op b a)).
Proof. exact (MK_COMB (@lem6149716 C op a b) (@lem6149715 C op b a)). Qed.
Lemma lem6149718 {C : Type'} (op : type1400 C) (a : C) : (term665 C op a) = (term1007 C op a).
Proof. exact (fun_ext (fun b : C => @lem6149717 C op b a)). Qed.
Lemma lem6149719 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149720 {C : Type'} (op : type1400 C) (a : C) : (term666 C op a) = (term1008 C op a).
Proof. exact (MK_COMB (@lem6149719 C) (@lem6149718 C op a)). Qed.
Lemma lem6149721 {C : Type'} (op : type1400 C) : (term667 C op) = (term1009 C op).
Proof. exact (fun_ext (fun a : C => @lem6149720 C op a)). Qed.
Lemma lem6149722 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149723 {C : Type'} (op : type1400 C) : (term668 C op) = (term1010 C op).
Proof. exact (MK_COMB (@lem6149722 C) (@lem6149721 C op)). Qed.
Lemma lem6149724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6149725 {C : Type'} (op : type1400 C) : (term669 C op) = (term1011 C op).
Proof. exact (MK_COMB (@lem6149724) (@lem6149723 C op)). Qed.
Lemma lem6149726 {C : Type'} (op : type1400 C) : (term670 C op) = (term1012 C op).
Proof. exact (MK_COMB (@lem6149725 C op) (@lem6149680 C op)). Qed.
Lemma lem6149727 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6149734 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149735 {C : Type'} (f : type402 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> C) f x).
Proof. exact (@lem6149734 (type1400 C) C f x). Qed.
Lemma lem6149737 {C : Type'} (op : type1400 C) : (@neutral C op) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (@lem6149735 C (@neutral C) op). Qed.
Lemma lem6149738 {C : Type'} (op : type1400 C) (a : C) : (op a) = (op a).
Proof. exact (eq_refl (op a)). Qed.
Lemma lem6149739 {C : Type'} (a : C) (op : type1400 C) : (term671 C a op) = (term1013 C a op).
Proof. exact (MK_COMB (@lem6149738 C op a) (@lem6149737 C op)). Qed.
Lemma lem6149741 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149742 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149741 C (C -> C) f x). Qed.
Lemma lem6149743 {C : Type'} (op : type1400 C) (a : C) : (op a) = (@I (C -> C -> C) op a).
Proof. exact (@lem6149742 C op a). Qed.
Lemma lem6149744 {C : Type'} (op : type1400 C) : (@I ((C -> C -> C) -> C) (@neutral C) op) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (eq_refl (@I ((C -> C -> C) -> C) (@neutral C) op)). Qed.
Lemma lem6149745 {C : Type'} (a : C) (op : type1400 C) : (term1013 C a op) = (term1014 C a op).
Proof. exact (MK_COMB (@lem6149743 C op a) (@lem6149744 C op)). Qed.
Lemma lem6149747 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149748 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149747 C C f x). Qed.
Lemma lem6149749 {C : Type'} (a : C) (op : type1400 C) : (term1014 C a op) = (term1015 C a op).
Proof. exact (@lem6149748 C (@I (C -> C -> C) op a) (@I ((C -> C -> C) -> C) (@neutral C) op)). Qed.
Lemma lem6149750 {C : Type'} (a : C) (op : type1400 C) : (term1013 C a op) = (term1015 C a op).
Proof. exact (TRANS (@lem6149745 C a op) (@lem6149749 C a op)). Qed.
Lemma lem6149751 {C : Type'} (a : C) (op : type1400 C) : (term671 C a op) = (term1015 C a op).
Proof. exact (TRANS (@lem6149739 C a op) (@lem6149750 C a op)). Qed.
Lemma lem6149752 {C : Type'} (a : C) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem6149753 {C : Type'} (a : C) (op : type1400 C) : (term1016 C a op) = (term1017 C a op).
Proof. exact (MK_COMB (@lem6149727 C) (@lem6149751 C a op)). Qed.
Lemma lem6149754 {C : Type'} (op : type1400 C) (a : C) : ((term671 C a op) = a) = ((term1015 C a op) = a).
Proof. exact (MK_COMB (@lem6149753 C a op) (@lem6149752 C a)). Qed.
Lemma lem6149755 {C : Type'} (op : type1400 C) : (term672 C op) = (term1018 C op).
Proof. exact (fun_ext (fun a : C => @lem6149754 C op a)). Qed.
Lemma lem6149756 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149757 {C : Type'} (op : type1400 C) : (term673 C op) = (term1019 C op).
Proof. exact (MK_COMB (@lem6149756 C) (@lem6149755 C op)). Qed.
Lemma lem6149758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6149759 {C : Type'} (op : type1400 C) : (term674 C op) = (term1020 C op).
Proof. exact (MK_COMB (@lem6149758) (@lem6149757 C op)). Qed.
Lemma lem6149760 {C : Type'} (op : type1400 C) : (term675 C op) = (term1021 C op).
Proof. exact (MK_COMB (@lem6149759 C op) (@lem6149726 C op)). Qed.
Lemma lem6149761 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6149762 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6149767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149768 {C : Type'} (f : type402 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> C) f x).
Proof. exact (@lem6149767 (type1400 C) C f x). Qed.
Lemma lem6149770 {C : Type'} (op : type1400 C) : (@neutral C op) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (@lem6149768 C (@neutral C) op). Qed.
Lemma lem6149771 {C : Type'} (a : C) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem6149772 {C : Type'} (op : type1400 C) : (term970 C op) = (term971 C op).
Proof. exact (MK_COMB (@lem6149762 C op) (@lem6149770 C op)). Qed.
Lemma lem6149773 {C : Type'} (op : type1400 C) (a : C) : (term676 C op a) = (term1022 C op a).
Proof. exact (MK_COMB (@lem6149772 C op) (@lem6149771 C a)). Qed.
Lemma lem6149775 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149776 {C : Type'} (f : type1400 C) (x : C) : (f x) = (@I (C -> C -> C) f x).
Proof. exact (@lem6149775 C (C -> C) f x). Qed.
Lemma lem6149777 {C : Type'} (op : type1400 C) : (term971 C op) = (term973 C op).
Proof. exact (@lem6149776 C op (@I ((C -> C -> C) -> C) (@neutral C) op)). Qed.
Lemma lem6149778 {C : Type'} (a : C) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem6149779 {C : Type'} (op : type1400 C) (a : C) : (term1022 C op a) = (term1023 C op a).
Proof. exact (MK_COMB (@lem6149777 C op) (@lem6149778 C a)). Qed.
Lemma lem6149781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149782 {C : Type'} (f : C -> C) (x : C) : (f x) = (@I (C -> C) f x).
Proof. exact (@lem6149781 C C f x). Qed.
Lemma lem6149783 {C : Type'} (op : type1400 C) (a : C) : (term1023 C op a) = (term1024 C op a).
Proof. exact (@lem6149782 C (term973 C op) a). Qed.
Lemma lem6149784 {C : Type'} (op : type1400 C) (a : C) : (term1022 C op a) = (term1024 C op a).
Proof. exact (TRANS (@lem6149779 C op a) (@lem6149783 C op a)). Qed.
Lemma lem6149785 {C : Type'} (op : type1400 C) (a : C) : (term676 C op a) = (term1024 C op a).
Proof. exact (TRANS (@lem6149773 C op a) (@lem6149784 C op a)). Qed.
Lemma lem6149786 {C : Type'} (a : C) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem6149787 {C : Type'} (op : type1400 C) (a : C) : (term1025 C op a) = (term1026 C op a).
Proof. exact (MK_COMB (@lem6149761 C) (@lem6149785 C op a)). Qed.
Lemma lem6149788 {C : Type'} (op : type1400 C) (a : C) : ((term676 C op a) = a) = ((term1024 C op a) = a).
Proof. exact (MK_COMB (@lem6149787 C op a) (@lem6149786 C a)). Qed.
Lemma lem6149789 {C : Type'} (op : type1400 C) : (term677 C op) = (term1027 C op).
Proof. exact (fun_ext (fun a : C => @lem6149788 C op a)). Qed.
Lemma lem6149790 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6149791 {C : Type'} (op : type1400 C) : (term678 C op) = (term1028 C op).
Proof. exact (MK_COMB (@lem6149790 C) (@lem6149789 C op)). Qed.
Lemma lem6149792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6149793 {C : Type'} (op : type1400 C) : (term679 C op) = (term1029 C op).
Proof. exact (MK_COMB (@lem6149792) (@lem6149791 C op)). Qed.
Lemma lem6149794 {C : Type'} (op : type1400 C) : (term680 C op) = (term1030 C op).
Proof. exact (MK_COMB (@lem6149793 C op) (@lem6149760 C op)). Qed.
Lemma lem6149795 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6149800 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149801 {C : Type'} (f : type403 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> Prop) f x).
Proof. exact (@lem6149800 (type1400 C) Prop f x). Qed.
Lemma lem6149803 {C : Type'} (op : type1400 C) : (@monoidal C op) = (@I ((C -> C -> C) -> Prop) (@monoidal C) op).
Proof. exact (@lem6149801 C (@monoidal C) op). Qed.
Lemma lem6149804 {C : Type'} (op : type1400 C) : (term1031 C op) = (term1032 C op).
Proof. exact (MK_COMB (@lem6149795) (@lem6149803 C op)). Qed.
Lemma lem6149805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6149806 {C : Type'} (op : type1400 C) : (term966 C op) = (term1033 C op).
Proof. exact (MK_COMB (@lem6149805) (@lem6149804 C op)). Qed.
Lemma lem6149807 {C : Type'} (op : type1400 C) : (term967 C op) = (term1034 C op).
Proof. exact (MK_COMB (@lem6149806 C op) (@lem6149794 C op)). Qed.
Lemma lem6149808 {C : Type'} : (term968 C) = (term1035 C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6149807 C op)). Qed.
Lemma lem6149809 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6149810 {C : Type'} : (term969 C) = (term1036 C).
Proof. exact (MK_COMB (@lem6149809 C) (@lem6149808 C)). Qed.
Lemma lem6149811 {C : Type'} (h1 : term603 C) : term1036 C.
Proof. exact (EQ_MP (@lem6149810 C) (@lem6148658 C h1)). Qed.
Lemma lem6149851 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6149860 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149861 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem6149860 (A -> B) (type678 A B) f x). Qed.
Lemma lem6149862 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem6149861 A B (@IMAGE A B) f). Qed.
Lemma lem6149863 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6149864 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem6149862 A B f) (@lem6149863 A s)). Qed.
Lemma lem6149866 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149867 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem6149866 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem6149868 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term700 A B f s).
Proof. exact (@lem6149867 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem6149870 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term700 A B f s).
Proof. exact (TRANS (@lem6149864 A B f s) (@lem6149868 A B f s)). Qed.
Lemma lem6149871 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6149872 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@iterate C B op).
Proof. exact (eq_refl (@iterate C B op)). Qed.
Lemma lem6149873 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term701 A B C op f s) = (term702 A B C op f s).
Proof. exact (MK_COMB (@lem6149872 B C op) (@lem6149870 A B f s)). Qed.
Lemma lem6149874 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term703 A B C op f s g).
Proof. exact (MK_COMB (@lem6149873 A B C op f s) (@lem6149871 B C g)). Qed.
Lemma lem6149876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149877 {B C : Type'} (f : type750 B C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) f x).
Proof. exact (@lem6149876 (type1400 C) (type632 B C) f x). Qed.
Lemma lem6149878 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) (@iterate C B) op).
Proof. exact (@lem6149877 B C (@iterate C B) op). Qed.
Lemma lem6149879 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term700 A B f s) = (term700 A B f s).
Proof. exact (eq_refl (term700 A B f s)). Qed.
Lemma lem6149880 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term702 A B C op f s) = (term704 A B C op f s).
Proof. exact (MK_COMB (@lem6149878 B C op) (@lem6149879 A B f s)). Qed.
Lemma lem6149882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149883 {B C : Type'} (f : type632 B C) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> C) -> C) f x).
Proof. exact (@lem6149882 (B -> Prop) (type570 B C) f x). Qed.
Lemma lem6149884 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term704 A B C op f s) = (term705 A B C op f s).
Proof. exact (@lem6149883 B C (@I ((C -> C -> C) -> (B -> Prop) -> (B -> C) -> C) (@iterate C B) op) (term700 A B f s)). Qed.
Lemma lem6149885 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term702 A B C op f s) = (term705 A B C op f s).
Proof. exact (TRANS (@lem6149880 A B C op f s) (@lem6149884 A B C op f s)). Qed.
Lemma lem6149886 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6149887 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term703 A B C op f s g) = (term706 A B C op f s g).
Proof. exact (MK_COMB (@lem6149885 A B C op f s) (@lem6149886 B C g)). Qed.
Lemma lem6149889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149890 {B C : Type'} (f : type570 B C) (x : B -> C) : (f x) = (@I ((B -> C) -> C) f x).
Proof. exact (@lem6149889 (B -> C) C f x). Qed.
Lemma lem6149891 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term706 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (@lem6149890 B C (term705 A B C op f s) g). Qed.
Lemma lem6149892 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term703 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (TRANS (@lem6149887 A B C op f s g) (@lem6149891 A B C op f s g)). Qed.
Lemma lem6149893 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term33 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (TRANS (@lem6149874 A B C op f s g) (@lem6149892 A B C op f s g)). Qed.
Lemma lem6149903 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149904 {A B C : Type'} (f : type808 A B C) (x : B -> C) : (f x) = (@I ((B -> C) -> (A -> B) -> A -> C) f x).
Proof. exact (@lem6149903 (B -> C) (type550 A B C) f x). Qed.
Lemma lem6149905 {A B C : Type'} (g : B -> C) : (@o A B C g) = (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g).
Proof. exact (@lem6149904 A B C (@o A B C) g). Qed.
Lemma lem6149906 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6149907 {A B C : Type'} (g : B -> C) (f : A -> B) : (@o A B C g f) = (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g f).
Proof. exact (MK_COMB (@lem6149905 A B C g) (@lem6149906 A B f)). Qed.
Lemma lem6149909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149910 {A B C : Type'} (f : type550 A B C) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> C) f x).
Proof. exact (@lem6149909 (A -> B) (A -> C) f x). Qed.
Lemma lem6149911 {A B C : Type'} (g : B -> C) (f : A -> B) : (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g f) = (term708 A B C g f).
Proof. exact (@lem6149910 A B C (@I ((B -> C) -> (A -> B) -> A -> C) (@o A B C) g) f). Qed.
Lemma lem6149913 {A B C : Type'} (g : B -> C) (f : A -> B) : (@o A B C g f) = (term708 A B C g f).
Proof. exact (TRANS (@lem6149907 A B C g f) (@lem6149911 A B C g f)). Qed.
Lemma lem6149915 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem6149916 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term34 A B C op s g f) = (term709 A B C op s g f).
Proof. exact (MK_COMB (@lem6149915 A C op s) (@lem6149913 A B C g f)). Qed.
Lemma lem6149918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149919 {A C : Type'} (f : type750 A C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem6149918 (type1400 C) (type632 A C) f x). Qed.
Lemma lem6149920 {A C : Type'} (op : type1400 C) : (@iterate C A op) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op).
Proof. exact (@lem6149919 A C (@iterate C A) op). Qed.
Lemma lem6149921 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6149922 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s).
Proof. exact (MK_COMB (@lem6149920 A C op) (@lem6149921 A s)). Qed.
Lemma lem6149924 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149925 {A C : Type'} (f : type632 A C) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> C) -> C) f x).
Proof. exact (@lem6149924 (A -> Prop) (type570 A C) f x). Qed.
Lemma lem6149926 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op s) = (term710 A C op s).
Proof. exact (@lem6149925 A C (@I ((C -> C -> C) -> (A -> Prop) -> (A -> C) -> C) (@iterate C A) op) s). Qed.
Lemma lem6149927 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (term710 A C op s).
Proof. exact (TRANS (@lem6149922 A C op s) (@lem6149926 A C op s)). Qed.
Lemma lem6149928 {A B C : Type'} (g : B -> C) (f : A -> B) : (term708 A B C g f) = (term708 A B C g f).
Proof. exact (eq_refl (term708 A B C g f)). Qed.
Lemma lem6149929 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term709 A B C op s g f) = (term711 A B C op s g f).
Proof. exact (MK_COMB (@lem6149927 A C op s) (@lem6149928 A B C g f)). Qed.
Lemma lem6149931 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149932 {A C : Type'} (f : type570 A C) (x : A -> C) : (f x) = (@I ((A -> C) -> C) f x).
Proof. exact (@lem6149931 (A -> C) C f x). Qed.
Lemma lem6149933 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term711 A B C op s g f) = (term712 A B C op s g f).
Proof. exact (@lem6149932 A C (term710 A C op s) (term708 A B C g f)). Qed.
Lemma lem6149934 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term709 A B C op s g f) = (term712 A B C op s g f).
Proof. exact (TRANS (@lem6149929 A B C op s g f) (@lem6149933 A B C op s g f)). Qed.
Lemma lem6149935 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term34 A B C op s g f) = (term712 A B C op s g f).
Proof. exact (TRANS (@lem6149916 A B C op s g f) (@lem6149934 A B C op s g f)). Qed.
Lemma lem6149936 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term594 A B C op f s g) = (term713 A B C op f s g).
Proof. exact (MK_COMB (@lem6149851 C) (@lem6149893 A B C op f s g)). Qed.
Lemma lem6149937 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term33 A B C op f s g) = (term34 A B C op s g f)) = ((term707 A B C op f s g) = (term712 A B C op s g f)).
Proof. exact (MK_COMB (@lem6149936 A B C op f s g) (@lem6149935 A B C op s g f)). Qed.
Lemma lem6149938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6149939 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6149940 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6149945 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149946 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6149945 A B f x). Qed.
Lemma lem6149948 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6149946 A B f y). Qed.
Lemma lem6149949 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term406 A B C g f y).
Proof. exact (MK_COMB (@lem6149940 B C g) (@lem6149948 A B f y)). Qed.
Lemma lem6149951 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149952 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem6149951 B C f x). Qed.
Lemma lem6149953 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term406 A B C g f y) = (term407 A B C g f y).
Proof. exact (@lem6149952 B C g (@I (A -> B) f y)). Qed.
Lemma lem6149954 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term110 A B C g f y) = (term407 A B C g f y).
Proof. exact (TRANS (@lem6149949 A B C g f y) (@lem6149953 A B C g f y)). Qed.
Lemma lem6149959 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149960 {C : Type'} (f : type402 C) (x : type1400 C) : (f x) = (@I ((C -> C -> C) -> C) f x).
Proof. exact (@lem6149959 (type1400 C) C f x). Qed.
Lemma lem6149962 {C : Type'} (op : type1400 C) : (@neutral C op) = (@I ((C -> C -> C) -> C) (@neutral C) op).
Proof. exact (@lem6149960 C (@neutral C) op). Qed.
Lemma lem6149963 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) : (term119 A B C g f y) = (term408 A B C g f y).
Proof. exact (MK_COMB (@lem6149939 C) (@lem6149954 A B C g f y)). Qed.
Lemma lem6149964 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : ((term110 A B C g f y) = (@neutral C op)) = ((term407 A B C g f y) = (@I ((C -> C -> C) -> C) (@neutral C) op)).
Proof. exact (MK_COMB (@lem6149963 A B C g f y) (@lem6149962 C op)). Qed.
Lemma lem6149965 {A B C : Type'} (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term421 A B C g f y op) = (term697 A B C g f y op).
Proof. exact (MK_COMB (@lem6149938) (@lem6149964 A B C g f y op)). Qed.
Lemma lem6149966 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6149971 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149972 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6149971 A B f x). Qed.
Lemma lem6149974 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem6149972 A B f x'). Qed.
Lemma lem6149979 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6149980 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem6149979 A B f x). Qed.
Lemma lem6149982 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem6149980 A B f y). Qed.
Lemma lem6149983 {A B : Type'} (f : A -> B) (x' : A) : (term409 A B f x') = (term410 A B f x').
Proof. exact (MK_COMB (@lem6149966 B) (@lem6149974 A B f x')). Qed.
Lemma lem6149984 {A B : Type'} (x' : A) (f : A -> B) (y : A) : ((f x') = (f y)) = ((@I (A -> B) f x') = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem6149983 A B f x') (@lem6149982 A B f y)). Qed.
Lemma lem6149993 {A : Type'} (x' : A) (y : A) : (term423 A x' y) = (term423 A x' y).
Proof. exact (eq_refl (term423 A x' y)). Qed.
Lemma lem6149994 {A B : Type'} (x' : A) (f : A -> B) (y : A) : (term118 A B x' f y) = (term424 A B x' f y).
Proof. exact (MK_COMB (@lem6149993 A x' y) (@lem6149984 A B x' f y)). Qed.
Lemma lem6150001 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6150002 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6150001 A (type686 A) f x). Qed.
Lemma lem6150003 {A : Type'} (y : A) : (@IN A y) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y).
Proof. exact (@lem6150002 A (@IN A) y). Qed.
Lemma lem6150004 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6150005 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y s).
Proof. exact (MK_COMB (@lem6150003 A y) (@lem6150004 A s)). Qed.
Lemma lem6150007 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6150008 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6150007 (A -> Prop) Prop f x). Qed.
Lemma lem6150009 {A : Type'} (y : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y s) = (term685 A y s).
Proof. exact (@lem6150008 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y) s). Qed.
Lemma lem6150011 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (term685 A y s).
Proof. exact (TRANS (@lem6150005 A y s) (@lem6150009 A y s)). Qed.
Lemma lem6150012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6150013 {A : Type'} (y : A) (s : A -> Prop) : (term425 A y s) = (term714 A y s).
Proof. exact (MK_COMB (@lem6150012) (@lem6150011 A y s)). Qed.
Lemma lem6150014 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term159 A B s x' f y) = (term715 A B s x' f y).
Proof. exact (MK_COMB (@lem6150013 A y s) (@lem6149994 A B x' f y)). Qed.
Lemma lem6150021 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6150022 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6150021 A (type686 A) f x). Qed.
Lemma lem6150023 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem6150022 A (@IN A) x'). Qed.
Lemma lem6150024 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6150025 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem6150023 A x') (@lem6150024 A s)). Qed.
Lemma lem6150027 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6150028 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6150027 (A -> Prop) Prop f x). Qed.
Lemma lem6150029 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term685 A x' s).
Proof. exact (@lem6150028 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem6150031 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term685 A x' s).
Proof. exact (TRANS (@lem6150025 A x' s) (@lem6150029 A x' s)). Qed.
Lemma lem6150032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6150033 {A : Type'} (x' : A) (s : A -> Prop) : (term425 A x' s) = (term714 A x' s).
Proof. exact (MK_COMB (@lem6150032) (@lem6150031 A x' s)). Qed.
Lemma lem6150034 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term152 A B s x' f y) = (term716 A B s x' f y).
Proof. exact (MK_COMB (@lem6150033 A x' s) (@lem6150014 A B s x' f y)). Qed.
Lemma lem6150035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6150036 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (y : A) : (term428 A B s x' f y) = (term717 A B s x' f y).
Proof. exact (MK_COMB (@lem6150035) (@lem6150034 A B s x' f y)). Qed.
Lemma lem6150037 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term325 A B C s x' g f y op) = (term718 A B C s x' g f y op).
Proof. exact (MK_COMB (@lem6150036 A B s x' f y) (@lem6149965 A B C g f y op)). Qed.
Lemma lem6150038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6150039 {A B C : Type'} (s : A -> Prop) (x' : A) (g : B -> C) (f : A -> B) (y : A) (op : type1400 C) : (term372 A B C s x' g f y op) = (term719 A B C s x' g f y op).
Proof. exact (MK_COMB (@lem6150038) (@lem6150037 A B C s x' g f y op)). Qed.
Lemma lem6150040 {A B C : Type'} (x' : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term374 A B C x' y op s g f) = (term720 A B C x' y op s g f).
Proof. exact (MK_COMB (@lem6150039 A B C s x' g f y op) (@lem6149937 A B C op s g f)). Qed.
Lemma lem6150041 {A B C : Type'} (x' : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term374 A B C x' y op s g f) : term720 A B C x' y op s g f.
Proof. exact (EQ_MP (@lem6150040 A B C x' y op s g f) (@lem6148661 A B C x' y op s g f h1)). Qed.
Lemma lem6151085 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6151086 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6151085 C P Q). Qed.
Lemma lem6151087 {C : Type'} (op : type1400 C) : (term1039 C op) = (term1040 C op).
Proof. exact (@lem6151086 C (term1001 C op) (term987 C op)). Qed.
Lemma lem6151088 {C : Type'} (a : C) (op : type1400 C) : (term1041 C op a) = (term1000 C a op).
Proof. exact (eq_refl (term1041 C op a)). Qed.
Lemma lem6151089 {C : Type'} (op : type1400 C) : (term1042 C op) = (term1001 C op).
Proof. exact (fun_ext (fun a : C => @lem6151088 C a op)). Qed.
Lemma lem6151090 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151091 {C : Type'} (op : type1400 C) : (term1043 C op) = (term1002 C op).
Proof. exact (MK_COMB (@lem6151090 C) (@lem6151089 C op)). Qed.
Lemma lem6151092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151093 {C : Type'} (op : type1400 C) : (term1044 C op) = (term1003 C op).
Proof. exact (MK_COMB (@lem6151092) (@lem6151091 C op)). Qed.
Lemma lem6151094 {C : Type'} (op : type1400 C) (a : C) : (term1045 C op a) = (term986 C op a).
Proof. exact (eq_refl (term1045 C op a)). Qed.
Lemma lem6151095 {C : Type'} (op : type1400 C) : (term1046 C op) = (term987 C op).
Proof. exact (fun_ext (fun a : C => @lem6151094 C op a)). Qed.
Lemma lem6151096 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151097 {C : Type'} (op : type1400 C) : (term1047 C op) = (term988 C op).
Proof. exact (MK_COMB (@lem6151096 C) (@lem6151095 C op)). Qed.
Lemma lem6151098 {C : Type'} (op : type1400 C) : (term1039 C op) = (term1004 C op).
Proof. exact (MK_COMB (@lem6151093 C op) (@lem6151097 C op)). Qed.
Lemma lem6151099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151100 {C : Type'} (op : type1400 C) : (term1048 C op) = (term1049 C op).
Proof. exact (MK_COMB (@lem6151099) (@lem6151098 C op)). Qed.
Lemma lem6151101 {C : Type'} (a : C) (op : type1400 C) : (term1041 C op a) = (term1000 C a op).
Proof. exact (eq_refl (term1041 C op a)). Qed.
Lemma lem6151102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151103 {C : Type'} (a : C) (op : type1400 C) : (term1050 C op a) = (term1051 C a op).
Proof. exact (MK_COMB (@lem6151102) (@lem6151101 C a op)). Qed.
Lemma lem6151104 {C : Type'} (op : type1400 C) (a : C) : (term1045 C op a) = (term986 C op a).
Proof. exact (eq_refl (term1045 C op a)). Qed.
Lemma lem6151105 {C : Type'} (op : type1400 C) (a : C) : (term1052 C op a) = (term1053 C op a).
Proof. exact (MK_COMB (@lem6151103 C a op) (@lem6151104 C op a)). Qed.
Lemma lem6151106 {C : Type'} (op : type1400 C) : (term1054 C op) = (term1055 C op).
Proof. exact (fun_ext (fun a : C => @lem6151105 C op a)). Qed.
Lemma lem6151107 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151108 {C : Type'} (op : type1400 C) : (term1040 C op) = (term1056 C op).
Proof. exact (MK_COMB (@lem6151107 C) (@lem6151106 C op)). Qed.
Lemma lem6151109 {C : Type'} (op : type1400 C) : ((term1039 C op) = (term1040 C op)) = ((term1004 C op) = (term1056 C op)).
Proof. exact (MK_COMB (@lem6151100 C op) (@lem6151108 C op)). Qed.
Lemma lem6151110 {C : Type'} (op : type1400 C) : (term1004 C op) = (term1056 C op).
Proof. exact (EQ_MP (@lem6151109 C op) (@lem6151087 C op)). Qed.
Lemma lem6151112 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6151113 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6151112 C P Q). Qed.
Lemma lem6151114 {C : Type'} (op : type1400 C) (a : C) : (term1057 C op a) = (term1058 C op a).
Proof. exact (@lem6151113 C (term999 C a op) (term985 C op a)). Qed.
Lemma lem6151115 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1059 C a op b) = (term998 C a op b).
Proof. exact (eq_refl (term1059 C a op b)). Qed.
Lemma lem6151116 {C : Type'} (a : C) (op : type1400 C) : (term1060 C a op) = (term999 C a op).
Proof. exact (fun_ext (fun b : C => @lem6151115 C a op b)). Qed.
Lemma lem6151117 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151118 {C : Type'} (a : C) (op : type1400 C) : (term1061 C a op) = (term1000 C a op).
Proof. exact (MK_COMB (@lem6151117 C) (@lem6151116 C a op)). Qed.
Lemma lem6151119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151120 {C : Type'} (a : C) (op : type1400 C) : (term1062 C a op) = (term1051 C a op).
Proof. exact (MK_COMB (@lem6151119) (@lem6151118 C a op)). Qed.
Lemma lem6151121 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1063 C op a b) = (term984 C b op a).
Proof. exact (eq_refl (term1063 C op a b)). Qed.
Lemma lem6151122 {C : Type'} (op : type1400 C) (a : C) : (term1064 C op a) = (term985 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151121 C b op a)). Qed.
Lemma lem6151123 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151124 {C : Type'} (op : type1400 C) (a : C) : (term1065 C op a) = (term986 C op a).
Proof. exact (MK_COMB (@lem6151123 C) (@lem6151122 C op a)). Qed.
Lemma lem6151125 {C : Type'} (op : type1400 C) (a : C) : (term1057 C op a) = (term1053 C op a).
Proof. exact (MK_COMB (@lem6151120 C a op) (@lem6151124 C op a)). Qed.
Lemma lem6151126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151127 {C : Type'} (op : type1400 C) (a : C) : (term1066 C op a) = (term1067 C op a).
Proof. exact (MK_COMB (@lem6151126) (@lem6151125 C op a)). Qed.
Lemma lem6151128 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1059 C a op b) = (term998 C a op b).
Proof. exact (eq_refl (term1059 C a op b)). Qed.
Lemma lem6151129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151130 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1068 C a op b) = (term1069 C a op b).
Proof. exact (MK_COMB (@lem6151129) (@lem6151128 C a op b)). Qed.
Lemma lem6151131 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1063 C op a b) = (term984 C b op a).
Proof. exact (eq_refl (term1063 C op a b)). Qed.
Lemma lem6151132 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1070 C op a b) = (term1071 C b op a).
Proof. exact (MK_COMB (@lem6151130 C a op b) (@lem6151131 C b op a)). Qed.
Lemma lem6151133 {C : Type'} (op : type1400 C) (a : C) : (term1072 C op a) = (term1073 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151132 C b op a)). Qed.
Lemma lem6151134 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151135 {C : Type'} (op : type1400 C) (a : C) : (term1058 C op a) = (term1074 C op a).
Proof. exact (MK_COMB (@lem6151134 C) (@lem6151133 C op a)). Qed.
Lemma lem6151136 {C : Type'} (op : type1400 C) (a : C) : ((term1057 C op a) = (term1058 C op a)) = ((term1053 C op a) = (term1074 C op a)).
Proof. exact (MK_COMB (@lem6151127 C op a) (@lem6151135 C op a)). Qed.
Lemma lem6151137 {C : Type'} (op : type1400 C) (a : C) : (term1053 C op a) = (term1074 C op a).
Proof. exact (EQ_MP (@lem6151136 C op a) (@lem6151114 C op a)). Qed.
Lemma lem6151139 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6151140 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6151139 C P Q). Qed.
Lemma lem6151141 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1075 C b op a) = (term1076 C b op a).
Proof. exact (@lem6151140 C (term997 C a op b) (term983 C b op a)). Qed.
Lemma lem6151142 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term1077 C a op b c) = ((term994 C op a b c) = (term980 C a op b c)).
Proof. exact (eq_refl (term1077 C a op b c)). Qed.
Lemma lem6151143 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1078 C a op b) = (term997 C a op b).
Proof. exact (fun_ext (fun c : C => @lem6151142 C a op b c)). Qed.
Lemma lem6151144 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151145 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1079 C a op b) = (term998 C a op b).
Proof. exact (MK_COMB (@lem6151144 C) (@lem6151143 C a op b)). Qed.
Lemma lem6151146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151147 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1080 C a op b) = (term1069 C a op b).
Proof. exact (MK_COMB (@lem6151146) (@lem6151145 C a op b)). Qed.
Lemma lem6151148 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1081 C b op a c) = ((term980 C a op b c) = (term980 C b op a c)).
Proof. exact (eq_refl (term1081 C b op a c)). Qed.
Lemma lem6151149 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1082 C b op a) = (term983 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151148 C b op a c)). Qed.
Lemma lem6151150 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151151 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1083 C b op a) = (term984 C b op a).
Proof. exact (MK_COMB (@lem6151150 C) (@lem6151149 C b op a)). Qed.
Lemma lem6151152 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1075 C b op a) = (term1071 C b op a).
Proof. exact (MK_COMB (@lem6151147 C a op b) (@lem6151151 C b op a)). Qed.
Lemma lem6151153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151154 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1084 C b op a) = (term1085 C b op a).
Proof. exact (MK_COMB (@lem6151153) (@lem6151152 C b op a)). Qed.
Lemma lem6151155 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term1077 C a op b c) = ((term994 C op a b c) = (term980 C a op b c)).
Proof. exact (eq_refl (term1077 C a op b c)). Qed.
Lemma lem6151156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151157 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term1086 C a op b c) = (term1087 C a op b c).
Proof. exact (MK_COMB (@lem6151156) (@lem6151155 C a op b c)). Qed.
Lemma lem6151158 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1081 C b op a c) = ((term980 C a op b c) = (term980 C b op a c)).
Proof. exact (eq_refl (term1081 C b op a c)). Qed.
Lemma lem6151159 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1088 C b op a c) = (term1089 C b op a c).
Proof. exact (MK_COMB (@lem6151157 C a op b c) (@lem6151158 C b op a c)). Qed.
Lemma lem6151160 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1090 C b op a) = (term1091 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151159 C b op a c)). Qed.
Lemma lem6151161 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151162 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1076 C b op a) = (term1092 C b op a).
Proof. exact (MK_COMB (@lem6151161 C) (@lem6151160 C b op a)). Qed.
Lemma lem6151163 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1075 C b op a) = (term1076 C b op a)) = ((term1071 C b op a) = (term1092 C b op a)).
Proof. exact (MK_COMB (@lem6151154 C b op a) (@lem6151162 C b op a)). Qed.
Lemma lem6151164 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1071 C b op a) = (term1092 C b op a).
Proof. exact (EQ_MP (@lem6151163 C b op a) (@lem6151141 C b op a)). Qed.
Lemma lem6151165 {C : Type'} (op : type1400 C) (a : C) : (term1073 C op a) = (term1093 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151164 C b op a)). Qed.
Lemma lem6151166 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151167 {C : Type'} (op : type1400 C) (a : C) : (term1074 C op a) = (term1094 C op a).
Proof. exact (MK_COMB (@lem6151166 C) (@lem6151165 C op a)). Qed.
Lemma lem6151168 {C : Type'} (op : type1400 C) (a : C) : (term1053 C op a) = (term1094 C op a).
Proof. exact (TRANS (@lem6151137 C op a) (@lem6151167 C op a)). Qed.
Lemma lem6151169 {C : Type'} (op : type1400 C) : (term1055 C op) = (term1095 C op).
Proof. exact (fun_ext (fun a : C => @lem6151168 C op a)). Qed.
Lemma lem6151170 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151171 {C : Type'} (op : type1400 C) : (term1056 C op) = (term1096 C op).
Proof. exact (MK_COMB (@lem6151170 C) (@lem6151169 C op)). Qed.
Lemma lem6151172 {C : Type'} (op : type1400 C) : (term1004 C op) = (term1096 C op).
Proof. exact (TRANS (@lem6151110 C op) (@lem6151171 C op)). Qed.
Lemma lem6151173 {C : Type'} (op : type1400 C) : (term1011 C op) = (term1011 C op).
Proof. exact (eq_refl (term1011 C op)). Qed.
Lemma lem6151174 {C : Type'} (op : type1400 C) : (term1012 C op) = (term1097 C op).
Proof. exact (MK_COMB (@lem6151173 C op) (@lem6151172 C op)). Qed.
Lemma lem6151176 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6151177 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6151176 C P Q). Qed.
Lemma lem6151178 {C : Type'} (op : type1400 C) : (term1098 C op) = (term1099 C op).
Proof. exact (@lem6151177 C (term1009 C op) (term1095 C op)). Qed.
Lemma lem6151179 {C : Type'} (op : type1400 C) (a : C) : (term1100 C op a) = (term1008 C op a).
Proof. exact (eq_refl (term1100 C op a)). Qed.
Lemma lem6151180 {C : Type'} (op : type1400 C) : (term1101 C op) = (term1009 C op).
Proof. exact (fun_ext (fun a : C => @lem6151179 C op a)). Qed.
Lemma lem6151181 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151182 {C : Type'} (op : type1400 C) : (term1102 C op) = (term1010 C op).
Proof. exact (MK_COMB (@lem6151181 C) (@lem6151180 C op)). Qed.
Lemma lem6151183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151184 {C : Type'} (op : type1400 C) : (term1103 C op) = (term1011 C op).
Proof. exact (MK_COMB (@lem6151183) (@lem6151182 C op)). Qed.
Lemma lem6151185 {C : Type'} (op : type1400 C) (a : C) : (term1104 C op a) = (term1094 C op a).
Proof. exact (eq_refl (term1104 C op a)). Qed.
Lemma lem6151186 {C : Type'} (op : type1400 C) : (term1105 C op) = (term1095 C op).
Proof. exact (fun_ext (fun a : C => @lem6151185 C op a)). Qed.
Lemma lem6151187 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151188 {C : Type'} (op : type1400 C) : (term1106 C op) = (term1096 C op).
Proof. exact (MK_COMB (@lem6151187 C) (@lem6151186 C op)). Qed.
Lemma lem6151189 {C : Type'} (op : type1400 C) : (term1098 C op) = (term1097 C op).
Proof. exact (MK_COMB (@lem6151184 C op) (@lem6151188 C op)). Qed.
Lemma lem6151190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151191 {C : Type'} (op : type1400 C) : (term1107 C op) = (term1108 C op).
Proof. exact (MK_COMB (@lem6151190) (@lem6151189 C op)). Qed.
Lemma lem6151192 {C : Type'} (op : type1400 C) (a : C) : (term1100 C op a) = (term1008 C op a).
Proof. exact (eq_refl (term1100 C op a)). Qed.
Lemma lem6151193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151194 {C : Type'} (op : type1400 C) (a : C) : (term1109 C op a) = (term1110 C op a).
Proof. exact (MK_COMB (@lem6151193) (@lem6151192 C op a)). Qed.
Lemma lem6151195 {C : Type'} (op : type1400 C) (a : C) : (term1104 C op a) = (term1094 C op a).
Proof. exact (eq_refl (term1104 C op a)). Qed.
Lemma lem6151196 {C : Type'} (op : type1400 C) (a : C) : (term1111 C op a) = (term1112 C op a).
Proof. exact (MK_COMB (@lem6151194 C op a) (@lem6151195 C op a)). Qed.
Lemma lem6151197 {C : Type'} (op : type1400 C) : (term1113 C op) = (term1114 C op).
Proof. exact (fun_ext (fun a : C => @lem6151196 C op a)). Qed.
Lemma lem6151198 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151199 {C : Type'} (op : type1400 C) : (term1099 C op) = (term1115 C op).
Proof. exact (MK_COMB (@lem6151198 C) (@lem6151197 C op)). Qed.
Lemma lem6151200 {C : Type'} (op : type1400 C) : ((term1098 C op) = (term1099 C op)) = ((term1097 C op) = (term1115 C op)).
Proof. exact (MK_COMB (@lem6151191 C op) (@lem6151199 C op)). Qed.
Lemma lem6151201 {C : Type'} (op : type1400 C) : (term1097 C op) = (term1115 C op).
Proof. exact (EQ_MP (@lem6151200 C op) (@lem6151178 C op)). Qed.
Lemma lem6151203 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6151204 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6151203 C P Q). Qed.
Lemma lem6151205 {C : Type'} (op : type1400 C) (a : C) : (term1116 C op a) = (term1117 C op a).
Proof. exact (@lem6151204 C (term1007 C op a) (term1093 C op a)). Qed.
Lemma lem6151206 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1118 C op a b) = ((term977 C op a b) = (term977 C op b a)).
Proof. exact (eq_refl (term1118 C op a b)). Qed.
Lemma lem6151207 {C : Type'} (op : type1400 C) (a : C) : (term1119 C op a) = (term1007 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151206 C op b a)). Qed.
Lemma lem6151208 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151209 {C : Type'} (op : type1400 C) (a : C) : (term1120 C op a) = (term1008 C op a).
Proof. exact (MK_COMB (@lem6151208 C) (@lem6151207 C op a)). Qed.
Lemma lem6151210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151211 {C : Type'} (op : type1400 C) (a : C) : (term1121 C op a) = (term1110 C op a).
Proof. exact (MK_COMB (@lem6151210) (@lem6151209 C op a)). Qed.
Lemma lem6151212 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1122 C op a b) = (term1092 C b op a).
Proof. exact (eq_refl (term1122 C op a b)). Qed.
Lemma lem6151213 {C : Type'} (op : type1400 C) (a : C) : (term1123 C op a) = (term1093 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151212 C b op a)). Qed.
Lemma lem6151214 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151215 {C : Type'} (op : type1400 C) (a : C) : (term1124 C op a) = (term1094 C op a).
Proof. exact (MK_COMB (@lem6151214 C) (@lem6151213 C op a)). Qed.
Lemma lem6151216 {C : Type'} (op : type1400 C) (a : C) : (term1116 C op a) = (term1112 C op a).
Proof. exact (MK_COMB (@lem6151211 C op a) (@lem6151215 C op a)). Qed.
Lemma lem6151217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151218 {C : Type'} (op : type1400 C) (a : C) : (term1125 C op a) = (term1126 C op a).
Proof. exact (MK_COMB (@lem6151217) (@lem6151216 C op a)). Qed.
Lemma lem6151219 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1118 C op a b) = ((term977 C op a b) = (term977 C op b a)).
Proof. exact (eq_refl (term1118 C op a b)). Qed.
Lemma lem6151220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151221 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1127 C op a b) = (term1128 C op b a).
Proof. exact (MK_COMB (@lem6151220) (@lem6151219 C op b a)). Qed.
Lemma lem6151222 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1122 C op a b) = (term1092 C b op a).
Proof. exact (eq_refl (term1122 C op a b)). Qed.
Lemma lem6151223 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1129 C op a b) = (term1130 C b op a).
Proof. exact (MK_COMB (@lem6151221 C op b a) (@lem6151222 C b op a)). Qed.
Lemma lem6151224 {C : Type'} (op : type1400 C) (a : C) : (term1131 C op a) = (term1132 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151223 C b op a)). Qed.
Lemma lem6151225 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151226 {C : Type'} (op : type1400 C) (a : C) : (term1117 C op a) = (term1133 C op a).
Proof. exact (MK_COMB (@lem6151225 C) (@lem6151224 C op a)). Qed.
Lemma lem6151227 {C : Type'} (op : type1400 C) (a : C) : ((term1116 C op a) = (term1117 C op a)) = ((term1112 C op a) = (term1133 C op a)).
Proof. exact (MK_COMB (@lem6151218 C op a) (@lem6151226 C op a)). Qed.
Lemma lem6151228 {C : Type'} (op : type1400 C) (a : C) : (term1112 C op a) = (term1133 C op a).
Proof. exact (EQ_MP (@lem6151227 C op a) (@lem6151205 C op a)). Qed.
Lemma lem6151230 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6151231 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6151230 C P Q). Qed.
Lemma lem6151232 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1136 C b op a) = (term1137 C b op a).
Proof. exact (@lem6151231 C ((term977 C op a b) = (term977 C op b a)) (term1091 C b op a)). Qed.
Lemma lem6151233 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1138 C b op a c) = (term1089 C b op a c).
Proof. exact (eq_refl (term1138 C b op a c)). Qed.
Lemma lem6151234 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1139 C b op a) = (term1091 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151233 C b op a c)). Qed.
Lemma lem6151235 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151236 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1140 C b op a) = (term1092 C b op a).
Proof. exact (MK_COMB (@lem6151235 C) (@lem6151234 C b op a)). Qed.
Lemma lem6151237 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1128 C op b a) = (term1128 C op b a).
Proof. exact (eq_refl (term1128 C op b a)). Qed.
Lemma lem6151238 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1136 C b op a) = (term1130 C b op a).
Proof. exact (MK_COMB (@lem6151237 C op b a) (@lem6151236 C b op a)). Qed.
Lemma lem6151239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151240 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1141 C b op a) = (term1142 C b op a).
Proof. exact (MK_COMB (@lem6151239) (@lem6151238 C b op a)). Qed.
Lemma lem6151241 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1138 C b op a c) = (term1089 C b op a c).
Proof. exact (eq_refl (term1138 C b op a c)). Qed.
Lemma lem6151242 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1128 C op b a) = (term1128 C op b a).
Proof. exact (eq_refl (term1128 C op b a)). Qed.
Lemma lem6151243 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1143 C b op a c) = (term1144 C b op a c).
Proof. exact (MK_COMB (@lem6151242 C op b a) (@lem6151241 C b op a c)). Qed.
Lemma lem6151244 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1145 C b op a) = (term1146 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151243 C b op a c)). Qed.
Lemma lem6151245 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151246 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1137 C b op a) = (term1147 C b op a).
Proof. exact (MK_COMB (@lem6151245 C) (@lem6151244 C b op a)). Qed.
Lemma lem6151247 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1136 C b op a) = (term1137 C b op a)) = ((term1130 C b op a) = (term1147 C b op a)).
Proof. exact (MK_COMB (@lem6151240 C b op a) (@lem6151246 C b op a)). Qed.
Lemma lem6151248 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1130 C b op a) = (term1147 C b op a).
Proof. exact (EQ_MP (@lem6151247 C b op a) (@lem6151232 C b op a)). Qed.
Lemma lem6151249 {C : Type'} (op : type1400 C) (a : C) : (term1132 C op a) = (term1148 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151248 C b op a)). Qed.
Lemma lem6151250 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151251 {C : Type'} (op : type1400 C) (a : C) : (term1133 C op a) = (term1149 C op a).
Proof. exact (MK_COMB (@lem6151250 C) (@lem6151249 C op a)). Qed.
Lemma lem6151252 {C : Type'} (op : type1400 C) (a : C) : (term1112 C op a) = (term1149 C op a).
Proof. exact (TRANS (@lem6151228 C op a) (@lem6151251 C op a)). Qed.
Lemma lem6151253 {C : Type'} (op : type1400 C) : (term1114 C op) = (term1150 C op).
Proof. exact (fun_ext (fun a : C => @lem6151252 C op a)). Qed.
Lemma lem6151254 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151255 {C : Type'} (op : type1400 C) : (term1115 C op) = (term1151 C op).
Proof. exact (MK_COMB (@lem6151254 C) (@lem6151253 C op)). Qed.
Lemma lem6151256 {C : Type'} (op : type1400 C) : (term1097 C op) = (term1151 C op).
Proof. exact (TRANS (@lem6151201 C op) (@lem6151255 C op)). Qed.
Lemma lem6151257 {C : Type'} (op : type1400 C) : (term1012 C op) = (term1151 C op).
Proof. exact (TRANS (@lem6151174 C op) (@lem6151256 C op)). Qed.
Lemma lem6151258 {C : Type'} (op : type1400 C) : (term1020 C op) = (term1020 C op).
Proof. exact (eq_refl (term1020 C op)). Qed.
Lemma lem6151259 {C : Type'} (op : type1400 C) : (term1021 C op) = (term1152 C op).
Proof. exact (MK_COMB (@lem6151258 C op) (@lem6151257 C op)). Qed.
Lemma lem6151261 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6151262 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6151261 C P Q). Qed.
Lemma lem6151263 {C : Type'} (op : type1400 C) : (term1153 C op) = (term1154 C op).
Proof. exact (@lem6151262 C (term1018 C op) (term1150 C op)). Qed.
Lemma lem6151264 {C : Type'} (op : type1400 C) (a : C) : (term1155 C op a) = ((term1015 C a op) = a).
Proof. exact (eq_refl (term1155 C op a)). Qed.
Lemma lem6151265 {C : Type'} (op : type1400 C) : (term1156 C op) = (term1018 C op).
Proof. exact (fun_ext (fun a : C => @lem6151264 C op a)). Qed.
Lemma lem6151266 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151267 {C : Type'} (op : type1400 C) : (term1157 C op) = (term1019 C op).
Proof. exact (MK_COMB (@lem6151266 C) (@lem6151265 C op)). Qed.
Lemma lem6151268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151269 {C : Type'} (op : type1400 C) : (term1158 C op) = (term1020 C op).
Proof. exact (MK_COMB (@lem6151268) (@lem6151267 C op)). Qed.
Lemma lem6151270 {C : Type'} (op : type1400 C) (a : C) : (term1159 C op a) = (term1149 C op a).
Proof. exact (eq_refl (term1159 C op a)). Qed.
Lemma lem6151271 {C : Type'} (op : type1400 C) : (term1160 C op) = (term1150 C op).
Proof. exact (fun_ext (fun a : C => @lem6151270 C op a)). Qed.
Lemma lem6151272 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151273 {C : Type'} (op : type1400 C) : (term1161 C op) = (term1151 C op).
Proof. exact (MK_COMB (@lem6151272 C) (@lem6151271 C op)). Qed.
Lemma lem6151274 {C : Type'} (op : type1400 C) : (term1153 C op) = (term1152 C op).
Proof. exact (MK_COMB (@lem6151269 C op) (@lem6151273 C op)). Qed.
Lemma lem6151275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151276 {C : Type'} (op : type1400 C) : (term1162 C op) = (term1163 C op).
Proof. exact (MK_COMB (@lem6151275) (@lem6151274 C op)). Qed.
Lemma lem6151277 {C : Type'} (op : type1400 C) (a : C) : (term1155 C op a) = ((term1015 C a op) = a).
Proof. exact (eq_refl (term1155 C op a)). Qed.
Lemma lem6151278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151279 {C : Type'} (op : type1400 C) (a : C) : (term1164 C op a) = (term1165 C op a).
Proof. exact (MK_COMB (@lem6151278) (@lem6151277 C op a)). Qed.
Lemma lem6151280 {C : Type'} (op : type1400 C) (a : C) : (term1159 C op a) = (term1149 C op a).
Proof. exact (eq_refl (term1159 C op a)). Qed.
Lemma lem6151281 {C : Type'} (op : type1400 C) (a : C) : (term1166 C op a) = (term1167 C op a).
Proof. exact (MK_COMB (@lem6151279 C op a) (@lem6151280 C op a)). Qed.
Lemma lem6151282 {C : Type'} (op : type1400 C) : (term1168 C op) = (term1169 C op).
Proof. exact (fun_ext (fun a : C => @lem6151281 C op a)). Qed.
Lemma lem6151283 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151284 {C : Type'} (op : type1400 C) : (term1154 C op) = (term1170 C op).
Proof. exact (MK_COMB (@lem6151283 C) (@lem6151282 C op)). Qed.
Lemma lem6151285 {C : Type'} (op : type1400 C) : ((term1153 C op) = (term1154 C op)) = ((term1152 C op) = (term1170 C op)).
Proof. exact (MK_COMB (@lem6151276 C op) (@lem6151284 C op)). Qed.
Lemma lem6151286 {C : Type'} (op : type1400 C) : (term1152 C op) = (term1170 C op).
Proof. exact (EQ_MP (@lem6151285 C op) (@lem6151263 C op)). Qed.
Lemma lem6151288 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6151289 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6151288 C P Q). Qed.
Lemma lem6151290 {C : Type'} (op : type1400 C) (a : C) : (term1171 C op a) = (term1172 C op a).
Proof. exact (@lem6151289 C ((term1015 C a op) = a) (term1148 C op a)). Qed.
Lemma lem6151291 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1173 C op a b) = (term1147 C b op a).
Proof. exact (eq_refl (term1173 C op a b)). Qed.
Lemma lem6151292 {C : Type'} (op : type1400 C) (a : C) : (term1174 C op a) = (term1148 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151291 C b op a)). Qed.
Lemma lem6151293 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151294 {C : Type'} (op : type1400 C) (a : C) : (term1175 C op a) = (term1149 C op a).
Proof. exact (MK_COMB (@lem6151293 C) (@lem6151292 C op a)). Qed.
Lemma lem6151295 {C : Type'} (op : type1400 C) (a : C) : (term1165 C op a) = (term1165 C op a).
Proof. exact (eq_refl (term1165 C op a)). Qed.
Lemma lem6151296 {C : Type'} (op : type1400 C) (a : C) : (term1171 C op a) = (term1167 C op a).
Proof. exact (MK_COMB (@lem6151295 C op a) (@lem6151294 C op a)). Qed.
Lemma lem6151297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151298 {C : Type'} (op : type1400 C) (a : C) : (term1176 C op a) = (term1177 C op a).
Proof. exact (MK_COMB (@lem6151297) (@lem6151296 C op a)). Qed.
Lemma lem6151299 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1173 C op a b) = (term1147 C b op a).
Proof. exact (eq_refl (term1173 C op a b)). Qed.
Lemma lem6151300 {C : Type'} (op : type1400 C) (a : C) : (term1165 C op a) = (term1165 C op a).
Proof. exact (eq_refl (term1165 C op a)). Qed.
Lemma lem6151301 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1178 C op a b) = (term1179 C b op a).
Proof. exact (MK_COMB (@lem6151300 C op a) (@lem6151299 C b op a)). Qed.
Lemma lem6151302 {C : Type'} (op : type1400 C) (a : C) : (term1180 C op a) = (term1181 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151301 C b op a)). Qed.
Lemma lem6151303 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151304 {C : Type'} (op : type1400 C) (a : C) : (term1172 C op a) = (term1182 C op a).
Proof. exact (MK_COMB (@lem6151303 C) (@lem6151302 C op a)). Qed.
Lemma lem6151305 {C : Type'} (op : type1400 C) (a : C) : ((term1171 C op a) = (term1172 C op a)) = ((term1167 C op a) = (term1182 C op a)).
Proof. exact (MK_COMB (@lem6151298 C op a) (@lem6151304 C op a)). Qed.
Lemma lem6151306 {C : Type'} (op : type1400 C) (a : C) : (term1167 C op a) = (term1182 C op a).
Proof. exact (EQ_MP (@lem6151305 C op a) (@lem6151290 C op a)). Qed.
Lemma lem6151308 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6151309 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6151308 C P Q). Qed.
Lemma lem6151310 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1183 C b op a) = (term1184 C b op a).
Proof. exact (@lem6151309 C ((term1015 C a op) = a) (term1146 C b op a)). Qed.
Lemma lem6151311 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1185 C b op a c) = (term1144 C b op a c).
Proof. exact (eq_refl (term1185 C b op a c)). Qed.
Lemma lem6151312 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1186 C b op a) = (term1146 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151311 C b op a c)). Qed.
Lemma lem6151313 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151314 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1187 C b op a) = (term1147 C b op a).
Proof. exact (MK_COMB (@lem6151313 C) (@lem6151312 C b op a)). Qed.
Lemma lem6151315 {C : Type'} (op : type1400 C) (a : C) : (term1165 C op a) = (term1165 C op a).
Proof. exact (eq_refl (term1165 C op a)). Qed.
Lemma lem6151316 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1183 C b op a) = (term1179 C b op a).
Proof. exact (MK_COMB (@lem6151315 C op a) (@lem6151314 C b op a)). Qed.
Lemma lem6151317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151318 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1188 C b op a) = (term1189 C b op a).
Proof. exact (MK_COMB (@lem6151317) (@lem6151316 C b op a)). Qed.
Lemma lem6151319 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1185 C b op a c) = (term1144 C b op a c).
Proof. exact (eq_refl (term1185 C b op a c)). Qed.
Lemma lem6151320 {C : Type'} (op : type1400 C) (a : C) : (term1165 C op a) = (term1165 C op a).
Proof. exact (eq_refl (term1165 C op a)). Qed.
Lemma lem6151321 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1190 C b op a c) = (term1191 C b op a c).
Proof. exact (MK_COMB (@lem6151320 C op a) (@lem6151319 C b op a c)). Qed.
Lemma lem6151322 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1192 C b op a) = (term1193 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151321 C b op a c)). Qed.
Lemma lem6151323 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151324 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1184 C b op a) = (term1194 C b op a).
Proof. exact (MK_COMB (@lem6151323 C) (@lem6151322 C b op a)). Qed.
Lemma lem6151325 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1183 C b op a) = (term1184 C b op a)) = ((term1179 C b op a) = (term1194 C b op a)).
Proof. exact (MK_COMB (@lem6151318 C b op a) (@lem6151324 C b op a)). Qed.
Lemma lem6151326 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1179 C b op a) = (term1194 C b op a).
Proof. exact (EQ_MP (@lem6151325 C b op a) (@lem6151310 C b op a)). Qed.
Lemma lem6151327 {C : Type'} (op : type1400 C) (a : C) : (term1181 C op a) = (term1195 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151326 C b op a)). Qed.
Lemma lem6151328 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151329 {C : Type'} (op : type1400 C) (a : C) : (term1182 C op a) = (term1196 C op a).
Proof. exact (MK_COMB (@lem6151328 C) (@lem6151327 C op a)). Qed.
Lemma lem6151330 {C : Type'} (op : type1400 C) (a : C) : (term1167 C op a) = (term1196 C op a).
Proof. exact (TRANS (@lem6151306 C op a) (@lem6151329 C op a)). Qed.
Lemma lem6151331 {C : Type'} (op : type1400 C) : (term1169 C op) = (term1197 C op).
Proof. exact (fun_ext (fun a : C => @lem6151330 C op a)). Qed.
Lemma lem6151332 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151333 {C : Type'} (op : type1400 C) : (term1170 C op) = (term1198 C op).
Proof. exact (MK_COMB (@lem6151332 C) (@lem6151331 C op)). Qed.
Lemma lem6151334 {C : Type'} (op : type1400 C) : (term1152 C op) = (term1198 C op).
Proof. exact (TRANS (@lem6151286 C op) (@lem6151333 C op)). Qed.
Lemma lem6151335 {C : Type'} (op : type1400 C) : (term1021 C op) = (term1198 C op).
Proof. exact (TRANS (@lem6151259 C op) (@lem6151334 C op)). Qed.
Lemma lem6151336 {C : Type'} (op : type1400 C) : (term1029 C op) = (term1029 C op).
Proof. exact (eq_refl (term1029 C op)). Qed.
Lemma lem6151337 {C : Type'} (op : type1400 C) : (term1030 C op) = (term1199 C op).
Proof. exact (MK_COMB (@lem6151336 C op) (@lem6151335 C op)). Qed.
Lemma lem6151339 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6151340 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6151339 C P Q). Qed.
Lemma lem6151341 {C : Type'} (op : type1400 C) : (term1200 C op) = (term1201 C op).
Proof. exact (@lem6151340 C (term1027 C op) (term1197 C op)). Qed.
Lemma lem6151342 {C : Type'} (op : type1400 C) (a : C) : (term1202 C op a) = ((term1024 C op a) = a).
Proof. exact (eq_refl (term1202 C op a)). Qed.
Lemma lem6151343 {C : Type'} (op : type1400 C) : (term1203 C op) = (term1027 C op).
Proof. exact (fun_ext (fun a : C => @lem6151342 C op a)). Qed.
Lemma lem6151344 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151345 {C : Type'} (op : type1400 C) : (term1204 C op) = (term1028 C op).
Proof. exact (MK_COMB (@lem6151344 C) (@lem6151343 C op)). Qed.
Lemma lem6151346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151347 {C : Type'} (op : type1400 C) : (term1205 C op) = (term1029 C op).
Proof. exact (MK_COMB (@lem6151346) (@lem6151345 C op)). Qed.
Lemma lem6151348 {C : Type'} (op : type1400 C) (a : C) : (term1206 C op a) = (term1196 C op a).
Proof. exact (eq_refl (term1206 C op a)). Qed.
Lemma lem6151349 {C : Type'} (op : type1400 C) : (term1207 C op) = (term1197 C op).
Proof. exact (fun_ext (fun a : C => @lem6151348 C op a)). Qed.
Lemma lem6151350 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151351 {C : Type'} (op : type1400 C) : (term1208 C op) = (term1198 C op).
Proof. exact (MK_COMB (@lem6151350 C) (@lem6151349 C op)). Qed.
Lemma lem6151352 {C : Type'} (op : type1400 C) : (term1200 C op) = (term1199 C op).
Proof. exact (MK_COMB (@lem6151347 C op) (@lem6151351 C op)). Qed.
Lemma lem6151353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151354 {C : Type'} (op : type1400 C) : (term1209 C op) = (term1210 C op).
Proof. exact (MK_COMB (@lem6151353) (@lem6151352 C op)). Qed.
Lemma lem6151355 {C : Type'} (op : type1400 C) (a : C) : (term1202 C op a) = ((term1024 C op a) = a).
Proof. exact (eq_refl (term1202 C op a)). Qed.
Lemma lem6151356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6151357 {C : Type'} (op : type1400 C) (a : C) : (term1211 C op a) = (term1212 C op a).
Proof. exact (MK_COMB (@lem6151356) (@lem6151355 C op a)). Qed.
Lemma lem6151358 {C : Type'} (op : type1400 C) (a : C) : (term1206 C op a) = (term1196 C op a).
Proof. exact (eq_refl (term1206 C op a)). Qed.
Lemma lem6151359 {C : Type'} (op : type1400 C) (a : C) : (term1213 C op a) = (term1214 C op a).
Proof. exact (MK_COMB (@lem6151357 C op a) (@lem6151358 C op a)). Qed.
Lemma lem6151360 {C : Type'} (op : type1400 C) : (term1215 C op) = (term1216 C op).
Proof. exact (fun_ext (fun a : C => @lem6151359 C op a)). Qed.
Lemma lem6151361 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151362 {C : Type'} (op : type1400 C) : (term1201 C op) = (term1217 C op).
Proof. exact (MK_COMB (@lem6151361 C) (@lem6151360 C op)). Qed.
Lemma lem6151363 {C : Type'} (op : type1400 C) : ((term1200 C op) = (term1201 C op)) = ((term1199 C op) = (term1217 C op)).
Proof. exact (MK_COMB (@lem6151354 C op) (@lem6151362 C op)). Qed.
Lemma lem6151364 {C : Type'} (op : type1400 C) : (term1199 C op) = (term1217 C op).
Proof. exact (EQ_MP (@lem6151363 C op) (@lem6151341 C op)). Qed.
Lemma lem6151366 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6151367 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6151366 C P Q). Qed.
Lemma lem6151368 {C : Type'} (op : type1400 C) (a : C) : (term1218 C op a) = (term1219 C op a).
Proof. exact (@lem6151367 C ((term1024 C op a) = a) (term1195 C op a)). Qed.
Lemma lem6151369 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1220 C op a b) = (term1194 C b op a).
Proof. exact (eq_refl (term1220 C op a b)). Qed.
Lemma lem6151370 {C : Type'} (op : type1400 C) (a : C) : (term1221 C op a) = (term1195 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151369 C b op a)). Qed.
Lemma lem6151371 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151372 {C : Type'} (op : type1400 C) (a : C) : (term1222 C op a) = (term1196 C op a).
Proof. exact (MK_COMB (@lem6151371 C) (@lem6151370 C op a)). Qed.
Lemma lem6151373 {C : Type'} (op : type1400 C) (a : C) : (term1212 C op a) = (term1212 C op a).
Proof. exact (eq_refl (term1212 C op a)). Qed.
Lemma lem6151374 {C : Type'} (op : type1400 C) (a : C) : (term1218 C op a) = (term1214 C op a).
Proof. exact (MK_COMB (@lem6151373 C op a) (@lem6151372 C op a)). Qed.
Lemma lem6151375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151376 {C : Type'} (op : type1400 C) (a : C) : (term1223 C op a) = (term1224 C op a).
Proof. exact (MK_COMB (@lem6151375) (@lem6151374 C op a)). Qed.
Lemma lem6151377 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1220 C op a b) = (term1194 C b op a).
Proof. exact (eq_refl (term1220 C op a b)). Qed.
Lemma lem6151378 {C : Type'} (op : type1400 C) (a : C) : (term1212 C op a) = (term1212 C op a).
Proof. exact (eq_refl (term1212 C op a)). Qed.
Lemma lem6151379 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1225 C op a b) = (term1226 C b op a).
Proof. exact (MK_COMB (@lem6151378 C op a) (@lem6151377 C b op a)). Qed.
Lemma lem6151380 {C : Type'} (op : type1400 C) (a : C) : (term1227 C op a) = (term1228 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151379 C b op a)). Qed.
Lemma lem6151381 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151382 {C : Type'} (op : type1400 C) (a : C) : (term1219 C op a) = (term1229 C op a).
Proof. exact (MK_COMB (@lem6151381 C) (@lem6151380 C op a)). Qed.
Lemma lem6151383 {C : Type'} (op : type1400 C) (a : C) : ((term1218 C op a) = (term1219 C op a)) = ((term1214 C op a) = (term1229 C op a)).
Proof. exact (MK_COMB (@lem6151376 C op a) (@lem6151382 C op a)). Qed.
Lemma lem6151384 {C : Type'} (op : type1400 C) (a : C) : (term1214 C op a) = (term1229 C op a).
Proof. exact (EQ_MP (@lem6151383 C op a) (@lem6151368 C op a)). Qed.
Lemma lem6151386 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6151387 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6151386 C P Q). Qed.
Lemma lem6151388 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1230 C b op a) = (term1231 C b op a).
Proof. exact (@lem6151387 C ((term1024 C op a) = a) (term1193 C b op a)). Qed.
Lemma lem6151389 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1232 C b op a c) = (term1191 C b op a c).
Proof. exact (eq_refl (term1232 C b op a c)). Qed.
Lemma lem6151390 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1233 C b op a) = (term1193 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151389 C b op a c)). Qed.
Lemma lem6151391 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151392 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1234 C b op a) = (term1194 C b op a).
Proof. exact (MK_COMB (@lem6151391 C) (@lem6151390 C b op a)). Qed.
Lemma lem6151393 {C : Type'} (op : type1400 C) (a : C) : (term1212 C op a) = (term1212 C op a).
Proof. exact (eq_refl (term1212 C op a)). Qed.
Lemma lem6151394 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1230 C b op a) = (term1226 C b op a).
Proof. exact (MK_COMB (@lem6151393 C op a) (@lem6151392 C b op a)). Qed.
Lemma lem6151395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151396 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1235 C b op a) = (term1236 C b op a).
Proof. exact (MK_COMB (@lem6151395) (@lem6151394 C b op a)). Qed.
Lemma lem6151397 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1232 C b op a c) = (term1191 C b op a c).
Proof. exact (eq_refl (term1232 C b op a c)). Qed.
Lemma lem6151398 {C : Type'} (op : type1400 C) (a : C) : (term1212 C op a) = (term1212 C op a).
Proof. exact (eq_refl (term1212 C op a)). Qed.
Lemma lem6151399 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1237 C b op a c) = (term1238 C b op a c).
Proof. exact (MK_COMB (@lem6151398 C op a) (@lem6151397 C b op a c)). Qed.
Lemma lem6151400 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1239 C b op a) = (term1240 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151399 C b op a c)). Qed.
Lemma lem6151401 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151402 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1231 C b op a) = (term1241 C b op a).
Proof. exact (MK_COMB (@lem6151401 C) (@lem6151400 C b op a)). Qed.
Lemma lem6151403 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1230 C b op a) = (term1231 C b op a)) = ((term1226 C b op a) = (term1241 C b op a)).
Proof. exact (MK_COMB (@lem6151396 C b op a) (@lem6151402 C b op a)). Qed.
Lemma lem6151404 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1226 C b op a) = (term1241 C b op a).
Proof. exact (EQ_MP (@lem6151403 C b op a) (@lem6151388 C b op a)). Qed.
Lemma lem6151405 {C : Type'} (op : type1400 C) (a : C) : (term1228 C op a) = (term1242 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151404 C b op a)). Qed.
Lemma lem6151406 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151407 {C : Type'} (op : type1400 C) (a : C) : (term1229 C op a) = (term1243 C op a).
Proof. exact (MK_COMB (@lem6151406 C) (@lem6151405 C op a)). Qed.
Lemma lem6151408 {C : Type'} (op : type1400 C) (a : C) : (term1214 C op a) = (term1243 C op a).
Proof. exact (TRANS (@lem6151384 C op a) (@lem6151407 C op a)). Qed.
Lemma lem6151409 {C : Type'} (op : type1400 C) : (term1216 C op) = (term1244 C op).
Proof. exact (fun_ext (fun a : C => @lem6151408 C op a)). Qed.
Lemma lem6151410 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151411 {C : Type'} (op : type1400 C) : (term1217 C op) = (term1245 C op).
Proof. exact (MK_COMB (@lem6151410 C) (@lem6151409 C op)). Qed.
Lemma lem6151412 {C : Type'} (op : type1400 C) : (term1199 C op) = (term1245 C op).
Proof. exact (TRANS (@lem6151364 C op) (@lem6151411 C op)). Qed.
Lemma lem6151413 {C : Type'} (op : type1400 C) : (term1030 C op) = (term1245 C op).
Proof. exact (TRANS (@lem6151337 C op) (@lem6151412 C op)). Qed.
Lemma lem6151414 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6151415 {C : Type'} (op : type1400 C) : (term1034 C op) = (term1246 C op).
Proof. exact (MK_COMB (@lem6151414 C op) (@lem6151413 C op)). Qed.
Lemma lem6151417 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1247 A P Q) = (term1248 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6151418 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1247 C P Q) = (term1248 C P Q).
Proof. exact (@lem6151417 C P Q). Qed.
Lemma lem6151419 {C : Type'} (op : type1400 C) : (term1249 C op) = (term1250 C op).
Proof. exact (@lem6151418 C (term1032 C op) (term1244 C op)). Qed.
Lemma lem6151420 {C : Type'} (op : type1400 C) (a : C) : (term1251 C op a) = (term1243 C op a).
Proof. exact (eq_refl (term1251 C op a)). Qed.
Lemma lem6151421 {C : Type'} (op : type1400 C) : (term1252 C op) = (term1244 C op).
Proof. exact (fun_ext (fun a : C => @lem6151420 C op a)). Qed.
Lemma lem6151422 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151423 {C : Type'} (op : type1400 C) : (term1253 C op) = (term1245 C op).
Proof. exact (MK_COMB (@lem6151422 C) (@lem6151421 C op)). Qed.
Lemma lem6151424 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6151425 {C : Type'} (op : type1400 C) : (term1249 C op) = (term1246 C op).
Proof. exact (MK_COMB (@lem6151424 C op) (@lem6151423 C op)). Qed.
Lemma lem6151426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151427 {C : Type'} (op : type1400 C) : (term1254 C op) = (term1255 C op).
Proof. exact (MK_COMB (@lem6151426) (@lem6151425 C op)). Qed.
Lemma lem6151428 {C : Type'} (op : type1400 C) (a : C) : (term1251 C op a) = (term1243 C op a).
Proof. exact (eq_refl (term1251 C op a)). Qed.
Lemma lem6151429 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6151430 {C : Type'} (op : type1400 C) (a : C) : (term1256 C op a) = (term1257 C op a).
Proof. exact (MK_COMB (@lem6151429 C op) (@lem6151428 C op a)). Qed.
Lemma lem6151431 {C : Type'} (op : type1400 C) : (term1258 C op) = (term1259 C op).
Proof. exact (fun_ext (fun a : C => @lem6151430 C op a)). Qed.
Lemma lem6151432 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151433 {C : Type'} (op : type1400 C) : (term1250 C op) = (term1260 C op).
Proof. exact (MK_COMB (@lem6151432 C) (@lem6151431 C op)). Qed.
Lemma lem6151434 {C : Type'} (op : type1400 C) : ((term1249 C op) = (term1250 C op)) = ((term1246 C op) = (term1260 C op)).
Proof. exact (MK_COMB (@lem6151427 C op) (@lem6151433 C op)). Qed.
Lemma lem6151435 {C : Type'} (op : type1400 C) : (term1246 C op) = (term1260 C op).
Proof. exact (EQ_MP (@lem6151434 C op) (@lem6151419 C op)). Qed.
Lemma lem6151437 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1247 A P Q) = (term1248 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6151438 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1247 C P Q) = (term1248 C P Q).
Proof. exact (@lem6151437 C P Q). Qed.
Lemma lem6151439 {C : Type'} (op : type1400 C) (a : C) : (term1261 C op a) = (term1262 C op a).
Proof. exact (@lem6151438 C (term1032 C op) (term1242 C op a)). Qed.
Lemma lem6151440 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1263 C op a b) = (term1241 C b op a).
Proof. exact (eq_refl (term1263 C op a b)). Qed.
Lemma lem6151441 {C : Type'} (op : type1400 C) (a : C) : (term1264 C op a) = (term1242 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151440 C b op a)). Qed.
Lemma lem6151442 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151443 {C : Type'} (op : type1400 C) (a : C) : (term1265 C op a) = (term1243 C op a).
Proof. exact (MK_COMB (@lem6151442 C) (@lem6151441 C op a)). Qed.
Lemma lem6151444 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6151445 {C : Type'} (op : type1400 C) (a : C) : (term1261 C op a) = (term1257 C op a).
Proof. exact (MK_COMB (@lem6151444 C op) (@lem6151443 C op a)). Qed.
Lemma lem6151446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151447 {C : Type'} (op : type1400 C) (a : C) : (term1266 C op a) = (term1267 C op a).
Proof. exact (MK_COMB (@lem6151446) (@lem6151445 C op a)). Qed.
Lemma lem6151448 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1263 C op a b) = (term1241 C b op a).
Proof. exact (eq_refl (term1263 C op a b)). Qed.
Lemma lem6151449 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6151450 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1268 C op a b) = (term1269 C b op a).
Proof. exact (MK_COMB (@lem6151449 C op) (@lem6151448 C b op a)). Qed.
Lemma lem6151451 {C : Type'} (op : type1400 C) (a : C) : (term1270 C op a) = (term1271 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151450 C b op a)). Qed.
Lemma lem6151452 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151453 {C : Type'} (op : type1400 C) (a : C) : (term1262 C op a) = (term1272 C op a).
Proof. exact (MK_COMB (@lem6151452 C) (@lem6151451 C op a)). Qed.
Lemma lem6151454 {C : Type'} (op : type1400 C) (a : C) : ((term1261 C op a) = (term1262 C op a)) = ((term1257 C op a) = (term1272 C op a)).
Proof. exact (MK_COMB (@lem6151447 C op a) (@lem6151453 C op a)). Qed.
Lemma lem6151455 {C : Type'} (op : type1400 C) (a : C) : (term1257 C op a) = (term1272 C op a).
Proof. exact (EQ_MP (@lem6151454 C op a) (@lem6151439 C op a)). Qed.
Lemma lem6151457 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1247 A P Q) = (term1248 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6151458 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1247 C P Q) = (term1248 C P Q).
Proof. exact (@lem6151457 C P Q). Qed.
Lemma lem6151459 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1273 C b op a) = (term1274 C b op a).
Proof. exact (@lem6151458 C (term1032 C op) (term1240 C b op a)). Qed.
Lemma lem6151460 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1275 C b op a c) = (term1238 C b op a c).
Proof. exact (eq_refl (term1275 C b op a c)). Qed.
Lemma lem6151461 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1276 C b op a) = (term1240 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151460 C b op a c)). Qed.
Lemma lem6151462 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151463 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1277 C b op a) = (term1241 C b op a).
Proof. exact (MK_COMB (@lem6151462 C) (@lem6151461 C b op a)). Qed.
Lemma lem6151464 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6151465 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1273 C b op a) = (term1269 C b op a).
Proof. exact (MK_COMB (@lem6151464 C op) (@lem6151463 C b op a)). Qed.
Lemma lem6151466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6151467 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1278 C b op a) = (term1279 C b op a).
Proof. exact (MK_COMB (@lem6151466) (@lem6151465 C b op a)). Qed.
Lemma lem6151468 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1275 C b op a c) = (term1238 C b op a c).
Proof. exact (eq_refl (term1275 C b op a c)). Qed.
Lemma lem6151469 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6151470 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1280 C b op a c) = (term1281 C b op a c).
Proof. exact (MK_COMB (@lem6151469 C op) (@lem6151468 C b op a c)). Qed.
Lemma lem6151471 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1282 C b op a) = (term1283 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151470 C b op a c)). Qed.
Lemma lem6151472 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151473 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1274 C b op a) = (term1284 C b op a).
Proof. exact (MK_COMB (@lem6151472 C) (@lem6151471 C b op a)). Qed.
Lemma lem6151474 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1273 C b op a) = (term1274 C b op a)) = ((term1269 C b op a) = (term1284 C b op a)).
Proof. exact (MK_COMB (@lem6151467 C b op a) (@lem6151473 C b op a)). Qed.
Lemma lem6151475 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1269 C b op a) = (term1284 C b op a).
Proof. exact (EQ_MP (@lem6151474 C b op a) (@lem6151459 C b op a)). Qed.
Lemma lem6151476 {C : Type'} (op : type1400 C) (a : C) : (term1271 C op a) = (term1285 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151475 C b op a)). Qed.
Lemma lem6151477 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151478 {C : Type'} (op : type1400 C) (a : C) : (term1272 C op a) = (term1286 C op a).
Proof. exact (MK_COMB (@lem6151477 C) (@lem6151476 C op a)). Qed.
Lemma lem6151479 {C : Type'} (op : type1400 C) (a : C) : (term1257 C op a) = (term1286 C op a).
Proof. exact (TRANS (@lem6151455 C op a) (@lem6151478 C op a)). Qed.
Lemma lem6151480 {C : Type'} (op : type1400 C) : (term1259 C op) = (term1287 C op).
Proof. exact (fun_ext (fun a : C => @lem6151479 C op a)). Qed.
Lemma lem6151481 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151482 {C : Type'} (op : type1400 C) : (term1260 C op) = (term1288 C op).
Proof. exact (MK_COMB (@lem6151481 C) (@lem6151480 C op)). Qed.
Lemma lem6151483 {C : Type'} (op : type1400 C) : (term1246 C op) = (term1288 C op).
Proof. exact (TRANS (@lem6151435 C op) (@lem6151482 C op)). Qed.
Lemma lem6151484 {C : Type'} (op : type1400 C) : (term1034 C op) = (term1288 C op).
Proof. exact (TRANS (@lem6151415 C op) (@lem6151483 C op)). Qed.
Lemma lem6151485 {C : Type'} : (term1035 C) = (term1289 C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6151484 C op)). Qed.
Lemma lem6151486 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6151487 {C : Type'} : (term1036 C) = (term1290 C).
Proof. exact (MK_COMB (@lem6151486 C) (@lem6151485 C)). Qed.
Lemma lem6151509 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1281 C b op a c) = (term1291 C b op a c).
Proof. exact (@lem19490 ((term1024 C op a) = a) (term1032 C op) (term1191 C b op a c)). Qed.
Lemma lem6151510 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1292 C b op a c) = (term1293 C b op a c).
Proof. exact (@lem19490 ((term1015 C a op) = a) (term1032 C op) (term1144 C b op a c)). Qed.
Lemma lem6151511 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1294 C b op a c) = (term1295 C b op a c).
Proof. exact (@lem19490 ((term977 C op a b) = (term977 C op b a)) (term1032 C op) (term1089 C b op a c)). Qed.
Lemma lem6151518 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1296 C b op a c) = (term1297 C b op a c).
Proof. exact (@lem19490 ((term994 C op a b c) = (term980 C a op b c)) (term1032 C op) ((term980 C a op b c) = (term980 C b op a c))). Qed.
Lemma lem6151521 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1298 C op b a) = (term1298 C op b a).
Proof. exact (eq_refl (term1298 C op b a)). Qed.
Lemma lem6151522 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1295 C b op a c) = (term1299 C b op a c).
Proof. exact (MK_COMB (@lem6151521 C op b a) (@lem6151518 C b op a c)). Qed.
Lemma lem6151523 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1294 C b op a c) = (term1299 C b op a c).
Proof. exact (TRANS (@lem6151511 C b op a c) (@lem6151522 C b op a c)). Qed.
Lemma lem6151526 {C : Type'} (op : type1400 C) (a : C) : (term1300 C op a) = (term1300 C op a).
Proof. exact (eq_refl (term1300 C op a)). Qed.
Lemma lem6151527 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1293 C b op a c) = (term1301 C b op a c).
Proof. exact (MK_COMB (@lem6151526 C op a) (@lem6151523 C b op a c)). Qed.
Lemma lem6151528 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1292 C b op a c) = (term1301 C b op a c).
Proof. exact (TRANS (@lem6151510 C b op a c) (@lem6151527 C b op a c)). Qed.
Lemma lem6151531 {C : Type'} (op : type1400 C) (a : C) : (term1302 C op a) = (term1302 C op a).
Proof. exact (eq_refl (term1302 C op a)). Qed.
Lemma lem6151532 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1291 C b op a c) = (term1303 C b op a c).
Proof. exact (MK_COMB (@lem6151531 C op a) (@lem6151528 C b op a c)). Qed.
Lemma lem6151534 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1281 C b op a c) = (term1303 C b op a c).
Proof. exact (TRANS (@lem6151509 C b op a c) (@lem6151532 C b op a c)). Qed.
Lemma lem6151535 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1283 C b op a) = (term1304 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6151534 C b op a c)). Qed.
Lemma lem6151536 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151537 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1284 C b op a) = (term1305 C b op a).
Proof. exact (MK_COMB (@lem6151536 C) (@lem6151535 C b op a)). Qed.
Lemma lem6151538 {C : Type'} (op : type1400 C) (a : C) : (term1285 C op a) = (term1306 C op a).
Proof. exact (fun_ext (fun b : C => @lem6151537 C b op a)). Qed.
Lemma lem6151539 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151540 {C : Type'} (op : type1400 C) (a : C) : (term1286 C op a) = (term1307 C op a).
Proof. exact (MK_COMB (@lem6151539 C) (@lem6151538 C op a)). Qed.
Lemma lem6151541 {C : Type'} (op : type1400 C) : (term1287 C op) = (term1308 C op).
Proof. exact (fun_ext (fun a : C => @lem6151540 C op a)). Qed.
Lemma lem6151542 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6151543 {C : Type'} (op : type1400 C) : (term1288 C op) = (term1309 C op).
Proof. exact (MK_COMB (@lem6151542 C) (@lem6151541 C op)). Qed.
Lemma lem6151544 {C : Type'} : (term1289 C) = (term1310 C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6151543 C op)). Qed.
Lemma lem6151545 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6151546 {C : Type'} : (term1290 C) = (term1311 C).
Proof. exact (MK_COMB (@lem6151545 C) (@lem6151544 C)). Qed.
Lemma lem6151547 {C : Type'} : (term1036 C) = (term1311 C).
Proof. exact (TRANS (@lem6151487 C) (@lem6151546 C)). Qed.
Lemma lem6151548 {C : Type'} (h1 : term603 C) : term1311 C.
Proof. exact (EQ_MP (@lem6151547 C) (@lem6149811 C h1)). Qed.
Lemma lem6152608 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6152609 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6152608 C P Q). Qed.
Lemma lem6152610 {C : Type'} (op : type1400 C) : (term1039 C op) = (term1040 C op).
Proof. exact (@lem6152609 C (term1001 C op) (term987 C op)). Qed.
Lemma lem6152611 {C : Type'} (a : C) (op : type1400 C) : (term1041 C op a) = (term1000 C a op).
Proof. exact (eq_refl (term1041 C op a)). Qed.
Lemma lem6152612 {C : Type'} (op : type1400 C) : (term1042 C op) = (term1001 C op).
Proof. exact (fun_ext (fun a : C => @lem6152611 C a op)). Qed.
Lemma lem6152613 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152614 {C : Type'} (op : type1400 C) : (term1043 C op) = (term1002 C op).
Proof. exact (MK_COMB (@lem6152613 C) (@lem6152612 C op)). Qed.
Lemma lem6152615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152616 {C : Type'} (op : type1400 C) : (term1044 C op) = (term1003 C op).
Proof. exact (MK_COMB (@lem6152615) (@lem6152614 C op)). Qed.
Lemma lem6152617 {C : Type'} (op : type1400 C) (a : C) : (term1045 C op a) = (term986 C op a).
Proof. exact (eq_refl (term1045 C op a)). Qed.
Lemma lem6152618 {C : Type'} (op : type1400 C) : (term1046 C op) = (term987 C op).
Proof. exact (fun_ext (fun a : C => @lem6152617 C op a)). Qed.
Lemma lem6152619 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152620 {C : Type'} (op : type1400 C) : (term1047 C op) = (term988 C op).
Proof. exact (MK_COMB (@lem6152619 C) (@lem6152618 C op)). Qed.
Lemma lem6152621 {C : Type'} (op : type1400 C) : (term1039 C op) = (term1004 C op).
Proof. exact (MK_COMB (@lem6152616 C op) (@lem6152620 C op)). Qed.
Lemma lem6152622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152623 {C : Type'} (op : type1400 C) : (term1048 C op) = (term1049 C op).
Proof. exact (MK_COMB (@lem6152622) (@lem6152621 C op)). Qed.
Lemma lem6152624 {C : Type'} (a : C) (op : type1400 C) : (term1041 C op a) = (term1000 C a op).
Proof. exact (eq_refl (term1041 C op a)). Qed.
Lemma lem6152625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152626 {C : Type'} (a : C) (op : type1400 C) : (term1050 C op a) = (term1051 C a op).
Proof. exact (MK_COMB (@lem6152625) (@lem6152624 C a op)). Qed.
Lemma lem6152627 {C : Type'} (op : type1400 C) (a : C) : (term1045 C op a) = (term986 C op a).
Proof. exact (eq_refl (term1045 C op a)). Qed.
Lemma lem6152628 {C : Type'} (op : type1400 C) (a : C) : (term1052 C op a) = (term1053 C op a).
Proof. exact (MK_COMB (@lem6152626 C a op) (@lem6152627 C op a)). Qed.
Lemma lem6152629 {C : Type'} (op : type1400 C) : (term1054 C op) = (term1055 C op).
Proof. exact (fun_ext (fun a : C => @lem6152628 C op a)). Qed.
Lemma lem6152630 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152631 {C : Type'} (op : type1400 C) : (term1040 C op) = (term1056 C op).
Proof. exact (MK_COMB (@lem6152630 C) (@lem6152629 C op)). Qed.
Lemma lem6152632 {C : Type'} (op : type1400 C) : ((term1039 C op) = (term1040 C op)) = ((term1004 C op) = (term1056 C op)).
Proof. exact (MK_COMB (@lem6152623 C op) (@lem6152631 C op)). Qed.
Lemma lem6152633 {C : Type'} (op : type1400 C) : (term1004 C op) = (term1056 C op).
Proof. exact (EQ_MP (@lem6152632 C op) (@lem6152610 C op)). Qed.
Lemma lem6152635 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6152636 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6152635 C P Q). Qed.
Lemma lem6152637 {C : Type'} (op : type1400 C) (a : C) : (term1057 C op a) = (term1058 C op a).
Proof. exact (@lem6152636 C (term999 C a op) (term985 C op a)). Qed.
Lemma lem6152638 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1059 C a op b) = (term998 C a op b).
Proof. exact (eq_refl (term1059 C a op b)). Qed.
Lemma lem6152639 {C : Type'} (a : C) (op : type1400 C) : (term1060 C a op) = (term999 C a op).
Proof. exact (fun_ext (fun b : C => @lem6152638 C a op b)). Qed.
Lemma lem6152640 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152641 {C : Type'} (a : C) (op : type1400 C) : (term1061 C a op) = (term1000 C a op).
Proof. exact (MK_COMB (@lem6152640 C) (@lem6152639 C a op)). Qed.
Lemma lem6152642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152643 {C : Type'} (a : C) (op : type1400 C) : (term1062 C a op) = (term1051 C a op).
Proof. exact (MK_COMB (@lem6152642) (@lem6152641 C a op)). Qed.
Lemma lem6152644 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1063 C op a b) = (term984 C b op a).
Proof. exact (eq_refl (term1063 C op a b)). Qed.
Lemma lem6152645 {C : Type'} (op : type1400 C) (a : C) : (term1064 C op a) = (term985 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152644 C b op a)). Qed.
Lemma lem6152646 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152647 {C : Type'} (op : type1400 C) (a : C) : (term1065 C op a) = (term986 C op a).
Proof. exact (MK_COMB (@lem6152646 C) (@lem6152645 C op a)). Qed.
Lemma lem6152648 {C : Type'} (op : type1400 C) (a : C) : (term1057 C op a) = (term1053 C op a).
Proof. exact (MK_COMB (@lem6152643 C a op) (@lem6152647 C op a)). Qed.
Lemma lem6152649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152650 {C : Type'} (op : type1400 C) (a : C) : (term1066 C op a) = (term1067 C op a).
Proof. exact (MK_COMB (@lem6152649) (@lem6152648 C op a)). Qed.
Lemma lem6152651 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1059 C a op b) = (term998 C a op b).
Proof. exact (eq_refl (term1059 C a op b)). Qed.
Lemma lem6152652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152653 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1068 C a op b) = (term1069 C a op b).
Proof. exact (MK_COMB (@lem6152652) (@lem6152651 C a op b)). Qed.
Lemma lem6152654 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1063 C op a b) = (term984 C b op a).
Proof. exact (eq_refl (term1063 C op a b)). Qed.
Lemma lem6152655 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1070 C op a b) = (term1071 C b op a).
Proof. exact (MK_COMB (@lem6152653 C a op b) (@lem6152654 C b op a)). Qed.
Lemma lem6152656 {C : Type'} (op : type1400 C) (a : C) : (term1072 C op a) = (term1073 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152655 C b op a)). Qed.
Lemma lem6152657 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152658 {C : Type'} (op : type1400 C) (a : C) : (term1058 C op a) = (term1074 C op a).
Proof. exact (MK_COMB (@lem6152657 C) (@lem6152656 C op a)). Qed.
Lemma lem6152659 {C : Type'} (op : type1400 C) (a : C) : ((term1057 C op a) = (term1058 C op a)) = ((term1053 C op a) = (term1074 C op a)).
Proof. exact (MK_COMB (@lem6152650 C op a) (@lem6152658 C op a)). Qed.
Lemma lem6152660 {C : Type'} (op : type1400 C) (a : C) : (term1053 C op a) = (term1074 C op a).
Proof. exact (EQ_MP (@lem6152659 C op a) (@lem6152637 C op a)). Qed.
Lemma lem6152662 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6152663 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6152662 C P Q). Qed.
Lemma lem6152664 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1075 C b op a) = (term1076 C b op a).
Proof. exact (@lem6152663 C (term997 C a op b) (term983 C b op a)). Qed.
Lemma lem6152665 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term1077 C a op b c) = ((term994 C op a b c) = (term980 C a op b c)).
Proof. exact (eq_refl (term1077 C a op b c)). Qed.
Lemma lem6152666 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1078 C a op b) = (term997 C a op b).
Proof. exact (fun_ext (fun c : C => @lem6152665 C a op b c)). Qed.
Lemma lem6152667 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152668 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1079 C a op b) = (term998 C a op b).
Proof. exact (MK_COMB (@lem6152667 C) (@lem6152666 C a op b)). Qed.
Lemma lem6152669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152670 {C : Type'} (a : C) (op : type1400 C) (b : C) : (term1080 C a op b) = (term1069 C a op b).
Proof. exact (MK_COMB (@lem6152669) (@lem6152668 C a op b)). Qed.
Lemma lem6152671 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1081 C b op a c) = ((term980 C a op b c) = (term980 C b op a c)).
Proof. exact (eq_refl (term1081 C b op a c)). Qed.
Lemma lem6152672 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1082 C b op a) = (term983 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152671 C b op a c)). Qed.
Lemma lem6152673 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152674 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1083 C b op a) = (term984 C b op a).
Proof. exact (MK_COMB (@lem6152673 C) (@lem6152672 C b op a)). Qed.
Lemma lem6152675 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1075 C b op a) = (term1071 C b op a).
Proof. exact (MK_COMB (@lem6152670 C a op b) (@lem6152674 C b op a)). Qed.
Lemma lem6152676 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152677 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1084 C b op a) = (term1085 C b op a).
Proof. exact (MK_COMB (@lem6152676) (@lem6152675 C b op a)). Qed.
Lemma lem6152678 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term1077 C a op b c) = ((term994 C op a b c) = (term980 C a op b c)).
Proof. exact (eq_refl (term1077 C a op b c)). Qed.
Lemma lem6152679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152680 {C : Type'} (a : C) (op : type1400 C) (b : C) (c : C) : (term1086 C a op b c) = (term1087 C a op b c).
Proof. exact (MK_COMB (@lem6152679) (@lem6152678 C a op b c)). Qed.
Lemma lem6152681 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1081 C b op a c) = ((term980 C a op b c) = (term980 C b op a c)).
Proof. exact (eq_refl (term1081 C b op a c)). Qed.
Lemma lem6152682 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1088 C b op a c) = (term1089 C b op a c).
Proof. exact (MK_COMB (@lem6152680 C a op b c) (@lem6152681 C b op a c)). Qed.
Lemma lem6152683 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1090 C b op a) = (term1091 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152682 C b op a c)). Qed.
Lemma lem6152684 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152685 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1076 C b op a) = (term1092 C b op a).
Proof. exact (MK_COMB (@lem6152684 C) (@lem6152683 C b op a)). Qed.
Lemma lem6152686 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1075 C b op a) = (term1076 C b op a)) = ((term1071 C b op a) = (term1092 C b op a)).
Proof. exact (MK_COMB (@lem6152677 C b op a) (@lem6152685 C b op a)). Qed.
Lemma lem6152687 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1071 C b op a) = (term1092 C b op a).
Proof. exact (EQ_MP (@lem6152686 C b op a) (@lem6152664 C b op a)). Qed.
Lemma lem6152688 {C : Type'} (op : type1400 C) (a : C) : (term1073 C op a) = (term1093 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152687 C b op a)). Qed.
Lemma lem6152689 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152690 {C : Type'} (op : type1400 C) (a : C) : (term1074 C op a) = (term1094 C op a).
Proof. exact (MK_COMB (@lem6152689 C) (@lem6152688 C op a)). Qed.
Lemma lem6152691 {C : Type'} (op : type1400 C) (a : C) : (term1053 C op a) = (term1094 C op a).
Proof. exact (TRANS (@lem6152660 C op a) (@lem6152690 C op a)). Qed.
Lemma lem6152692 {C : Type'} (op : type1400 C) : (term1055 C op) = (term1095 C op).
Proof. exact (fun_ext (fun a : C => @lem6152691 C op a)). Qed.
Lemma lem6152693 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152694 {C : Type'} (op : type1400 C) : (term1056 C op) = (term1096 C op).
Proof. exact (MK_COMB (@lem6152693 C) (@lem6152692 C op)). Qed.
Lemma lem6152695 {C : Type'} (op : type1400 C) : (term1004 C op) = (term1096 C op).
Proof. exact (TRANS (@lem6152633 C op) (@lem6152694 C op)). Qed.
Lemma lem6152696 {C : Type'} (op : type1400 C) : (term1011 C op) = (term1011 C op).
Proof. exact (eq_refl (term1011 C op)). Qed.
Lemma lem6152697 {C : Type'} (op : type1400 C) : (term1012 C op) = (term1097 C op).
Proof. exact (MK_COMB (@lem6152696 C op) (@lem6152695 C op)). Qed.
Lemma lem6152699 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6152700 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6152699 C P Q). Qed.
Lemma lem6152701 {C : Type'} (op : type1400 C) : (term1098 C op) = (term1099 C op).
Proof. exact (@lem6152700 C (term1009 C op) (term1095 C op)). Qed.
Lemma lem6152702 {C : Type'} (op : type1400 C) (a : C) : (term1100 C op a) = (term1008 C op a).
Proof. exact (eq_refl (term1100 C op a)). Qed.
Lemma lem6152703 {C : Type'} (op : type1400 C) : (term1101 C op) = (term1009 C op).
Proof. exact (fun_ext (fun a : C => @lem6152702 C op a)). Qed.
Lemma lem6152704 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152705 {C : Type'} (op : type1400 C) : (term1102 C op) = (term1010 C op).
Proof. exact (MK_COMB (@lem6152704 C) (@lem6152703 C op)). Qed.
Lemma lem6152706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152707 {C : Type'} (op : type1400 C) : (term1103 C op) = (term1011 C op).
Proof. exact (MK_COMB (@lem6152706) (@lem6152705 C op)). Qed.
Lemma lem6152708 {C : Type'} (op : type1400 C) (a : C) : (term1104 C op a) = (term1094 C op a).
Proof. exact (eq_refl (term1104 C op a)). Qed.
Lemma lem6152709 {C : Type'} (op : type1400 C) : (term1105 C op) = (term1095 C op).
Proof. exact (fun_ext (fun a : C => @lem6152708 C op a)). Qed.
Lemma lem6152710 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152711 {C : Type'} (op : type1400 C) : (term1106 C op) = (term1096 C op).
Proof. exact (MK_COMB (@lem6152710 C) (@lem6152709 C op)). Qed.
Lemma lem6152712 {C : Type'} (op : type1400 C) : (term1098 C op) = (term1097 C op).
Proof. exact (MK_COMB (@lem6152707 C op) (@lem6152711 C op)). Qed.
Lemma lem6152713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152714 {C : Type'} (op : type1400 C) : (term1107 C op) = (term1108 C op).
Proof. exact (MK_COMB (@lem6152713) (@lem6152712 C op)). Qed.
Lemma lem6152715 {C : Type'} (op : type1400 C) (a : C) : (term1100 C op a) = (term1008 C op a).
Proof. exact (eq_refl (term1100 C op a)). Qed.
Lemma lem6152716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152717 {C : Type'} (op : type1400 C) (a : C) : (term1109 C op a) = (term1110 C op a).
Proof. exact (MK_COMB (@lem6152716) (@lem6152715 C op a)). Qed.
Lemma lem6152718 {C : Type'} (op : type1400 C) (a : C) : (term1104 C op a) = (term1094 C op a).
Proof. exact (eq_refl (term1104 C op a)). Qed.
Lemma lem6152719 {C : Type'} (op : type1400 C) (a : C) : (term1111 C op a) = (term1112 C op a).
Proof. exact (MK_COMB (@lem6152717 C op a) (@lem6152718 C op a)). Qed.
Lemma lem6152720 {C : Type'} (op : type1400 C) : (term1113 C op) = (term1114 C op).
Proof. exact (fun_ext (fun a : C => @lem6152719 C op a)). Qed.
Lemma lem6152721 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152722 {C : Type'} (op : type1400 C) : (term1099 C op) = (term1115 C op).
Proof. exact (MK_COMB (@lem6152721 C) (@lem6152720 C op)). Qed.
Lemma lem6152723 {C : Type'} (op : type1400 C) : ((term1098 C op) = (term1099 C op)) = ((term1097 C op) = (term1115 C op)).
Proof. exact (MK_COMB (@lem6152714 C op) (@lem6152722 C op)). Qed.
Lemma lem6152724 {C : Type'} (op : type1400 C) : (term1097 C op) = (term1115 C op).
Proof. exact (EQ_MP (@lem6152723 C op) (@lem6152701 C op)). Qed.
Lemma lem6152726 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6152727 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6152726 C P Q). Qed.
Lemma lem6152728 {C : Type'} (op : type1400 C) (a : C) : (term1116 C op a) = (term1117 C op a).
Proof. exact (@lem6152727 C (term1007 C op a) (term1093 C op a)). Qed.
Lemma lem6152729 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1118 C op a b) = ((term977 C op a b) = (term977 C op b a)).
Proof. exact (eq_refl (term1118 C op a b)). Qed.
Lemma lem6152730 {C : Type'} (op : type1400 C) (a : C) : (term1119 C op a) = (term1007 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152729 C op b a)). Qed.
Lemma lem6152731 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152732 {C : Type'} (op : type1400 C) (a : C) : (term1120 C op a) = (term1008 C op a).
Proof. exact (MK_COMB (@lem6152731 C) (@lem6152730 C op a)). Qed.
Lemma lem6152733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152734 {C : Type'} (op : type1400 C) (a : C) : (term1121 C op a) = (term1110 C op a).
Proof. exact (MK_COMB (@lem6152733) (@lem6152732 C op a)). Qed.
Lemma lem6152735 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1122 C op a b) = (term1092 C b op a).
Proof. exact (eq_refl (term1122 C op a b)). Qed.
Lemma lem6152736 {C : Type'} (op : type1400 C) (a : C) : (term1123 C op a) = (term1093 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152735 C b op a)). Qed.
Lemma lem6152737 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152738 {C : Type'} (op : type1400 C) (a : C) : (term1124 C op a) = (term1094 C op a).
Proof. exact (MK_COMB (@lem6152737 C) (@lem6152736 C op a)). Qed.
Lemma lem6152739 {C : Type'} (op : type1400 C) (a : C) : (term1116 C op a) = (term1112 C op a).
Proof. exact (MK_COMB (@lem6152734 C op a) (@lem6152738 C op a)). Qed.
Lemma lem6152740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152741 {C : Type'} (op : type1400 C) (a : C) : (term1125 C op a) = (term1126 C op a).
Proof. exact (MK_COMB (@lem6152740) (@lem6152739 C op a)). Qed.
Lemma lem6152742 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1118 C op a b) = ((term977 C op a b) = (term977 C op b a)).
Proof. exact (eq_refl (term1118 C op a b)). Qed.
Lemma lem6152743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152744 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1127 C op a b) = (term1128 C op b a).
Proof. exact (MK_COMB (@lem6152743) (@lem6152742 C op b a)). Qed.
Lemma lem6152745 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1122 C op a b) = (term1092 C b op a).
Proof. exact (eq_refl (term1122 C op a b)). Qed.
Lemma lem6152746 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1129 C op a b) = (term1130 C b op a).
Proof. exact (MK_COMB (@lem6152744 C op b a) (@lem6152745 C b op a)). Qed.
Lemma lem6152747 {C : Type'} (op : type1400 C) (a : C) : (term1131 C op a) = (term1132 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152746 C b op a)). Qed.
Lemma lem6152748 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152749 {C : Type'} (op : type1400 C) (a : C) : (term1117 C op a) = (term1133 C op a).
Proof. exact (MK_COMB (@lem6152748 C) (@lem6152747 C op a)). Qed.
Lemma lem6152750 {C : Type'} (op : type1400 C) (a : C) : ((term1116 C op a) = (term1117 C op a)) = ((term1112 C op a) = (term1133 C op a)).
Proof. exact (MK_COMB (@lem6152741 C op a) (@lem6152749 C op a)). Qed.
Lemma lem6152751 {C : Type'} (op : type1400 C) (a : C) : (term1112 C op a) = (term1133 C op a).
Proof. exact (EQ_MP (@lem6152750 C op a) (@lem6152728 C op a)). Qed.
Lemma lem6152753 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6152754 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6152753 C P Q). Qed.
Lemma lem6152755 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1136 C b op a) = (term1137 C b op a).
Proof. exact (@lem6152754 C ((term977 C op a b) = (term977 C op b a)) (term1091 C b op a)). Qed.
Lemma lem6152756 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1138 C b op a c) = (term1089 C b op a c).
Proof. exact (eq_refl (term1138 C b op a c)). Qed.
Lemma lem6152757 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1139 C b op a) = (term1091 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152756 C b op a c)). Qed.
Lemma lem6152758 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152759 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1140 C b op a) = (term1092 C b op a).
Proof. exact (MK_COMB (@lem6152758 C) (@lem6152757 C b op a)). Qed.
Lemma lem6152760 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1128 C op b a) = (term1128 C op b a).
Proof. exact (eq_refl (term1128 C op b a)). Qed.
Lemma lem6152761 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1136 C b op a) = (term1130 C b op a).
Proof. exact (MK_COMB (@lem6152760 C op b a) (@lem6152759 C b op a)). Qed.
Lemma lem6152762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152763 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1141 C b op a) = (term1142 C b op a).
Proof. exact (MK_COMB (@lem6152762) (@lem6152761 C b op a)). Qed.
Lemma lem6152764 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1138 C b op a c) = (term1089 C b op a c).
Proof. exact (eq_refl (term1138 C b op a c)). Qed.
Lemma lem6152765 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1128 C op b a) = (term1128 C op b a).
Proof. exact (eq_refl (term1128 C op b a)). Qed.
Lemma lem6152766 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1143 C b op a c) = (term1144 C b op a c).
Proof. exact (MK_COMB (@lem6152765 C op b a) (@lem6152764 C b op a c)). Qed.
Lemma lem6152767 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1145 C b op a) = (term1146 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152766 C b op a c)). Qed.
Lemma lem6152768 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152769 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1137 C b op a) = (term1147 C b op a).
Proof. exact (MK_COMB (@lem6152768 C) (@lem6152767 C b op a)). Qed.
Lemma lem6152770 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1136 C b op a) = (term1137 C b op a)) = ((term1130 C b op a) = (term1147 C b op a)).
Proof. exact (MK_COMB (@lem6152763 C b op a) (@lem6152769 C b op a)). Qed.
Lemma lem6152771 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1130 C b op a) = (term1147 C b op a).
Proof. exact (EQ_MP (@lem6152770 C b op a) (@lem6152755 C b op a)). Qed.
Lemma lem6152772 {C : Type'} (op : type1400 C) (a : C) : (term1132 C op a) = (term1148 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152771 C b op a)). Qed.
Lemma lem6152773 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152774 {C : Type'} (op : type1400 C) (a : C) : (term1133 C op a) = (term1149 C op a).
Proof. exact (MK_COMB (@lem6152773 C) (@lem6152772 C op a)). Qed.
Lemma lem6152775 {C : Type'} (op : type1400 C) (a : C) : (term1112 C op a) = (term1149 C op a).
Proof. exact (TRANS (@lem6152751 C op a) (@lem6152774 C op a)). Qed.
Lemma lem6152776 {C : Type'} (op : type1400 C) : (term1114 C op) = (term1150 C op).
Proof. exact (fun_ext (fun a : C => @lem6152775 C op a)). Qed.
Lemma lem6152777 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152778 {C : Type'} (op : type1400 C) : (term1115 C op) = (term1151 C op).
Proof. exact (MK_COMB (@lem6152777 C) (@lem6152776 C op)). Qed.
Lemma lem6152779 {C : Type'} (op : type1400 C) : (term1097 C op) = (term1151 C op).
Proof. exact (TRANS (@lem6152724 C op) (@lem6152778 C op)). Qed.
Lemma lem6152780 {C : Type'} (op : type1400 C) : (term1012 C op) = (term1151 C op).
Proof. exact (TRANS (@lem6152697 C op) (@lem6152779 C op)). Qed.
Lemma lem6152781 {C : Type'} (op : type1400 C) : (term1020 C op) = (term1020 C op).
Proof. exact (eq_refl (term1020 C op)). Qed.
Lemma lem6152782 {C : Type'} (op : type1400 C) : (term1021 C op) = (term1152 C op).
Proof. exact (MK_COMB (@lem6152781 C op) (@lem6152780 C op)). Qed.
Lemma lem6152784 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6152785 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6152784 C P Q). Qed.
Lemma lem6152786 {C : Type'} (op : type1400 C) : (term1153 C op) = (term1154 C op).
Proof. exact (@lem6152785 C (term1018 C op) (term1150 C op)). Qed.
Lemma lem6152787 {C : Type'} (op : type1400 C) (a : C) : (term1155 C op a) = ((term1015 C a op) = a).
Proof. exact (eq_refl (term1155 C op a)). Qed.
Lemma lem6152788 {C : Type'} (op : type1400 C) : (term1156 C op) = (term1018 C op).
Proof. exact (fun_ext (fun a : C => @lem6152787 C op a)). Qed.
Lemma lem6152789 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152790 {C : Type'} (op : type1400 C) : (term1157 C op) = (term1019 C op).
Proof. exact (MK_COMB (@lem6152789 C) (@lem6152788 C op)). Qed.
Lemma lem6152791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152792 {C : Type'} (op : type1400 C) : (term1158 C op) = (term1020 C op).
Proof. exact (MK_COMB (@lem6152791) (@lem6152790 C op)). Qed.
Lemma lem6152793 {C : Type'} (op : type1400 C) (a : C) : (term1159 C op a) = (term1149 C op a).
Proof. exact (eq_refl (term1159 C op a)). Qed.
Lemma lem6152794 {C : Type'} (op : type1400 C) : (term1160 C op) = (term1150 C op).
Proof. exact (fun_ext (fun a : C => @lem6152793 C op a)). Qed.
Lemma lem6152795 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152796 {C : Type'} (op : type1400 C) : (term1161 C op) = (term1151 C op).
Proof. exact (MK_COMB (@lem6152795 C) (@lem6152794 C op)). Qed.
Lemma lem6152797 {C : Type'} (op : type1400 C) : (term1153 C op) = (term1152 C op).
Proof. exact (MK_COMB (@lem6152792 C op) (@lem6152796 C op)). Qed.
Lemma lem6152798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152799 {C : Type'} (op : type1400 C) : (term1162 C op) = (term1163 C op).
Proof. exact (MK_COMB (@lem6152798) (@lem6152797 C op)). Qed.
Lemma lem6152800 {C : Type'} (op : type1400 C) (a : C) : (term1155 C op a) = ((term1015 C a op) = a).
Proof. exact (eq_refl (term1155 C op a)). Qed.
Lemma lem6152801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152802 {C : Type'} (op : type1400 C) (a : C) : (term1164 C op a) = (term1165 C op a).
Proof. exact (MK_COMB (@lem6152801) (@lem6152800 C op a)). Qed.
Lemma lem6152803 {C : Type'} (op : type1400 C) (a : C) : (term1159 C op a) = (term1149 C op a).
Proof. exact (eq_refl (term1159 C op a)). Qed.
Lemma lem6152804 {C : Type'} (op : type1400 C) (a : C) : (term1166 C op a) = (term1167 C op a).
Proof. exact (MK_COMB (@lem6152802 C op a) (@lem6152803 C op a)). Qed.
Lemma lem6152805 {C : Type'} (op : type1400 C) : (term1168 C op) = (term1169 C op).
Proof. exact (fun_ext (fun a : C => @lem6152804 C op a)). Qed.
Lemma lem6152806 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152807 {C : Type'} (op : type1400 C) : (term1154 C op) = (term1170 C op).
Proof. exact (MK_COMB (@lem6152806 C) (@lem6152805 C op)). Qed.
Lemma lem6152808 {C : Type'} (op : type1400 C) : ((term1153 C op) = (term1154 C op)) = ((term1152 C op) = (term1170 C op)).
Proof. exact (MK_COMB (@lem6152799 C op) (@lem6152807 C op)). Qed.
Lemma lem6152809 {C : Type'} (op : type1400 C) : (term1152 C op) = (term1170 C op).
Proof. exact (EQ_MP (@lem6152808 C op) (@lem6152786 C op)). Qed.
Lemma lem6152811 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6152812 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6152811 C P Q). Qed.
Lemma lem6152813 {C : Type'} (op : type1400 C) (a : C) : (term1171 C op a) = (term1172 C op a).
Proof. exact (@lem6152812 C ((term1015 C a op) = a) (term1148 C op a)). Qed.
Lemma lem6152814 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1173 C op a b) = (term1147 C b op a).
Proof. exact (eq_refl (term1173 C op a b)). Qed.
Lemma lem6152815 {C : Type'} (op : type1400 C) (a : C) : (term1174 C op a) = (term1148 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152814 C b op a)). Qed.
Lemma lem6152816 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152817 {C : Type'} (op : type1400 C) (a : C) : (term1175 C op a) = (term1149 C op a).
Proof. exact (MK_COMB (@lem6152816 C) (@lem6152815 C op a)). Qed.
Lemma lem6152818 {C : Type'} (op : type1400 C) (a : C) : (term1165 C op a) = (term1165 C op a).
Proof. exact (eq_refl (term1165 C op a)). Qed.
Lemma lem6152819 {C : Type'} (op : type1400 C) (a : C) : (term1171 C op a) = (term1167 C op a).
Proof. exact (MK_COMB (@lem6152818 C op a) (@lem6152817 C op a)). Qed.
Lemma lem6152820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152821 {C : Type'} (op : type1400 C) (a : C) : (term1176 C op a) = (term1177 C op a).
Proof. exact (MK_COMB (@lem6152820) (@lem6152819 C op a)). Qed.
Lemma lem6152822 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1173 C op a b) = (term1147 C b op a).
Proof. exact (eq_refl (term1173 C op a b)). Qed.
Lemma lem6152823 {C : Type'} (op : type1400 C) (a : C) : (term1165 C op a) = (term1165 C op a).
Proof. exact (eq_refl (term1165 C op a)). Qed.
Lemma lem6152824 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1178 C op a b) = (term1179 C b op a).
Proof. exact (MK_COMB (@lem6152823 C op a) (@lem6152822 C b op a)). Qed.
Lemma lem6152825 {C : Type'} (op : type1400 C) (a : C) : (term1180 C op a) = (term1181 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152824 C b op a)). Qed.
Lemma lem6152826 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152827 {C : Type'} (op : type1400 C) (a : C) : (term1172 C op a) = (term1182 C op a).
Proof. exact (MK_COMB (@lem6152826 C) (@lem6152825 C op a)). Qed.
Lemma lem6152828 {C : Type'} (op : type1400 C) (a : C) : ((term1171 C op a) = (term1172 C op a)) = ((term1167 C op a) = (term1182 C op a)).
Proof. exact (MK_COMB (@lem6152821 C op a) (@lem6152827 C op a)). Qed.
Lemma lem6152829 {C : Type'} (op : type1400 C) (a : C) : (term1167 C op a) = (term1182 C op a).
Proof. exact (EQ_MP (@lem6152828 C op a) (@lem6152813 C op a)). Qed.
Lemma lem6152831 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6152832 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6152831 C P Q). Qed.
Lemma lem6152833 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1183 C b op a) = (term1184 C b op a).
Proof. exact (@lem6152832 C ((term1015 C a op) = a) (term1146 C b op a)). Qed.
Lemma lem6152834 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1185 C b op a c) = (term1144 C b op a c).
Proof. exact (eq_refl (term1185 C b op a c)). Qed.
Lemma lem6152835 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1186 C b op a) = (term1146 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152834 C b op a c)). Qed.
Lemma lem6152836 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152837 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1187 C b op a) = (term1147 C b op a).
Proof. exact (MK_COMB (@lem6152836 C) (@lem6152835 C b op a)). Qed.
Lemma lem6152838 {C : Type'} (op : type1400 C) (a : C) : (term1165 C op a) = (term1165 C op a).
Proof. exact (eq_refl (term1165 C op a)). Qed.
Lemma lem6152839 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1183 C b op a) = (term1179 C b op a).
Proof. exact (MK_COMB (@lem6152838 C op a) (@lem6152837 C b op a)). Qed.
Lemma lem6152840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152841 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1188 C b op a) = (term1189 C b op a).
Proof. exact (MK_COMB (@lem6152840) (@lem6152839 C b op a)). Qed.
Lemma lem6152842 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1185 C b op a c) = (term1144 C b op a c).
Proof. exact (eq_refl (term1185 C b op a c)). Qed.
Lemma lem6152843 {C : Type'} (op : type1400 C) (a : C) : (term1165 C op a) = (term1165 C op a).
Proof. exact (eq_refl (term1165 C op a)). Qed.
Lemma lem6152844 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1190 C b op a c) = (term1191 C b op a c).
Proof. exact (MK_COMB (@lem6152843 C op a) (@lem6152842 C b op a c)). Qed.
Lemma lem6152845 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1192 C b op a) = (term1193 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152844 C b op a c)). Qed.
Lemma lem6152846 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152847 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1184 C b op a) = (term1194 C b op a).
Proof. exact (MK_COMB (@lem6152846 C) (@lem6152845 C b op a)). Qed.
Lemma lem6152848 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1183 C b op a) = (term1184 C b op a)) = ((term1179 C b op a) = (term1194 C b op a)).
Proof. exact (MK_COMB (@lem6152841 C b op a) (@lem6152847 C b op a)). Qed.
Lemma lem6152849 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1179 C b op a) = (term1194 C b op a).
Proof. exact (EQ_MP (@lem6152848 C b op a) (@lem6152833 C b op a)). Qed.
Lemma lem6152850 {C : Type'} (op : type1400 C) (a : C) : (term1181 C op a) = (term1195 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152849 C b op a)). Qed.
Lemma lem6152851 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152852 {C : Type'} (op : type1400 C) (a : C) : (term1182 C op a) = (term1196 C op a).
Proof. exact (MK_COMB (@lem6152851 C) (@lem6152850 C op a)). Qed.
Lemma lem6152853 {C : Type'} (op : type1400 C) (a : C) : (term1167 C op a) = (term1196 C op a).
Proof. exact (TRANS (@lem6152829 C op a) (@lem6152852 C op a)). Qed.
Lemma lem6152854 {C : Type'} (op : type1400 C) : (term1169 C op) = (term1197 C op).
Proof. exact (fun_ext (fun a : C => @lem6152853 C op a)). Qed.
Lemma lem6152855 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152856 {C : Type'} (op : type1400 C) : (term1170 C op) = (term1198 C op).
Proof. exact (MK_COMB (@lem6152855 C) (@lem6152854 C op)). Qed.
Lemma lem6152857 {C : Type'} (op : type1400 C) : (term1152 C op) = (term1198 C op).
Proof. exact (TRANS (@lem6152809 C op) (@lem6152856 C op)). Qed.
Lemma lem6152858 {C : Type'} (op : type1400 C) : (term1021 C op) = (term1198 C op).
Proof. exact (TRANS (@lem6152782 C op) (@lem6152857 C op)). Qed.
Lemma lem6152859 {C : Type'} (op : type1400 C) : (term1029 C op) = (term1029 C op).
Proof. exact (eq_refl (term1029 C op)). Qed.
Lemma lem6152860 {C : Type'} (op : type1400 C) : (term1030 C op) = (term1199 C op).
Proof. exact (MK_COMB (@lem6152859 C op) (@lem6152858 C op)). Qed.
Lemma lem6152862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1037 A P Q) = (term1038 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6152863 {C : Type'} (P : C -> Prop) (Q : C -> Prop) : (term1037 C P Q) = (term1038 C P Q).
Proof. exact (@lem6152862 C P Q). Qed.
Lemma lem6152864 {C : Type'} (op : type1400 C) : (term1200 C op) = (term1201 C op).
Proof. exact (@lem6152863 C (term1027 C op) (term1197 C op)). Qed.
Lemma lem6152865 {C : Type'} (op : type1400 C) (a : C) : (term1202 C op a) = ((term1024 C op a) = a).
Proof. exact (eq_refl (term1202 C op a)). Qed.
Lemma lem6152866 {C : Type'} (op : type1400 C) : (term1203 C op) = (term1027 C op).
Proof. exact (fun_ext (fun a : C => @lem6152865 C op a)). Qed.
Lemma lem6152867 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152868 {C : Type'} (op : type1400 C) : (term1204 C op) = (term1028 C op).
Proof. exact (MK_COMB (@lem6152867 C) (@lem6152866 C op)). Qed.
Lemma lem6152869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152870 {C : Type'} (op : type1400 C) : (term1205 C op) = (term1029 C op).
Proof. exact (MK_COMB (@lem6152869) (@lem6152868 C op)). Qed.
Lemma lem6152871 {C : Type'} (op : type1400 C) (a : C) : (term1206 C op a) = (term1196 C op a).
Proof. exact (eq_refl (term1206 C op a)). Qed.
Lemma lem6152872 {C : Type'} (op : type1400 C) : (term1207 C op) = (term1197 C op).
Proof. exact (fun_ext (fun a : C => @lem6152871 C op a)). Qed.
Lemma lem6152873 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152874 {C : Type'} (op : type1400 C) : (term1208 C op) = (term1198 C op).
Proof. exact (MK_COMB (@lem6152873 C) (@lem6152872 C op)). Qed.
Lemma lem6152875 {C : Type'} (op : type1400 C) : (term1200 C op) = (term1199 C op).
Proof. exact (MK_COMB (@lem6152870 C op) (@lem6152874 C op)). Qed.
Lemma lem6152876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152877 {C : Type'} (op : type1400 C) : (term1209 C op) = (term1210 C op).
Proof. exact (MK_COMB (@lem6152876) (@lem6152875 C op)). Qed.
Lemma lem6152878 {C : Type'} (op : type1400 C) (a : C) : (term1202 C op a) = ((term1024 C op a) = a).
Proof. exact (eq_refl (term1202 C op a)). Qed.
Lemma lem6152879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6152880 {C : Type'} (op : type1400 C) (a : C) : (term1211 C op a) = (term1212 C op a).
Proof. exact (MK_COMB (@lem6152879) (@lem6152878 C op a)). Qed.
Lemma lem6152881 {C : Type'} (op : type1400 C) (a : C) : (term1206 C op a) = (term1196 C op a).
Proof. exact (eq_refl (term1206 C op a)). Qed.
Lemma lem6152882 {C : Type'} (op : type1400 C) (a : C) : (term1213 C op a) = (term1214 C op a).
Proof. exact (MK_COMB (@lem6152880 C op a) (@lem6152881 C op a)). Qed.
Lemma lem6152883 {C : Type'} (op : type1400 C) : (term1215 C op) = (term1216 C op).
Proof. exact (fun_ext (fun a : C => @lem6152882 C op a)). Qed.
Lemma lem6152884 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152885 {C : Type'} (op : type1400 C) : (term1201 C op) = (term1217 C op).
Proof. exact (MK_COMB (@lem6152884 C) (@lem6152883 C op)). Qed.
Lemma lem6152886 {C : Type'} (op : type1400 C) : ((term1200 C op) = (term1201 C op)) = ((term1199 C op) = (term1217 C op)).
Proof. exact (MK_COMB (@lem6152877 C op) (@lem6152885 C op)). Qed.
Lemma lem6152887 {C : Type'} (op : type1400 C) : (term1199 C op) = (term1217 C op).
Proof. exact (EQ_MP (@lem6152886 C op) (@lem6152864 C op)). Qed.
Lemma lem6152889 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6152890 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6152889 C P Q). Qed.
Lemma lem6152891 {C : Type'} (op : type1400 C) (a : C) : (term1218 C op a) = (term1219 C op a).
Proof. exact (@lem6152890 C ((term1024 C op a) = a) (term1195 C op a)). Qed.
Lemma lem6152892 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1220 C op a b) = (term1194 C b op a).
Proof. exact (eq_refl (term1220 C op a b)). Qed.
Lemma lem6152893 {C : Type'} (op : type1400 C) (a : C) : (term1221 C op a) = (term1195 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152892 C b op a)). Qed.
Lemma lem6152894 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152895 {C : Type'} (op : type1400 C) (a : C) : (term1222 C op a) = (term1196 C op a).
Proof. exact (MK_COMB (@lem6152894 C) (@lem6152893 C op a)). Qed.
Lemma lem6152896 {C : Type'} (op : type1400 C) (a : C) : (term1212 C op a) = (term1212 C op a).
Proof. exact (eq_refl (term1212 C op a)). Qed.
Lemma lem6152897 {C : Type'} (op : type1400 C) (a : C) : (term1218 C op a) = (term1214 C op a).
Proof. exact (MK_COMB (@lem6152896 C op a) (@lem6152895 C op a)). Qed.
Lemma lem6152898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152899 {C : Type'} (op : type1400 C) (a : C) : (term1223 C op a) = (term1224 C op a).
Proof. exact (MK_COMB (@lem6152898) (@lem6152897 C op a)). Qed.
Lemma lem6152900 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1220 C op a b) = (term1194 C b op a).
Proof. exact (eq_refl (term1220 C op a b)). Qed.
Lemma lem6152901 {C : Type'} (op : type1400 C) (a : C) : (term1212 C op a) = (term1212 C op a).
Proof. exact (eq_refl (term1212 C op a)). Qed.
Lemma lem6152902 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1225 C op a b) = (term1226 C b op a).
Proof. exact (MK_COMB (@lem6152901 C op a) (@lem6152900 C b op a)). Qed.
Lemma lem6152903 {C : Type'} (op : type1400 C) (a : C) : (term1227 C op a) = (term1228 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152902 C b op a)). Qed.
Lemma lem6152904 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152905 {C : Type'} (op : type1400 C) (a : C) : (term1219 C op a) = (term1229 C op a).
Proof. exact (MK_COMB (@lem6152904 C) (@lem6152903 C op a)). Qed.
Lemma lem6152906 {C : Type'} (op : type1400 C) (a : C) : ((term1218 C op a) = (term1219 C op a)) = ((term1214 C op a) = (term1229 C op a)).
Proof. exact (MK_COMB (@lem6152899 C op a) (@lem6152905 C op a)). Qed.
Lemma lem6152907 {C : Type'} (op : type1400 C) (a : C) : (term1214 C op a) = (term1229 C op a).
Proof. exact (EQ_MP (@lem6152906 C op a) (@lem6152891 C op a)). Qed.
Lemma lem6152909 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1134 A P Q) = (term1135 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6152910 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1134 C P Q) = (term1135 C P Q).
Proof. exact (@lem6152909 C P Q). Qed.
Lemma lem6152911 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1230 C b op a) = (term1231 C b op a).
Proof. exact (@lem6152910 C ((term1024 C op a) = a) (term1193 C b op a)). Qed.
Lemma lem6152912 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1232 C b op a c) = (term1191 C b op a c).
Proof. exact (eq_refl (term1232 C b op a c)). Qed.
Lemma lem6152913 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1233 C b op a) = (term1193 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152912 C b op a c)). Qed.
Lemma lem6152914 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152915 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1234 C b op a) = (term1194 C b op a).
Proof. exact (MK_COMB (@lem6152914 C) (@lem6152913 C b op a)). Qed.
Lemma lem6152916 {C : Type'} (op : type1400 C) (a : C) : (term1212 C op a) = (term1212 C op a).
Proof. exact (eq_refl (term1212 C op a)). Qed.
Lemma lem6152917 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1230 C b op a) = (term1226 C b op a).
Proof. exact (MK_COMB (@lem6152916 C op a) (@lem6152915 C b op a)). Qed.
Lemma lem6152918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152919 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1235 C b op a) = (term1236 C b op a).
Proof. exact (MK_COMB (@lem6152918) (@lem6152917 C b op a)). Qed.
Lemma lem6152920 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1232 C b op a c) = (term1191 C b op a c).
Proof. exact (eq_refl (term1232 C b op a c)). Qed.
Lemma lem6152921 {C : Type'} (op : type1400 C) (a : C) : (term1212 C op a) = (term1212 C op a).
Proof. exact (eq_refl (term1212 C op a)). Qed.
Lemma lem6152922 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1237 C b op a c) = (term1238 C b op a c).
Proof. exact (MK_COMB (@lem6152921 C op a) (@lem6152920 C b op a c)). Qed.
Lemma lem6152923 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1239 C b op a) = (term1240 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152922 C b op a c)). Qed.
Lemma lem6152924 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152925 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1231 C b op a) = (term1241 C b op a).
Proof. exact (MK_COMB (@lem6152924 C) (@lem6152923 C b op a)). Qed.
Lemma lem6152926 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1230 C b op a) = (term1231 C b op a)) = ((term1226 C b op a) = (term1241 C b op a)).
Proof. exact (MK_COMB (@lem6152919 C b op a) (@lem6152925 C b op a)). Qed.
Lemma lem6152927 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1226 C b op a) = (term1241 C b op a).
Proof. exact (EQ_MP (@lem6152926 C b op a) (@lem6152911 C b op a)). Qed.
Lemma lem6152928 {C : Type'} (op : type1400 C) (a : C) : (term1228 C op a) = (term1242 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152927 C b op a)). Qed.
Lemma lem6152929 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152930 {C : Type'} (op : type1400 C) (a : C) : (term1229 C op a) = (term1243 C op a).
Proof. exact (MK_COMB (@lem6152929 C) (@lem6152928 C op a)). Qed.
Lemma lem6152931 {C : Type'} (op : type1400 C) (a : C) : (term1214 C op a) = (term1243 C op a).
Proof. exact (TRANS (@lem6152907 C op a) (@lem6152930 C op a)). Qed.
Lemma lem6152932 {C : Type'} (op : type1400 C) : (term1216 C op) = (term1244 C op).
Proof. exact (fun_ext (fun a : C => @lem6152931 C op a)). Qed.
Lemma lem6152933 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152934 {C : Type'} (op : type1400 C) : (term1217 C op) = (term1245 C op).
Proof. exact (MK_COMB (@lem6152933 C) (@lem6152932 C op)). Qed.
Lemma lem6152935 {C : Type'} (op : type1400 C) : (term1199 C op) = (term1245 C op).
Proof. exact (TRANS (@lem6152887 C op) (@lem6152934 C op)). Qed.
Lemma lem6152936 {C : Type'} (op : type1400 C) : (term1030 C op) = (term1245 C op).
Proof. exact (TRANS (@lem6152860 C op) (@lem6152935 C op)). Qed.
Lemma lem6152937 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6152938 {C : Type'} (op : type1400 C) : (term1034 C op) = (term1246 C op).
Proof. exact (MK_COMB (@lem6152937 C op) (@lem6152936 C op)). Qed.
Lemma lem6152940 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1247 A P Q) = (term1248 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6152941 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1247 C P Q) = (term1248 C P Q).
Proof. exact (@lem6152940 C P Q). Qed.
Lemma lem6152942 {C : Type'} (op : type1400 C) : (term1249 C op) = (term1250 C op).
Proof. exact (@lem6152941 C (term1032 C op) (term1244 C op)). Qed.
Lemma lem6152943 {C : Type'} (op : type1400 C) (a : C) : (term1251 C op a) = (term1243 C op a).
Proof. exact (eq_refl (term1251 C op a)). Qed.
Lemma lem6152944 {C : Type'} (op : type1400 C) : (term1252 C op) = (term1244 C op).
Proof. exact (fun_ext (fun a : C => @lem6152943 C op a)). Qed.
Lemma lem6152945 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152946 {C : Type'} (op : type1400 C) : (term1253 C op) = (term1245 C op).
Proof. exact (MK_COMB (@lem6152945 C) (@lem6152944 C op)). Qed.
Lemma lem6152947 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6152948 {C : Type'} (op : type1400 C) : (term1249 C op) = (term1246 C op).
Proof. exact (MK_COMB (@lem6152947 C op) (@lem6152946 C op)). Qed.
Lemma lem6152949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152950 {C : Type'} (op : type1400 C) : (term1254 C op) = (term1255 C op).
Proof. exact (MK_COMB (@lem6152949) (@lem6152948 C op)). Qed.
Lemma lem6152951 {C : Type'} (op : type1400 C) (a : C) : (term1251 C op a) = (term1243 C op a).
Proof. exact (eq_refl (term1251 C op a)). Qed.
Lemma lem6152952 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6152953 {C : Type'} (op : type1400 C) (a : C) : (term1256 C op a) = (term1257 C op a).
Proof. exact (MK_COMB (@lem6152952 C op) (@lem6152951 C op a)). Qed.
Lemma lem6152954 {C : Type'} (op : type1400 C) : (term1258 C op) = (term1259 C op).
Proof. exact (fun_ext (fun a : C => @lem6152953 C op a)). Qed.
Lemma lem6152955 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152956 {C : Type'} (op : type1400 C) : (term1250 C op) = (term1260 C op).
Proof. exact (MK_COMB (@lem6152955 C) (@lem6152954 C op)). Qed.
Lemma lem6152957 {C : Type'} (op : type1400 C) : ((term1249 C op) = (term1250 C op)) = ((term1246 C op) = (term1260 C op)).
Proof. exact (MK_COMB (@lem6152950 C op) (@lem6152956 C op)). Qed.
Lemma lem6152958 {C : Type'} (op : type1400 C) : (term1246 C op) = (term1260 C op).
Proof. exact (EQ_MP (@lem6152957 C op) (@lem6152942 C op)). Qed.
Lemma lem6152960 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1247 A P Q) = (term1248 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6152961 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1247 C P Q) = (term1248 C P Q).
Proof. exact (@lem6152960 C P Q). Qed.
Lemma lem6152962 {C : Type'} (op : type1400 C) (a : C) : (term1261 C op a) = (term1262 C op a).
Proof. exact (@lem6152961 C (term1032 C op) (term1242 C op a)). Qed.
Lemma lem6152963 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1263 C op a b) = (term1241 C b op a).
Proof. exact (eq_refl (term1263 C op a b)). Qed.
Lemma lem6152964 {C : Type'} (op : type1400 C) (a : C) : (term1264 C op a) = (term1242 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152963 C b op a)). Qed.
Lemma lem6152965 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152966 {C : Type'} (op : type1400 C) (a : C) : (term1265 C op a) = (term1243 C op a).
Proof. exact (MK_COMB (@lem6152965 C) (@lem6152964 C op a)). Qed.
Lemma lem6152967 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6152968 {C : Type'} (op : type1400 C) (a : C) : (term1261 C op a) = (term1257 C op a).
Proof. exact (MK_COMB (@lem6152967 C op) (@lem6152966 C op a)). Qed.
Lemma lem6152969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152970 {C : Type'} (op : type1400 C) (a : C) : (term1266 C op a) = (term1267 C op a).
Proof. exact (MK_COMB (@lem6152969) (@lem6152968 C op a)). Qed.
Lemma lem6152971 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1263 C op a b) = (term1241 C b op a).
Proof. exact (eq_refl (term1263 C op a b)). Qed.
Lemma lem6152972 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6152973 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1268 C op a b) = (term1269 C b op a).
Proof. exact (MK_COMB (@lem6152972 C op) (@lem6152971 C b op a)). Qed.
Lemma lem6152974 {C : Type'} (op : type1400 C) (a : C) : (term1270 C op a) = (term1271 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152973 C b op a)). Qed.
Lemma lem6152975 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152976 {C : Type'} (op : type1400 C) (a : C) : (term1262 C op a) = (term1272 C op a).
Proof. exact (MK_COMB (@lem6152975 C) (@lem6152974 C op a)). Qed.
Lemma lem6152977 {C : Type'} (op : type1400 C) (a : C) : ((term1261 C op a) = (term1262 C op a)) = ((term1257 C op a) = (term1272 C op a)).
Proof. exact (MK_COMB (@lem6152970 C op a) (@lem6152976 C op a)). Qed.
Lemma lem6152978 {C : Type'} (op : type1400 C) (a : C) : (term1257 C op a) = (term1272 C op a).
Proof. exact (EQ_MP (@lem6152977 C op a) (@lem6152962 C op a)). Qed.
Lemma lem6152980 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1247 A P Q) = (term1248 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6152981 {C : Type'} (P : Prop) (Q : C -> Prop) : (term1247 C P Q) = (term1248 C P Q).
Proof. exact (@lem6152980 C P Q). Qed.
Lemma lem6152982 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1273 C b op a) = (term1274 C b op a).
Proof. exact (@lem6152981 C (term1032 C op) (term1240 C b op a)). Qed.
Lemma lem6152983 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1275 C b op a c) = (term1238 C b op a c).
Proof. exact (eq_refl (term1275 C b op a c)). Qed.
Lemma lem6152984 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1276 C b op a) = (term1240 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152983 C b op a c)). Qed.
Lemma lem6152985 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152986 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1277 C b op a) = (term1241 C b op a).
Proof. exact (MK_COMB (@lem6152985 C) (@lem6152984 C b op a)). Qed.
Lemma lem6152987 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6152988 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1273 C b op a) = (term1269 C b op a).
Proof. exact (MK_COMB (@lem6152987 C op) (@lem6152986 C b op a)). Qed.
Lemma lem6152989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6152990 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1278 C b op a) = (term1279 C b op a).
Proof. exact (MK_COMB (@lem6152989) (@lem6152988 C b op a)). Qed.
Lemma lem6152991 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1275 C b op a c) = (term1238 C b op a c).
Proof. exact (eq_refl (term1275 C b op a c)). Qed.
Lemma lem6152992 {C : Type'} (op : type1400 C) : (term1033 C op) = (term1033 C op).
Proof. exact (eq_refl (term1033 C op)). Qed.
Lemma lem6152993 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1280 C b op a c) = (term1281 C b op a c).
Proof. exact (MK_COMB (@lem6152992 C op) (@lem6152991 C b op a c)). Qed.
Lemma lem6152994 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1282 C b op a) = (term1283 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6152993 C b op a c)). Qed.
Lemma lem6152995 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6152996 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1274 C b op a) = (term1284 C b op a).
Proof. exact (MK_COMB (@lem6152995 C) (@lem6152994 C b op a)). Qed.
Lemma lem6152997 {C : Type'} (b : C) (op : type1400 C) (a : C) : ((term1273 C b op a) = (term1274 C b op a)) = ((term1269 C b op a) = (term1284 C b op a)).
Proof. exact (MK_COMB (@lem6152990 C b op a) (@lem6152996 C b op a)). Qed.
Lemma lem6152998 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1269 C b op a) = (term1284 C b op a).
Proof. exact (EQ_MP (@lem6152997 C b op a) (@lem6152982 C b op a)). Qed.
Lemma lem6152999 {C : Type'} (op : type1400 C) (a : C) : (term1271 C op a) = (term1285 C op a).
Proof. exact (fun_ext (fun b : C => @lem6152998 C b op a)). Qed.
Lemma lem6153000 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6153001 {C : Type'} (op : type1400 C) (a : C) : (term1272 C op a) = (term1286 C op a).
Proof. exact (MK_COMB (@lem6153000 C) (@lem6152999 C op a)). Qed.
Lemma lem6153002 {C : Type'} (op : type1400 C) (a : C) : (term1257 C op a) = (term1286 C op a).
Proof. exact (TRANS (@lem6152978 C op a) (@lem6153001 C op a)). Qed.
Lemma lem6153003 {C : Type'} (op : type1400 C) : (term1259 C op) = (term1287 C op).
Proof. exact (fun_ext (fun a : C => @lem6153002 C op a)). Qed.
Lemma lem6153004 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6153005 {C : Type'} (op : type1400 C) : (term1260 C op) = (term1288 C op).
Proof. exact (MK_COMB (@lem6153004 C) (@lem6153003 C op)). Qed.
Lemma lem6153006 {C : Type'} (op : type1400 C) : (term1246 C op) = (term1288 C op).
Proof. exact (TRANS (@lem6152958 C op) (@lem6153005 C op)). Qed.
Lemma lem6153007 {C : Type'} (op : type1400 C) : (term1034 C op) = (term1288 C op).
Proof. exact (TRANS (@lem6152938 C op) (@lem6153006 C op)). Qed.
Lemma lem6153008 {C : Type'} : (term1035 C) = (term1289 C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6153007 C op)). Qed.
Lemma lem6153009 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6153010 {C : Type'} : (term1036 C) = (term1290 C).
Proof. exact (MK_COMB (@lem6153009 C) (@lem6153008 C)). Qed.
Lemma lem6153032 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1281 C b op a c) = (term1291 C b op a c).
Proof. exact (@lem19490 ((term1024 C op a) = a) (term1032 C op) (term1191 C b op a c)). Qed.
Lemma lem6153033 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1292 C b op a c) = (term1293 C b op a c).
Proof. exact (@lem19490 ((term1015 C a op) = a) (term1032 C op) (term1144 C b op a c)). Qed.
Lemma lem6153034 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1294 C b op a c) = (term1295 C b op a c).
Proof. exact (@lem19490 ((term977 C op a b) = (term977 C op b a)) (term1032 C op) (term1089 C b op a c)). Qed.
Lemma lem6153041 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1296 C b op a c) = (term1297 C b op a c).
Proof. exact (@lem19490 ((term994 C op a b c) = (term980 C a op b c)) (term1032 C op) ((term980 C a op b c) = (term980 C b op a c))). Qed.
Lemma lem6153044 {C : Type'} (op : type1400 C) (b : C) (a : C) : (term1298 C op b a) = (term1298 C op b a).
Proof. exact (eq_refl (term1298 C op b a)). Qed.
Lemma lem6153045 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1295 C b op a c) = (term1299 C b op a c).
Proof. exact (MK_COMB (@lem6153044 C op b a) (@lem6153041 C b op a c)). Qed.
Lemma lem6153046 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1294 C b op a c) = (term1299 C b op a c).
Proof. exact (TRANS (@lem6153034 C b op a c) (@lem6153045 C b op a c)). Qed.
Lemma lem6153049 {C : Type'} (op : type1400 C) (a : C) : (term1300 C op a) = (term1300 C op a).
Proof. exact (eq_refl (term1300 C op a)). Qed.
Lemma lem6153050 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1293 C b op a c) = (term1301 C b op a c).
Proof. exact (MK_COMB (@lem6153049 C op a) (@lem6153046 C b op a c)). Qed.
Lemma lem6153051 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1292 C b op a c) = (term1301 C b op a c).
Proof. exact (TRANS (@lem6153033 C b op a c) (@lem6153050 C b op a c)). Qed.
Lemma lem6153054 {C : Type'} (op : type1400 C) (a : C) : (term1302 C op a) = (term1302 C op a).
Proof. exact (eq_refl (term1302 C op a)). Qed.
Lemma lem6153055 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1291 C b op a c) = (term1303 C b op a c).
Proof. exact (MK_COMB (@lem6153054 C op a) (@lem6153051 C b op a c)). Qed.
Lemma lem6153057 {C : Type'} (b : C) (op : type1400 C) (a : C) (c : C) : (term1281 C b op a c) = (term1303 C b op a c).
Proof. exact (TRANS (@lem6153032 C b op a c) (@lem6153055 C b op a c)). Qed.
Lemma lem6153058 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1283 C b op a) = (term1304 C b op a).
Proof. exact (fun_ext (fun c : C => @lem6153057 C b op a c)). Qed.
Lemma lem6153059 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6153060 {C : Type'} (b : C) (op : type1400 C) (a : C) : (term1284 C b op a) = (term1305 C b op a).
Proof. exact (MK_COMB (@lem6153059 C) (@lem6153058 C b op a)). Qed.
Lemma lem6153061 {C : Type'} (op : type1400 C) (a : C) : (term1285 C op a) = (term1306 C op a).
Proof. exact (fun_ext (fun b : C => @lem6153060 C b op a)). Qed.
Lemma lem6153062 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6153063 {C : Type'} (op : type1400 C) (a : C) : (term1286 C op a) = (term1307 C op a).
Proof. exact (MK_COMB (@lem6153062 C) (@lem6153061 C op a)). Qed.
Lemma lem6153064 {C : Type'} (op : type1400 C) : (term1287 C op) = (term1308 C op).
Proof. exact (fun_ext (fun a : C => @lem6153063 C op a)). Qed.
Lemma lem6153065 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem6153066 {C : Type'} (op : type1400 C) : (term1288 C op) = (term1309 C op).
Proof. exact (MK_COMB (@lem6153065 C) (@lem6153064 C op)). Qed.
Lemma lem6153067 {C : Type'} : (term1289 C) = (term1310 C).
Proof. exact (fun_ext (fun op : type1400 C => @lem6153066 C op)). Qed.
Lemma lem6153068 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6153069 {C : Type'} : (term1290 C) = (term1311 C).
Proof. exact (MK_COMB (@lem6153068 C) (@lem6153067 C)). Qed.
Lemma lem6153070 {C : Type'} : (term1036 C) = (term1311 C).
Proof. exact (TRANS (@lem6153010 C) (@lem6153069 C)). Qed.
Lemma lem6153071 {C : Type'} (h1 : term603 C) : term1311 C.
Proof. exact (EQ_MP (@lem6153070 C) (@lem6149811 C h1)). Qed.
Lemma lem6153114 {C : Type'} (_77407 : type1400 C) (h1 : term603 C) : term1312 C _77407.
Proof. exact (@lem6151548 C h1 _77407). Qed.
Lemma lem6153115 {C : Type'} (_77407 : type1400 C) : (term1312 C _77407) = (term1309 C _77407).
Proof. exact (eq_refl (term1312 C _77407)). Qed.
Lemma lem6153116 {C : Type'} (_77407 : type1400 C) (h1 : term603 C) : term1309 C _77407.
Proof. exact (EQ_MP (@lem6153115 C _77407) (@lem6153114 C _77407 h1)). Qed.
Lemma lem6153117 {C : Type'} (_77407 : type1400 C) (_77408 : C) (h1 : term603 C) : term1313 C _77407 _77408.
Proof. exact (@lem6153116 C _77407 h1 _77408). Qed.
Lemma lem6153118 {C : Type'} (_77407 : type1400 C) (_77408 : C) : (term1313 C _77407 _77408) = (term1307 C _77407 _77408).
Proof. exact (eq_refl (term1313 C _77407 _77408)). Qed.
Lemma lem6153119 {C : Type'} (_77407 : type1400 C) (_77408 : C) (h1 : term603 C) : term1307 C _77407 _77408.
Proof. exact (EQ_MP (@lem6153118 C _77407 _77408) (@lem6153117 C _77407 _77408 h1)). Qed.
Lemma lem6153120 {C : Type'} (_77407 : type1400 C) (_77408 : C) (_77409 : C) (h1 : term603 C) : term1314 C _77407 _77408 _77409.
Proof. exact (@lem6153119 C _77407 _77408 h1 _77409). Qed.
Lemma lem6153121 {C : Type'} (_77409 : C) (_77407 : type1400 C) (_77408 : C) : (term1314 C _77407 _77408 _77409) = (term1305 C _77409 _77407 _77408).
Proof. exact (eq_refl (term1314 C _77407 _77408 _77409)). Qed.
Lemma lem6153122 {C : Type'} (_77409 : C) (_77407 : type1400 C) (_77408 : C) (h1 : term603 C) : term1305 C _77409 _77407 _77408.
Proof. exact (EQ_MP (@lem6153121 C _77409 _77407 _77408) (@lem6153120 C _77407 _77408 _77409 h1)). Qed.
Lemma lem6153123 {C : Type'} (_77409 : C) (_77407 : type1400 C) (_77408 : C) (_77410 : C) (h1 : term603 C) : term1315 C _77409 _77407 _77408 _77410.
Proof. exact (@lem6153122 C _77409 _77407 _77408 h1 _77410). Qed.
Lemma lem6153124 {C : Type'} (_77409 : C) (_77407 : type1400 C) (_77408 : C) (_77410 : C) : (term1315 C _77409 _77407 _77408 _77410) = (term1303 C _77409 _77407 _77408 _77410).
Proof. exact (eq_refl (term1315 C _77409 _77407 _77408 _77410)). Qed.
Lemma lem6153125 {C : Type'} (_77409 : C) (_77407 : type1400 C) (_77408 : C) (_77410 : C) (h1 : term603 C) : term1303 C _77409 _77407 _77408 _77410.
Proof. exact (EQ_MP (@lem6153124 C _77409 _77407 _77408 _77410) (@lem6153123 C _77409 _77407 _77408 _77410 h1)). Qed.
Lemma lem6153156 {C : Type'} (_77421 : type1400 C) (h1 : term603 C) : term1312 C _77421.
Proof. exact (@lem6153071 C h1 _77421). Qed.
Lemma lem6153157 {C : Type'} (_77421 : type1400 C) : (term1312 C _77421) = (term1309 C _77421).
Proof. exact (eq_refl (term1312 C _77421)). Qed.
Lemma lem6153158 {C : Type'} (_77421 : type1400 C) (h1 : term603 C) : term1309 C _77421.
Proof. exact (EQ_MP (@lem6153157 C _77421) (@lem6153156 C _77421 h1)). Qed.
Lemma lem6153159 {C : Type'} (_77421 : type1400 C) (_77422 : C) (h1 : term603 C) : term1313 C _77421 _77422.
Proof. exact (@lem6153158 C _77421 h1 _77422). Qed.
Lemma lem6153160 {C : Type'} (_77421 : type1400 C) (_77422 : C) : (term1313 C _77421 _77422) = (term1307 C _77421 _77422).
Proof. exact (eq_refl (term1313 C _77421 _77422)). Qed.
Lemma lem6153161 {C : Type'} (_77421 : type1400 C) (_77422 : C) (h1 : term603 C) : term1307 C _77421 _77422.
Proof. exact (EQ_MP (@lem6153160 C _77421 _77422) (@lem6153159 C _77421 _77422 h1)). Qed.
Lemma lem6153162 {C : Type'} (_77421 : type1400 C) (_77422 : C) (_77423 : C) (h1 : term603 C) : term1314 C _77421 _77422 _77423.
Proof. exact (@lem6153161 C _77421 _77422 h1 _77423). Qed.
Lemma lem6153163 {C : Type'} (_77423 : C) (_77421 : type1400 C) (_77422 : C) : (term1314 C _77421 _77422 _77423) = (term1305 C _77423 _77421 _77422).
Proof. exact (eq_refl (term1314 C _77421 _77422 _77423)). Qed.
Lemma lem6153164 {C : Type'} (_77423 : C) (_77421 : type1400 C) (_77422 : C) (h1 : term603 C) : term1305 C _77423 _77421 _77422.
Proof. exact (EQ_MP (@lem6153163 C _77423 _77421 _77422) (@lem6153162 C _77421 _77422 _77423 h1)). Qed.
Lemma lem6153165 {C : Type'} (_77423 : C) (_77421 : type1400 C) (_77422 : C) (_77424 : C) (h1 : term603 C) : term1315 C _77423 _77421 _77422 _77424.
Proof. exact (@lem6153164 C _77423 _77421 _77422 h1 _77424). Qed.
Lemma lem6153166 {C : Type'} (_77423 : C) (_77421 : type1400 C) (_77422 : C) (_77424 : C) : (term1315 C _77423 _77421 _77422 _77424) = (term1303 C _77423 _77421 _77422 _77424).
Proof. exact (eq_refl (term1315 C _77423 _77421 _77422 _77424)). Qed.
Lemma lem6153167 {C : Type'} (_77423 : C) (_77421 : type1400 C) (_77422 : C) (_77424 : C) (h1 : term603 C) : term1303 C _77423 _77421 _77422 _77424.
Proof. exact (EQ_MP (@lem6153166 C _77423 _77421 _77422 _77424) (@lem6153165 C _77423 _77421 _77422 _77424 h1)). Qed.
Lemma lem6153235 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term927 A B C op f s g) : term976 A B C op f s g.
Proof. exact (EQ_MP (@lem6148940 A B C op f s g) (@lem6148211 A B C op f s g h1)). Qed.
Lemma lem6153255 {C : Type'} (_77407 : type1400 C) (_77408 : C) (h1 : term603 C) : term1316 C _77407 _77408.
Proof. exact (proj1 (@lem6153125 C (@el C) _77407 _77408 (@el C) h1)). Qed.
Lemma lem6153443 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term927 A B C op f s g) : term976 A B C op f s g.
Proof. exact (EQ_MP (@lem6148940 A B C op f s g) (@lem6148211 A B C op f s g h1)). Qed.
Lemma lem6153455 {C : Type'} (_77421 : type1400 C) (_77422 : C) (h1 : term603 C) : term1316 C _77421 _77422.
Proof. exact (proj1 (@lem6153167 C (@el C) _77421 _77422 (@el C) h1)). Qed.
Lemma lem6153974 {C : Type'} (x : C) (y : C) (z : C) : term527 C x y z.
Proof. exact (@lem21385 C x y z). Qed.
Lemma lem6154020 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @I ((C -> C -> C) -> Prop) (@monoidal C) op.
Proof. exact (EQ_MP (@lem6148669 C op) (@lem6147877 C op h1)). Qed.
Lemma lem6154021 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term1317 C op.
Proof. exact (fun h0 : term1032 C op => @lem6154020 C op h1). Qed.
Lemma lem6154023 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154024 {C : Type'} (op : type1400 C) : (term1317 C op) = (@I ((C -> C -> C) -> Prop) (@monoidal C) op).
Proof. exact (@lem6154023 (@I ((C -> C -> C) -> Prop) (@monoidal C) op)). Qed.
Lemma lem6154025 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @I ((C -> C -> C) -> Prop) (@monoidal C) op.
Proof. exact (EQ_MP (@lem6154024 C op) (@lem6154021 C op h1)). Qed.
Lemma lem6154031 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6154032 {C : Type'} (_77408 : C) (_77407 : type1400 C) : (term1316 C _77407 _77408) = (term1318 C _77408 _77407).
Proof. exact (@lem6154031 ((term1024 C _77407 _77408) = _77408) (term1032 C _77407)). Qed.
Lemma lem6154040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6154041 {C : Type'} (_77408 : C) (_77407 : type1400 C) : (term1319 C _77407 _77408) = (term1320 C _77408 _77407).
Proof. exact (MK_COMB (@lem6154040) (@lem6154032 C _77408 _77407)). Qed.
Lemma lem6154049 {C : Type'} (_77408 : C) (_77407 : type1400 C) : (term1318 C _77408 _77407) = (term1318 C _77408 _77407).
Proof. exact (eq_refl (term1318 C _77408 _77407)). Qed.
Lemma lem6154050 {C : Type'} (_77408 : C) (_77407 : type1400 C) : ((term1316 C _77407 _77408) = (term1318 C _77408 _77407)) = ((term1318 C _77408 _77407) = (term1318 C _77408 _77407)).
Proof. exact (MK_COMB (@lem6154041 C _77408 _77407) (@lem6154049 C _77408 _77407)). Qed.
Lemma lem6154052 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6154053 (x : Prop) : (x = x) = True.
Proof. exact (@lem6154052 Prop x). Qed.
Lemma lem6154054 {C : Type'} (_77408 : C) (_77407 : type1400 C) : ((term1318 C _77408 _77407) = (term1318 C _77408 _77407)) = True.
Proof. exact (@lem6154053 (term1318 C _77408 _77407)). Qed.
Lemma lem6154055 {C : Type'} (_77408 : C) (_77407 : type1400 C) : ((term1316 C _77407 _77408) = (term1318 C _77408 _77407)) = True.
Proof. exact (TRANS (@lem6154050 C _77408 _77407) (@lem6154054 C _77408 _77407)). Qed.
Lemma lem6154056 {C : Type'} (_77408 : C) (_77407 : type1400 C) : True = ((term1316 C _77407 _77408) = (term1318 C _77408 _77407)).
Proof. exact (SYM (@lem6154055 C _77408 _77407)). Qed.
Lemma lem6154057 {C : Type'} (_77408 : C) (_77407 : type1400 C) : (term1316 C _77407 _77408) = (term1318 C _77408 _77407).
Proof. exact (EQ_MP (@lem6154056 C _77408 _77407) (@lem0)). Qed.
Lemma lem6154058 {C : Type'} (_77408 : C) (_77407 : type1400 C) (h1 : term603 C) : term1318 C _77408 _77407.
Proof. exact (EQ_MP (@lem6154057 C _77408 _77407) (@lem6153255 C _77407 _77408 h1)). Qed.
Lemma lem6154060 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6154061 {C : Type'} (_77407 : type1400 C) (_77408 : C) : (term1318 C _77408 _77407) = (term1321 C _77407 _77408).
Proof. exact (@lem6154060 (term1032 C _77407) ((term1024 C _77407 _77408) = _77408)). Qed.
Lemma lem6154063 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6154064 {C : Type'} (_77407 : type1400 C) : (term1322 C _77407) = (@I ((C -> C -> C) -> Prop) (@monoidal C) _77407).
Proof. exact (@lem6154063 (@I ((C -> C -> C) -> Prop) (@monoidal C) _77407)). Qed.
Lemma lem6154065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6154066 {C : Type'} (_77407 : type1400 C) : (term1323 C _77407) = (term1324 C _77407).
Proof. exact (MK_COMB (@lem6154065) (@lem6154064 C _77407)). Qed.
Lemma lem6154067 {C : Type'} (_77407 : type1400 C) (_77408 : C) : ((term1024 C _77407 _77408) = _77408) = ((term1024 C _77407 _77408) = _77408).
Proof. exact (eq_refl ((term1024 C _77407 _77408) = _77408)). Qed.
Lemma lem6154068 {C : Type'} (_77407 : type1400 C) (_77408 : C) : (term1321 C _77407 _77408) = (term1325 C _77407 _77408).
Proof. exact (MK_COMB (@lem6154066 C _77407) (@lem6154067 C _77407 _77408)). Qed.
Lemma lem6154069 {C : Type'} (_77407 : type1400 C) (_77408 : C) : (term1318 C _77408 _77407) = (term1325 C _77407 _77408).
Proof. exact (TRANS (@lem6154061 C _77407 _77408) (@lem6154068 C _77407 _77408)). Qed.
Lemma lem6154072 {C : Type'} (_77407 : type1400 C) (_77408 : C) (h1 : term603 C) : term1325 C _77407 _77408.
Proof. exact (EQ_MP (@lem6154069 C _77407 _77408) (@lem6154058 C _77408 _77407 h1)). Qed.
Lemma lem6154073 {C : Type'} (_77407 : type1400 C) (_77408 : C) (h1 : term603 C) : term1325 C _77407 _77408.
Proof. exact (@lem6154072 C _77407 _77408 h1). Qed.
Lemma lem6154074 {C : Type'} (op : type1400 C) (_77408 : C) (h1 : term603 C) : term1325 C op _77408.
Proof. exact (@lem6154073 C op _77408 h1). Qed.
Lemma lem6154077 {C : Type'} (_77408 : C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term1024 C op _77408) = _77408.
Proof. exact (@lem6154074 C op _77408 h1 (@lem6154025 C op h2)). Qed.
Lemma lem6154078 {C : Type'} (_77408 : C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term1024 C op _77408) = _77408.
Proof. exact (@lem6154077 C _77408 op h1 h2). Qed.
Lemma lem6154079 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term975 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (@lem6154078 C (term707 A B C op f s g) op h1 h2). Qed.
Lemma lem6154080 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : term1326 A B C op f s g.
Proof. exact (fun h0 : term1327 A B C op f s g => @lem6154079 A B C f s g op h1 h2). Qed.
Lemma lem6154082 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154083 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1326 A B C op f s g) = ((term975 A B C op f s g) = (term707 A B C op f s g)).
Proof. exact (@lem6154082 ((term975 A B C op f s g) = (term707 A B C op f s g))). Qed.
Lemma lem6154084 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term975 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (EQ_MP (@lem6154083 A B C op f s g) (@lem6154080 A B C f s g op h1 h2)). Qed.
Lemma lem6154086 {C : Type'} (x : C) : x = x.
Proof. exact (@lem21386 C x). Qed.
Lemma lem6154087 {C : Type'} (x : C) : x = x.
Proof. exact (@lem6154086 C x). Qed.
Lemma lem6154088 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term975 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (@lem6154087 C (term975 A B C op f s g)). Qed.
Lemma lem6154089 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term1328 A B C op f s g.
Proof. exact (fun h0 : term1329 A B C op f s g => @lem6154088 A B C op f s g). Qed.
Lemma lem6154091 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154092 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1328 A B C op f s g) = ((term975 A B C op f s g) = (term975 A B C op f s g)).
Proof. exact (@lem6154091 ((term975 A B C op f s g) = (term975 A B C op f s g))). Qed.
Lemma lem6154093 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term975 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (EQ_MP (@lem6154092 A B C op f s g) (@lem6154089 A B C op f s g)). Qed.
Lemma lem6154111 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6154112 {C : Type'} (y : C) (x : C) (z : C) : (term532 C x y z) = (term533 C y x z).
Proof. exact (@lem6154111 (y = z) (term389 C x z)). Qed.
Lemma lem6154122 {C : Type'} (x : C) (y : C) : (term534 C x y) = (term534 C x y).
Proof. exact (eq_refl (term534 C x y)). Qed.
Lemma lem6154123 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term535 C y x z).
Proof. exact (MK_COMB (@lem6154122 C x y) (@lem6154112 C y x z)). Qed.
Lemma lem6154127 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6154128 {C : Type'} (y : C) (x : C) (z : C) : (term535 C y x z) = (term536 C y x z).
Proof. exact (@lem6154127 (y = z) (term389 C x y) (term389 C x z)). Qed.
Lemma lem6154150 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term536 C y x z).
Proof. exact (TRANS (@lem6154123 C y x z) (@lem6154128 C y x z)). Qed.
Lemma lem6154151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6154152 {C : Type'} (y : C) (x : C) (z : C) : (term537 C x y z) = (term538 C y x z).
Proof. exact (MK_COMB (@lem6154151) (@lem6154150 C y x z)). Qed.
Lemma lem6154174 {C : Type'} (y : C) (x : C) (z : C) : (term536 C y x z) = (term536 C y x z).
Proof. exact (eq_refl (term536 C y x z)). Qed.
Lemma lem6154175 {C : Type'} (y : C) (x : C) (z : C) : ((term527 C x y z) = (term536 C y x z)) = ((term536 C y x z) = (term536 C y x z)).
Proof. exact (MK_COMB (@lem6154152 C y x z) (@lem6154174 C y x z)). Qed.
Lemma lem6154177 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6154178 (x : Prop) : (x = x) = True.
Proof. exact (@lem6154177 Prop x). Qed.
Lemma lem6154179 {C : Type'} (y : C) (x : C) (z : C) : ((term536 C y x z) = (term536 C y x z)) = True.
Proof. exact (@lem6154178 (term536 C y x z)). Qed.
Lemma lem6154180 {C : Type'} (y : C) (x : C) (z : C) : ((term527 C x y z) = (term536 C y x z)) = True.
Proof. exact (TRANS (@lem6154175 C y x z) (@lem6154179 C y x z)). Qed.
Lemma lem6154181 {C : Type'} (y : C) (x : C) (z : C) : True = ((term527 C x y z) = (term536 C y x z)).
Proof. exact (SYM (@lem6154180 C y x z)). Qed.
Lemma lem6154182 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term536 C y x z).
Proof. exact (EQ_MP (@lem6154181 C y x z) (@lem0)). Qed.
Lemma lem6154183 {C : Type'} (y : C) (x : C) (z : C) : term536 C y x z.
Proof. exact (EQ_MP (@lem6154182 C y x z) (@lem6153974 C x y z)). Qed.
Lemma lem6154185 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6154186 {C : Type'} (x : C) (y : C) (z : C) : (term536 C y x z) = (term539 C x y z).
Proof. exact (@lem6154185 (term540 C y x z) (y = z)). Qed.
Lemma lem6154188 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6154189 {C : Type'} (y : C) (x : C) (z : C) : (term541 C y x z) = (term542 C y x z).
Proof. exact (@lem6154188 (term389 C x y) (term389 C x z)). Qed.
Lemma lem6154191 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6154192 {C : Type'} (x : C) (y : C) : (term382 C x y) = (x = y).
Proof. exact (@lem6154191 (x = y)). Qed.
Lemma lem6154193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6154194 {C : Type'} (x : C) (y : C) : (term543 C x y) = (term544 C x y).
Proof. exact (MK_COMB (@lem6154193) (@lem6154192 C x y)). Qed.
Lemma lem6154196 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6154197 {C : Type'} (x : C) (z : C) : (term382 C x z) = (x = z).
Proof. exact (@lem6154196 (x = z)). Qed.
Lemma lem6154198 {C : Type'} (y : C) (x : C) (z : C) : (term542 C y x z) = (term545 C y x z).
Proof. exact (MK_COMB (@lem6154194 C x y) (@lem6154197 C x z)). Qed.
Lemma lem6154199 {C : Type'} (y : C) (x : C) (z : C) : (term541 C y x z) = (term545 C y x z).
Proof. exact (TRANS (@lem6154189 C y x z) (@lem6154198 C y x z)). Qed.
Lemma lem6154200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6154201 {C : Type'} (y : C) (x : C) (z : C) : (term546 C y x z) = (term547 C y x z).
Proof. exact (MK_COMB (@lem6154200) (@lem6154199 C y x z)). Qed.
Lemma lem6154202 {C : Type'} (y : C) (z : C) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6154203 {C : Type'} (x : C) (y : C) (z : C) : (term539 C x y z) = (term548 C x y z).
Proof. exact (MK_COMB (@lem6154201 C y x z) (@lem6154202 C y z)). Qed.
Lemma lem6154204 {C : Type'} (x : C) (y : C) (z : C) : (term536 C y x z) = (term548 C x y z).
Proof. exact (TRANS (@lem6154186 C x y z) (@lem6154203 C x y z)). Qed.
Lemma lem6154206 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : term1330 A B C op f s g.
Proof. exact (conj (@lem6154084 A B C f s g op h1 h2) (@lem6154093 A B C op f s g)). Qed.
Lemma lem6154208 {C : Type'} (x : C) (y : C) (z : C) : term548 C x y z.
Proof. exact (EQ_MP (@lem6154204 C x y z) (@lem6154183 C y x z)). Qed.
Lemma lem6154209 {C : Type'} (x : C) (y : C) (z : C) : term548 C x y z.
Proof. exact (@lem6154208 C x y z). Qed.
Lemma lem6154210 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term1331 A B C op f s g.
Proof. exact (@lem6154209 C (term975 A B C op f s g) (term707 A B C op f s g) (term975 A B C op f s g)). Qed.
Lemma lem6154213 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term707 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (@lem6154210 A B C op f s g (@lem6154206 A B C f s g op h1 h2)). Qed.
Lemma lem6154214 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term707 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (@lem6154213 A B C f s g op h1 h2). Qed.
Lemma lem6154215 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : term1332 A B C op f s g.
Proof. exact (fun h0 : term976 A B C op f s g => @lem6154214 A B C f s g op h1 h2). Qed.
Lemma lem6154217 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154218 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1332 A B C op f s g) = ((term707 A B C op f s g) = (term975 A B C op f s g)).
Proof. exact (@lem6154217 ((term707 A B C op f s g) = (term975 A B C op f s g))). Qed.
Lemma lem6154219 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term707 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (EQ_MP (@lem6154218 A B C op f s g) (@lem6154215 A B C f s g op h1 h2)). Qed.
Lemma lem6154222 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6154224 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term976 A B C op f s g) = (term1333 A B C op f s g).
Proof. exact (@lem6154222 ((term707 A B C op f s g) = (term975 A B C op f s g))). Qed.
Lemma lem6154227 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term927 A B C op f s g) : term1333 A B C op f s g.
Proof. exact (EQ_MP (@lem6154224 A B C op f s g) (@lem6153235 A B C op f s g h1)). Qed.
Lemma lem6154230 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term603 C) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) : False.
Proof. exact (@lem6154227 A B C op f s g h3 (@lem6154219 A B C f s g op h1 h2)). Qed.
Lemma lem6154231 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term603 C) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) : term526.
Proof. exact (fun h0 : ~ False => @lem6154230 A B C op f s g h1 h2 h3). Qed.
Lemma lem6154233 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154234 : term526 = False.
Proof. exact (@lem6154233 False). Qed.
Lemma lem6154235 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term603 C) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) : False.
Proof. exact (EQ_MP (@lem6154234) (@lem6154231 A B C op f s g h1 h2 h3)). Qed.
Lemma lem6154649 {C : Type'} (x : C) (y : C) (z : C) : term527 C x y z.
Proof. exact (@lem21385 C x y z). Qed.
Lemma lem6154707 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @I ((C -> C -> C) -> Prop) (@monoidal C) op.
Proof. exact (EQ_MP (@lem6148669 C op) (@lem6147877 C op h1)). Qed.
Lemma lem6154708 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term1317 C op.
Proof. exact (fun h0 : term1032 C op => @lem6154707 C op h1). Qed.
Lemma lem6154710 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154711 {C : Type'} (op : type1400 C) : (term1317 C op) = (@I ((C -> C -> C) -> Prop) (@monoidal C) op).
Proof. exact (@lem6154710 (@I ((C -> C -> C) -> Prop) (@monoidal C) op)). Qed.
Lemma lem6154712 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @I ((C -> C -> C) -> Prop) (@monoidal C) op.
Proof. exact (EQ_MP (@lem6154711 C op) (@lem6154708 C op h1)). Qed.
Lemma lem6154718 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6154719 {C : Type'} (_77422 : C) (_77421 : type1400 C) : (term1316 C _77421 _77422) = (term1318 C _77422 _77421).
Proof. exact (@lem6154718 ((term1024 C _77421 _77422) = _77422) (term1032 C _77421)). Qed.
Lemma lem6154727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6154728 {C : Type'} (_77422 : C) (_77421 : type1400 C) : (term1319 C _77421 _77422) = (term1320 C _77422 _77421).
Proof. exact (MK_COMB (@lem6154727) (@lem6154719 C _77422 _77421)). Qed.
Lemma lem6154736 {C : Type'} (_77422 : C) (_77421 : type1400 C) : (term1318 C _77422 _77421) = (term1318 C _77422 _77421).
Proof. exact (eq_refl (term1318 C _77422 _77421)). Qed.
Lemma lem6154737 {C : Type'} (_77422 : C) (_77421 : type1400 C) : ((term1316 C _77421 _77422) = (term1318 C _77422 _77421)) = ((term1318 C _77422 _77421) = (term1318 C _77422 _77421)).
Proof. exact (MK_COMB (@lem6154728 C _77422 _77421) (@lem6154736 C _77422 _77421)). Qed.
Lemma lem6154739 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6154740 (x : Prop) : (x = x) = True.
Proof. exact (@lem6154739 Prop x). Qed.
Lemma lem6154741 {C : Type'} (_77422 : C) (_77421 : type1400 C) : ((term1318 C _77422 _77421) = (term1318 C _77422 _77421)) = True.
Proof. exact (@lem6154740 (term1318 C _77422 _77421)). Qed.
Lemma lem6154742 {C : Type'} (_77422 : C) (_77421 : type1400 C) : ((term1316 C _77421 _77422) = (term1318 C _77422 _77421)) = True.
Proof. exact (TRANS (@lem6154737 C _77422 _77421) (@lem6154741 C _77422 _77421)). Qed.
Lemma lem6154743 {C : Type'} (_77422 : C) (_77421 : type1400 C) : True = ((term1316 C _77421 _77422) = (term1318 C _77422 _77421)).
Proof. exact (SYM (@lem6154742 C _77422 _77421)). Qed.
Lemma lem6154744 {C : Type'} (_77422 : C) (_77421 : type1400 C) : (term1316 C _77421 _77422) = (term1318 C _77422 _77421).
Proof. exact (EQ_MP (@lem6154743 C _77422 _77421) (@lem0)). Qed.
Lemma lem6154745 {C : Type'} (_77422 : C) (_77421 : type1400 C) (h1 : term603 C) : term1318 C _77422 _77421.
Proof. exact (EQ_MP (@lem6154744 C _77422 _77421) (@lem6153455 C _77421 _77422 h1)). Qed.
Lemma lem6154747 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6154748 {C : Type'} (_77421 : type1400 C) (_77422 : C) : (term1318 C _77422 _77421) = (term1321 C _77421 _77422).
Proof. exact (@lem6154747 (term1032 C _77421) ((term1024 C _77421 _77422) = _77422)). Qed.
Lemma lem6154750 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6154751 {C : Type'} (_77421 : type1400 C) : (term1322 C _77421) = (@I ((C -> C -> C) -> Prop) (@monoidal C) _77421).
Proof. exact (@lem6154750 (@I ((C -> C -> C) -> Prop) (@monoidal C) _77421)). Qed.
Lemma lem6154752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6154753 {C : Type'} (_77421 : type1400 C) : (term1323 C _77421) = (term1324 C _77421).
Proof. exact (MK_COMB (@lem6154752) (@lem6154751 C _77421)). Qed.
Lemma lem6154754 {C : Type'} (_77421 : type1400 C) (_77422 : C) : ((term1024 C _77421 _77422) = _77422) = ((term1024 C _77421 _77422) = _77422).
Proof. exact (eq_refl ((term1024 C _77421 _77422) = _77422)). Qed.
Lemma lem6154755 {C : Type'} (_77421 : type1400 C) (_77422 : C) : (term1321 C _77421 _77422) = (term1325 C _77421 _77422).
Proof. exact (MK_COMB (@lem6154753 C _77421) (@lem6154754 C _77421 _77422)). Qed.
Lemma lem6154756 {C : Type'} (_77421 : type1400 C) (_77422 : C) : (term1318 C _77422 _77421) = (term1325 C _77421 _77422).
Proof. exact (TRANS (@lem6154748 C _77421 _77422) (@lem6154755 C _77421 _77422)). Qed.
Lemma lem6154759 {C : Type'} (_77421 : type1400 C) (_77422 : C) (h1 : term603 C) : term1325 C _77421 _77422.
Proof. exact (EQ_MP (@lem6154756 C _77421 _77422) (@lem6154745 C _77422 _77421 h1)). Qed.
Lemma lem6154760 {C : Type'} (_77421 : type1400 C) (_77422 : C) (h1 : term603 C) : term1325 C _77421 _77422.
Proof. exact (@lem6154759 C _77421 _77422 h1). Qed.
Lemma lem6154761 {C : Type'} (op : type1400 C) (_77422 : C) (h1 : term603 C) : term1325 C op _77422.
Proof. exact (@lem6154760 C op _77422 h1). Qed.
Lemma lem6154764 {C : Type'} (_77422 : C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term1024 C op _77422) = _77422.
Proof. exact (@lem6154761 C op _77422 h1 (@lem6154712 C op h2)). Qed.
Lemma lem6154765 {C : Type'} (_77422 : C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term1024 C op _77422) = _77422.
Proof. exact (@lem6154764 C _77422 op h1 h2). Qed.
Lemma lem6154766 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term975 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (@lem6154765 C (term707 A B C op f s g) op h1 h2). Qed.
Lemma lem6154767 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : term1326 A B C op f s g.
Proof. exact (fun h0 : term1327 A B C op f s g => @lem6154766 A B C f s g op h1 h2). Qed.
Lemma lem6154769 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154770 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1326 A B C op f s g) = ((term975 A B C op f s g) = (term707 A B C op f s g)).
Proof. exact (@lem6154769 ((term975 A B C op f s g) = (term707 A B C op f s g))). Qed.
Lemma lem6154771 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term975 A B C op f s g) = (term707 A B C op f s g).
Proof. exact (EQ_MP (@lem6154770 A B C op f s g) (@lem6154767 A B C f s g op h1 h2)). Qed.
Lemma lem6154773 {C : Type'} (x : C) : x = x.
Proof. exact (@lem21386 C x). Qed.
Lemma lem6154774 {C : Type'} (x : C) : x = x.
Proof. exact (@lem6154773 C x). Qed.
Lemma lem6154775 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term975 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (@lem6154774 C (term975 A B C op f s g)). Qed.
Lemma lem6154776 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term1328 A B C op f s g.
Proof. exact (fun h0 : term1329 A B C op f s g => @lem6154775 A B C op f s g). Qed.
Lemma lem6154778 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154779 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1328 A B C op f s g) = ((term975 A B C op f s g) = (term975 A B C op f s g)).
Proof. exact (@lem6154778 ((term975 A B C op f s g) = (term975 A B C op f s g))). Qed.
Lemma lem6154780 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term975 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (EQ_MP (@lem6154779 A B C op f s g) (@lem6154776 A B C op f s g)). Qed.
Lemma lem6154798 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6154799 {C : Type'} (y : C) (x : C) (z : C) : (term532 C x y z) = (term533 C y x z).
Proof. exact (@lem6154798 (y = z) (term389 C x z)). Qed.
Lemma lem6154809 {C : Type'} (x : C) (y : C) : (term534 C x y) = (term534 C x y).
Proof. exact (eq_refl (term534 C x y)). Qed.
Lemma lem6154810 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term535 C y x z).
Proof. exact (MK_COMB (@lem6154809 C x y) (@lem6154799 C y x z)). Qed.
Lemma lem6154814 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6154815 {C : Type'} (y : C) (x : C) (z : C) : (term535 C y x z) = (term536 C y x z).
Proof. exact (@lem6154814 (y = z) (term389 C x y) (term389 C x z)). Qed.
Lemma lem6154837 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term536 C y x z).
Proof. exact (TRANS (@lem6154810 C y x z) (@lem6154815 C y x z)). Qed.
Lemma lem6154838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6154839 {C : Type'} (y : C) (x : C) (z : C) : (term537 C x y z) = (term538 C y x z).
Proof. exact (MK_COMB (@lem6154838) (@lem6154837 C y x z)). Qed.
Lemma lem6154861 {C : Type'} (y : C) (x : C) (z : C) : (term536 C y x z) = (term536 C y x z).
Proof. exact (eq_refl (term536 C y x z)). Qed.
Lemma lem6154862 {C : Type'} (y : C) (x : C) (z : C) : ((term527 C x y z) = (term536 C y x z)) = ((term536 C y x z) = (term536 C y x z)).
Proof. exact (MK_COMB (@lem6154839 C y x z) (@lem6154861 C y x z)). Qed.
Lemma lem6154864 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6154865 (x : Prop) : (x = x) = True.
Proof. exact (@lem6154864 Prop x). Qed.
Lemma lem6154866 {C : Type'} (y : C) (x : C) (z : C) : ((term536 C y x z) = (term536 C y x z)) = True.
Proof. exact (@lem6154865 (term536 C y x z)). Qed.
Lemma lem6154867 {C : Type'} (y : C) (x : C) (z : C) : ((term527 C x y z) = (term536 C y x z)) = True.
Proof. exact (TRANS (@lem6154862 C y x z) (@lem6154866 C y x z)). Qed.
Lemma lem6154868 {C : Type'} (y : C) (x : C) (z : C) : True = ((term527 C x y z) = (term536 C y x z)).
Proof. exact (SYM (@lem6154867 C y x z)). Qed.
Lemma lem6154869 {C : Type'} (y : C) (x : C) (z : C) : (term527 C x y z) = (term536 C y x z).
Proof. exact (EQ_MP (@lem6154868 C y x z) (@lem0)). Qed.
Lemma lem6154870 {C : Type'} (y : C) (x : C) (z : C) : term536 C y x z.
Proof. exact (EQ_MP (@lem6154869 C y x z) (@lem6154649 C x y z)). Qed.
Lemma lem6154872 (b : Prop) (a : Prop) : (a \/ b) = (term503 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6154873 {C : Type'} (x : C) (y : C) (z : C) : (term536 C y x z) = (term539 C x y z).
Proof. exact (@lem6154872 (term540 C y x z) (y = z)). Qed.
Lemma lem6154875 (a : Prop) (b : Prop) : (term505 a b) = (term506 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6154876 {C : Type'} (y : C) (x : C) (z : C) : (term541 C y x z) = (term542 C y x z).
Proof. exact (@lem6154875 (term389 C x y) (term389 C x z)). Qed.
Lemma lem6154878 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6154879 {C : Type'} (x : C) (y : C) : (term382 C x y) = (x = y).
Proof. exact (@lem6154878 (x = y)). Qed.
Lemma lem6154880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6154881 {C : Type'} (x : C) (y : C) : (term543 C x y) = (term544 C x y).
Proof. exact (MK_COMB (@lem6154880) (@lem6154879 C x y)). Qed.
Lemma lem6154883 (a : Prop) : (term290 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6154884 {C : Type'} (x : C) (z : C) : (term382 C x z) = (x = z).
Proof. exact (@lem6154883 (x = z)). Qed.
Lemma lem6154885 {C : Type'} (y : C) (x : C) (z : C) : (term542 C y x z) = (term545 C y x z).
Proof. exact (MK_COMB (@lem6154881 C x y) (@lem6154884 C x z)). Qed.
Lemma lem6154886 {C : Type'} (y : C) (x : C) (z : C) : (term541 C y x z) = (term545 C y x z).
Proof. exact (TRANS (@lem6154876 C y x z) (@lem6154885 C y x z)). Qed.
Lemma lem6154887 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6154888 {C : Type'} (y : C) (x : C) (z : C) : (term546 C y x z) = (term547 C y x z).
Proof. exact (MK_COMB (@lem6154887) (@lem6154886 C y x z)). Qed.
Lemma lem6154889 {C : Type'} (y : C) (z : C) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6154890 {C : Type'} (x : C) (y : C) (z : C) : (term539 C x y z) = (term548 C x y z).
Proof. exact (MK_COMB (@lem6154888 C y x z) (@lem6154889 C y z)). Qed.
Lemma lem6154891 {C : Type'} (x : C) (y : C) (z : C) : (term536 C y x z) = (term548 C x y z).
Proof. exact (TRANS (@lem6154873 C x y z) (@lem6154890 C x y z)). Qed.
Lemma lem6154893 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : term1330 A B C op f s g.
Proof. exact (conj (@lem6154771 A B C f s g op h1 h2) (@lem6154780 A B C op f s g)). Qed.
Lemma lem6154895 {C : Type'} (x : C) (y : C) (z : C) : term548 C x y z.
Proof. exact (EQ_MP (@lem6154891 C x y z) (@lem6154870 C y x z)). Qed.
Lemma lem6154896 {C : Type'} (x : C) (y : C) (z : C) : term548 C x y z.
Proof. exact (@lem6154895 C x y z). Qed.
Lemma lem6154897 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term1331 A B C op f s g.
Proof. exact (@lem6154896 C (term975 A B C op f s g) (term707 A B C op f s g) (term975 A B C op f s g)). Qed.
Lemma lem6154900 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term707 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (@lem6154897 A B C op f s g (@lem6154893 A B C f s g op h1 h2)). Qed.
Lemma lem6154901 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term707 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (@lem6154900 A B C f s g op h1 h2). Qed.
Lemma lem6154902 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : term1332 A B C op f s g.
Proof. exact (fun h0 : term976 A B C op f s g => @lem6154901 A B C f s g op h1 h2). Qed.
Lemma lem6154904 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154905 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1332 A B C op f s g) = ((term707 A B C op f s g) = (term975 A B C op f s g)).
Proof. exact (@lem6154904 ((term707 A B C op f s g) = (term975 A B C op f s g))). Qed.
Lemma lem6154906 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : term603 C) (h2 : @monoidal C op) : (term707 A B C op f s g) = (term975 A B C op f s g).
Proof. exact (EQ_MP (@lem6154905 A B C op f s g) (@lem6154902 A B C f s g op h1 h2)). Qed.
Lemma lem6154909 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6154911 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term976 A B C op f s g) = (term1333 A B C op f s g).
Proof. exact (@lem6154909 ((term707 A B C op f s g) = (term975 A B C op f s g))). Qed.
Lemma lem6154914 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term927 A B C op f s g) : term1333 A B C op f s g.
Proof. exact (EQ_MP (@lem6154911 A B C op f s g) (@lem6153443 A B C op f s g h1)). Qed.
Lemma lem6154917 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term603 C) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) : False.
Proof. exact (@lem6154914 A B C op f s g h3 (@lem6154906 A B C f s g op h1 h2)). Qed.
Lemma lem6154918 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term603 C) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) : term526.
Proof. exact (fun h0 : ~ False => @lem6154917 A B C op f s g h1 h2 h3). Qed.
Lemma lem6154920 (p : Prop) : (term475 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6154921 : term526 = False.
Proof. exact (@lem6154920 False). Qed.
Lemma lem6154922 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term603 C) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) : False.
Proof. exact (EQ_MP (@lem6154921) (@lem6154918 A B C op f s g h1 h2 h3)). Qed.
Lemma lem6154923 {A B C : Type'} (x' : A) (y : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) (h4 : term374 A B C x' y op s g f) : False.
Proof. exact (or_elim (@lem6150041 A B C x' y op s g f h4) (fun h0 : term718 A B C s x' g f y op => @lem6154235 A B C op f s g h1 h2 h3) (fun h0 : (term707 A B C op f s g) = (term712 A B C op s g f) => @lem6154922 A B C op f s g h1 h2 h3)). Qed.
Lemma lem6154924 {A B C : Type'} (x' : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (h1 : term603 C) (h2 : term377 A B C x' op s g f) (h3 : @monoidal C op) (h4 : term927 A B C op f s g) : False.
Proof. exact (ex_elim (@lem6148660 A B C x' op s g f h2) (fun y : A => fun h0 : term376 A B C x' op s g f y => @lem6154923 A B C x' y op s g f h1 h3 h4 h0)). Qed.
Lemma lem6154925 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) (h4 : term175 A B C op s g f) : False.
Proof. exact (ex_elim (@lem6148030 A B C op s g f h4) (fun x' : A => fun h0 : term378 A B C op s g f x' => @lem6154924 A B C x' op f s g h1 h0 h2 h3)). Qed.
Lemma lem6154926 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : term559 A B a f s) (h3 : @monoidal C op) (h4 : term927 A B C op f s g) (h5 : term175 A B C op s g f) : False.
Proof. exact (ex_elim (@lem6148205 A B a f s h2) (fun x : A => fun h0 : term684 A B a f s x => @lem6154925 A B C op s g f h1 h3 h4 h5)). Qed.
Lemma lem6154927 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : term559 A B a f s) (h3 : @monoidal C op) (h4 : term927 A B C op f s g) (h5 : term175 A B C op s g f) : (term927 A B C op f s g) = False.
Proof. exact (prop_ext (fun h6 : term927 A B C op f s g => @lem6154926 A B C a op s g f h1 h2 h3 h4 h5) (fun h6 : False => @lem6148211 A B C op f s g h4)). Qed.
Lemma lem6154928 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : term559 A B a f s) (h3 : @monoidal C op) (h4 : term927 A B C op f s g) (h5 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6154927 A B C a op s g f h1 h2 h3 h4 h5) (@lem6148211 A B C op f s g h4)). Qed.
Lemma lem6154929 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : term559 A B a f s) (h3 : @monoidal C op) (h4 : term927 A B C op f s g) (h5 : term175 A B C op s g f) : (term559 A B a f s) = False.
Proof. exact (prop_ext (fun h6 : term559 A B a f s => @lem6154928 A B C a op s g f h1 h2 h3 h4 h5) (fun h6 : False => @lem6148205 A B a f s h2)). Qed.
Lemma lem6154930 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : term559 A B a f s) (h3 : @monoidal C op) (h4 : term927 A B C op f s g) (h5 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6154929 A B C a op s g f h1 h2 h3 h4 h5) (@lem6148205 A B a f s h2)). Qed.
Lemma lem6154931 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : term559 A B a f s) (h3 : @monoidal C op) (h4 : term927 A B C op f s g) (h5 : term175 A B C op s g f) : (@monoidal C op) = False.
Proof. exact (prop_ext (fun h6 : @monoidal C op => @lem6154930 A B C a op s g f h1 h2 h3 h4 h5) (fun h6 : False => @lem6147877 C op h3)). Qed.
Lemma lem6154932 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term603 C) (h2 : term559 A B a f s) (h3 : @monoidal C op) (h4 : term927 A B C op f s g) (h5 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6154931 A B C a op s g f h1 h2 h3 h4 h5) (@lem6147877 C op h3)). Qed.
Lemma lem6154933 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term559 A B a f s) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) (h4 : term175 A B C op s g f) : term608 C.
Proof. exact (fun h0 : term603 C => @lem6154932 A B C a op s g f h0 h1 h2 h3 h4). Qed.
Lemma lem6154934 {C : Type'} : (term608 C) = (term609 C).
Proof. exact (@lem69 (term603 C)). Qed.
Lemma lem6154935 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term559 A B a f s) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) (h4 : term175 A B C op s g f) : term609 C.
Proof. exact (EQ_MP (@lem6154934 C) (@lem6154933 A B C a op s g f h1 h2 h3 h4)). Qed.
Lemma lem6154936 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term559 A B a f s) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) (h4 : term175 A B C op s g f) : term612 B C.
Proof. exact (fun h0 : term603 B => @lem6154935 A B C a op s g f h1 h2 h3 h4). Qed.
Lemma lem6154937 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term559 A B a f s) (h2 : @monoidal C op) (h3 : term927 A B C op f s g) (h4 : term175 A B C op s g f) : term614 A B C.
Proof. exact (fun h0 : term603 A => @lem6154936 A B C a op s g f h1 h2 h3 h4). Qed.
Lemma lem6154938 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term559 A B a f s) (h2 : @monoidal C op) (h3 : term175 A B C op s g f) : term934 A B C op f s g.
Proof. exact (fun h0 : term927 A B C op f s g => @lem6154937 A B C a op s g f h1 h2 h0 h3). Qed.
Lemma lem6154939 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term175 A B C op s g f) : term936 A B C a op f s g.
Proof. exact (fun h0 : term559 A B a f s => @lem6154938 A B C a op s g f h0 h1 h2). Qed.
Lemma lem6154940 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term175 A B C op s g f) : term938 A B C a op f s g.
Proof. exact (fun h0 : term270 A B C a s g f op => @lem6154939 A B C a op s g f h1 h2). Qed.
Lemma lem6154941 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term175 A B C op s g f) : term940 A B C a op f s g.
Proof. exact (fun h0 : @FINITE A s => @lem6154940 A B C a op s g f h1 h2). Qed.
Lemma lem6154942 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term175 A B C op s g f) : term942 A B C a op f s g.
Proof. exact (fun h0 : term180 A a s => @lem6154941 A B C a op s g f h1 h2). Qed.
Lemma lem6154943 {A B C : Type'} (a : A) (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term944 A B C a op f s g.
Proof. exact (fun h0 : term175 A B C op s g f => @lem6154942 A B C a op s g f h1 h0). Qed.
Lemma lem6154944 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term945 A B C a op f s g.
Proof. exact (fun h0 : @monoidal C op => @lem6154943 A B C a f s g op h0). Qed.
Lemma lem6154949 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term949 A B C op f s g.
Proof. exact (fun a : A => @lem6154944 A B C a op f s g). Qed.
Lemma lem6154954 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : term953 A B C f s g.
Proof. exact (fun op : type1400 C => @lem6154949 A B C op f s g). Qed.
Lemma lem6154959 {A B C : Type'} (s : A -> Prop) (g : B -> C) : term957 A B C s g.
Proof. exact (fun f : A -> B => @lem6154954 A B C f s g). Qed.
Lemma lem6154964 {A B C : Type'} (g : B -> C) : term961 A B C g.
Proof. exact (fun s : A -> Prop => @lem6154959 A B C s g). Qed.
Lemma lem6154969 {A B C : Type'} : term965 A B C.
Proof. exact (fun g : B -> C => @lem6154964 A B C g). Qed.
Lemma lem6154970 {A B C : Type'} : term964 A B C.
Proof. exact (EQ_MP (@lem6147861 A B C) (@lem6154969 A B C)). Qed.
Lemma lem6154971 {A B C : Type'} (g : B -> C) : term1334 A B C g.
Proof. exact (@lem6154970 A B C g). Qed.
Lemma lem6154972 {A B C : Type'} (g : B -> C) : (term1334 A B C g) = (term960 A B C g).
Proof. exact (eq_refl (term1334 A B C g)). Qed.
Lemma lem6154973 {A B C : Type'} (g : B -> C) : term960 A B C g.
Proof. exact (EQ_MP (@lem6154972 A B C g) (@lem6154971 A B C g)). Qed.
Lemma lem6154974 {A B C : Type'} (g : B -> C) (s : A -> Prop) : term1335 A B C g s.
Proof. exact (@lem6154973 A B C g s). Qed.
Lemma lem6154975 {A B C : Type'} (s : A -> Prop) (g : B -> C) : (term1335 A B C g s) = (term956 A B C s g).
Proof. exact (eq_refl (term1335 A B C g s)). Qed.
Lemma lem6154976 {A B C : Type'} (s : A -> Prop) (g : B -> C) : term956 A B C s g.
Proof. exact (EQ_MP (@lem6154975 A B C s g) (@lem6154974 A B C g s)). Qed.
Lemma lem6154977 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : term1336 A B C s g f.
Proof. exact (@lem6154976 A B C s g f). Qed.
Lemma lem6154978 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1336 A B C s g f) = (term952 A B C f s g).
Proof. exact (eq_refl (term1336 A B C s g f)). Qed.
Lemma lem6154979 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) : term952 A B C f s g.
Proof. exact (EQ_MP (@lem6154978 A B C f s g) (@lem6154977 A B C s g f)). Qed.
Lemma lem6154980 {A B C : Type'} (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) : term1337 A B C f s g op.
Proof. exact (@lem6154979 A B C f s g op). Qed.
Lemma lem6154981 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1337 A B C f s g op) = (term948 A B C op f s g).
Proof. exact (eq_refl (term1337 A B C f s g op)). Qed.
Lemma lem6154982 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term948 A B C op f s g.
Proof. exact (EQ_MP (@lem6154981 A B C op f s g) (@lem6154980 A B C f s g op)). Qed.
Lemma lem6154983 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) (a : A) : term1338 A B C op f s g a.
Proof. exact (@lem6154982 A B C op f s g a). Qed.
Lemma lem6154984 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term1338 A B C op f s g a) = (term928 A B C a op f s g).
Proof. exact (eq_refl (term1338 A B C op f s g a)). Qed.
Lemma lem6154985 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term928 A B C a op f s g.
Proof. exact (EQ_MP (@lem6154984 A B C a op f s g) (@lem6154983 A B C op f s g a)). Qed.
Lemma lem6154987 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term928 A B C a op f s g.
Proof. exact (@lem6146877 A B C a op f s g (@lem6154985 A B C a op f s g)). Qed.
Lemma lem6154988 {A B C : Type'} (a : A) (f : A -> B) (s : A -> Prop) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term943 A B C a op f s g.
Proof. exact (@lem6154987 A B C a op f s g (@lem6113800 C op h1)). Qed.
Lemma lem6154989 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term175 A B C op s g f) : term941 A B C a op f s g.
Proof. exact (@lem6154988 A B C a f s g op h1 (@lem6135446 A B C op s g f h2)). Qed.
Lemma lem6154990 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term180 A a s) (h3 : term175 A B C op s g f) : term939 A B C a op f s g.
Proof. exact (@lem6154989 A B C a op s g f h1 h3 (@lem6135448 A a s h2)). Qed.
Lemma lem6154991 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : term937 A B C a op f s g.
Proof. exact (@lem6154990 A B C a op s g f h2 h3 h4 (@lem6135447 A s h1)). Qed.
Lemma lem6154992 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term935 A B C a op f s g.
Proof. exact (@lem6154991 A B C a op s g f h2 h3 h4 h5 (@lem6135449 A B C a s g f op h1)). Qed.
Lemma lem6154993 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : term933 A B C op f s g.
Proof. exact (@lem6154992 A B C a op s g f h1 h3 h4 h5 h6 (@lem6137888 A B a f s h2)). Qed.
Lemma lem6154994 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term927 A B C op f s g) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : term613 A B C.
Proof. exact (@lem6154993 A B C a op s g f h1 h2 h3 h4 h6 h7 (@lem6146856 A B C op f s g h5)). Qed.
Lemma lem6154995 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term927 A B C op f s g) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : term611 B C.
Proof. exact (@lem6154994 A B C a op s g f h1 h2 h3 h4 h5 h6 h7 (@lem6146858 A)). Qed.
Lemma lem6154996 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term927 A B C op f s g) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : term608 C.
Proof. exact (@lem6154995 A B C a op s g f h1 h2 h3 h4 h5 h6 h7 (@lem6146859 B)). Qed.
Lemma lem6154997 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term927 A B C op f s g) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : False.
Proof. exact (@lem6154996 A B C a op s g f h1 h2 h3 h4 h5 h6 h7 (@lem6146857 C)). Qed.
Lemma lem6154998 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term927 A B C op f s g) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : (term927 A B C op f s g) = False.
Proof. exact (prop_ext (fun h8 : term927 A B C op f s g => @lem6154997 A B C a op s g f h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem6146856 A B C op f s g h5)). Qed.
Lemma lem6154999 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term927 A B C op f s g) (h6 : term180 A a s) (h7 : term175 A B C op s g f) : False.
Proof. exact (EQ_MP (@lem6154998 A B C a op s g f h1 h2 h3 h4 h5 h6 h7) (@lem6146856 A B C op f s g h5)). Qed.
Lemma lem6155000 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : term926 A B C op f s g.
Proof. exact (fun h0 : term927 A B C op f s g => @lem6154999 A B C a op s g f h1 h2 h3 h4 h0 h5 h6). Qed.
Lemma lem6155001 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : (term33 A B C op f s g) = (term599 A B C op f s g).
Proof. exact (EQ_MP (@lem6146855 A B C op f s g) (@lem6155000 A B C a op s g f h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem6155002 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : (term110 A B C g f a) = (@neutral C op)) (h7 : term175 A B C op s g f) : (term33 A B C op f s g) = (term564 A B C a op f s g).
Proof. exact (EQ_MP (@lem6138023 A B C s g f a op h6) (@lem6155001 A B C a op s g f h1 h2 h3 h4 h5 h7)). Qed.
Lemma lem6155003 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : ((term110 A B C g f a) = (@neutral C op)) = ((term33 A B C op f s g) = (term564 A B C a op f s g)).
Proof. exact (prop_ext (fun h7 : (term110 A B C g f a) = (@neutral C op) => @lem6155002 A B C a op s g f h1 h2 h3 h4 h5 h7 h6) (fun h7 : (term33 A B C op f s g) = (term564 A B C a op f s g) => @lem6146851 A B C a op s g f h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem6155004 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : (term33 A B C op f s g) = (term564 A B C a op f s g).
Proof. exact (EQ_MP (@lem6155003 A B C a op s g f h1 h2 h3 h4 h5 h6) (@lem6146851 A B C a op s g f h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem6155006 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : (term564 A B C a op f s g) = (term279 A B C a op f s g).
Proof. exact (EQ_MP (@lem6138008 A B C a op f s g) (@lem0)). Qed.
Lemma lem6155007 {A B C : Type'} (a : A) (op : type1400 C) (f : A -> B) (s : A -> Prop) (g : B -> C) : term577 A B C a op f s g.
Proof. exact (fun h0 : term1339 A B a f s => @lem6155006 A B C a op f s g). Qed.
Lemma lem6155008 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : (term33 A B C op f s g) = (term279 A B C a op f s g).
Proof. exact (EQ_MP (@lem6137963 A B C a op f s g) (@lem6155004 A B C a op s g f h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem6155009 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : (term559 A B a f s) = ((term33 A B C op f s g) = (term279 A B C a op f s g)).
Proof. exact (prop_ext (fun h7 : term559 A B a f s => @lem6155008 A B C a op s g f h1 h2 h3 h4 h5 h6) (fun h7 : (term33 A B C op f s g) = (term279 A B C a op f s g) => @lem6137888 A B a f s h2)). Qed.
Lemma lem6155010 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : term559 A B a f s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term180 A a s) (h6 : term175 A B C op s g f) : (term33 A B C op f s g) = (term279 A B C a op f s g).
Proof. exact (EQ_MP (@lem6155009 A B C a op s g f h1 h2 h3 h4 h5 h6) (@lem6137888 A B a f s h2)). Qed.
Lemma lem6155011 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term581 A B C a op f s g.
Proof. exact (fun h0 : term559 A B a f s => @lem6155010 A B C a op s g f h1 h0 h2 h3 h4 h5). Qed.
Lemma lem6155012 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : term584 A B C a op f s g.
Proof. exact (conj (@lem6155011 A B C a op s g f h1 h2 h3 h4 h5) (@lem6155007 A B C a op f s g)). Qed.
Lemma lem6155013 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term565 A B C a op f s g) = (term279 A B C a op f s g).
Proof. exact (EQ_MP (@lem6137887 A B C a op f s g) (@lem6155012 A B C a op s g f h1 h2 h3 h4 h5)). Qed.
Lemma lem6155014 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term222 A B C a op f s g) = (term279 A B C a op f s g).
Proof. exact (EQ_MP (@lem6137869 A B C a op f s g) (@lem6155013 A B C a op s g f h1 h2 h3 h4 h5)). Qed.
Lemma lem6155015 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : (term34 A B C op s g f) = (term33 A B C op f s g)) (h6 : term175 A B C op s g f) : (term222 A B C a op f s g) = (term234 A B C a op s g f).
Proof. exact (EQ_MP (@lem6135463 A B C a op f s g h5) (@lem6155014 A B C a op s g f h1 h2 h3 h4 h6)). Qed.
Lemma lem6155016 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : ((term34 A B C op s g f) = (term33 A B C op f s g)) = ((term222 A B C a op f s g) = (term234 A B C a op s g f)).
Proof. exact (prop_ext (fun h6 : (term34 A B C op s g f) = (term33 A B C op f s g) => @lem6155015 A B C a op s g f h1 h2 h3 h4 h6 h5) (fun h6 : (term222 A B C a op f s g) = (term234 A B C a op s g f) => @lem6137842 A B C a op s g f h1 h2 h3 h4 h5)). Qed.
Lemma lem6155017 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term222 A B C a op f s g) = (term234 A B C a op s g f).
Proof. exact (EQ_MP (@lem6155016 A B C a op s g f h1 h2 h3 h4 h5) (@lem6137842 A B C a op s g f h1 h2 h3 h4 h5)). Qed.
Lemma lem6155018 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term270 A B C a s g f op) = ((term222 A B C a op f s g) = (term234 A B C a op s g f)).
Proof. exact (prop_ext (fun h6 : term270 A B C a s g f op => @lem6155017 A B C a op s g f h1 h2 h3 h4 h5) (fun h6 : (term222 A B C a op f s g) = (term234 A B C a op s g f) => @lem6135449 A B C a s g f op h1)). Qed.
Lemma lem6155019 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : term270 A B C a s g f op) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term180 A a s) (h5 : term175 A B C op s g f) : (term222 A B C a op f s g) = (term234 A B C a op s g f).
Proof. exact (EQ_MP (@lem6155018 A B C a op s g f h1 h2 h3 h4 h5) (@lem6135449 A B C a s g f op h1)). Qed.
Lemma lem6155020 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : term273 A B C a op s g f.
Proof. exact (fun h0 : term270 A B C a s g f op => @lem6155019 A B C a op s g f h0 h1 h2 h3 h4). Qed.
Lemma lem6155021 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) (s : A -> Prop) (h1 : term177 A B C op g f a s) : term49 A a s.
Proof. exact (proj2 (@lem6135444 A B C op g f a s h1)). Qed.
Lemma lem6155022 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) (s : A -> Prop) (h1 : term177 A B C op g f a s) : term175 A B C op s g f.
Proof. exact (proj1 (@lem6135444 A B C op g f a s h1)). Qed.
Lemma lem6155023 {A : Type'} (a : A) (s : A -> Prop) (h1 : term49 A a s) : @FINITE A s.
Proof. exact (proj2 (@lem6135445 A a s h1)). Qed.
Lemma lem6155024 {A : Type'} (a : A) (s : A -> Prop) (h1 : term49 A a s) : term180 A a s.
Proof. exact (proj1 (@lem6135445 A a s h1)). Qed.
Lemma lem6155025 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : (@FINITE A s) = (term273 A B C a op s g f).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem6155020 A B C a op s g f h1 h2 h3 h4) (fun h5 : term273 A B C a op s g f => @lem6135447 A s h1)). Qed.
Lemma lem6155026 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : term273 A B C a op s g f.
Proof. exact (EQ_MP (@lem6155025 A B C a op s g f h1 h2 h3 h4) (@lem6135447 A s h1)). Qed.
Lemma lem6155027 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : (term180 A a s) = (term273 A B C a op s g f).
Proof. exact (prop_ext (fun h5 : term180 A a s => @lem6155026 A B C a op s g f h1 h2 h3 h4) (fun h5 : term273 A B C a op s g f => @lem6135448 A a s h3)). Qed.
Lemma lem6155028 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : term180 A a s) (h4 : term175 A B C op s g f) : term273 A B C a op s g f.
Proof. exact (EQ_MP (@lem6155027 A B C a op s g f h1 h2 h3 h4) (@lem6135448 A a s h3)). Qed.
Lemma lem6155029 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term180 A a s) (h3 : term49 A a s) (h4 : term175 A B C op s g f) : (@FINITE A s) = (term273 A B C a op s g f).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem6155028 A B C a op s g f h5 h1 h2 h4) (fun h5 : term273 A B C a op s g f => @lem6155023 A a s h3)). Qed.
Lemma lem6155030 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term180 A a s) (h3 : term49 A a s) (h4 : term175 A B C op s g f) : term273 A B C a op s g f.
Proof. exact (EQ_MP (@lem6155029 A B C a op s g f h1 h2 h3 h4) (@lem6155023 A a s h3)). Qed.
Lemma lem6155031 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term49 A a s) (h3 : term175 A B C op s g f) : (term180 A a s) = (term273 A B C a op s g f).
Proof. exact (prop_ext (fun h4 : term180 A a s => @lem6155030 A B C a op s g f h1 h4 h2 h3) (fun h4 : term273 A B C a op s g f => @lem6155024 A a s h2)). Qed.
Lemma lem6155032 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term49 A a s) (h3 : term175 A B C op s g f) : term273 A B C a op s g f.
Proof. exact (EQ_MP (@lem6155031 A B C a op s g f h1 h2 h3) (@lem6155024 A a s h2)). Qed.
Lemma lem6155033 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term49 A a s) (h3 : term175 A B C op s g f) : (term175 A B C op s g f) = (term273 A B C a op s g f).
Proof. exact (prop_ext (fun h4 : term175 A B C op s g f => @lem6155032 A B C a op s g f h1 h2 h3) (fun h4 : term273 A B C a op s g f => @lem6135446 A B C op s g f h3)). Qed.
Lemma lem6155034 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term49 A a s) (h3 : term175 A B C op s g f) : term273 A B C a op s g f.
Proof. exact (EQ_MP (@lem6155033 A B C a op s g f h1 h2 h3) (@lem6135446 A B C op s g f h3)). Qed.
Lemma lem6155035 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term177 A B C op g f a s) (h3 : term175 A B C op s g f) : (term49 A a s) = (term273 A B C a op s g f).
Proof. exact (prop_ext (fun h4 : term49 A a s => @lem6155034 A B C a op s g f h1 h4 h3) (fun h4 : term273 A B C a op s g f => @lem6155021 A B C op g f a s h2)). Qed.
Lemma lem6155036 {A B C : Type'} (a : A) (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) (h1 : @monoidal C op) (h2 : term177 A B C op g f a s) (h3 : term175 A B C op s g f) : term273 A B C a op s g f.
Proof. exact (EQ_MP (@lem6155035 A B C a op s g f h1 h2 h3) (@lem6155021 A B C op g f a s h2)). Qed.
Lemma lem6155037 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f a s) : (term175 A B C op s g f) = (term273 A B C a op s g f).
Proof. exact (prop_ext (fun h3 : term175 A B C op s g f => @lem6155036 A B C a op s g f h1 h2 h3) (fun h3 : term273 A B C a op s g f => @lem6155022 A B C op g f a s h2)). Qed.
Lemma lem6155038 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) (a : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term177 A B C op g f a s) : term273 A B C a op s g f.
Proof. exact (EQ_MP (@lem6155037 A B C op g f a s h1 h2) (@lem6155022 A B C op g f a s h2)). Qed.
Lemma lem6155039 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term275 A B C a op s g f.
Proof. exact (fun h0 : term177 A B C op g f a s => @lem6155038 A B C op g f a s h1 h0). Qed.
Lemma lem6155040 {A B C : Type'} (a : A) (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term254 A B C a op s g f.
Proof. exact (EQ_MP (@lem6135443 A B C a op s g f) (@lem6155039 A B C a s g f op h1)). Qed.
Lemma lem6155045 {A B C : Type'} (a : A) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term256 A B C a op g f.
Proof. exact (fun s : A -> Prop => @lem6155040 A B C a s g f op h1). Qed.
Lemma lem6155050 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term258 A B C op g f.
Proof. exact (fun a : A => @lem6155045 A B C a g f op h1). Qed.
Lemma lem6155051 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term67 A B C op g f.
Proof. exact (EQ_MP (@lem6135327 A B C g f op h1) (@lem6155050 A B C g f op h1)). Qed.
Lemma lem6155052 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term38 A B C op g f.
Proof. exact (@lem6113844 A B C op g f (@lem6155051 A B C g f op h1)). Qed.
Lemma lem6155053 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term37 A B C op g f.
Proof. exact (EQ_MP (@lem6113811 A B C op g f) (@lem6155052 A B C g f op h1)). Qed.
Lemma lem6155058 {A B C : Type'} (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term1340 A B C op g.
Proof. exact (fun f : A -> B => @lem6155053 A B C g f op h1). Qed.
Lemma lem6155063 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term1341 A B C op.
Proof. exact (fun g : B -> C => @lem6155058 A B C g op h1). Qed.
Lemma lem6155064 {A B C : Type'} (op : type1400 C) : term1342 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem6155063 A B C op h0). Qed.
Lemma lem6155069 {A B C : Type'} : term1343 A B C.
Proof. exact (fun op : type1400 C => @lem6155064 A B C op). Qed.
