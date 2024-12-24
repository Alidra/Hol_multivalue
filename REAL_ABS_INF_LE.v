Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_INF_LE_term_abbrevs.
Require Import REAL_BOUNDS_LE_spec.
Require Import REAL_INF_BOUNDS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem5243753 (x : real) (k : real) (h1 : (term0 x k) = (term1 x k)) : (term0 x k) = (term1 x k).
Proof. exact (h1). Qed.
Lemma lem5243754 (x : real) (k : real) (h1 : (term0 x k) = (term1 x k)) : (term1 x k) = (term0 x k).
Proof. exact (SYM (@lem5243753 x k h1)). Qed.
Lemma lem5243755 (x : real) (k : real) (h1 : (term1 x k) = (term0 x k)) : (term1 x k) = (term0 x k).
Proof. exact (h1). Qed.
Lemma lem5243756 (x : real) (k : real) (h1 : (term1 x k) = (term0 x k)) : (term0 x k) = (term1 x k).
Proof. exact (SYM (@lem5243755 x k h1)). Qed.
Lemma lem5243757 (x : real) (k : real) : ((term0 x k) = (term1 x k)) = ((term1 x k) = (term0 x k)).
Proof. exact (prop_ext (fun h1 : (term0 x k) = (term1 x k) => @lem5243754 x k h1) (fun h1 : (term1 x k) = (term0 x k) => @lem5243756 x k h1)). Qed.
Lemma lem5243758 (x : real) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun k : real => @lem5243757 x k)). Qed.
Lemma lem5243759 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243760 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem5243759) (@lem5243758 x)). Qed.
Lemma lem5243761 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem5243760 x)). Qed.
Lemma lem5243762 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243763 : term8 = term9.
Proof. exact (MK_COMB (@lem5243762) (@lem5243761)). Qed.
Lemma lem5243764 : term9.
Proof. exact (EQ_MP (@lem5243763) (@lem1553652)). Qed.
Lemma lem5243765 (s : real -> Prop) : term10 s.
Proof. exact (@lem5243750 s). Qed.
Lemma lem5243766 (s : real -> Prop) : (term10 s) = (term11 s).
Proof. exact (eq_refl (term10 s)). Qed.
Lemma lem5243767 (s : real -> Prop) : term11 s.
Proof. exact (EQ_MP (@lem5243766 s) (@lem5243765 s)). Qed.
Lemma lem5243768 (s : real -> Prop) (a : real) : term12 s a.
Proof. exact (@lem5243767 s a). Qed.
Lemma lem5243769 (a : real) (s : real -> Prop) : (term12 s a) = (term13 a s).
Proof. exact (eq_refl (term12 s a)). Qed.
Lemma lem5243770 (a : real) (s : real -> Prop) : term13 a s.
Proof. exact (EQ_MP (@lem5243769 a s) (@lem5243768 s a)). Qed.
Lemma lem5243771 (a : real) (s : real -> Prop) (b : real) : term14 a s b.
Proof. exact (@lem5243770 a s b). Qed.
Lemma lem5243772 (a : real) (s : real -> Prop) (b : real) : (term14 a s b) = (term15 a s b).
Proof. exact (eq_refl (term14 a s b)). Qed.
Lemma lem5243773 (a : real) (s : real -> Prop) (b : real) : term15 a s b.
Proof. exact (EQ_MP (@lem5243772 a s b) (@lem5243771 a s b)). Qed.
Lemma lem5243774 (a : real) (s : real -> Prop) (b : real) : (term15 a s b) = ((term15 a s b) = True).
Proof. exact (@lem7 (term15 a s b)). Qed.
Lemma lem5243776 (x : real) : term16 x.
Proof. exact (@lem5243764 x). Qed.
Lemma lem5243777 (x : real) : (term16 x) = (term5 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem5243778 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem5243777 x) (@lem5243776 x)). Qed.
Lemma lem5243779 (x : real) (k : real) : term17 x k.
Proof. exact (@lem5243778 x k). Qed.
Lemma lem5243780 (x : real) (k : real) : (term17 x k) = ((term1 x k) = (term0 x k)).
Proof. exact (eq_refl (term17 x k)). Qed.
Lemma lem5243803 (x : real) (k : real) : (term1 x k) = (term0 x k).
Proof. exact (EQ_MP (@lem5243780 x k) (@lem5243779 x k)). Qed.
Lemma lem5243804 (x : real) (a : real) : (term1 x a) = (term0 x a).
Proof. exact (@lem5243803 x a). Qed.
Lemma lem5243807 (x : real) (s : real -> Prop) : (term18 x s) = (term18 x s).
Proof. exact (eq_refl (term18 x s)). Qed.
Lemma lem5243808 (s : real -> Prop) (x : real) (a : real) : (term19 s x a) = (term20 s x a).
Proof. exact (MK_COMB (@lem5243807 x s) (@lem5243804 x a)). Qed.
Lemma lem5243811 (s : real -> Prop) (a : real) : (term21 s a) = (term22 s a).
Proof. exact (fun_ext (fun x : real => @lem5243808 s x a)). Qed.
Lemma lem5243812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243813 (s : real -> Prop) (a : real) : (term23 s a) = (term24 s a).
Proof. exact (MK_COMB (@lem5243812) (@lem5243811 s a)). Qed.
Lemma lem5243818 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (eq_refl (term25 s)). Qed.
Lemma lem5243819 (s : real -> Prop) (a : real) : (term26 s a) = (term27 s a).
Proof. exact (MK_COMB (@lem5243818 s) (@lem5243813 s a)). Qed.
Lemma lem5243822 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5243823 (s : real -> Prop) (a : real) : (term28 s a) = (term29 s a).
Proof. exact (MK_COMB (@lem5243822) (@lem5243819 s a)). Qed.
Lemma lem5243825 (x : real) (k : real) : (term1 x k) = (term0 x k).
Proof. exact (EQ_MP (@lem5243780 x k) (@lem5243779 x k)). Qed.
Lemma lem5243826 (s : real -> Prop) (a : real) : (term30 s a) = (term31 s a).
Proof. exact (@lem5243825 (inf s) a). Qed.
Lemma lem5243829 (s : real -> Prop) (a : real) : (term32 s a) = (term33 s a).
Proof. exact (MK_COMB (@lem5243823 s a) (@lem5243826 s a)). Qed.
Lemma lem5243831 (a : real) (s : real -> Prop) (b : real) : (term15 a s b) = True.
Proof. exact (EQ_MP (@lem5243774 a s b) (@lem5243773 a s b)). Qed.
Lemma lem5243832 (s : real -> Prop) (a : real) : (term33 s a) = True.
Proof. exact (@lem5243831 (real_neg a) s a). Qed.
Lemma lem5243833 (s : real -> Prop) (a : real) : (term32 s a) = True.
Proof. exact (TRANS (@lem5243829 s a) (@lem5243832 s a)). Qed.
Lemma lem5243834 (s : real -> Prop) : (term34 s) = term35.
Proof. exact (fun_ext (fun a : real => @lem5243833 s a)). Qed.
Lemma lem5243835 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243836 (s : real -> Prop) : (term36 s) = term37.
Proof. exact (MK_COMB (@lem5243835) (@lem5243834 s)). Qed.
Lemma lem5243838 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5243839 (t : Prop) : (term39 t) = t.
Proof. exact (@lem5243838 real t). Qed.
Lemma lem5243840 : term37 = True.
Proof. exact (@lem5243839 True). Qed.
Lemma lem5243841 (s : real -> Prop) : (term36 s) = True.
Proof. exact (TRANS (@lem5243836 s) (@lem5243840)). Qed.
Lemma lem5243842 : term40 = term41.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5243841 s)). Qed.
Lemma lem5243843 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5243844 : term42 = term43.
Proof. exact (MK_COMB (@lem5243843) (@lem5243842)). Qed.
Lemma lem5243846 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5243847 (t : Prop) : (term44 t) = t.
Proof. exact (@lem5243846 (real -> Prop) t). Qed.
Lemma lem5243848 : term43 = True.
Proof. exact (@lem5243847 True). Qed.
Lemma lem5243849 : term42 = True.
Proof. exact (TRANS (@lem5243844) (@lem5243848)). Qed.
Lemma lem5243850 : True = term42.
Proof. exact (SYM (@lem5243849)). Qed.
Lemma lem5243851 : term42.
Proof. exact (EQ_MP (@lem5243850) (@lem0)). Qed.
