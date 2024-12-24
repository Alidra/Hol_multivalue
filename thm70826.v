Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm70826_term_abbrevs.
Require Import thm70623_spec.
Require Import thm70773_spec.
Require Import thm9396_spec.
Lemma lem70774 (P : ind -> Prop) : term0 P.
Proof. exact (@lem9396 ind P). Qed.
Lemma lem70775 : term1.
Proof. exact (@lem70774 term2). Qed.
Lemma lem70776 : term3.
Proof. exact (@lem70775 (@lem70623)). Qed.
Lemma lem70777 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem70778 : term4.
Proof. exact (EQ_MP (@lem70777) (@lem70776)). Qed.
Lemma lem70779 (h1 : IND_0 = term5) : IND_0 = term5.
Proof. exact (h1). Qed.
Lemma lem70780 (h1 : IND_0 = term5) : term5 = IND_0.
Proof. exact (SYM (@lem70779 h1)). Qed.
Lemma lem70781 (h1 : term5 = IND_0) : term5 = IND_0.
Proof. exact (h1). Qed.
Lemma lem70782 (h1 : term5 = IND_0) : IND_0 = term5.
Proof. exact (SYM (@lem70781 h1)). Qed.
Lemma lem70783 : (IND_0 = term5) = (term5 = IND_0).
Proof. exact (prop_ext (fun h1 : IND_0 = term5 => @lem70780 h1) (fun h1 : term5 = IND_0 => @lem70782 h1)). Qed.
Lemma lem70808 : term5 = IND_0.
Proof. exact (EQ_MP (@lem70783) (@lem70773)). Qed.
Lemma lem70809 (x : ind) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem70810 (x : ind) : ((IND_SUC x) = term5) = ((IND_SUC x) = IND_0).
Proof. exact (MK_COMB (@lem70809 x) (@lem70808)). Qed.
Lemma lem70813 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem70814 (x : ind) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem70813) (@lem70810 x)). Qed.
Lemma lem70815 : term9 = term10.
Proof. exact (fun_ext (fun x : ind => @lem70814 x)). Qed.
Lemma lem70816 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem70817 : term11 = term12.
Proof. exact (MK_COMB (@lem70816) (@lem70815)). Qed.
Lemma lem70822 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem70823 : term4 = term14.
Proof. exact (MK_COMB (@lem70822) (@lem70817)). Qed.
Lemma lem70826 : term14.
Proof. exact (EQ_MP (@lem70823) (@lem70778)). Qed.
