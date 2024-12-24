Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1094865_term_abbrevs.
Require Import thm1094488_spec.
Require Import thm1094834_spec.
Lemma lem1094835 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1094836 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1094835 A) (@lem1094488 A)). Qed.
Lemma lem1094837 {A : Type'} : term2 A.
Proof. exact (@lem1094836 A term3). Qed.
Lemma lem1094838 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1094839 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1094838 A) (@lem1094837 A)). Qed.
Lemma lem1094840 {A : Type'} (h1 : (@hd A) = (term5 A)) : (@hd A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1094841 {A : Type'} (h1 : (@hd A) = (term5 A)) : (term5 A) = (@hd A).
Proof. exact (SYM (@lem1094840 A h1)). Qed.
Lemma lem1094842 {A : Type'} (h1 : (term5 A) = (@hd A)) : (term5 A) = (@hd A).
Proof. exact (h1). Qed.
Lemma lem1094843 {A : Type'} (h1 : (term5 A) = (@hd A)) : (@hd A) = (term5 A).
Proof. exact (SYM (@lem1094842 A h1)). Qed.
Lemma lem1094844 {A : Type'} : ((@hd A) = (term5 A)) = ((term5 A) = (@hd A)).
Proof. exact (prop_ext (fun h1 : (@hd A) = (term5 A) => @lem1094841 A h1) (fun h1 : (term5 A) = (@hd A) => @lem1094843 A h1)). Qed.
Lemma lem1094847 {A : Type'} : (term5 A) = (@hd A).
Proof. exact (EQ_MP (@lem1094844 A) (@lem1094834 A)). Qed.
Lemma lem1094848 {A : Type'} : (term5 A) = (@hd A).
Proof. exact (@lem1094847 A). Qed.
Lemma lem1094849 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1094850 {A : Type'} (h : A) (t : list A) : (term6 A h t) = (term7 A h t).
Proof. exact (MK_COMB (@lem1094848 A) (@lem1094849 A h t)). Qed.
Lemma lem1094851 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1094852 {A : Type'} (h : A) (t : list A) : (term8 A h t) = (term9 A h t).
Proof. exact (MK_COMB (@lem1094851 A) (@lem1094850 A h t)). Qed.
Lemma lem1094853 {A : Type'} (h : A) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1094854 {A : Type'} (t : list A) (h : A) : ((term6 A h t) = h) = ((term7 A h t) = h).
Proof. exact (MK_COMB (@lem1094852 A h t) (@lem1094853 A h)). Qed.
Lemma lem1094855 {A : Type'} (t : list A) : (term10 A t) = (term11 A t).
Proof. exact (fun_ext (fun h : A => @lem1094854 A t h)). Qed.
Lemma lem1094856 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1094857 {A : Type'} (t : list A) : (term12 A t) = (term13 A t).
Proof. exact (MK_COMB (@lem1094856 A) (@lem1094855 A t)). Qed.
Lemma lem1094858 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (fun_ext (fun t : list A => @lem1094857 A t)). Qed.
Lemma lem1094859 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1094860 {A : Type'} : (term4 A) = (term16 A).
Proof. exact (MK_COMB (@lem1094859 A) (@lem1094858 A)). Qed.
Lemma lem1094861 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem1094860 A) (@lem1094839 A)). Qed.
Lemma lem1094862 {A : Type'} (t : list A) : term17 A t.
Proof. exact (@lem1094861 A t). Qed.
Lemma lem1094863 {A : Type'} (t : list A) : (term17 A t) = (term13 A t).
Proof. exact (eq_refl (term17 A t)). Qed.
Lemma lem1094864 {A : Type'} (t : list A) : term13 A t.
Proof. exact (EQ_MP (@lem1094863 A t) (@lem1094862 A t)). Qed.
Lemma lem1094865 {A : Type'} (t : list A) (h : A) : term18 A t h.
Proof. exact (@lem1094864 A t h). Qed.
