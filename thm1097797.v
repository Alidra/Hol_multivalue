Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1097797_term_abbrevs.
Require Import thm1097384_spec.
Require Import thm1097740_spec.
Lemma lem1097741 {A B : Type'} : (term0 A B) = (term1 A B).
Proof. exact (eq_refl (term0 A B)). Qed.
Lemma lem1097742 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem1097741 A B) (@lem1097384 A B)). Qed.
Lemma lem1097743 {A B : Type'} : term2 A B.
Proof. exact (@lem1097742 A B term3). Qed.
Lemma lem1097744 {A B : Type'} : (term2 A B) = (term4 A B).
Proof. exact (eq_refl (term2 A B)). Qed.
Lemma lem1097745 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem1097744 A B) (@lem1097743 A B)). Qed.
Lemma lem1097746 {A B : Type'} (h1 : (@List.map A B) = (term5 A B)) : (@List.map A B) = (term5 A B).
Proof. exact (h1). Qed.
Lemma lem1097747 {A B : Type'} (h1 : (@List.map A B) = (term5 A B)) : (term5 A B) = (@List.map A B).
Proof. exact (SYM (@lem1097746 A B h1)). Qed.
Lemma lem1097748 {A B : Type'} (h1 : (term5 A B) = (@List.map A B)) : (term5 A B) = (@List.map A B).
Proof. exact (h1). Qed.
Lemma lem1097749 {A B : Type'} (h1 : (term5 A B) = (@List.map A B)) : (@List.map A B) = (term5 A B).
Proof. exact (SYM (@lem1097748 A B h1)). Qed.
Lemma lem1097750 {A B : Type'} : ((@List.map A B) = (term5 A B)) = ((term5 A B) = (@List.map A B)).
Proof. exact (prop_ext (fun h1 : (@List.map A B) = (term5 A B) => @lem1097747 A B h1) (fun h1 : (term5 A B) = (@List.map A B) => @lem1097749 A B h1)). Qed.
Lemma lem1097753 {A B : Type'} : (term5 A B) = (@List.map A B).
Proof. exact (EQ_MP (@lem1097750 A B) (@lem1097740 A B)). Qed.
Lemma lem1097754 {A B : Type'} : (term5 A B) = (@List.map A B).
Proof. exact (@lem1097753 A B). Qed.
Lemma lem1097755 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097756 {A B : Type'} (f : A -> B) : (term6 A B f) = (@List.map A B f).
Proof. exact (MK_COMB (@lem1097754 A B) (@lem1097755 A B f)). Qed.
Lemma lem1097757 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1097758 {A B : Type'} (f : A -> B) : (term7 A B f) = (@List.map A B f (@nil A)).
Proof. exact (MK_COMB (@lem1097756 A B f) (@lem1097757 A)). Qed.
Lemma lem1097759 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1097760 {A B : Type'} (f : A -> B) : (term8 A B f) = (term9 A B f).
Proof. exact (MK_COMB (@lem1097759 B) (@lem1097758 A B f)). Qed.
Lemma lem1097761 {B : Type'} : (@nil B) = (@nil B).
Proof. exact (eq_refl (@nil B)). Qed.
Lemma lem1097762 {A B : Type'} (f : A -> B) : ((term7 A B f) = (@nil B)) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (MK_COMB (@lem1097760 A B f) (@lem1097761 B)). Qed.
Lemma lem1097763 {A B : Type'} : (term10 A B) = (term11 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1097762 A B f)). Qed.
Lemma lem1097764 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1097765 {A B : Type'} : (term12 A B) = (term13 A B).
Proof. exact (MK_COMB (@lem1097764 A B) (@lem1097763 A B)). Qed.
Lemma lem1097766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1097767 {A B : Type'} : (term14 A B) = (term15 A B).
Proof. exact (MK_COMB (@lem1097766) (@lem1097765 A B)). Qed.
Lemma lem1097769 {A B : Type'} : (term5 A B) = (@List.map A B).
Proof. exact (EQ_MP (@lem1097750 A B) (@lem1097740 A B)). Qed.
Lemma lem1097770 {A B : Type'} : (term5 A B) = (@List.map A B).
Proof. exact (@lem1097769 A B). Qed.
Lemma lem1097771 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097772 {A B : Type'} (f : A -> B) : (term6 A B f) = (@List.map A B f).
Proof. exact (MK_COMB (@lem1097770 A B) (@lem1097771 A B f)). Qed.
Lemma lem1097773 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1097774 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term16 A B f h t) = (term17 A B f h t).
Proof. exact (MK_COMB (@lem1097772 A B f) (@lem1097773 A h t)). Qed.
Lemma lem1097775 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1097776 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term18 A B f h t) = (term19 A B f h t).
Proof. exact (MK_COMB (@lem1097775 B) (@lem1097774 A B f h t)). Qed.
Lemma lem1097778 {A B : Type'} : (term5 A B) = (@List.map A B).
Proof. exact (EQ_MP (@lem1097750 A B) (@lem1097740 A B)). Qed.
Lemma lem1097779 {A B : Type'} : (term5 A B) = (@List.map A B).
Proof. exact (@lem1097778 A B). Qed.
Lemma lem1097780 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1097781 {A B : Type'} (f : A -> B) : (term6 A B f) = (@List.map A B f).
Proof. exact (MK_COMB (@lem1097779 A B) (@lem1097780 A B f)). Qed.
Lemma lem1097782 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1097783 {A B : Type'} (f : A -> B) (t : list A) : (term20 A B f t) = (@List.map A B f t).
Proof. exact (MK_COMB (@lem1097781 A B f) (@lem1097782 A t)). Qed.
Lemma lem1097784 {A B : Type'} (f : A -> B) (h : A) : (term21 A B f h) = (term21 A B f h).
Proof. exact (eq_refl (term21 A B f h)). Qed.
Lemma lem1097785 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term22 A B h f t) = (term23 A B h f t).
Proof. exact (MK_COMB (@lem1097784 A B f h) (@lem1097783 A B f t)). Qed.
Lemma lem1097786 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((term16 A B f h t) = (term22 A B h f t)) = ((term17 A B f h t) = (term23 A B h f t)).
Proof. exact (MK_COMB (@lem1097776 A B f h t) (@lem1097785 A B h f t)). Qed.
Lemma lem1097787 {A B : Type'} (h : A) (f : A -> B) : (term24 A B h f) = (term25 A B h f).
Proof. exact (fun_ext (fun t : list A => @lem1097786 A B h f t)). Qed.
Lemma lem1097788 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1097789 {A B : Type'} (h : A) (f : A -> B) : (term26 A B h f) = (term27 A B h f).
Proof. exact (MK_COMB (@lem1097788 A) (@lem1097787 A B h f)). Qed.
Lemma lem1097790 {A B : Type'} (f : A -> B) : (term28 A B f) = (term29 A B f).
Proof. exact (fun_ext (fun h : A => @lem1097789 A B h f)). Qed.
Lemma lem1097791 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1097792 {A B : Type'} (f : A -> B) : (term30 A B f) = (term31 A B f).
Proof. exact (MK_COMB (@lem1097791 A) (@lem1097790 A B f)). Qed.
Lemma lem1097793 {A B : Type'} : (term32 A B) = (term33 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1097792 A B f)). Qed.
Lemma lem1097794 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1097795 {A B : Type'} : (term34 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem1097794 A B) (@lem1097793 A B)). Qed.
Lemma lem1097796 {A B : Type'} : (term4 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem1097767 A B) (@lem1097795 A B)). Qed.
Lemma lem1097797 {A B : Type'} : term36 A B.
Proof. exact (EQ_MP (@lem1097796 A B) (@lem1097745 A B)). Qed.
