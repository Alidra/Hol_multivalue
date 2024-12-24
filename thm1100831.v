Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1100831_term_abbrevs.
Require Import thm1100408_spec.
Require Import thm1100774_spec.
Lemma lem1100775 {_25307 : Type'} : (term0 _25307) = (term1 _25307).
Proof. exact (eq_refl (term0 _25307)). Qed.
Lemma lem1100776 {_25307 : Type'} : term1 _25307.
Proof. exact (EQ_MP (@lem1100775 _25307) (@lem1100408 _25307)). Qed.
Lemma lem1100777 {_25307 : Type'} : term2 _25307.
Proof. exact (@lem1100776 _25307 term3). Qed.
Lemma lem1100778 {_25307 : Type'} : (term2 _25307) = (term4 _25307).
Proof. exact (eq_refl (term2 _25307)). Qed.
Lemma lem1100779 {_25307 : Type'} : term4 _25307.
Proof. exact (EQ_MP (@lem1100778 _25307) (@lem1100777 _25307)). Qed.
Lemma lem1100780 {_25307 : Type'} (h1 : (@List.Forall _25307) = (term5 _25307)) : (@List.Forall _25307) = (term5 _25307).
Proof. exact (h1). Qed.
Lemma lem1100781 {_25307 : Type'} (h1 : (@List.Forall _25307) = (term5 _25307)) : (term5 _25307) = (@List.Forall _25307).
Proof. exact (SYM (@lem1100780 _25307 h1)). Qed.
Lemma lem1100782 {_25307 : Type'} (h1 : (term5 _25307) = (@List.Forall _25307)) : (term5 _25307) = (@List.Forall _25307).
Proof. exact (h1). Qed.
Lemma lem1100783 {_25307 : Type'} (h1 : (term5 _25307) = (@List.Forall _25307)) : (@List.Forall _25307) = (term5 _25307).
Proof. exact (SYM (@lem1100782 _25307 h1)). Qed.
Lemma lem1100784 {_25307 : Type'} : ((@List.Forall _25307) = (term5 _25307)) = ((term5 _25307) = (@List.Forall _25307)).
Proof. exact (prop_ext (fun h1 : (@List.Forall _25307) = (term5 _25307) => @lem1100781 _25307 h1) (fun h1 : (term5 _25307) = (@List.Forall _25307) => @lem1100783 _25307 h1)). Qed.
Lemma lem1100787 {_25307 : Type'} : (term5 _25307) = (@List.Forall _25307).
Proof. exact (EQ_MP (@lem1100784 _25307) (@lem1100774 _25307)). Qed.
Lemma lem1100788 {_25307 : Type'} : (term5 _25307) = (@List.Forall _25307).
Proof. exact (@lem1100787 _25307). Qed.
Lemma lem1100789 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100790 {_25307 : Type'} (P : _25307 -> Prop) : (term6 _25307 P) = (@List.Forall _25307 P).
Proof. exact (MK_COMB (@lem1100788 _25307) (@lem1100789 _25307 P)). Qed.
Lemma lem1100791 {_25307 : Type'} : (@nil _25307) = (@nil _25307).
Proof. exact (eq_refl (@nil _25307)). Qed.
Lemma lem1100792 {_25307 : Type'} (P : _25307 -> Prop) : (term7 _25307 P) = (@List.Forall _25307 P (@nil _25307)).
Proof. exact (MK_COMB (@lem1100790 _25307 P) (@lem1100791 _25307)). Qed.
Lemma lem1100793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100794 {_25307 : Type'} (P : _25307 -> Prop) : (term8 _25307 P) = (term9 _25307 P).
Proof. exact (MK_COMB (@lem1100793) (@lem1100792 _25307 P)). Qed.
Lemma lem1100795 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1100796 {_25307 : Type'} (P : _25307 -> Prop) : ((term7 _25307 P) = True) = ((@List.Forall _25307 P (@nil _25307)) = True).
Proof. exact (MK_COMB (@lem1100794 _25307 P) (@lem1100795)). Qed.
Lemma lem1100797 {_25307 : Type'} : (term10 _25307) = (term11 _25307).
Proof. exact (fun_ext (fun P : _25307 -> Prop => @lem1100796 _25307 P)). Qed.
Lemma lem1100798 {_25307 : Type'} : (@all (_25307 -> Prop)) = (@all (_25307 -> Prop)).
Proof. exact (eq_refl (@all (_25307 -> Prop))). Qed.
Lemma lem1100799 {_25307 : Type'} : (term12 _25307) = (term13 _25307).
Proof. exact (MK_COMB (@lem1100798 _25307) (@lem1100797 _25307)). Qed.
Lemma lem1100800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1100801 {_25307 : Type'} : (term14 _25307) = (term15 _25307).
Proof. exact (MK_COMB (@lem1100800) (@lem1100799 _25307)). Qed.
Lemma lem1100803 {_25307 : Type'} : (term5 _25307) = (@List.Forall _25307).
Proof. exact (EQ_MP (@lem1100784 _25307) (@lem1100774 _25307)). Qed.
Lemma lem1100804 {_25307 : Type'} : (term5 _25307) = (@List.Forall _25307).
Proof. exact (@lem1100803 _25307). Qed.
Lemma lem1100805 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100806 {_25307 : Type'} (P : _25307 -> Prop) : (term6 _25307 P) = (@List.Forall _25307 P).
Proof. exact (MK_COMB (@lem1100804 _25307) (@lem1100805 _25307 P)). Qed.
Lemma lem1100807 {_25307 : Type'} (h : _25307) (t : list _25307) : (@cons _25307 h t) = (@cons _25307 h t).
Proof. exact (eq_refl (@cons _25307 h t)). Qed.
Lemma lem1100808 {_25307 : Type'} (P : _25307 -> Prop) (h : _25307) (t : list _25307) : (term16 _25307 P h t) = (term17 _25307 P h t).
Proof. exact (MK_COMB (@lem1100806 _25307 P) (@lem1100807 _25307 h t)). Qed.
Lemma lem1100809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100810 {_25307 : Type'} (P : _25307 -> Prop) (h : _25307) (t : list _25307) : (term18 _25307 P h t) = (term19 _25307 P h t).
Proof. exact (MK_COMB (@lem1100809) (@lem1100808 _25307 P h t)). Qed.
Lemma lem1100812 {_25307 : Type'} : (term5 _25307) = (@List.Forall _25307).
Proof. exact (EQ_MP (@lem1100784 _25307) (@lem1100774 _25307)). Qed.
Lemma lem1100813 {_25307 : Type'} : (term5 _25307) = (@List.Forall _25307).
Proof. exact (@lem1100812 _25307). Qed.
Lemma lem1100814 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100815 {_25307 : Type'} (P : _25307 -> Prop) : (term6 _25307 P) = (@List.Forall _25307 P).
Proof. exact (MK_COMB (@lem1100813 _25307) (@lem1100814 _25307 P)). Qed.
Lemma lem1100816 {_25307 : Type'} (t : list _25307) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1100817 {_25307 : Type'} (P : _25307 -> Prop) (t : list _25307) : (term20 _25307 P t) = (@List.Forall _25307 P t).
Proof. exact (MK_COMB (@lem1100815 _25307 P) (@lem1100816 _25307 t)). Qed.
Lemma lem1100818 {_25307 : Type'} (P : _25307 -> Prop) (h : _25307) : (term21 _25307 P h) = (term21 _25307 P h).
Proof. exact (eq_refl (term21 _25307 P h)). Qed.
Lemma lem1100819 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term22 _25307 h P t) = (term23 _25307 h P t).
Proof. exact (MK_COMB (@lem1100818 _25307 P h) (@lem1100817 _25307 P t)). Qed.
Lemma lem1100820 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : ((term16 _25307 P h t) = (term22 _25307 h P t)) = ((term17 _25307 P h t) = (term23 _25307 h P t)).
Proof. exact (MK_COMB (@lem1100810 _25307 P h t) (@lem1100819 _25307 h P t)). Qed.
Lemma lem1100821 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) : (term24 _25307 h P) = (term25 _25307 h P).
Proof. exact (fun_ext (fun t : list _25307 => @lem1100820 _25307 h P t)). Qed.
Lemma lem1100822 {_25307 : Type'} : (@all (list _25307)) = (@all (list _25307)).
Proof. exact (eq_refl (@all (list _25307))). Qed.
Lemma lem1100823 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) : (term26 _25307 h P) = (term27 _25307 h P).
Proof. exact (MK_COMB (@lem1100822 _25307) (@lem1100821 _25307 h P)). Qed.
Lemma lem1100824 {_25307 : Type'} (h : _25307) : (term28 _25307 h) = (term29 _25307 h).
Proof. exact (fun_ext (fun P : _25307 -> Prop => @lem1100823 _25307 h P)). Qed.
Lemma lem1100825 {_25307 : Type'} : (@all (_25307 -> Prop)) = (@all (_25307 -> Prop)).
Proof. exact (eq_refl (@all (_25307 -> Prop))). Qed.
Lemma lem1100826 {_25307 : Type'} (h : _25307) : (term30 _25307 h) = (term31 _25307 h).
Proof. exact (MK_COMB (@lem1100825 _25307) (@lem1100824 _25307 h)). Qed.
Lemma lem1100827 {_25307 : Type'} : (term32 _25307) = (term33 _25307).
Proof. exact (fun_ext (fun h : _25307 => @lem1100826 _25307 h)). Qed.
Lemma lem1100828 {_25307 : Type'} : (@all _25307) = (@all _25307).
Proof. exact (eq_refl (@all _25307)). Qed.
Lemma lem1100829 {_25307 : Type'} : (term34 _25307) = (term35 _25307).
Proof. exact (MK_COMB (@lem1100828 _25307) (@lem1100827 _25307)). Qed.
Lemma lem1100830 {_25307 : Type'} : (term4 _25307) = (term36 _25307).
Proof. exact (MK_COMB (@lem1100801 _25307) (@lem1100829 _25307)). Qed.
Lemma lem1100831 {_25307 : Type'} : term36 _25307.
Proof. exact (EQ_MP (@lem1100830 _25307) (@lem1100779 _25307)). Qed.
