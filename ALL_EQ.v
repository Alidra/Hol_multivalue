Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_EQ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm7_spec.
Lemma lem1123798 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1123799 {_26443 : Type'} (P : type1143 _26443) : term0 _26443 P.
Proof. exact (@lem1123798 _26443 P). Qed.
Lemma lem1123800 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : term1 _26443 R P Q.
Proof. exact (@lem1123799 _26443 (term2 _26443 R P Q)). Qed.
Lemma lem1123801 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term3 _26443 R P Q) = (term4 _26443 R P Q).
Proof. exact (eq_refl (term3 _26443 R P Q)). Qed.
Lemma lem1123802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123803 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term5 _26443 R P Q) = (term6 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123802) (@lem1123801 _26443 R P Q)). Qed.
Lemma lem1123804 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) : (term7 _26443 R P Q t) = (term8 _26443 R P Q t).
Proof. exact (eq_refl (term7 _26443 R P Q t)). Qed.
Lemma lem1123805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123806 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) : (term9 _26443 R P Q t) = (term10 _26443 R P Q t).
Proof. exact (MK_COMB (@lem1123805) (@lem1123804 _26443 R P Q t)). Qed.
Lemma lem1123807 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h : _26443) (t : list _26443) : (term11 _26443 R P Q h t) = (term12 _26443 R P Q h t).
Proof. exact (eq_refl (term11 _26443 R P Q h t)). Qed.
Lemma lem1123808 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h : _26443) (t : list _26443) : (term13 _26443 R P Q h t) = (term14 _26443 R P Q h t).
Proof. exact (MK_COMB (@lem1123806 _26443 R P Q t) (@lem1123807 _26443 R P Q h t)). Qed.
Lemma lem1123809 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h : _26443) : (term15 _26443 R P Q h) = (term16 _26443 R P Q h).
Proof. exact (fun_ext (fun t : list _26443 => @lem1123808 _26443 R P Q h t)). Qed.
Lemma lem1123810 {_26443 : Type'} : (@all (list _26443)) = (@all (list _26443)).
Proof. exact (eq_refl (@all (list _26443))). Qed.
Lemma lem1123811 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h : _26443) : (term17 _26443 R P Q h) = (term18 _26443 R P Q h).
Proof. exact (MK_COMB (@lem1123810 _26443) (@lem1123809 _26443 R P Q h)). Qed.
Lemma lem1123812 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term19 _26443 R P Q) = (term20 _26443 R P Q).
Proof. exact (fun_ext (fun h : _26443 => @lem1123811 _26443 R P Q h)). Qed.
Lemma lem1123813 {_26443 : Type'} : (@all _26443) = (@all _26443).
Proof. exact (eq_refl (@all _26443)). Qed.
Lemma lem1123814 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term21 _26443 R P Q) = (term22 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123813 _26443) (@lem1123812 _26443 R P Q)). Qed.
Lemma lem1123815 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term23 _26443 R P Q) = (term24 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123803 _26443 R P Q) (@lem1123814 _26443 R P Q)). Qed.
Lemma lem1123816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123817 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term25 _26443 R P Q) = (term26 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123816) (@lem1123815 _26443 R P Q)). Qed.
Lemma lem1123818 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (l : list _26443) : (term7 _26443 R P Q l) = (term8 _26443 R P Q l).
Proof. exact (eq_refl (term7 _26443 R P Q l)). Qed.
Lemma lem1123819 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term27 _26443 R P Q) = (term2 _26443 R P Q).
Proof. exact (fun_ext (fun l : list _26443 => @lem1123818 _26443 R P Q l)). Qed.
Lemma lem1123820 {_26443 : Type'} : (@all (list _26443)) = (@all (list _26443)).
Proof. exact (eq_refl (@all (list _26443))). Qed.
Lemma lem1123821 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term28 _26443 R P Q) = (term29 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123820 _26443) (@lem1123819 _26443 R P Q)). Qed.
Lemma lem1123822 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term1 _26443 R P Q) = (term30 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123817 _26443 R P Q) (@lem1123821 _26443 R P Q)). Qed.
Lemma lem1123823 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : term30 _26443 R P Q.
Proof. exact (EQ_MP (@lem1123822 _26443 R P Q) (@lem1123800 _26443 R P Q)). Qed.
Lemma lem1123824 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term8 _26443 R P Q t) : term8 _26443 R P Q t.
Proof. exact (h1). Qed.
Lemma lem1123830 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1123831 {_26443 : Type'} (P : _26443 -> Prop) : (@List.Forall _26443 P (@nil _26443)) = True.
Proof. exact (@lem1123830 _26443 P). Qed.
Lemma lem1123832 {_26443 : Type'} (R : _26443 -> Prop) : (@List.Forall _26443 R (@nil _26443)) = True.
Proof. exact (@lem1123831 _26443 R). Qed.
Lemma lem1123833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123834 {_26443 : Type'} (R : _26443 -> Prop) : (term31 _26443 R) = (and True).
Proof. exact (MK_COMB (@lem1123833) (@lem1123832 _26443 R)). Qed.
Lemma lem1123843 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term32 _26443 R P Q) = (term32 _26443 R P Q).
Proof. exact (eq_refl (term32 _26443 R P Q)). Qed.
Lemma lem1123844 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term33 _26443 R P Q) = (term34 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123834 _26443 R) (@lem1123843 _26443 R P Q)). Qed.
Lemma lem1123846 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1123847 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term34 _26443 R P Q) = (term32 _26443 R P Q).
Proof. exact (@lem1123846 (term32 _26443 R P Q)). Qed.
Lemma lem1123856 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term33 _26443 R P Q) = (term32 _26443 R P Q).
Proof. exact (TRANS (@lem1123844 _26443 R P Q) (@lem1123847 _26443 R P Q)). Qed.
Lemma lem1123857 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123858 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term35 _26443 R P Q) = (term36 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123857) (@lem1123856 _26443 R P Q)). Qed.
Lemma lem1123862 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1123863 {_26443 : Type'} (P : _26443 -> Prop) : (@List.Forall _26443 P (@nil _26443)) = True.
Proof. exact (@lem1123862 _26443 P). Qed.
Lemma lem1123864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123865 {_26443 : Type'} (P : _26443 -> Prop) : (term37 _26443 P) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1123864) (@lem1123863 _26443 P)). Qed.
Lemma lem1123867 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1123868 {_26443 : Type'} (P : _26443 -> Prop) : (@List.Forall _26443 P (@nil _26443)) = True.
Proof. exact (@lem1123867 _26443 P). Qed.
Lemma lem1123869 {_26443 : Type'} (Q : _26443 -> Prop) : (@List.Forall _26443 Q (@nil _26443)) = True.
Proof. exact (@lem1123868 _26443 Q). Qed.
Lemma lem1123870 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) : ((@List.Forall _26443 P (@nil _26443)) = (@List.Forall _26443 Q (@nil _26443))) = (True = True).
Proof. exact (MK_COMB (@lem1123865 _26443 P) (@lem1123869 _26443 Q)). Qed.
Lemma lem1123872 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1123873 : (True = True) = True.
Proof. exact (@lem1123872 True). Qed.
Lemma lem1123874 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) : ((@List.Forall _26443 P (@nil _26443)) = (@List.Forall _26443 Q (@nil _26443))) = True.
Proof. exact (TRANS (@lem1123870 _26443 P Q) (@lem1123873)). Qed.
Lemma lem1123875 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term4 _26443 R P Q) = (term38 _26443 R P Q).
Proof. exact (MK_COMB (@lem1123858 _26443 R P Q) (@lem1123874 _26443 P Q)). Qed.
Lemma lem1123877 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1123878 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term38 _26443 R P Q) = True.
Proof. exact (@lem1123877 (term32 _26443 R P Q)). Qed.
Lemma lem1123879 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term4 _26443 R P Q) = True.
Proof. exact (TRANS (@lem1123875 _26443 R P Q) (@lem1123878 _26443 R P Q)). Qed.
Lemma lem1123880 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : True = (term4 _26443 R P Q).
Proof. exact (SYM (@lem1123879 _26443 R P Q)). Qed.
Lemma lem1123881 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : term4 _26443 R P Q.
Proof. exact (EQ_MP (@lem1123880 _26443 R P Q) (@lem0)). Qed.
Lemma lem1123887 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term39 _25307 P h t) = (term40 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1123888 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (t : list _26443) : (term39 _26443 P h t) = (term40 _26443 h P t).
Proof. exact (@lem1123887 _26443 h P t). Qed.
Lemma lem1123889 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (t : list _26443) : (term39 _26443 R h t) = (term40 _26443 h R t).
Proof. exact (@lem1123888 _26443 h R t). Qed.
Lemma lem1123892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123893 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (t : list _26443) : (term41 _26443 R h t) = (term42 _26443 h R t).
Proof. exact (MK_COMB (@lem1123892) (@lem1123889 _26443 h R t)). Qed.
Lemma lem1123902 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term32 _26443 R P Q) = (term32 _26443 R P Q).
Proof. exact (eq_refl (term32 _26443 R P Q)). Qed.
Lemma lem1123903 {_26443 : Type'} (h : _26443) (t : list _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term43 _26443 h t R P Q) = (term44 _26443 h t R P Q).
Proof. exact (MK_COMB (@lem1123893 _26443 h R t) (@lem1123902 _26443 R P Q)). Qed.
Lemma lem1123906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123907 {_26443 : Type'} (h : _26443) (t : list _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : (term45 _26443 h t R P Q) = (term46 _26443 h t R P Q).
Proof. exact (MK_COMB (@lem1123906) (@lem1123903 _26443 h t R P Q)). Qed.
Lemma lem1123911 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term39 _25307 P h t) = (term40 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1123912 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (t : list _26443) : (term39 _26443 P h t) = (term40 _26443 h P t).
Proof. exact (@lem1123911 _26443 h P t). Qed.
Lemma lem1123915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123916 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (t : list _26443) : (term47 _26443 P h t) = (term48 _26443 h P t).
Proof. exact (MK_COMB (@lem1123915) (@lem1123912 _26443 h P t)). Qed.
Lemma lem1123918 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term39 _25307 P h t) = (term40 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1123919 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (t : list _26443) : (term39 _26443 P h t) = (term40 _26443 h P t).
Proof. exact (@lem1123918 _26443 h P t). Qed.
Lemma lem1123920 {_26443 : Type'} (h : _26443) (Q : _26443 -> Prop) (t : list _26443) : (term39 _26443 Q h t) = (term40 _26443 h Q t).
Proof. exact (@lem1123919 _26443 h Q t). Qed.
Lemma lem1123923 {_26443 : Type'} (P : _26443 -> Prop) (h : _26443) (Q : _26443 -> Prop) (t : list _26443) : ((term39 _26443 P h t) = (term39 _26443 Q h t)) = ((term40 _26443 h P t) = (term40 _26443 h Q t)).
Proof. exact (MK_COMB (@lem1123916 _26443 h P t) (@lem1123920 _26443 h Q t)). Qed.
Lemma lem1123926 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (h : _26443) (Q : _26443 -> Prop) (t : list _26443) : (term12 _26443 R P Q h t) = (term49 _26443 R P h Q t).
Proof. exact (MK_COMB (@lem1123907 _26443 h t R P Q) (@lem1123923 _26443 P h Q t)). Qed.
Lemma lem1123929 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h : _26443) (t : list _26443) : (term49 _26443 R P h Q t) = (term12 _26443 R P Q h t).
Proof. exact (SYM (@lem1123926 _26443 R P h Q t)). Qed.
Lemma lem1123930 {_26443 : Type'} (h : _26443) (t : list _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term44 _26443 h t R P Q) : term44 _26443 h t R P Q.
Proof. exact (h1). Qed.
Lemma lem1123931 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term32 _26443 R P Q.
Proof. exact (h1). Qed.
Lemma lem1123932 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (t : list _26443) (h1 : term40 _26443 h R t) : term40 _26443 h R t.
Proof. exact (h1). Qed.
Lemma lem1123933 {_26443 : Type'} (R : _26443 -> Prop) (t : list _26443) (h1 : @List.Forall _26443 R t) : @List.Forall _26443 R t.
Proof. exact (h1). Qed.
Lemma lem1123934 {_26443 : Type'} (R : _26443 -> Prop) (h : _26443) (h1 : R h) : R h.
Proof. exact (h1). Qed.
Lemma lem1123935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123936 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term32 _26443 R P Q.
Proof. exact (h1). Qed.
Lemma lem1123937 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term50 _26443 R P Q x.
Proof. exact (@lem1123936 _26443 R P Q h1 x). Qed.
Lemma lem1123938 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (x : _26443) : (term50 _26443 R P Q x) = (term51 _26443 R P Q x).
Proof. exact (eq_refl (term50 _26443 R P Q x)). Qed.
Lemma lem1123939 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term51 _26443 R P Q x.
Proof. exact (EQ_MP (@lem1123938 _26443 R P Q x) (@lem1123937 _26443 x R P Q h1)). Qed.
Lemma lem1123940 {_26443 : Type'} (R : _26443 -> Prop) (x : _26443) (h1 : R x) : R x.
Proof. exact (h1). Qed.
Lemma lem1123941 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (x : _26443) (h1 : term32 _26443 R P Q) (h2 : R x) : (P x) = (Q x).
Proof. exact (@lem1123939 _26443 x R P Q h1 (@lem1123940 _26443 R x h2)). Qed.
Lemma lem1123942 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (x : _26443) (h1 : R x) : term52 _26443 R P Q x.
Proof. exact (fun h0 : term32 _26443 R P Q => @lem1123941 _26443 P Q R x h0 h1). Qed.
Lemma lem1123943 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term32 _26443 R P Q.
Proof. exact (h1). Qed.
Lemma lem1123944 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (x : _26443) (h1 : term32 _26443 R P Q) (h2 : R x) : (P x) = (Q x).
Proof. exact (@lem1123942 _26443 P Q R x h2 (@lem1123943 _26443 R P Q h1)). Qed.
Lemma lem1123945 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term51 _26443 R P Q x.
Proof. exact (fun h0 : R x => @lem1123944 _26443 P Q R x h1 h0). Qed.
Lemma lem1123946 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term32 _26443 R P Q.
Proof. exact (fun x : _26443 => @lem1123945 _26443 x R P Q h1). Qed.
Lemma lem1123947 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : term53 _26443 R P Q.
Proof. exact (fun h0 : term32 _26443 R P Q => @lem1123946 _26443 R P Q h0). Qed.
Lemma lem1123948 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term32 _26443 R P Q.
Proof. exact (@lem1123947 _26443 R P Q (@lem1123931 _26443 R P Q h1)). Qed.
Lemma lem1123949 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term50 _26443 R P Q x.
Proof. exact (@lem1123948 _26443 R P Q h1 x). Qed.
Lemma lem1123950 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (x : _26443) : (term50 _26443 R P Q x) = (term51 _26443 R P Q x).
Proof. exact (eq_refl (term50 _26443 R P Q x)). Qed.
Lemma lem1123953 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term51 _26443 R P Q x.
Proof. exact (EQ_MP (@lem1123950 _26443 R P Q x) (@lem1123949 _26443 x R P Q h1)). Qed.
Lemma lem1123954 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term51 _26443 R P Q x.
Proof. exact (@lem1123953 _26443 x R P Q h1). Qed.
Lemma lem1123955 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term51 _26443 R P Q h.
Proof. exact (@lem1123954 _26443 h R P Q h1). Qed.
Lemma lem1123974 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term8 _26443 R P Q t) : term8 _26443 R P Q t.
Proof. exact (h1). Qed.
Lemma lem1123975 {_26443 : Type'} (t : list _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term54 _26443 t R P Q) : term54 _26443 t R P Q.
Proof. exact (h1). Qed.
Lemma lem1123976 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term54 _26443 t R P Q) (h2 : term8 _26443 R P Q t) : (@List.Forall _26443 P t) = (@List.Forall _26443 Q t).
Proof. exact (@lem1123974 _26443 R P Q t h2 (@lem1123975 _26443 t R P Q h1)). Qed.
Lemma lem1123977 {_26443 : Type'} (t : list _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term54 _26443 t R P Q) : term55 _26443 R P Q t.
Proof. exact (fun h0 : term8 _26443 R P Q t => @lem1123976 _26443 R P Q t h1 h0). Qed.
Lemma lem1123978 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term8 _26443 R P Q t) : term8 _26443 R P Q t.
Proof. exact (h1). Qed.
Lemma lem1123979 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term54 _26443 t R P Q) (h2 : term8 _26443 R P Q t) : (@List.Forall _26443 P t) = (@List.Forall _26443 Q t).
Proof. exact (@lem1123977 _26443 t R P Q h1 (@lem1123978 _26443 R P Q t h2)). Qed.
Lemma lem1123980 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term8 _26443 R P Q t) : term8 _26443 R P Q t.
Proof. exact (fun h0 : term54 _26443 t R P Q => @lem1123979 _26443 R P Q t h0 h1). Qed.
Lemma lem1123981 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) : term56 _26443 R P Q t.
Proof. exact (fun h0 : term8 _26443 R P Q t => @lem1123980 _26443 R P Q t h0). Qed.
Lemma lem1123984 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term8 _26443 R P Q t) : term8 _26443 R P Q t.
Proof. exact (@lem1123981 _26443 R P Q t (@lem1123824 _26443 R P Q t h1)). Qed.
Lemma lem1123987 {_26443 : Type'} (R : _26443 -> Prop) (h : _26443) : (R h) = ((R h) = True).
Proof. exact (@lem7 (R h)). Qed.
Lemma lem1123997 {_26443 : Type'} (R : _26443 -> Prop) (h : _26443) (h1 : R h) : (R h) = True.
Proof. exact (EQ_MP (@lem1123987 _26443 R h) (@lem1123934 _26443 R h h1)). Qed.
Lemma lem1123998 {_26443 : Type'} (R : _26443 -> Prop) (h : _26443) (h1 : R h) : True = (R h).
Proof. exact (SYM (@lem1123997 _26443 R h h1)). Qed.
Lemma lem1123999 {_26443 : Type'} (R : _26443 -> Prop) (h : _26443) (h1 : R h) : R h.
Proof. exact (EQ_MP (@lem1123998 _26443 R h h1) (@lem0)). Qed.
Lemma lem1124004 {_26443 : Type'} (R : _26443 -> Prop) (t : list _26443) : (@List.Forall _26443 R t) = ((@List.Forall _26443 R t) = True).
Proof. exact (@lem7 (@List.Forall _26443 R t)). Qed.
Lemma lem1124006 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term50 _26443 R P Q x.
Proof. exact (@lem1123931 _26443 R P Q h1 x). Qed.
Lemma lem1124007 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (x : _26443) : (term50 _26443 R P Q x) = (term51 _26443 R P Q x).
Proof. exact (eq_refl (term50 _26443 R P Q x)). Qed.
Lemma lem1124008 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : term51 _26443 R P Q x.
Proof. exact (EQ_MP (@lem1124007 _26443 R P Q x) (@lem1124006 _26443 x R P Q h1)). Qed.
Lemma lem1124009 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (x : _26443) : (term51 _26443 R P Q x) = ((term51 _26443 R P Q x) = True).
Proof. exact (@lem7 (term51 _26443 R P Q x)). Qed.
Lemma lem1124014 {_26443 : Type'} (R : _26443 -> Prop) (t : list _26443) (h1 : @List.Forall _26443 R t) : (@List.Forall _26443 R t) = True.
Proof. exact (EQ_MP (@lem1124004 _26443 R t) (@lem1123933 _26443 R t h1)). Qed.
Lemma lem1124015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1124016 {_26443 : Type'} (R : _26443 -> Prop) (t : list _26443) (h1 : @List.Forall _26443 R t) : (term57 _26443 R t) = (and True).
Proof. exact (MK_COMB (@lem1124015) (@lem1124014 _26443 R t h1)). Qed.
Lemma lem1124022 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : (term51 _26443 R P Q x) = True.
Proof. exact (EQ_MP (@lem1124009 _26443 R P Q x) (@lem1124008 _26443 x R P Q h1)). Qed.
Lemma lem1124023 {_26443 : Type'} (x : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : (term51 _26443 R P Q x) = True.
Proof. exact (@lem1124022 _26443 x R P Q h1). Qed.
Lemma lem1124024 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : (term58 _26443 R P Q) = (term59 _26443).
Proof. exact (fun_ext (fun x : _26443 => @lem1124023 _26443 x R P Q h1)). Qed.
Lemma lem1124025 {_26443 : Type'} : (@all _26443) = (@all _26443).
Proof. exact (eq_refl (@all _26443)). Qed.
Lemma lem1124026 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : (term32 _26443 R P Q) = (term60 _26443).
Proof. exact (MK_COMB (@lem1124025 _26443) (@lem1124024 _26443 R P Q h1)). Qed.
Lemma lem1124028 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1124029 {_26443 : Type'} (t : Prop) : (term61 _26443 t) = t.
Proof. exact (@lem1124028 _26443 t). Qed.
Lemma lem1124030 {_26443 : Type'} : (term60 _26443) = True.
Proof. exact (@lem1124029 _26443 True). Qed.
Lemma lem1124031 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term32 _26443 R P Q) : (term32 _26443 R P Q) = True.
Proof. exact (TRANS (@lem1124026 _26443 R P Q h1) (@lem1124030 _26443)). Qed.
Lemma lem1124032 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : @List.Forall _26443 R t) : (term54 _26443 t R P Q) = (True /\ True).
Proof. exact (MK_COMB (@lem1124016 _26443 R t h2) (@lem1124031 _26443 R P Q h1)). Qed.
Lemma lem1124034 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1124035 : (True /\ True) = True.
Proof. exact (@lem1124034 True). Qed.
Lemma lem1124036 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : @List.Forall _26443 R t) : (term54 _26443 t R P Q) = True.
Proof. exact (TRANS (@lem1124032 _26443 P Q R t h1 h2) (@lem1124035)). Qed.
Lemma lem1124037 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : @List.Forall _26443 R t) : True = (term54 _26443 t R P Q).
Proof. exact (SYM (@lem1124036 _26443 P Q R t h1 h2)). Qed.
Lemma lem1124038 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : @List.Forall _26443 R t) : term54 _26443 t R P Q.
Proof. exact (EQ_MP (@lem1124037 _26443 P Q R t h1 h2) (@lem0)). Qed.
Lemma lem1124039 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : term8 _26443 R P Q t) (h3 : @List.Forall _26443 R t) : (@List.Forall _26443 P t) = (@List.Forall _26443 Q t).
Proof. exact (@lem1123984 _26443 R P Q t h2 (@lem1124038 _26443 P Q R t h1 h3)). Qed.
Lemma lem1124040 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (h : _26443) (h1 : term32 _26443 R P Q) (h2 : R h) : (P h) = (Q h).
Proof. exact (@lem1123955 _26443 h R P Q h1 (@lem1123999 _26443 R h h2)). Qed.
Lemma lem1124041 {_26443 : Type'} (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (h : _26443) (h1 : term32 _26443 R P Q) (h2 : R h) : (term62 _26443 P h) = (term62 _26443 Q h).
Proof. exact (MK_COMB (@lem1123935) (@lem1124040 _26443 P Q R h h1 h2)). Qed.
Lemma lem1124042 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term8 _26443 R P Q t) (h4 : @List.Forall _26443 R t) : (term40 _26443 h P t) = (term40 _26443 h Q t).
Proof. exact (MK_COMB (@lem1124041 _26443 P Q R h h1 h2) (@lem1124039 _26443 P Q R t h1 h3 h4)). Qed.
Lemma lem1124043 {_26443 : Type'} (h : _26443) (t : list _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term44 _26443 h t R P Q) : term32 _26443 R P Q.
Proof. exact (proj2 (@lem1123930 _26443 h t R P Q h1)). Qed.
Lemma lem1124044 {_26443 : Type'} (h : _26443) (t : list _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h1 : term44 _26443 h t R P Q) : term40 _26443 h R t.
Proof. exact (proj1 (@lem1123930 _26443 h t R P Q h1)). Qed.
Lemma lem1124045 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term8 _26443 R P Q t) (h4 : @List.Forall _26443 R t) : (term32 _26443 R P Q) = ((term40 _26443 h P t) = (term40 _26443 h Q t)).
Proof. exact (prop_ext (fun h5 : term32 _26443 R P Q => @lem1124042 _26443 h P Q R t h1 h2 h3 h4) (fun h5 : (term40 _26443 h P t) = (term40 _26443 h Q t) => @lem1123931 _26443 R P Q h1)). Qed.
Lemma lem1124046 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term8 _26443 R P Q t) (h4 : @List.Forall _26443 R t) : (term40 _26443 h P t) = (term40 _26443 h Q t).
Proof. exact (EQ_MP (@lem1124045 _26443 h P Q R t h1 h2 h3 h4) (@lem1123931 _26443 R P Q h1)). Qed.
Lemma lem1124047 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (t : list _26443) (h1 : term40 _26443 h R t) : @List.Forall _26443 R t.
Proof. exact (proj2 (@lem1123932 _26443 h R t h1)). Qed.
Lemma lem1124048 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (t : list _26443) (h1 : term40 _26443 h R t) : R h.
Proof. exact (proj1 (@lem1123932 _26443 h R t h1)). Qed.
Lemma lem1124049 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term8 _26443 R P Q t) (h4 : @List.Forall _26443 R t) : (@List.Forall _26443 R t) = ((term40 _26443 h P t) = (term40 _26443 h Q t)).
Proof. exact (prop_ext (fun h5 : @List.Forall _26443 R t => @lem1124046 _26443 h P Q R t h1 h2 h3 h4) (fun h5 : (term40 _26443 h P t) = (term40 _26443 h Q t) => @lem1123933 _26443 R t h4)). Qed.
Lemma lem1124050 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term8 _26443 R P Q t) (h4 : @List.Forall _26443 R t) : (term40 _26443 h P t) = (term40 _26443 h Q t).
Proof. exact (EQ_MP (@lem1124049 _26443 h P Q R t h1 h2 h3 h4) (@lem1123933 _26443 R t h4)). Qed.
Lemma lem1124051 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term8 _26443 R P Q t) (h4 : @List.Forall _26443 R t) : (R h) = ((term40 _26443 h P t) = (term40 _26443 h Q t)).
Proof. exact (prop_ext (fun h5 : R h => @lem1124050 _26443 h P Q R t h1 h2 h3 h4) (fun h5 : (term40 _26443 h P t) = (term40 _26443 h Q t) => @lem1123934 _26443 R h h2)). Qed.
Lemma lem1124052 {_26443 : Type'} (h : _26443) (P : _26443 -> Prop) (Q : _26443 -> Prop) (R : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term8 _26443 R P Q t) (h4 : @List.Forall _26443 R t) : (term40 _26443 h P t) = (term40 _26443 h Q t).
Proof. exact (EQ_MP (@lem1124051 _26443 h P Q R t h1 h2 h3 h4) (@lem1123934 _26443 R h h2)). Qed.
Lemma lem1124053 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term40 _26443 h R t) (h4 : term8 _26443 R P Q t) : (@List.Forall _26443 R t) = ((term40 _26443 h P t) = (term40 _26443 h Q t)).
Proof. exact (prop_ext (fun h5 : @List.Forall _26443 R t => @lem1124052 _26443 h P Q R t h1 h2 h4 h5) (fun h5 : (term40 _26443 h P t) = (term40 _26443 h Q t) => @lem1124047 _26443 h R t h3)). Qed.
Lemma lem1124054 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : R h) (h3 : term40 _26443 h R t) (h4 : term8 _26443 R P Q t) : (term40 _26443 h P t) = (term40 _26443 h Q t).
Proof. exact (EQ_MP (@lem1124053 _26443 h R P Q t h1 h2 h3 h4) (@lem1124047 _26443 h R t h3)). Qed.
Lemma lem1124055 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : term40 _26443 h R t) (h3 : term8 _26443 R P Q t) : (R h) = ((term40 _26443 h P t) = (term40 _26443 h Q t)).
Proof. exact (prop_ext (fun h4 : R h => @lem1124054 _26443 h R P Q t h1 h4 h2 h3) (fun h4 : (term40 _26443 h P t) = (term40 _26443 h Q t) => @lem1124048 _26443 h R t h2)). Qed.
Lemma lem1124056 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term32 _26443 R P Q) (h2 : term40 _26443 h R t) (h3 : term8 _26443 R P Q t) : (term40 _26443 h P t) = (term40 _26443 h Q t).
Proof. exact (EQ_MP (@lem1124055 _26443 h R P Q t h1 h2 h3) (@lem1124048 _26443 h R t h2)). Qed.
Lemma lem1124057 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term40 _26443 h R t) (h2 : term44 _26443 h t R P Q) (h3 : term8 _26443 R P Q t) : (term32 _26443 R P Q) = ((term40 _26443 h P t) = (term40 _26443 h Q t)).
Proof. exact (prop_ext (fun h4 : term32 _26443 R P Q => @lem1124056 _26443 h R P Q t h4 h1 h3) (fun h4 : (term40 _26443 h P t) = (term40 _26443 h Q t) => @lem1124043 _26443 h t R P Q h2)). Qed.
Lemma lem1124058 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term40 _26443 h R t) (h2 : term44 _26443 h t R P Q) (h3 : term8 _26443 R P Q t) : (term40 _26443 h P t) = (term40 _26443 h Q t).
Proof. exact (EQ_MP (@lem1124057 _26443 h R P Q t h1 h2 h3) (@lem1124043 _26443 h t R P Q h2)). Qed.
Lemma lem1124059 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term44 _26443 h t R P Q) (h2 : term8 _26443 R P Q t) : (term40 _26443 h R t) = ((term40 _26443 h P t) = (term40 _26443 h Q t)).
Proof. exact (prop_ext (fun h3 : term40 _26443 h R t => @lem1124058 _26443 h R P Q t h3 h1 h2) (fun h3 : (term40 _26443 h P t) = (term40 _26443 h Q t) => @lem1124044 _26443 h t R P Q h1)). Qed.
Lemma lem1124060 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term44 _26443 h t R P Q) (h2 : term8 _26443 R P Q t) : (term40 _26443 h P t) = (term40 _26443 h Q t).
Proof. exact (EQ_MP (@lem1124059 _26443 h R P Q t h1 h2) (@lem1124044 _26443 h t R P Q h1)). Qed.
Lemma lem1124061 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term8 _26443 R P Q t) : term49 _26443 R P h Q t.
Proof. exact (fun h0 : term44 _26443 h t R P Q => @lem1124060 _26443 h R P Q t h0 h1). Qed.
Lemma lem1124062 {_26443 : Type'} (h : _26443) (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (t : list _26443) (h1 : term8 _26443 R P Q t) : term12 _26443 R P Q h t.
Proof. exact (EQ_MP (@lem1123929 _26443 R P Q h t) (@lem1124061 _26443 h R P Q t h1)). Qed.
Lemma lem1124063 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h : _26443) (t : list _26443) : term14 _26443 R P Q h t.
Proof. exact (fun h0 : term8 _26443 R P Q t => @lem1124062 _26443 h R P Q t h0). Qed.
Lemma lem1124068 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) (h : _26443) : term18 _26443 R P Q h.
Proof. exact (fun t : list _26443 => @lem1124063 _26443 R P Q h t). Qed.
Lemma lem1124073 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : term22 _26443 R P Q.
Proof. exact (fun h : _26443 => @lem1124068 _26443 R P Q h). Qed.
Lemma lem1124074 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : term24 _26443 R P Q.
Proof. exact (conj (@lem1123881 _26443 R P Q) (@lem1124073 _26443 R P Q)). Qed.
Lemma lem1124075 {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop) : term29 _26443 R P Q.
Proof. exact (@lem1123823 _26443 R P Q (@lem1124074 _26443 R P Q)). Qed.
