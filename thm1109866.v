Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1109866_term_abbrevs.
Require Import thm1109409_spec.
Require Import thm1109797_spec.
Lemma lem1109798 {_25786 _25787 : Type'} : (term0 _25786 _25787) = (term1 _25786 _25787).
Proof. exact (eq_refl (term0 _25786 _25787)). Qed.
Lemma lem1109799 {_25786 _25787 : Type'} : term1 _25786 _25787.
Proof. exact (EQ_MP (@lem1109798 _25786 _25787) (@lem1109409 _25786 _25787)). Qed.
Lemma lem1109800 {_25786 _25787 : Type'} : term2 _25786 _25787.
Proof. exact (@lem1109799 _25786 _25787 term3). Qed.
Lemma lem1109801 {_25786 _25787 : Type'} : (term2 _25786 _25787) = (term4 _25786 _25787).
Proof. exact (eq_refl (term2 _25786 _25787)). Qed.
Lemma lem1109802 {_25786 _25787 : Type'} : term4 _25786 _25787.
Proof. exact (EQ_MP (@lem1109801 _25786 _25787) (@lem1109800 _25786 _25787)). Qed.
Lemma lem1109803 {_25786 _25787 : Type'} (h1 : (@ALLPAIRS _25786 _25787) = (term5 _25786 _25787)) : (@ALLPAIRS _25786 _25787) = (term5 _25786 _25787).
Proof. exact (h1). Qed.
Lemma lem1109804 {_25786 _25787 : Type'} (h1 : (@ALLPAIRS _25786 _25787) = (term5 _25786 _25787)) : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787).
Proof. exact (SYM (@lem1109803 _25786 _25787 h1)). Qed.
Lemma lem1109805 {_25786 _25787 : Type'} (h1 : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787)) : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787).
Proof. exact (h1). Qed.
Lemma lem1109806 {_25786 _25787 : Type'} (h1 : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787)) : (@ALLPAIRS _25786 _25787) = (term5 _25786 _25787).
Proof. exact (SYM (@lem1109805 _25786 _25787 h1)). Qed.
Lemma lem1109807 {_25786 _25787 : Type'} : ((@ALLPAIRS _25786 _25787) = (term5 _25786 _25787)) = ((term5 _25786 _25787) = (@ALLPAIRS _25786 _25787)).
Proof. exact (prop_ext (fun h1 : (@ALLPAIRS _25786 _25787) = (term5 _25786 _25787) => @lem1109804 _25786 _25787 h1) (fun h1 : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787) => @lem1109806 _25786 _25787 h1)). Qed.
Lemma lem1109810 {_25786 _25787 : Type'} : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787).
Proof. exact (EQ_MP (@lem1109807 _25786 _25787) (@lem1109797 _25786 _25787)). Qed.
Lemma lem1109811 {_25786 _25787 : Type'} : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787).
Proof. exact (@lem1109810 _25786 _25787). Qed.
Lemma lem1109812 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109813 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : (term6 _25786 _25787 f) = (@ALLPAIRS _25786 _25787 f).
Proof. exact (MK_COMB (@lem1109811 _25786 _25787) (@lem1109812 _25786 _25787 f)). Qed.
Lemma lem1109814 {_25787 : Type'} : (@nil _25787) = (@nil _25787).
Proof. exact (eq_refl (@nil _25787)). Qed.
Lemma lem1109815 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : (term7 _25786 _25787 f) = (@ALLPAIRS _25786 _25787 f (@nil _25787)).
Proof. exact (MK_COMB (@lem1109813 _25786 _25787 f) (@lem1109814 _25787)). Qed.
Lemma lem1109816 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109817 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (term8 _25786 _25787 f l) = (@ALLPAIRS _25786 _25787 f (@nil _25787) l).
Proof. exact (MK_COMB (@lem1109815 _25786 _25787 f) (@lem1109816 _25786 l)). Qed.
Lemma lem1109818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109819 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (term9 _25786 _25787 f l) = (term10 _25786 _25787 f l).
Proof. exact (MK_COMB (@lem1109818) (@lem1109817 _25786 _25787 f l)). Qed.
Lemma lem1109820 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1109821 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : ((term8 _25786 _25787 f l) = True) = ((@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True).
Proof. exact (MK_COMB (@lem1109819 _25786 _25787 f l) (@lem1109820)). Qed.
Lemma lem1109822 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : (term11 _25786 _25787 f) = (term12 _25786 _25787 f).
Proof. exact (fun_ext (fun l : list _25786 => @lem1109821 _25786 _25787 f l)). Qed.
Lemma lem1109823 {_25786 : Type'} : (@all (list _25786)) = (@all (list _25786)).
Proof. exact (eq_refl (@all (list _25786))). Qed.
Lemma lem1109824 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : (term13 _25786 _25787 f) = (term14 _25786 _25787 f).
Proof. exact (MK_COMB (@lem1109823 _25786) (@lem1109822 _25786 _25787 f)). Qed.
Lemma lem1109825 {_25786 _25787 : Type'} : (term15 _25786 _25787) = (term16 _25786 _25787).
Proof. exact (fun_ext (fun f : type1470 _25786 _25787 => @lem1109824 _25786 _25787 f)). Qed.
Lemma lem1109826 {_25786 _25787 : Type'} : (@all (_25787 -> _25786 -> Prop)) = (@all (_25787 -> _25786 -> Prop)).
Proof. exact (eq_refl (@all (_25787 -> _25786 -> Prop))). Qed.
Lemma lem1109827 {_25786 _25787 : Type'} : (term17 _25786 _25787) = (term18 _25786 _25787).
Proof. exact (MK_COMB (@lem1109826 _25786 _25787) (@lem1109825 _25786 _25787)). Qed.
Lemma lem1109828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1109829 {_25786 _25787 : Type'} : (term19 _25786 _25787) = (term20 _25786 _25787).
Proof. exact (MK_COMB (@lem1109828) (@lem1109827 _25786 _25787)). Qed.
Lemma lem1109831 {_25786 _25787 : Type'} : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787).
Proof. exact (EQ_MP (@lem1109807 _25786 _25787) (@lem1109797 _25786 _25787)). Qed.
Lemma lem1109832 {_25786 _25787 : Type'} : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787).
Proof. exact (@lem1109831 _25786 _25787). Qed.
Lemma lem1109833 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109834 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : (term6 _25786 _25787 f) = (@ALLPAIRS _25786 _25787 f).
Proof. exact (MK_COMB (@lem1109832 _25786 _25787) (@lem1109833 _25786 _25787 f)). Qed.
Lemma lem1109835 {_25787 : Type'} (h : _25787) (t : list _25787) : (@cons _25787 h t) = (@cons _25787 h t).
Proof. exact (eq_refl (@cons _25787 h t)). Qed.
Lemma lem1109836 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (h : _25787) (t : list _25787) : (term21 _25786 _25787 f h t) = (term22 _25786 _25787 f h t).
Proof. exact (MK_COMB (@lem1109834 _25786 _25787 f) (@lem1109835 _25787 h t)). Qed.
Lemma lem1109837 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109838 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (h : _25787) (t : list _25787) (l : list _25786) : (term23 _25786 _25787 f h t l) = (term24 _25786 _25787 f h t l).
Proof. exact (MK_COMB (@lem1109836 _25786 _25787 f h t) (@lem1109837 _25786 l)). Qed.
Lemma lem1109839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1109840 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (h : _25787) (t : list _25787) (l : list _25786) : (term25 _25786 _25787 f h t l) = (term26 _25786 _25787 f h t l).
Proof. exact (MK_COMB (@lem1109839) (@lem1109838 _25786 _25787 f h t l)). Qed.
Lemma lem1109842 {_25786 _25787 : Type'} : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787).
Proof. exact (EQ_MP (@lem1109807 _25786 _25787) (@lem1109797 _25786 _25787)). Qed.
Lemma lem1109843 {_25786 _25787 : Type'} : (term5 _25786 _25787) = (@ALLPAIRS _25786 _25787).
Proof. exact (@lem1109842 _25786 _25787). Qed.
Lemma lem1109844 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1109845 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : (term6 _25786 _25787 f) = (@ALLPAIRS _25786 _25787 f).
Proof. exact (MK_COMB (@lem1109843 _25786 _25787) (@lem1109844 _25786 _25787 f)). Qed.
Lemma lem1109846 {_25787 : Type'} (t : list _25787) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1109847 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (t : list _25787) : (term27 _25786 _25787 f t) = (@ALLPAIRS _25786 _25787 f t).
Proof. exact (MK_COMB (@lem1109845 _25786 _25787 f) (@lem1109846 _25787 t)). Qed.
Lemma lem1109848 {_25786 : Type'} (l : list _25786) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1109849 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term28 _25786 _25787 f t l) = (@ALLPAIRS _25786 _25787 f t l).
Proof. exact (MK_COMB (@lem1109847 _25786 _25787 f t) (@lem1109848 _25786 l)). Qed.
Lemma lem1109850 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (h : _25787) (l : list _25786) : (term29 _25786 _25787 f h l) = (term29 _25786 _25787 f h l).
Proof. exact (eq_refl (term29 _25786 _25787 f h l)). Qed.
Lemma lem1109851 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term30 _25786 _25787 h f t l) = (term31 _25786 _25787 h f t l).
Proof. exact (MK_COMB (@lem1109850 _25786 _25787 f h l) (@lem1109849 _25786 _25787 f t l)). Qed.
Lemma lem1109852 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : ((term23 _25786 _25787 f h t l) = (term30 _25786 _25787 h f t l)) = ((term24 _25786 _25787 f h t l) = (term31 _25786 _25787 h f t l)).
Proof. exact (MK_COMB (@lem1109840 _25786 _25787 f h t l) (@lem1109851 _25786 _25787 h f t l)). Qed.
Lemma lem1109853 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) : (term32 _25786 _25787 h f t) = (term33 _25786 _25787 h f t).
Proof. exact (fun_ext (fun l : list _25786 => @lem1109852 _25786 _25787 h f t l)). Qed.
Lemma lem1109854 {_25786 : Type'} : (@all (list _25786)) = (@all (list _25786)).
Proof. exact (eq_refl (@all (list _25786))). Qed.
Lemma lem1109855 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) : (term34 _25786 _25787 h f t) = (term35 _25786 _25787 h f t).
Proof. exact (MK_COMB (@lem1109854 _25786) (@lem1109853 _25786 _25787 h f t)). Qed.
Lemma lem1109856 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) : (term36 _25786 _25787 h f) = (term37 _25786 _25787 h f).
Proof. exact (fun_ext (fun t : list _25787 => @lem1109855 _25786 _25787 h f t)). Qed.
Lemma lem1109857 {_25787 : Type'} : (@all (list _25787)) = (@all (list _25787)).
Proof. exact (eq_refl (@all (list _25787))). Qed.
Lemma lem1109858 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) : (term38 _25786 _25787 h f) = (term39 _25786 _25787 h f).
Proof. exact (MK_COMB (@lem1109857 _25787) (@lem1109856 _25786 _25787 h f)). Qed.
Lemma lem1109859 {_25786 _25787 : Type'} (h : _25787) : (term40 _25786 _25787 h) = (term41 _25786 _25787 h).
Proof. exact (fun_ext (fun f : type1470 _25786 _25787 => @lem1109858 _25786 _25787 h f)). Qed.
Lemma lem1109860 {_25786 _25787 : Type'} : (@all (_25787 -> _25786 -> Prop)) = (@all (_25787 -> _25786 -> Prop)).
Proof. exact (eq_refl (@all (_25787 -> _25786 -> Prop))). Qed.
Lemma lem1109861 {_25786 _25787 : Type'} (h : _25787) : (term42 _25786 _25787 h) = (term43 _25786 _25787 h).
Proof. exact (MK_COMB (@lem1109860 _25786 _25787) (@lem1109859 _25786 _25787 h)). Qed.
Lemma lem1109862 {_25786 _25787 : Type'} : (term44 _25786 _25787) = (term45 _25786 _25787).
Proof. exact (fun_ext (fun h : _25787 => @lem1109861 _25786 _25787 h)). Qed.
Lemma lem1109863 {_25787 : Type'} : (@all _25787) = (@all _25787).
Proof. exact (eq_refl (@all _25787)). Qed.
Lemma lem1109864 {_25786 _25787 : Type'} : (term46 _25786 _25787) = (term47 _25786 _25787).
Proof. exact (MK_COMB (@lem1109863 _25787) (@lem1109862 _25786 _25787)). Qed.
Lemma lem1109865 {_25786 _25787 : Type'} : (term4 _25786 _25787) = (term48 _25786 _25787).
Proof. exact (MK_COMB (@lem1109829 _25786 _25787) (@lem1109864 _25786 _25787)). Qed.
Lemma lem1109866 {_25786 _25787 : Type'} : term48 _25786 _25787.
Proof. exact (EQ_MP (@lem1109865 _25786 _25787) (@lem1109802 _25786 _25787)). Qed.
