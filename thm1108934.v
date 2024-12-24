Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108934_term_abbrevs.
Require Import thm1108491_spec.
Require Import thm1108877_spec.
Lemma lem1108878 {_25719 _25727 : Type'} : (term0 _25719 _25727) = (term1 _25719 _25727).
Proof. exact (eq_refl (term0 _25719 _25727)). Qed.
Lemma lem1108879 {_25719 _25727 : Type'} : term1 _25719 _25727.
Proof. exact (EQ_MP (@lem1108878 _25719 _25727) (@lem1108491 _25719 _25727)). Qed.
Lemma lem1108880 {_25719 _25727 : Type'} : term2 _25719 _25727.
Proof. exact (@lem1108879 _25719 _25727 term3). Qed.
Lemma lem1108881 {_25719 _25727 : Type'} : (term2 _25719 _25727) = (term4 _25719 _25727).
Proof. exact (eq_refl (term2 _25719 _25727)). Qed.
Lemma lem1108882 {_25719 _25727 : Type'} : term4 _25719 _25727.
Proof. exact (EQ_MP (@lem1108881 _25719 _25727) (@lem1108880 _25719 _25727)). Qed.
Lemma lem1108883 {_25719 _25727 : Type'} (h1 : (@ZIP _25719 _25727) = (term5 _25719 _25727)) : (@ZIP _25719 _25727) = (term5 _25719 _25727).
Proof. exact (h1). Qed.
Lemma lem1108884 {_25719 _25727 : Type'} (h1 : (@ZIP _25719 _25727) = (term5 _25719 _25727)) : (term5 _25719 _25727) = (@ZIP _25719 _25727).
Proof. exact (SYM (@lem1108883 _25719 _25727 h1)). Qed.
Lemma lem1108885 {_25719 _25727 : Type'} (h1 : (term5 _25719 _25727) = (@ZIP _25719 _25727)) : (term5 _25719 _25727) = (@ZIP _25719 _25727).
Proof. exact (h1). Qed.
Lemma lem1108886 {_25719 _25727 : Type'} (h1 : (term5 _25719 _25727) = (@ZIP _25719 _25727)) : (@ZIP _25719 _25727) = (term5 _25719 _25727).
Proof. exact (SYM (@lem1108885 _25719 _25727 h1)). Qed.
Lemma lem1108887 {_25719 _25727 : Type'} : ((@ZIP _25719 _25727) = (term5 _25719 _25727)) = ((term5 _25719 _25727) = (@ZIP _25719 _25727)).
Proof. exact (prop_ext (fun h1 : (@ZIP _25719 _25727) = (term5 _25719 _25727) => @lem1108884 _25719 _25727 h1) (fun h1 : (term5 _25719 _25727) = (@ZIP _25719 _25727) => @lem1108886 _25719 _25727 h1)). Qed.
Lemma lem1108890 {_25719 _25727 : Type'} : (term5 _25719 _25727) = (@ZIP _25719 _25727).
Proof. exact (EQ_MP (@lem1108887 _25719 _25727) (@lem1108877 _25719 _25727)). Qed.
Lemma lem1108891 {_25719 _25727 : Type'} : (term5 _25719 _25727) = (@ZIP _25719 _25727).
Proof. exact (@lem1108890 _25719 _25727). Qed.
Lemma lem1108892 {_25719 : Type'} : (@nil _25719) = (@nil _25719).
Proof. exact (eq_refl (@nil _25719)). Qed.
Lemma lem1108893 {_25719 _25727 : Type'} : (term6 _25719 _25727) = (@ZIP _25719 _25727 (@nil _25719)).
Proof. exact (MK_COMB (@lem1108891 _25719 _25727) (@lem1108892 _25719)). Qed.
Lemma lem1108894 {_25727 : Type'} (l2 : list _25727) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1108895 {_25719 _25727 : Type'} (l2 : list _25727) : (term7 _25719 _25727 l2) = (@ZIP _25719 _25727 (@nil _25719) l2).
Proof. exact (MK_COMB (@lem1108893 _25719 _25727) (@lem1108894 _25727 l2)). Qed.
Lemma lem1108896 {_25719 _25727 : Type'} : (@eq (list (prod _25719 _25727))) = (@eq (list (prod _25719 _25727))).
Proof. exact (eq_refl (@eq (list (prod _25719 _25727)))). Qed.
Lemma lem1108897 {_25719 _25727 : Type'} (l2 : list _25727) : (term8 _25719 _25727 l2) = (term9 _25719 _25727 l2).
Proof. exact (MK_COMB (@lem1108896 _25719 _25727) (@lem1108895 _25719 _25727 l2)). Qed.
Lemma lem1108898 {_25719 _25727 : Type'} : (@nil (prod _25719 _25727)) = (@nil (prod _25719 _25727)).
Proof. exact (eq_refl (@nil (prod _25719 _25727))). Qed.
Lemma lem1108899 {_25719 _25727 : Type'} (l2 : list _25727) : ((term7 _25719 _25727 l2) = (@nil (prod _25719 _25727))) = ((@ZIP _25719 _25727 (@nil _25719) l2) = (@nil (prod _25719 _25727))).
Proof. exact (MK_COMB (@lem1108897 _25719 _25727 l2) (@lem1108898 _25719 _25727)). Qed.
Lemma lem1108900 {_25719 _25727 : Type'} : (term10 _25719 _25727) = (term11 _25719 _25727).
Proof. exact (fun_ext (fun l2 : list _25727 => @lem1108899 _25719 _25727 l2)). Qed.
Lemma lem1108901 {_25727 : Type'} : (@all (list _25727)) = (@all (list _25727)).
Proof. exact (eq_refl (@all (list _25727))). Qed.
Lemma lem1108902 {_25719 _25727 : Type'} : (term12 _25719 _25727) = (term13 _25719 _25727).
Proof. exact (MK_COMB (@lem1108901 _25727) (@lem1108900 _25719 _25727)). Qed.
Lemma lem1108903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1108904 {_25719 _25727 : Type'} : (term14 _25719 _25727) = (term15 _25719 _25727).
Proof. exact (MK_COMB (@lem1108903) (@lem1108902 _25719 _25727)). Qed.
Lemma lem1108906 {_25719 _25727 : Type'} : (term5 _25719 _25727) = (@ZIP _25719 _25727).
Proof. exact (EQ_MP (@lem1108887 _25719 _25727) (@lem1108877 _25719 _25727)). Qed.
Lemma lem1108907 {_25719 _25727 : Type'} : (term5 _25719 _25727) = (@ZIP _25719 _25727).
Proof. exact (@lem1108906 _25719 _25727). Qed.
Lemma lem1108908 {_25719 : Type'} (h1' : _25719) (t1 : list _25719) : (@cons _25719 h1' t1) = (@cons _25719 h1' t1).
Proof. exact (eq_refl (@cons _25719 h1' t1)). Qed.
Lemma lem1108909 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) : (term16 _25719 _25727 h1' t1) = (term17 _25719 _25727 h1' t1).
Proof. exact (MK_COMB (@lem1108907 _25719 _25727) (@lem1108908 _25719 h1' t1)). Qed.
Lemma lem1108910 {_25727 : Type'} (l2 : list _25727) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1108911 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : (term18 _25719 _25727 h1' t1 l2) = (term19 _25719 _25727 h1' t1 l2).
Proof. exact (MK_COMB (@lem1108909 _25719 _25727 h1' t1) (@lem1108910 _25727 l2)). Qed.
Lemma lem1108912 {_25719 _25727 : Type'} : (@eq (list (prod _25719 _25727))) = (@eq (list (prod _25719 _25727))).
Proof. exact (eq_refl (@eq (list (prod _25719 _25727)))). Qed.
Lemma lem1108913 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : (term20 _25719 _25727 h1' t1 l2) = (term21 _25719 _25727 h1' t1 l2).
Proof. exact (MK_COMB (@lem1108912 _25719 _25727) (@lem1108911 _25719 _25727 h1' t1 l2)). Qed.
Lemma lem1108915 {_25719 _25727 : Type'} : (term5 _25719 _25727) = (@ZIP _25719 _25727).
Proof. exact (EQ_MP (@lem1108887 _25719 _25727) (@lem1108877 _25719 _25727)). Qed.
Lemma lem1108916 {_25719 _25727 : Type'} : (term5 _25719 _25727) = (@ZIP _25719 _25727).
Proof. exact (@lem1108915 _25719 _25727). Qed.
Lemma lem1108917 {_25719 : Type'} (t1 : list _25719) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem1108918 {_25719 _25727 : Type'} (t1 : list _25719) : (term22 _25719 _25727 t1) = (@ZIP _25719 _25727 t1).
Proof. exact (MK_COMB (@lem1108916 _25719 _25727) (@lem1108917 _25719 t1)). Qed.
Lemma lem1108919 {_25727 : Type'} (l2 : list _25727) : (@tl _25727 l2) = (@tl _25727 l2).
Proof. exact (eq_refl (@tl _25727 l2)). Qed.
Lemma lem1108920 {_25719 _25727 : Type'} (t1 : list _25719) (l2 : list _25727) : (term23 _25719 _25727 t1 l2) = (term24 _25719 _25727 t1 l2).
Proof. exact (MK_COMB (@lem1108918 _25719 _25727 t1) (@lem1108919 _25727 l2)). Qed.
Lemma lem1108921 {_25719 _25727 : Type'} (h1' : _25719) (l2 : list _25727) : (term25 _25719 _25727 h1' l2) = (term25 _25719 _25727 h1' l2).
Proof. exact (eq_refl (term25 _25719 _25727 h1' l2)). Qed.
Lemma lem1108922 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : (term26 _25719 _25727 h1' t1 l2) = (term27 _25719 _25727 h1' t1 l2).
Proof. exact (MK_COMB (@lem1108921 _25719 _25727 h1' l2) (@lem1108920 _25719 _25727 t1 l2)). Qed.
Lemma lem1108923 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : ((term18 _25719 _25727 h1' t1 l2) = (term26 _25719 _25727 h1' t1 l2)) = ((term19 _25719 _25727 h1' t1 l2) = (term27 _25719 _25727 h1' t1 l2)).
Proof. exact (MK_COMB (@lem1108913 _25719 _25727 h1' t1 l2) (@lem1108922 _25719 _25727 h1' t1 l2)). Qed.
Lemma lem1108924 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) : (term28 _25719 _25727 h1' t1) = (term29 _25719 _25727 h1' t1).
Proof. exact (fun_ext (fun l2 : list _25727 => @lem1108923 _25719 _25727 h1' t1 l2)). Qed.
Lemma lem1108925 {_25727 : Type'} : (@all (list _25727)) = (@all (list _25727)).
Proof. exact (eq_refl (@all (list _25727))). Qed.
Lemma lem1108926 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) : (term30 _25719 _25727 h1' t1) = (term31 _25719 _25727 h1' t1).
Proof. exact (MK_COMB (@lem1108925 _25727) (@lem1108924 _25719 _25727 h1' t1)). Qed.
Lemma lem1108927 {_25719 _25727 : Type'} (h1' : _25719) : (term32 _25719 _25727 h1') = (term33 _25719 _25727 h1').
Proof. exact (fun_ext (fun t1 : list _25719 => @lem1108926 _25719 _25727 h1' t1)). Qed.
Lemma lem1108928 {_25719 : Type'} : (@all (list _25719)) = (@all (list _25719)).
Proof. exact (eq_refl (@all (list _25719))). Qed.
Lemma lem1108929 {_25719 _25727 : Type'} (h1' : _25719) : (term34 _25719 _25727 h1') = (term35 _25719 _25727 h1').
Proof. exact (MK_COMB (@lem1108928 _25719) (@lem1108927 _25719 _25727 h1')). Qed.
Lemma lem1108930 {_25719 _25727 : Type'} : (term36 _25719 _25727) = (term37 _25719 _25727).
Proof. exact (fun_ext (fun h1' : _25719 => @lem1108929 _25719 _25727 h1')). Qed.
Lemma lem1108931 {_25719 : Type'} : (@all _25719) = (@all _25719).
Proof. exact (eq_refl (@all _25719)). Qed.
Lemma lem1108932 {_25719 _25727 : Type'} : (term38 _25719 _25727) = (term39 _25719 _25727).
Proof. exact (MK_COMB (@lem1108931 _25719) (@lem1108930 _25719 _25727)). Qed.
Lemma lem1108933 {_25719 _25727 : Type'} : (term4 _25719 _25727) = (term40 _25719 _25727).
Proof. exact (MK_COMB (@lem1108904 _25719 _25727) (@lem1108932 _25719 _25727)). Qed.
Lemma lem1108934 {_25719 _25727 : Type'} : term40 _25719 _25727.
Proof. exact (EQ_MP (@lem1108933 _25719 _25727) (@lem1108882 _25719 _25727)). Qed.
