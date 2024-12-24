Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import APPEND_BUTLAST_LAST_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1098347_spec.
Require Import thm1098348_spec.
Require Import thm1098917_spec.
Require Import thm1098923_spec.
Require Import thm1098924_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1201818 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1201819 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1201820 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1201819 A h) (@lem1201818 A h)). Qed.
Lemma lem1201821 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem1201820 A h t). Qed.
Lemma lem1201822 {A : Type'} (h : A) (t : list A) : (term2 A h t) = (term3 A h t).
Proof. exact (eq_refl (term2 A h t)). Qed.
Lemma lem1201823 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (EQ_MP (@lem1201822 A h t) (@lem1201821 A h t)). Qed.
Lemma lem1201824 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1201840 {A : Type'} (P : type1143 A) : term5 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1201841 {_28076 : Type'} (P : type1143 _28076) : term5 _28076 P.
Proof. exact (@lem1201840 _28076 P). Qed.
Lemma lem1201842 {_28076 : Type'} : term6 _28076.
Proof. exact (@lem1201841 _28076 (term7 _28076)). Qed.
Lemma lem1201843 {_28076 : Type'} : (term8 _28076) = (term9 _28076).
Proof. exact (eq_refl (term8 _28076)). Qed.
Lemma lem1201844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1201845 {_28076 : Type'} : (term10 _28076) = (term11 _28076).
Proof. exact (MK_COMB (@lem1201844) (@lem1201843 _28076)). Qed.
Lemma lem1201846 {_28076 : Type'} (t : list _28076) : (term12 _28076 t) = (term13 _28076 t).
Proof. exact (eq_refl (term12 _28076 t)). Qed.
Lemma lem1201847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1201848 {_28076 : Type'} (t : list _28076) : (term14 _28076 t) = (term15 _28076 t).
Proof. exact (MK_COMB (@lem1201847) (@lem1201846 _28076 t)). Qed.
Lemma lem1201849 {_28076 : Type'} (h : _28076) (t : list _28076) : (term16 _28076 h t) = (term17 _28076 h t).
Proof. exact (eq_refl (term16 _28076 h t)). Qed.
Lemma lem1201850 {_28076 : Type'} (h : _28076) (t : list _28076) : (term18 _28076 h t) = (term19 _28076 h t).
Proof. exact (MK_COMB (@lem1201848 _28076 t) (@lem1201849 _28076 h t)). Qed.
Lemma lem1201851 {_28076 : Type'} (h : _28076) : (term20 _28076 h) = (term21 _28076 h).
Proof. exact (fun_ext (fun t : list _28076 => @lem1201850 _28076 h t)). Qed.
Lemma lem1201852 {_28076 : Type'} : (@all (list _28076)) = (@all (list _28076)).
Proof. exact (eq_refl (@all (list _28076))). Qed.
Lemma lem1201853 {_28076 : Type'} (h : _28076) : (term22 _28076 h) = (term23 _28076 h).
Proof. exact (MK_COMB (@lem1201852 _28076) (@lem1201851 _28076 h)). Qed.
Lemma lem1201854 {_28076 : Type'} : (term24 _28076) = (term25 _28076).
Proof. exact (fun_ext (fun h : _28076 => @lem1201853 _28076 h)). Qed.
Lemma lem1201855 {_28076 : Type'} : (@all _28076) = (@all _28076).
Proof. exact (eq_refl (@all _28076)). Qed.
Lemma lem1201856 {_28076 : Type'} : (term26 _28076) = (term27 _28076).
Proof. exact (MK_COMB (@lem1201855 _28076) (@lem1201854 _28076)). Qed.
Lemma lem1201857 {_28076 : Type'} : (term28 _28076) = (term29 _28076).
Proof. exact (MK_COMB (@lem1201845 _28076) (@lem1201856 _28076)). Qed.
Lemma lem1201858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1201859 {_28076 : Type'} : (term30 _28076) = (term31 _28076).
Proof. exact (MK_COMB (@lem1201858) (@lem1201857 _28076)). Qed.
Lemma lem1201860 {_28076 : Type'} (l : list _28076) : (term12 _28076 l) = (term13 _28076 l).
Proof. exact (eq_refl (term12 _28076 l)). Qed.
Lemma lem1201861 {_28076 : Type'} : (term32 _28076) = (term7 _28076).
Proof. exact (fun_ext (fun l : list _28076 => @lem1201860 _28076 l)). Qed.
Lemma lem1201862 {_28076 : Type'} : (@all (list _28076)) = (@all (list _28076)).
Proof. exact (eq_refl (@all (list _28076))). Qed.
Lemma lem1201863 {_28076 : Type'} : (term33 _28076) = (term34 _28076).
Proof. exact (MK_COMB (@lem1201862 _28076) (@lem1201861 _28076)). Qed.
Lemma lem1201864 {_28076 : Type'} : (term6 _28076) = (term35 _28076).
Proof. exact (MK_COMB (@lem1201859 _28076) (@lem1201863 _28076)). Qed.
Lemma lem1201865 {_28076 : Type'} : term35 _28076.
Proof. exact (EQ_MP (@lem1201864 _28076) (@lem1201842 _28076)). Qed.
Lemma lem1201866 {_28076 : Type'} (t : list _28076) (h1 : term13 _28076 t) : term13 _28076 t.
Proof. exact (h1). Qed.
Lemma lem1201870 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1201871 {_28076 : Type'} (x : list _28076) : (x = x) = True.
Proof. exact (@lem1201870 (list _28076) x). Qed.
Lemma lem1201872 {_28076 : Type'} : ((@nil _28076) = (@nil _28076)) = True.
Proof. exact (@lem1201871 _28076 (@nil _28076)). Qed.
Lemma lem1201873 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1201874 {_28076 : Type'} : (term36 _28076) = (~ True).
Proof. exact (MK_COMB (@lem1201873) (@lem1201872 _28076)). Qed.
Lemma lem1201876 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1201877 {_28076 : Type'} : (term36 _28076) = False.
Proof. exact (TRANS (@lem1201874 _28076) (@lem1201876)). Qed.
Lemma lem1201878 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1201879 {_28076 : Type'} : (term37 _28076) = (imp False).
Proof. exact (MK_COMB (@lem1201878) (@lem1201877 _28076)). Qed.
Lemma lem1201883 {_25251 : Type'} : (@List.removelast _25251 (@nil _25251)) = (@nil _25251).
Proof. exact (proj1 (@lem1098917 _25251)). Qed.
Lemma lem1201884 {_28076 : Type'} : (@List.removelast _28076 (@nil _28076)) = (@nil _28076).
Proof. exact (@lem1201883 _28076). Qed.
Lemma lem1201885 {_28076 : Type'} : (@List.app _28076) = (@List.app _28076).
Proof. exact (eq_refl (@List.app _28076)). Qed.
Lemma lem1201886 {_28076 : Type'} : (term38 _28076) = (@List.app _28076 (@nil _28076)).
Proof. exact (MK_COMB (@lem1201885 _28076) (@lem1201884 _28076)). Qed.
Lemma lem1201887 {_28076 : Type'} : (term39 _28076) = (term39 _28076).
Proof. exact (eq_refl (term39 _28076)). Qed.
Lemma lem1201888 {_28076 : Type'} : (term40 _28076) = (term41 _28076).
Proof. exact (MK_COMB (@lem1201886 _28076) (@lem1201887 _28076)). Qed.
Lemma lem1201889 {_28076 : Type'} : (@eq (list _28076)) = (@eq (list _28076)).
Proof. exact (eq_refl (@eq (list _28076))). Qed.
Lemma lem1201890 {_28076 : Type'} : (term42 _28076) = (term43 _28076).
Proof. exact (MK_COMB (@lem1201889 _28076) (@lem1201888 _28076)). Qed.
Lemma lem1201891 {_28076 : Type'} : (@nil _28076) = (@nil _28076).
Proof. exact (eq_refl (@nil _28076)). Qed.
Lemma lem1201892 {_28076 : Type'} : ((term40 _28076) = (@nil _28076)) = ((term41 _28076) = (@nil _28076)).
Proof. exact (MK_COMB (@lem1201890 _28076) (@lem1201891 _28076)). Qed.
Lemma lem1201895 {_28076 : Type'} : (term9 _28076) = (term44 _28076).
Proof. exact (MK_COMB (@lem1201879 _28076) (@lem1201892 _28076)). Qed.
Lemma lem1201897 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1201898 {_28076 : Type'} : (term44 _28076) = True.
Proof. exact (@lem1201897 ((term41 _28076) = (@nil _28076))). Qed.
Lemma lem1201899 {_28076 : Type'} : (term9 _28076) = True.
Proof. exact (TRANS (@lem1201895 _28076) (@lem1201898 _28076)). Qed.
Lemma lem1201900 {_28076 : Type'} : True = (term9 _28076).
Proof. exact (SYM (@lem1201899 _28076)). Qed.
Lemma lem1201901 {_28076 : Type'} : term9 _28076.
Proof. exact (EQ_MP (@lem1201900 _28076) (@lem0)). Qed.
Lemma lem1201905 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1201824 A h t (@lem1201823 A h t)). Qed.
Lemma lem1201906 {_28076 : Type'} (h : _28076) (t : list _28076) : ((@cons _28076 h t) = (@nil _28076)) = False.
Proof. exact (@lem1201905 _28076 h t). Qed.
Lemma lem1201907 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1201908 {_28076 : Type'} (h : _28076) (t : list _28076) : (term3 _28076 h t) = (~ False).
Proof. exact (MK_COMB (@lem1201907) (@lem1201906 _28076 h t)). Qed.
Lemma lem1201910 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1201911 {_28076 : Type'} (h : _28076) (t : list _28076) : (term3 _28076 h t) = True.
Proof. exact (TRANS (@lem1201908 _28076 h t) (@lem1201910)). Qed.
Lemma lem1201912 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1201913 {_28076 : Type'} (h : _28076) (t : list _28076) : (term45 _28076 h t) = (imp True).
Proof. exact (MK_COMB (@lem1201912) (@lem1201911 _28076 h t)). Qed.
Lemma lem1201917 {_25251 : Type'} (h : _25251) (t : list _25251) : (term46 _25251 h t) = (term47 _25251 h t).
Proof. exact (EQ_MP (@lem1098924 _25251 h t) (@lem1098923 _25251 h t)). Qed.
Lemma lem1201918 {_28076 : Type'} (h : _28076) (t : list _28076) : (term46 _28076 h t) = (term47 _28076 h t).
Proof. exact (@lem1201917 _28076 h t). Qed.
Lemma lem1201923 {_28076 : Type'} : (@List.app _28076) = (@List.app _28076).
Proof. exact (eq_refl (@List.app _28076)). Qed.
Lemma lem1201924 {_28076 : Type'} (h : _28076) (t : list _28076) : (term48 _28076 h t) = (term49 _28076 h t).
Proof. exact (MK_COMB (@lem1201923 _28076) (@lem1201918 _28076 h t)). Qed.
Lemma lem1201926 {A : Type'} (h : A) (t : list A) : (term50 A h t) = (term51 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1201927 {_28076 : Type'} (h : _28076) (t : list _28076) : (term50 _28076 h t) = (term51 _28076 h t).
Proof. exact (@lem1201926 _28076 h t). Qed.
Lemma lem1201932 {_28076 : Type'} : (@cons _28076) = (@cons _28076).
Proof. exact (eq_refl (@cons _28076)). Qed.
Lemma lem1201933 {_28076 : Type'} (h : _28076) (t : list _28076) : (term52 _28076 h t) = (term53 _28076 h t).
Proof. exact (MK_COMB (@lem1201932 _28076) (@lem1201927 _28076 h t)). Qed.
Lemma lem1201934 {_28076 : Type'} : (@nil _28076) = (@nil _28076).
Proof. exact (eq_refl (@nil _28076)). Qed.
Lemma lem1201935 {_28076 : Type'} (h : _28076) (t : list _28076) : (term54 _28076 h t) = (term55 _28076 h t).
Proof. exact (MK_COMB (@lem1201933 _28076 h t) (@lem1201934 _28076)). Qed.
Lemma lem1201936 {_28076 : Type'} (h : _28076) (t : list _28076) : (term56 _28076 h t) = (term57 _28076 h t).
Proof. exact (MK_COMB (@lem1201924 _28076 h t) (@lem1201935 _28076 h t)). Qed.
Lemma lem1201937 {_28076 : Type'} : (@eq (list _28076)) = (@eq (list _28076)).
Proof. exact (eq_refl (@eq (list _28076))). Qed.
Lemma lem1201938 {_28076 : Type'} (h : _28076) (t : list _28076) : (term58 _28076 h t) = (term59 _28076 h t).
Proof. exact (MK_COMB (@lem1201937 _28076) (@lem1201936 _28076 h t)). Qed.
Lemma lem1201939 {_28076 : Type'} (h : _28076) (t : list _28076) : (@cons _28076 h t) = (@cons _28076 h t).
Proof. exact (eq_refl (@cons _28076 h t)). Qed.
Lemma lem1201940 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term56 _28076 h t) = (@cons _28076 h t)) = ((term57 _28076 h t) = (@cons _28076 h t)).
Proof. exact (MK_COMB (@lem1201938 _28076 h t) (@lem1201939 _28076 h t)). Qed.
Lemma lem1201943 {_28076 : Type'} (h : _28076) (t : list _28076) : (term17 _28076 h t) = (term60 _28076 h t).
Proof. exact (MK_COMB (@lem1201913 _28076 h t) (@lem1201940 _28076 h t)). Qed.
Lemma lem1201945 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1201946 {_28076 : Type'} (h : _28076) (t : list _28076) : (term60 _28076 h t) = ((term57 _28076 h t) = (@cons _28076 h t)).
Proof. exact (@lem1201945 ((term57 _28076 h t) = (@cons _28076 h t))). Qed.
Lemma lem1201957 {_28076 : Type'} (h : _28076) (t : list _28076) : (term17 _28076 h t) = ((term57 _28076 h t) = (@cons _28076 h t)).
Proof. exact (TRANS (@lem1201943 _28076 h t) (@lem1201946 _28076 h t)). Qed.
Lemma lem1201958 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term57 _28076 h t) = (@cons _28076 h t)) = (term17 _28076 h t).
Proof. exact (SYM (@lem1201957 _28076 h t)). Qed.
Lemma lem1201959 {_28076 : Type'} (_474 : list _28076) (_475 : Prop) (_476 : type1143 _28076) (_477 : list _28076) : (term61 _28076 _476 _475 _474 _477) = (term62 _28076 _474 _475 _476 _477).
Proof. exact (@lem13473 (list _28076) _474 _475 _476 _477). Qed.
Lemma lem1201960 {_28076 : Type'} (_474 : list _28076) (_475 : Prop) (h : _28076) (t : list _28076) (_477 : list _28076) : (term63 _28076 h t _475 _474 _477) = (term64 _28076 _474 _475 h t _477).
Proof. exact (@lem1201959 _28076 _474 _475 (term65 _28076 h t) _477). Qed.
Lemma lem1201961 {_28076 : Type'} (h : _28076) (t : list _28076) : (term66 _28076 h t) = (term67 _28076 h t).
Proof. exact (@lem1201960 _28076 (@nil _28076) (t = (@nil _28076)) h t (term68 _28076 h t)). Qed.
Lemma lem1201962 {_28076 : Type'} (h : _28076) (t : list _28076) : (term69 _28076 h t) = ((term70 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl (term69 _28076 h t)). Qed.
Lemma lem1201963 {_28076 : Type'} (t : list _28076) : (term71 _28076 t) = (term71 _28076 t).
Proof. exact (eq_refl (term71 _28076 t)). Qed.
Lemma lem1201964 {_28076 : Type'} (h : _28076) (t : list _28076) : (term72 _28076 h t) = (term73 _28076 h t).
Proof. exact (MK_COMB (@lem1201963 _28076 t) (@lem1201962 _28076 h t)). Qed.
Lemma lem1201965 {_28076 : Type'} (h : _28076) (t : list _28076) : (term74 _28076 h t) = ((term75 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl (term74 _28076 h t)). Qed.
Lemma lem1201966 {_28076 : Type'} (t : list _28076) : (term76 _28076 t) = (term76 _28076 t).
Proof. exact (eq_refl (term76 _28076 t)). Qed.
Lemma lem1201967 {_28076 : Type'} (h : _28076) (t : list _28076) : (term77 _28076 h t) = (term78 _28076 h t).
Proof. exact (MK_COMB (@lem1201966 _28076 t) (@lem1201965 _28076 h t)). Qed.
Lemma lem1201968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1201969 {_28076 : Type'} (h : _28076) (t : list _28076) : (term79 _28076 h t) = (term80 _28076 h t).
Proof. exact (MK_COMB (@lem1201968) (@lem1201967 _28076 h t)). Qed.
Lemma lem1201970 {_28076 : Type'} (h : _28076) (t : list _28076) : (term67 _28076 h t) = (term81 _28076 h t).
Proof. exact (MK_COMB (@lem1201969 _28076 h t) (@lem1201964 _28076 h t)). Qed.
Lemma lem1201971 {_28076 : Type'} (h : _28076) (t : list _28076) : (term66 _28076 h t) = ((term57 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl (term66 _28076 h t)). Qed.
Lemma lem1201972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1201973 {_28076 : Type'} (h : _28076) (t : list _28076) : (term82 _28076 h t) = (term83 _28076 h t).
Proof. exact (MK_COMB (@lem1201972) (@lem1201971 _28076 h t)). Qed.
Lemma lem1201974 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term66 _28076 h t) = (term67 _28076 h t)) = (((term57 _28076 h t) = (@cons _28076 h t)) = (term81 _28076 h t)).
Proof. exact (MK_COMB (@lem1201973 _28076 h t) (@lem1201970 _28076 h t)). Qed.
Lemma lem1201975 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term57 _28076 h t) = (@cons _28076 h t)) = (term81 _28076 h t).
Proof. exact (EQ_MP (@lem1201974 _28076 h t) (@lem1201961 _28076 h t)). Qed.
Lemma lem1201976 {_28076 : Type'} (h : _28076) (t : list _28076) : (term81 _28076 h t) = ((term57 _28076 h t) = (@cons _28076 h t)).
Proof. exact (SYM (@lem1201975 _28076 h t)). Qed.
Lemma lem1201977 {_28076 : Type'} (t : list _28076) (h1 : t = (@nil _28076)) : t = (@nil _28076).
Proof. exact (h1). Qed.
Lemma lem1201978 {_28076 : Type'} (t : list _28076) : (t = (@nil _28076)) = ((t = (@nil _28076)) = True).
Proof. exact (@lem7 (t = (@nil _28076))). Qed.
Lemma lem1201979 {_28076 : Type'} (t : list _28076) (h1 : t = (@nil _28076)) : (t = (@nil _28076)) = True.
Proof. exact (EQ_MP (@lem1201978 _28076 t) (@lem1201977 _28076 t h1)). Qed.
Lemma lem1201980 {_28076 : Type'} (h : _28076) (t : list _28076) : (term84 _28076 h t) = (term84 _28076 h t).
Proof. exact (eq_refl (term84 _28076 h t)). Qed.
Lemma lem1201981 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : (term85 _28076 h t) = (term86 _28076 h t).
Proof. exact (MK_COMB (@lem1201980 _28076 h t) (@lem1201979 _28076 t h1)). Qed.
Lemma lem1201982 {_28076 : Type'} (h : _28076) (t : list _28076) : (term86 _28076 h t) = ((term87 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl (term86 _28076 h t)). Qed.
Lemma lem1201983 {_28076 : Type'} (h : _28076) (t : list _28076) : (term88 _28076 h t) = (term88 _28076 h t).
Proof. exact (eq_refl (term88 _28076 h t)). Qed.
Lemma lem1201984 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term85 _28076 h t) = (term86 _28076 h t)) = ((term85 _28076 h t) = ((term87 _28076 h t) = (@cons _28076 h t))).
Proof. exact (MK_COMB (@lem1201983 _28076 h t) (@lem1201982 _28076 h t)). Qed.
Lemma lem1201985 {_28076 : Type'} (h : _28076) (t : list _28076) : (term85 _28076 h t) = ((term75 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl (term85 _28076 h t)). Qed.
Lemma lem1201986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1201987 {_28076 : Type'} (h : _28076) (t : list _28076) : (term88 _28076 h t) = (term89 _28076 h t).
Proof. exact (MK_COMB (@lem1201986) (@lem1201985 _28076 h t)). Qed.
Lemma lem1201988 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term87 _28076 h t) = (@cons _28076 h t)) = ((term87 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl ((term87 _28076 h t) = (@cons _28076 h t))). Qed.
Lemma lem1201989 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term85 _28076 h t) = ((term87 _28076 h t) = (@cons _28076 h t))) = (((term75 _28076 h t) = (@cons _28076 h t)) = ((term87 _28076 h t) = (@cons _28076 h t))).
Proof. exact (MK_COMB (@lem1201987 _28076 h t) (@lem1201988 _28076 h t)). Qed.
Lemma lem1201990 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term85 _28076 h t) = (term86 _28076 h t)) = (((term75 _28076 h t) = (@cons _28076 h t)) = ((term87 _28076 h t) = (@cons _28076 h t))).
Proof. exact (TRANS (@lem1201984 _28076 h t) (@lem1201989 _28076 h t)). Qed.
Lemma lem1201991 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : ((term75 _28076 h t) = (@cons _28076 h t)) = ((term87 _28076 h t) = (@cons _28076 h t)).
Proof. exact (EQ_MP (@lem1201990 _28076 h t) (@lem1201981 _28076 h t h1)). Qed.
Lemma lem1201992 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : ((term87 _28076 h t) = (@cons _28076 h t)) = ((term75 _28076 h t) = (@cons _28076 h t)).
Proof. exact (SYM (@lem1201991 _28076 h t h1)). Qed.
Lemma lem1201993 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) : term90 _28076 t.
Proof. exact (h1). Qed.
Lemma lem1201994 {_28076 : Type'} (t : list _28076) : term91 _28076 t.
Proof. exact (@lem82 (t = (@nil _28076))). Qed.
Lemma lem1201995 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) : (t = (@nil _28076)) = False.
Proof. exact (@lem1201994 _28076 t (@lem1201993 _28076 t h1)). Qed.
Lemma lem1201996 {_28076 : Type'} (h : _28076) (t : list _28076) : (term92 _28076 h t) = (term92 _28076 h t).
Proof. exact (eq_refl (term92 _28076 h t)). Qed.
Lemma lem1201997 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) : (term93 _28076 h t) = (term94 _28076 h t).
Proof. exact (MK_COMB (@lem1201996 _28076 h t) (@lem1201995 _28076 t h1)). Qed.
Lemma lem1201998 {_28076 : Type'} (h : _28076) (t : list _28076) : (term94 _28076 h t) = ((term95 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl (term94 _28076 h t)). Qed.
Lemma lem1201999 {_28076 : Type'} (h : _28076) (t : list _28076) : (term96 _28076 h t) = (term96 _28076 h t).
Proof. exact (eq_refl (term96 _28076 h t)). Qed.
Lemma lem1202000 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term93 _28076 h t) = (term94 _28076 h t)) = ((term93 _28076 h t) = ((term95 _28076 h t) = (@cons _28076 h t))).
Proof. exact (MK_COMB (@lem1201999 _28076 h t) (@lem1201998 _28076 h t)). Qed.
Lemma lem1202001 {_28076 : Type'} (h : _28076) (t : list _28076) : (term93 _28076 h t) = ((term70 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl (term93 _28076 h t)). Qed.
Lemma lem1202002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1202003 {_28076 : Type'} (h : _28076) (t : list _28076) : (term96 _28076 h t) = (term97 _28076 h t).
Proof. exact (MK_COMB (@lem1202002) (@lem1202001 _28076 h t)). Qed.
Lemma lem1202004 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term95 _28076 h t) = (@cons _28076 h t)) = ((term95 _28076 h t) = (@cons _28076 h t)).
Proof. exact (eq_refl ((term95 _28076 h t) = (@cons _28076 h t))). Qed.
Lemma lem1202005 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term93 _28076 h t) = ((term95 _28076 h t) = (@cons _28076 h t))) = (((term70 _28076 h t) = (@cons _28076 h t)) = ((term95 _28076 h t) = (@cons _28076 h t))).
Proof. exact (MK_COMB (@lem1202003 _28076 h t) (@lem1202004 _28076 h t)). Qed.
Lemma lem1202006 {_28076 : Type'} (h : _28076) (t : list _28076) : ((term93 _28076 h t) = (term94 _28076 h t)) = (((term70 _28076 h t) = (@cons _28076 h t)) = ((term95 _28076 h t) = (@cons _28076 h t))).
Proof. exact (TRANS (@lem1202000 _28076 h t) (@lem1202005 _28076 h t)). Qed.
Lemma lem1202007 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) : ((term70 _28076 h t) = (@cons _28076 h t)) = ((term95 _28076 h t) = (@cons _28076 h t)).
Proof. exact (EQ_MP (@lem1202006 _28076 h t) (@lem1201997 _28076 h t h1)). Qed.
Lemma lem1202008 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) : ((term95 _28076 h t) = (@cons _28076 h t)) = ((term70 _28076 h t) = (@cons _28076 h t)).
Proof. exact (SYM (@lem1202007 _28076 h t h1)). Qed.
Lemma lem1202019 {A : Type'} : term98 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1202020 {A : Type'} (l : list A) : term99 A l.
Proof. exact (@lem1202019 A l). Qed.
Lemma lem1202021 {A : Type'} (l : list A) : (term99 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term99 A l)). Qed.
Lemma lem1202033 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1202021 A l) (@lem1202020 A l)). Qed.
Lemma lem1202034 {_28076 : Type'} (l : list _28076) : (@List.app _28076 (@nil _28076) l) = l.
Proof. exact (@lem1202033 _28076 l). Qed.
Lemma lem1202035 {_28076 : Type'} (h : _28076) (t : list _28076) : (term87 _28076 h t) = (term100 _28076 h t).
Proof. exact (@lem1202034 _28076 (term100 _28076 h t)). Qed.
Lemma lem1202037 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1202038 {_28076 : Type'} (t2 : _28076) (t1 : _28076) : (@COND _28076 True t1 t2) = t1.
Proof. exact (@lem1202037 _28076 t2 t1). Qed.
Lemma lem1202039 {_28076 : Type'} (t : list _28076) (h : _28076) : (term101 _28076 h t) = h.
Proof. exact (@lem1202038 _28076 (@LAST _28076 t) h). Qed.
Lemma lem1202040 {_28076 : Type'} : (@cons _28076) = (@cons _28076).
Proof. exact (eq_refl (@cons _28076)). Qed.
Lemma lem1202041 {_28076 : Type'} (t : list _28076) (h : _28076) : (term102 _28076 h t) = (@cons _28076 h).
Proof. exact (MK_COMB (@lem1202040 _28076) (@lem1202039 _28076 t h)). Qed.
Lemma lem1202042 {_28076 : Type'} : (@nil _28076) = (@nil _28076).
Proof. exact (eq_refl (@nil _28076)). Qed.
Lemma lem1202043 {_28076 : Type'} (t : list _28076) (h : _28076) : (term100 _28076 h t) = (@cons _28076 h (@nil _28076)).
Proof. exact (MK_COMB (@lem1202041 _28076 t h) (@lem1202042 _28076)). Qed.
Lemma lem1202044 {_28076 : Type'} (t : list _28076) (h : _28076) : (term87 _28076 h t) = (@cons _28076 h (@nil _28076)).
Proof. exact (TRANS (@lem1202035 _28076 h t) (@lem1202043 _28076 t h)). Qed.
Lemma lem1202045 {_28076 : Type'} : (@eq (list _28076)) = (@eq (list _28076)).
Proof. exact (eq_refl (@eq (list _28076))). Qed.
Lemma lem1202046 {_28076 : Type'} (t : list _28076) (h : _28076) : (term103 _28076 h t) = (term104 _28076 h).
Proof. exact (MK_COMB (@lem1202045 _28076) (@lem1202044 _28076 t h)). Qed.
Lemma lem1202048 {_28076 : Type'} (t : list _28076) (h1 : t = (@nil _28076)) : t = (@nil _28076).
Proof. exact (h1). Qed.
Lemma lem1202049 {_28076 : Type'} (h : _28076) : (@cons _28076 h) = (@cons _28076 h).
Proof. exact (eq_refl (@cons _28076 h)). Qed.
Lemma lem1202050 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : (@cons _28076 h t) = (@cons _28076 h (@nil _28076)).
Proof. exact (MK_COMB (@lem1202049 _28076 h) (@lem1202048 _28076 t h1)). Qed.
Lemma lem1202051 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : ((term87 _28076 h t) = (@cons _28076 h t)) = ((@cons _28076 h (@nil _28076)) = (@cons _28076 h (@nil _28076))).
Proof. exact (MK_COMB (@lem1202046 _28076 t h) (@lem1202050 _28076 h t h1)). Qed.
Lemma lem1202053 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1202054 {_28076 : Type'} (x : list _28076) : (x = x) = True.
Proof. exact (@lem1202053 (list _28076) x). Qed.
Lemma lem1202055 {_28076 : Type'} (h : _28076) : ((@cons _28076 h (@nil _28076)) = (@cons _28076 h (@nil _28076))) = True.
Proof. exact (@lem1202054 _28076 (@cons _28076 h (@nil _28076))). Qed.
Lemma lem1202056 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : ((term87 _28076 h t) = (@cons _28076 h t)) = True.
Proof. exact (TRANS (@lem1202051 _28076 h t h1) (@lem1202055 _28076 h)). Qed.
Lemma lem1202057 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : True = ((term87 _28076 h t) = (@cons _28076 h t)).
Proof. exact (SYM (@lem1202056 _28076 h t h1)). Qed.
Lemma lem1202058 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : (term87 _28076 h t) = (@cons _28076 h t).
Proof. exact (EQ_MP (@lem1202057 _28076 h t h1) (@lem0)). Qed.
Lemma lem1202059 {A : Type'} : term105 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1202060 {A : Type'} (h : A) : term106 A h.
Proof. exact (@lem1202059 A h). Qed.
Lemma lem1202061 {A : Type'} (h : A) : (term106 A h) = (term107 A h).
Proof. exact (eq_refl (term106 A h)). Qed.
Lemma lem1202062 {A : Type'} (h : A) : term107 A h.
Proof. exact (EQ_MP (@lem1202061 A h) (@lem1202060 A h)). Qed.
Lemma lem1202063 {A : Type'} (h : A) (t : list A) : term108 A h t.
Proof. exact (@lem1202062 A h t). Qed.
Lemma lem1202064 {A : Type'} (h : A) (t : list A) : (term108 A h t) = (term109 A h t).
Proof. exact (eq_refl (term108 A h t)). Qed.
Lemma lem1202065 {A : Type'} (h : A) (t : list A) : term109 A h t.
Proof. exact (EQ_MP (@lem1202064 A h t) (@lem1202063 A h t)). Qed.
Lemma lem1202066 {A : Type'} (h : A) (t : list A) (l : list A) : term110 A h t l.
Proof. exact (@lem1202065 A h t l). Qed.
Lemma lem1202067 {A : Type'} (h : A) (t : list A) (l : list A) : (term110 A h t l) = ((term111 A h t l) = (term112 A h t l)).
Proof. exact (eq_refl (term110 A h t l)). Qed.
Lemma lem1202073 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) : term90 _28076 t.
Proof. exact (h1). Qed.
Lemma lem1202074 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term113 _28076 t) = t.
Proof. exact (@lem1201866 _28076 t h2 (@lem1202073 _28076 t h1)). Qed.
Lemma lem1202080 {_28076 : Type'} (t : list _28076) : term91 _28076 t.
Proof. exact (@lem82 (t = (@nil _28076))). Qed.
Lemma lem1202096 {A : Type'} (h : A) (t : list A) (l : list A) : (term111 A h t l) = (term112 A h t l).
Proof. exact (EQ_MP (@lem1202067 A h t l) (@lem1202066 A h t l)). Qed.
Lemma lem1202097 {_28076 : Type'} (h : _28076) (t : list _28076) (l : list _28076) : (term111 _28076 h t l) = (term112 _28076 h t l).
Proof. exact (@lem1202096 _28076 h t l). Qed.
Lemma lem1202098 {_28076 : Type'} (h : _28076) (t : list _28076) : (term95 _28076 h t) = (term114 _28076 h t).
Proof. exact (@lem1202097 _28076 h (@List.removelast _28076 t) (term115 _28076 h t)). Qed.
Lemma lem1202100 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1202101 {_28076 : Type'} (t1 : _28076) (t2 : _28076) : (@COND _28076 False t1 t2) = t2.
Proof. exact (@lem1202100 _28076 t1 t2). Qed.
Lemma lem1202102 {_28076 : Type'} (h : _28076) (t : list _28076) : (term116 _28076 h t) = (@LAST _28076 t).
Proof. exact (@lem1202101 _28076 h (@LAST _28076 t)). Qed.
Lemma lem1202103 {_28076 : Type'} : (@cons _28076) = (@cons _28076).
Proof. exact (eq_refl (@cons _28076)). Qed.
Lemma lem1202104 {_28076 : Type'} (h : _28076) (t : list _28076) : (term117 _28076 h t) = (term118 _28076 t).
Proof. exact (MK_COMB (@lem1202103 _28076) (@lem1202102 _28076 h t)). Qed.
Lemma lem1202105 {_28076 : Type'} : (@nil _28076) = (@nil _28076).
Proof. exact (eq_refl (@nil _28076)). Qed.
Lemma lem1202106 {_28076 : Type'} (h : _28076) (t : list _28076) : (term115 _28076 h t) = (term119 _28076 t).
Proof. exact (MK_COMB (@lem1202104 _28076 h t) (@lem1202105 _28076)). Qed.
Lemma lem1202107 {_28076 : Type'} (t : list _28076) : (term120 _28076 t) = (term120 _28076 t).
Proof. exact (eq_refl (term120 _28076 t)). Qed.
Lemma lem1202108 {_28076 : Type'} (h : _28076) (t : list _28076) : (term121 _28076 h t) = (term113 _28076 t).
Proof. exact (MK_COMB (@lem1202107 _28076 t) (@lem1202106 _28076 h t)). Qed.
Lemma lem1202110 {_28076 : Type'} (t : list _28076) (h1 : term13 _28076 t) : term13 _28076 t.
Proof. exact (fun h0 : term90 _28076 t => @lem1202074 _28076 t h0 h1). Qed.
Lemma lem1202112 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) : (t = (@nil _28076)) = False.
Proof. exact (@lem1202080 _28076 t (@lem1201993 _28076 t h1)). Qed.
Lemma lem1202113 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1202114 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) : (term90 _28076 t) = (~ False).
Proof. exact (MK_COMB (@lem1202113) (@lem1202112 _28076 t h1)). Qed.
Lemma lem1202116 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1202117 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) : (term90 _28076 t) = True.
Proof. exact (TRANS (@lem1202114 _28076 t h1) (@lem1202116)). Qed.
Lemma lem1202118 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) : True = (term90 _28076 t).
Proof. exact (SYM (@lem1202117 _28076 t h1)). Qed.
Lemma lem1202119 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) : term90 _28076 t.
Proof. exact (EQ_MP (@lem1202118 _28076 t h1) (@lem0)). Qed.
Lemma lem1202120 {_28076 : Type'} (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term113 _28076 t) = t.
Proof. exact (@lem1202110 _28076 t h2 (@lem1202119 _28076 t h1)). Qed.
Lemma lem1202121 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term121 _28076 h t) = t.
Proof. exact (TRANS (@lem1202108 _28076 h t) (@lem1202120 _28076 t h1 h2)). Qed.
Lemma lem1202122 {_28076 : Type'} (h : _28076) : (@cons _28076 h) = (@cons _28076 h).
Proof. exact (eq_refl (@cons _28076 h)). Qed.
Lemma lem1202123 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term114 _28076 h t) = (@cons _28076 h t).
Proof. exact (MK_COMB (@lem1202122 _28076 h) (@lem1202121 _28076 h t h1 h2)). Qed.
Lemma lem1202124 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term95 _28076 h t) = (@cons _28076 h t).
Proof. exact (TRANS (@lem1202098 _28076 h t) (@lem1202123 _28076 h t h1 h2)). Qed.
Lemma lem1202125 {_28076 : Type'} : (@eq (list _28076)) = (@eq (list _28076)).
Proof. exact (eq_refl (@eq (list _28076))). Qed.
Lemma lem1202126 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term122 _28076 h t) = (term123 _28076 h t).
Proof. exact (MK_COMB (@lem1202125 _28076) (@lem1202124 _28076 h t h1 h2)). Qed.
Lemma lem1202127 {_28076 : Type'} (h : _28076) (t : list _28076) : (@cons _28076 h t) = (@cons _28076 h t).
Proof. exact (eq_refl (@cons _28076 h t)). Qed.
Lemma lem1202128 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : ((term95 _28076 h t) = (@cons _28076 h t)) = ((@cons _28076 h t) = (@cons _28076 h t)).
Proof. exact (MK_COMB (@lem1202126 _28076 h t h1 h2) (@lem1202127 _28076 h t)). Qed.
Lemma lem1202130 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1202131 {_28076 : Type'} (x : list _28076) : (x = x) = True.
Proof. exact (@lem1202130 (list _28076) x). Qed.
Lemma lem1202132 {_28076 : Type'} (h : _28076) (t : list _28076) : ((@cons _28076 h t) = (@cons _28076 h t)) = True.
Proof. exact (@lem1202131 _28076 (@cons _28076 h t)). Qed.
Lemma lem1202133 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : ((term95 _28076 h t) = (@cons _28076 h t)) = True.
Proof. exact (TRANS (@lem1202128 _28076 h t h1 h2) (@lem1202132 _28076 h t)). Qed.
Lemma lem1202134 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : True = ((term95 _28076 h t) = (@cons _28076 h t)).
Proof. exact (SYM (@lem1202133 _28076 h t h1 h2)). Qed.
Lemma lem1202135 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term95 _28076 h t) = (@cons _28076 h t).
Proof. exact (EQ_MP (@lem1202134 _28076 h t h1 h2) (@lem0)). Qed.
Lemma lem1202136 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term70 _28076 h t) = (@cons _28076 h t).
Proof. exact (EQ_MP (@lem1202008 _28076 h t h1) (@lem1202135 _28076 h t h1 h2)). Qed.
Lemma lem1202137 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term90 _28076 t) = ((term70 _28076 h t) = (@cons _28076 h t)).
Proof. exact (prop_ext (fun h3 : term90 _28076 t => @lem1202136 _28076 h t h1 h2) (fun h3 : (term70 _28076 h t) = (@cons _28076 h t) => @lem1201993 _28076 t h1)). Qed.
Lemma lem1202138 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term90 _28076 t) (h2 : term13 _28076 t) : (term70 _28076 h t) = (@cons _28076 h t).
Proof. exact (EQ_MP (@lem1202137 _28076 h t h1 h2) (@lem1201993 _28076 t h1)). Qed.
Lemma lem1202139 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term13 _28076 t) : term73 _28076 h t.
Proof. exact (fun h0 : term90 _28076 t => @lem1202138 _28076 h t h0 h1). Qed.
Lemma lem1202140 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : (term75 _28076 h t) = (@cons _28076 h t).
Proof. exact (EQ_MP (@lem1201992 _28076 h t h1) (@lem1202058 _28076 h t h1)). Qed.
Lemma lem1202141 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : (t = (@nil _28076)) = ((term75 _28076 h t) = (@cons _28076 h t)).
Proof. exact (prop_ext (fun h2 : t = (@nil _28076) => @lem1202140 _28076 h t h1) (fun h2 : (term75 _28076 h t) = (@cons _28076 h t) => @lem1201977 _28076 t h1)). Qed.
Lemma lem1202142 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : t = (@nil _28076)) : (term75 _28076 h t) = (@cons _28076 h t).
Proof. exact (EQ_MP (@lem1202141 _28076 h t h1) (@lem1201977 _28076 t h1)). Qed.
Lemma lem1202143 {_28076 : Type'} (h : _28076) (t : list _28076) : term78 _28076 h t.
Proof. exact (fun h0 : t = (@nil _28076) => @lem1202142 _28076 h t h0). Qed.
Lemma lem1202144 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term13 _28076 t) : term81 _28076 h t.
Proof. exact (conj (@lem1202143 _28076 h t) (@lem1202139 _28076 h t h1)). Qed.
Lemma lem1202145 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term13 _28076 t) : (term57 _28076 h t) = (@cons _28076 h t).
Proof. exact (EQ_MP (@lem1201976 _28076 h t) (@lem1202144 _28076 h t h1)). Qed.
Lemma lem1202146 {_28076 : Type'} (h : _28076) (t : list _28076) (h1 : term13 _28076 t) : term17 _28076 h t.
Proof. exact (EQ_MP (@lem1201958 _28076 h t) (@lem1202145 _28076 h t h1)). Qed.
Lemma lem1202147 {_28076 : Type'} (h : _28076) (t : list _28076) : term19 _28076 h t.
Proof. exact (fun h0 : term13 _28076 t => @lem1202146 _28076 h t h0). Qed.
Lemma lem1202152 {_28076 : Type'} (h : _28076) : term23 _28076 h.
Proof. exact (fun t : list _28076 => @lem1202147 _28076 h t). Qed.
Lemma lem1202157 {_28076 : Type'} : term27 _28076.
Proof. exact (fun h : _28076 => @lem1202152 _28076 h). Qed.
Lemma lem1202158 {_28076 : Type'} : term29 _28076.
Proof. exact (conj (@lem1201901 _28076) (@lem1202157 _28076)). Qed.
Lemma lem1202159 {_28076 : Type'} : term34 _28076.
Proof. exact (@lem1201865 _28076 (@lem1202158 _28076)). Qed.
