Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONS_HD_TL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1206886 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1206887 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1206888 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1206887 A h) (@lem1206886 A h)). Qed.
Lemma lem1206889 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem1206888 A h t). Qed.
Lemma lem1206890 {A : Type'} (h : A) (t : list A) : (term2 A h t) = (term3 A h t).
Proof. exact (eq_refl (term2 A h t)). Qed.
Lemma lem1206891 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (EQ_MP (@lem1206890 A h t) (@lem1206889 A h t)). Qed.
Lemma lem1206892 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1206895 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@cons A h t) = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1206896 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@nil A) = (@cons A h t).
Proof. exact (SYM (@lem1206895 A h t h1)). Qed.
Lemma lem1206897 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@nil A) = (@cons A h t).
Proof. exact (h1). Qed.
Lemma lem1206898 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@cons A h t) = (@nil A).
Proof. exact (SYM (@lem1206897 A h t h1)). Qed.
Lemma lem1206899 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = ((@nil A) = (@cons A h t)).
Proof. exact (prop_ext (fun h1 : (@cons A h t) = (@nil A) => @lem1206896 A h t h1) (fun h1 : (@nil A) = (@cons A h t) => @lem1206898 A h t h1)). Qed.
Lemma lem1206900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1206901 {A : Type'} (h : A) (t : list A) : (term3 A h t) = (term5 A h t).
Proof. exact (MK_COMB (@lem1206900) (@lem1206899 A h t)). Qed.
Lemma lem1206902 {A : Type'} (h : A) (t : list A) : term5 A h t.
Proof. exact (EQ_MP (@lem1206901 A h t) (@lem1206891 A h t)). Qed.
Lemma lem1206903 {A : Type'} (h : A) (t : list A) : term6 A h t.
Proof. exact (@lem82 ((@nil A) = (@cons A h t))). Qed.
Lemma lem1206906 {A : Type'} (P : type1143 A) : term7 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1206907 {_28337 : Type'} (P : type1143 _28337) : term7 _28337 P.
Proof. exact (@lem1206906 _28337 P). Qed.
Lemma lem1206908 {_28337 : Type'} : term8 _28337.
Proof. exact (@lem1206907 _28337 (term9 _28337)). Qed.
Lemma lem1206909 {_28337 : Type'} : (term10 _28337) = (term11 _28337).
Proof. exact (eq_refl (term10 _28337)). Qed.
Lemma lem1206910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1206911 {_28337 : Type'} : (term12 _28337) = (term13 _28337).
Proof. exact (MK_COMB (@lem1206910) (@lem1206909 _28337)). Qed.
Lemma lem1206912 {_28337 : Type'} (t : list _28337) : (term14 _28337 t) = (term15 _28337 t).
Proof. exact (eq_refl (term14 _28337 t)). Qed.
Lemma lem1206913 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206914 {_28337 : Type'} (t : list _28337) : (term16 _28337 t) = (term17 _28337 t).
Proof. exact (MK_COMB (@lem1206913) (@lem1206912 _28337 t)). Qed.
Lemma lem1206915 {_28337 : Type'} (h : _28337) (t : list _28337) : (term18 _28337 h t) = (term19 _28337 h t).
Proof. exact (eq_refl (term18 _28337 h t)). Qed.
Lemma lem1206916 {_28337 : Type'} (h : _28337) (t : list _28337) : (term20 _28337 h t) = (term21 _28337 h t).
Proof. exact (MK_COMB (@lem1206914 _28337 t) (@lem1206915 _28337 h t)). Qed.
Lemma lem1206917 {_28337 : Type'} (h : _28337) : (term22 _28337 h) = (term23 _28337 h).
Proof. exact (fun_ext (fun t : list _28337 => @lem1206916 _28337 h t)). Qed.
Lemma lem1206918 {_28337 : Type'} : (@all (list _28337)) = (@all (list _28337)).
Proof. exact (eq_refl (@all (list _28337))). Qed.
Lemma lem1206919 {_28337 : Type'} (h : _28337) : (term24 _28337 h) = (term25 _28337 h).
Proof. exact (MK_COMB (@lem1206918 _28337) (@lem1206917 _28337 h)). Qed.
Lemma lem1206920 {_28337 : Type'} : (term26 _28337) = (term27 _28337).
Proof. exact (fun_ext (fun h : _28337 => @lem1206919 _28337 h)). Qed.
Lemma lem1206921 {_28337 : Type'} : (@all _28337) = (@all _28337).
Proof. exact (eq_refl (@all _28337)). Qed.
Lemma lem1206922 {_28337 : Type'} : (term28 _28337) = (term29 _28337).
Proof. exact (MK_COMB (@lem1206921 _28337) (@lem1206920 _28337)). Qed.
Lemma lem1206923 {_28337 : Type'} : (term30 _28337) = (term31 _28337).
Proof. exact (MK_COMB (@lem1206911 _28337) (@lem1206922 _28337)). Qed.
Lemma lem1206924 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206925 {_28337 : Type'} : (term32 _28337) = (term33 _28337).
Proof. exact (MK_COMB (@lem1206924) (@lem1206923 _28337)). Qed.
Lemma lem1206926 {_28337 : Type'} (l : list _28337) : (term14 _28337 l) = (term15 _28337 l).
Proof. exact (eq_refl (term14 _28337 l)). Qed.
Lemma lem1206927 {_28337 : Type'} : (term34 _28337) = (term9 _28337).
Proof. exact (fun_ext (fun l : list _28337 => @lem1206926 _28337 l)). Qed.
Lemma lem1206928 {_28337 : Type'} : (@all (list _28337)) = (@all (list _28337)).
Proof. exact (eq_refl (@all (list _28337))). Qed.
Lemma lem1206929 {_28337 : Type'} : (term35 _28337) = (term36 _28337).
Proof. exact (MK_COMB (@lem1206928 _28337) (@lem1206927 _28337)). Qed.
Lemma lem1206930 {_28337 : Type'} : (term8 _28337) = (term37 _28337).
Proof. exact (MK_COMB (@lem1206925 _28337) (@lem1206929 _28337)). Qed.
Lemma lem1206931 {_28337 : Type'} : term37 _28337.
Proof. exact (EQ_MP (@lem1206930 _28337) (@lem1206908 _28337)). Qed.
Lemma lem1206936 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206937 {_28337 : Type'} (x : list _28337) : (x = x) = True.
Proof. exact (@lem1206936 (list _28337) x). Qed.
Lemma lem1206938 {_28337 : Type'} : ((@nil _28337) = (@nil _28337)) = True.
Proof. exact (@lem1206937 _28337 (@nil _28337)). Qed.
Lemma lem1206939 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1206940 {_28337 : Type'} : (term38 _28337) = (~ True).
Proof. exact (MK_COMB (@lem1206939) (@lem1206938 _28337)). Qed.
Lemma lem1206942 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1206943 {_28337 : Type'} : (term38 _28337) = False.
Proof. exact (TRANS (@lem1206940 _28337) (@lem1206942)). Qed.
Lemma lem1206944 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206945 {_28337 : Type'} : (term39 _28337) = (imp False).
Proof. exact (MK_COMB (@lem1206944) (@lem1206943 _28337)). Qed.
Lemma lem1206947 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1206903 A h t (@lem1206902 A h t)). Qed.
Lemma lem1206948 {_28337 : Type'} (h : _28337) (t : list _28337) : ((@nil _28337) = (@cons _28337 h t)) = False.
Proof. exact (@lem1206947 _28337 h t). Qed.
Lemma lem1206949 {_28337 : Type'} : ((@nil _28337) = (term40 _28337)) = False.
Proof. exact (@lem1206948 _28337 (@hd _28337 (@nil _28337)) (@tl _28337 (@nil _28337))). Qed.
Lemma lem1206950 {_28337 : Type'} : (term11 _28337) = (False -> False).
Proof. exact (MK_COMB (@lem1206945 _28337) (@lem1206949 _28337)). Qed.
Lemma lem1206952 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1206953 : (False -> False) = True.
Proof. exact (@lem1206952 False). Qed.
Lemma lem1206954 {_28337 : Type'} : (term11 _28337) = True.
Proof. exact (TRANS (@lem1206950 _28337) (@lem1206953)). Qed.
Lemma lem1206955 {_28337 : Type'} : True = (term11 _28337).
Proof. exact (SYM (@lem1206954 _28337)). Qed.
Lemma lem1206956 {_28337 : Type'} : term11 _28337.
Proof. exact (EQ_MP (@lem1206955 _28337) (@lem0)). Qed.
Lemma lem1206960 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1206892 A h t (@lem1206891 A h t)). Qed.
Lemma lem1206961 {_28337 : Type'} (h : _28337) (t : list _28337) : ((@cons _28337 h t) = (@nil _28337)) = False.
Proof. exact (@lem1206960 _28337 h t). Qed.
Lemma lem1206962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1206963 {_28337 : Type'} (h : _28337) (t : list _28337) : (term3 _28337 h t) = (~ False).
Proof. exact (MK_COMB (@lem1206962) (@lem1206961 _28337 h t)). Qed.
Lemma lem1206965 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1206966 {_28337 : Type'} (h : _28337) (t : list _28337) : (term3 _28337 h t) = True.
Proof. exact (TRANS (@lem1206963 _28337 h t) (@lem1206965)). Qed.
Lemma lem1206967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206968 {_28337 : Type'} (h : _28337) (t : list _28337) : (term41 _28337 h t) = (imp True).
Proof. exact (MK_COMB (@lem1206967) (@lem1206966 _28337 h t)). Qed.
Lemma lem1206972 {A : Type'} (t : list A) (h : A) : (term42 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1206973 {_28337 : Type'} (t : list _28337) (h : _28337) : (term42 _28337 h t) = h.
Proof. exact (@lem1206972 _28337 t h). Qed.
Lemma lem1206974 {_28337 : Type'} : (@cons _28337) = (@cons _28337).
Proof. exact (eq_refl (@cons _28337)). Qed.
Lemma lem1206975 {_28337 : Type'} (t : list _28337) (h : _28337) : (term43 _28337 h t) = (@cons _28337 h).
Proof. exact (MK_COMB (@lem1206974 _28337) (@lem1206973 _28337 t h)). Qed.
Lemma lem1206977 {A : Type'} (h : A) (t : list A) : (term44 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1206978 {_28337 : Type'} (h : _28337) (t : list _28337) : (term44 _28337 h t) = t.
Proof. exact (@lem1206977 _28337 h t). Qed.
Lemma lem1206979 {_28337 : Type'} (h : _28337) (t : list _28337) : (term45 _28337 h t) = (@cons _28337 h t).
Proof. exact (MK_COMB (@lem1206975 _28337 t h) (@lem1206978 _28337 h t)). Qed.
Lemma lem1206980 {_28337 : Type'} (h : _28337) (t : list _28337) : (term46 _28337 h t) = (term46 _28337 h t).
Proof. exact (eq_refl (term46 _28337 h t)). Qed.
Lemma lem1206981 {_28337 : Type'} (h : _28337) (t : list _28337) : ((@cons _28337 h t) = (term45 _28337 h t)) = ((@cons _28337 h t) = (@cons _28337 h t)).
Proof. exact (MK_COMB (@lem1206980 _28337 h t) (@lem1206979 _28337 h t)). Qed.
Lemma lem1206983 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206984 {_28337 : Type'} (x : list _28337) : (x = x) = True.
Proof. exact (@lem1206983 (list _28337) x). Qed.
Lemma lem1206985 {_28337 : Type'} (h : _28337) (t : list _28337) : ((@cons _28337 h t) = (@cons _28337 h t)) = True.
Proof. exact (@lem1206984 _28337 (@cons _28337 h t)). Qed.
Lemma lem1206986 {_28337 : Type'} (h : _28337) (t : list _28337) : ((@cons _28337 h t) = (term45 _28337 h t)) = True.
Proof. exact (TRANS (@lem1206981 _28337 h t) (@lem1206985 _28337 h t)). Qed.
Lemma lem1206987 {_28337 : Type'} (h : _28337) (t : list _28337) : (term19 _28337 h t) = (True -> True).
Proof. exact (MK_COMB (@lem1206968 _28337 h t) (@lem1206986 _28337 h t)). Qed.
Lemma lem1206989 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1206990 : (True -> True) = True.
Proof. exact (@lem1206989 True). Qed.
Lemma lem1206991 {_28337 : Type'} (h : _28337) (t : list _28337) : (term19 _28337 h t) = True.
Proof. exact (TRANS (@lem1206987 _28337 h t) (@lem1206990)). Qed.
Lemma lem1206992 {_28337 : Type'} (h : _28337) (t : list _28337) : True = (term19 _28337 h t).
Proof. exact (SYM (@lem1206991 _28337 h t)). Qed.
Lemma lem1206993 {_28337 : Type'} (h : _28337) (t : list _28337) : term19 _28337 h t.
Proof. exact (EQ_MP (@lem1206992 _28337 h t) (@lem0)). Qed.
Lemma lem1206994 {_28337 : Type'} (h : _28337) (t : list _28337) : term21 _28337 h t.
Proof. exact (fun h0 : term15 _28337 t => @lem1206993 _28337 h t). Qed.
Lemma lem1206999 {_28337 : Type'} (h : _28337) : term25 _28337 h.
Proof. exact (fun t : list _28337 => @lem1206994 _28337 h t). Qed.
Lemma lem1207004 {_28337 : Type'} : term29 _28337.
Proof. exact (fun h : _28337 => @lem1206999 _28337 h). Qed.
Lemma lem1207005 {_28337 : Type'} : term31 _28337.
Proof. exact (conj (@lem1206956 _28337) (@lem1207004 _28337)). Qed.
Lemma lem1207006 {_28337 : Type'} : term36 _28337.
Proof. exact (@lem1206931 _28337 (@lem1207005 _28337)). Qed.
