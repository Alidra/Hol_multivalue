Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20230_term_abbrevs.
Require Import EXISTS_REFL_spec.
Require Import LEFT_FORALL_IMP_THM_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem19794 {A : Type'} (a : A) : term0 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem19795 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (eq_refl (term0 A a)). Qed.
Lemma lem19796 {A : Type'} (a : A) : term1 A a.
Proof. exact (EQ_MP (@lem19795 A a) (@lem19794 A a)). Qed.
Lemma lem19797 {A : Type'} (a : A) : (term1 A a) = ((term1 A a) = True).
Proof. exact (@lem7 (term1 A a)). Qed.
Lemma lem19799 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (@lem6754 A P). Qed.
Lemma lem19800 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (eq_refl (term2 A P)). Qed.
Lemma lem19801 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (EQ_MP (@lem19800 A P) (@lem19799 A P)). Qed.
Lemma lem19802 {A : Type'} (P : A -> Prop) (Q : Prop) : term4 A P Q.
Proof. exact (@lem19801 A P Q). Qed.
Lemma lem19803 {A : Type'} (P : A -> Prop) (Q : Prop) : (term4 A P Q) = ((term5 A P Q) = (term6 A P Q)).
Proof. exact (eq_refl (term4 A P Q)). Qed.
Lemma lem19808 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem19809 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem19808 p q p' q'). Qed.
Lemma lem19810 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem19809 p q p'). Qed.
Lemma lem19811 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term10 _3603 P c Q.
Proof. exact (@lem19810 (term11 _3603 c P Q) (P = (term12 _3603 c Q))). Qed.
Lemma lem19812 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) (p' : Prop) : term13 _3603 P c Q p'.
Proof. exact (@lem19811 _3603 P c Q p'). Qed.
Lemma lem19813 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) (p' : Prop) : (term13 _3603 P c Q p') = (term14 _3603 P c Q p').
Proof. exact (eq_refl (term13 _3603 P c Q p')). Qed.
Lemma lem19814 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) (p' : Prop) : term14 _3603 P c Q p'.
Proof. exact (EQ_MP (@lem19813 _3603 P c Q p') (@lem19812 _3603 P c Q p')). Qed.
Lemma lem19815 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) (p' : Prop) (q' : Prop) : term15 _3603 P c Q p' q'.
Proof. exact (@lem19814 _3603 P c Q p' q'). Qed.
Lemma lem19816 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) (p' : Prop) (q' : Prop) : (term15 _3603 P c Q p' q') = (term16 _3603 P c Q p' q').
Proof. exact (eq_refl (term15 _3603 P c Q p' q')). Qed.
Lemma lem19817 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) (p' : Prop) (q' : Prop) : term16 _3603 P c Q p' q'.
Proof. exact (EQ_MP (@lem19816 _3603 P c Q p' q') (@lem19815 _3603 P c Q p' q')). Qed.
Lemma lem19851 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem19852 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem19851 p q p' q'). Qed.
Lemma lem19853 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem19852 p q p'). Qed.
Lemma lem19854 {_3603 : Type'} (c : _3603) (P : Prop) (Q : _3603 -> Prop) (a : _3603) : term17 _3603 c P Q a.
Proof. exact (@lem19853 (a = c) (P = (Q a))). Qed.
Lemma lem19855 {_3603 : Type'} (c : _3603) (P : Prop) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) : term18 _3603 c P Q a p'.
Proof. exact (@lem19854 _3603 c P Q a p'). Qed.
Lemma lem19856 {_3603 : Type'} (c : _3603) (P : Prop) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) : (term18 _3603 c P Q a p') = (term19 _3603 c P Q a p').
Proof. exact (eq_refl (term18 _3603 c P Q a p')). Qed.
Lemma lem19857 {_3603 : Type'} (c : _3603) (P : Prop) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) : term19 _3603 c P Q a p'.
Proof. exact (EQ_MP (@lem19856 _3603 c P Q a p') (@lem19855 _3603 c P Q a p')). Qed.
Lemma lem19858 {_3603 : Type'} (c : _3603) (P : Prop) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) (q' : Prop) : term20 _3603 c P Q a p' q'.
Proof. exact (@lem19857 _3603 c P Q a p' q'). Qed.
Lemma lem19859 {_3603 : Type'} (c : _3603) (P : Prop) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) (q' : Prop) : (term20 _3603 c P Q a p' q') = (term21 _3603 c P Q a p' q').
Proof. exact (eq_refl (term20 _3603 c P Q a p' q')). Qed.
Lemma lem19860 {_3603 : Type'} (c : _3603) (P : Prop) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) (q' : Prop) : term21 _3603 c P Q a p' q'.
Proof. exact (EQ_MP (@lem19859 _3603 c P Q a p' q') (@lem19858 _3603 c P Q a p' q')). Qed.
Lemma lem19863 {_3603 : Type'} (a : _3603) (c : _3603) : (a = c) = (a = c).
Proof. exact (eq_refl (a = c)). Qed.
Lemma lem19864 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (a : _3603) (c : _3603) (q' : Prop) : term22 _3603 P Q a c q'.
Proof. exact (@lem19860 _3603 c P Q a (a = c) q'). Qed.
Lemma lem19865 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (a : _3603) (c : _3603) (q' : Prop) : term23 _3603 P Q a c q'.
Proof. exact (@lem19864 _3603 P Q a c q' (@lem19863 _3603 a c)). Qed.
Lemma lem19870 {_3603 : Type'} (a : _3603) (c : _3603) (h1 : a = c) : a = c.
Proof. exact (h1). Qed.
Lemma lem19871 {_3603 : Type'} (Q : _3603 -> Prop) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem19872 {_3603 : Type'} (Q : _3603 -> Prop) (a : _3603) (c : _3603) (h1 : a = c) : (Q a) = (Q c).
Proof. exact (MK_COMB (@lem19871 _3603 Q) (@lem19870 _3603 a c h1)). Qed.
Lemma lem19873 (P : Prop) : (@eq Prop P) = (@eq Prop P).
Proof. exact (eq_refl (@eq Prop P)). Qed.
Lemma lem19874 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (a : _3603) (c : _3603) (h1 : a = c) : (P = (Q a)) = (P = (Q c)).
Proof. exact (MK_COMB (@lem19873 P) (@lem19872 _3603 Q a c h1)). Qed.
Lemma lem19877 {_3603 : Type'} (a : _3603) (P : Prop) (Q : _3603 -> Prop) (c : _3603) : term24 _3603 a P Q c.
Proof. exact (fun h0 : a = c => @lem19874 _3603 P Q a c h0). Qed.
Lemma lem19878 {_3603 : Type'} (a : _3603) (P : Prop) (Q : _3603 -> Prop) (c : _3603) : term25 _3603 a P Q c.
Proof. exact (@lem19865 _3603 P Q a c (P = (Q c))). Qed.
Lemma lem19879 {_3603 : Type'} (a : _3603) (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term26 _3603 c P Q a) = (term27 _3603 a P Q c).
Proof. exact (@lem19878 _3603 a P Q c (@lem19877 _3603 a P Q c)). Qed.
Lemma lem19911 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term28 _3603 c P Q) = (term29 _3603 P Q c).
Proof. exact (fun_ext (fun a : _3603 => @lem19879 _3603 a P Q c)). Qed.
Lemma lem19943 {_3603 : Type'} : (@all _3603) = (@all _3603).
Proof. exact (eq_refl (@all _3603)). Qed.
Lemma lem19944 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term11 _3603 c P Q) = (term30 _3603 P Q c).
Proof. exact (MK_COMB (@lem19943 _3603) (@lem19911 _3603 P Q c)). Qed.
Lemma lem19946 {A : Type'} (P : A -> Prop) (Q : Prop) : (term5 A P Q) = (term6 A P Q).
Proof. exact (EQ_MP (@lem19803 A P Q) (@lem19802 A P Q)). Qed.
Lemma lem19947 {_3603 : Type'} (P : _3603 -> Prop) (Q : Prop) : (term5 _3603 P Q) = (term6 _3603 P Q).
Proof. exact (@lem19946 _3603 P Q). Qed.
Lemma lem19948 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term31 _3603 P Q c) = (term32 _3603 P Q c).
Proof. exact (@lem19947 _3603 (term33 _3603 c) (P = (Q c))). Qed.
Lemma lem19949 {_3603 : Type'} (a : _3603) (c : _3603) : (term34 _3603 c a) = (a = c).
Proof. exact (eq_refl (term34 _3603 c a)). Qed.
Lemma lem19950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem19951 {_3603 : Type'} (a : _3603) (c : _3603) : (term35 _3603 c a) = (term36 _3603 a c).
Proof. exact (MK_COMB (@lem19950) (@lem19949 _3603 a c)). Qed.
Lemma lem19952 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (P = (Q c)) = (P = (Q c)).
Proof. exact (eq_refl (P = (Q c))). Qed.
Lemma lem19953 {_3603 : Type'} (a : _3603) (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term37 _3603 a P Q c) = (term27 _3603 a P Q c).
Proof. exact (MK_COMB (@lem19951 _3603 a c) (@lem19952 _3603 P Q c)). Qed.
Lemma lem19954 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term38 _3603 P Q c) = (term29 _3603 P Q c).
Proof. exact (fun_ext (fun a : _3603 => @lem19953 _3603 a P Q c)). Qed.
Lemma lem19955 {_3603 : Type'} : (@all _3603) = (@all _3603).
Proof. exact (eq_refl (@all _3603)). Qed.
Lemma lem19956 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term31 _3603 P Q c) = (term30 _3603 P Q c).
Proof. exact (MK_COMB (@lem19955 _3603) (@lem19954 _3603 P Q c)). Qed.
Lemma lem19957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19958 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term39 _3603 P Q c) = (term40 _3603 P Q c).
Proof. exact (MK_COMB (@lem19957) (@lem19956 _3603 P Q c)). Qed.
Lemma lem19959 {_3603 : Type'} (a : _3603) (c : _3603) : (term34 _3603 c a) = (a = c).
Proof. exact (eq_refl (term34 _3603 c a)). Qed.
Lemma lem19960 {_3603 : Type'} (c : _3603) : (term41 _3603 c) = (term33 _3603 c).
Proof. exact (fun_ext (fun a : _3603 => @lem19959 _3603 a c)). Qed.
Lemma lem19961 {_3603 : Type'} : (@ex _3603) = (@ex _3603).
Proof. exact (eq_refl (@ex _3603)). Qed.
Lemma lem19962 {_3603 : Type'} (c : _3603) : (term42 _3603 c) = (term1 _3603 c).
Proof. exact (MK_COMB (@lem19961 _3603) (@lem19960 _3603 c)). Qed.
Lemma lem19963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem19964 {_3603 : Type'} (c : _3603) : (term43 _3603 c) = (term44 _3603 c).
Proof. exact (MK_COMB (@lem19963) (@lem19962 _3603 c)). Qed.
Lemma lem19965 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (P = (Q c)) = (P = (Q c)).
Proof. exact (eq_refl (P = (Q c))). Qed.
Lemma lem19966 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term32 _3603 P Q c) = (term45 _3603 P Q c).
Proof. exact (MK_COMB (@lem19964 _3603 c) (@lem19965 _3603 P Q c)). Qed.
Lemma lem19967 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : ((term31 _3603 P Q c) = (term32 _3603 P Q c)) = ((term30 _3603 P Q c) = (term45 _3603 P Q c)).
Proof. exact (MK_COMB (@lem19958 _3603 P Q c) (@lem19966 _3603 P Q c)). Qed.
Lemma lem19968 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term30 _3603 P Q c) = (term45 _3603 P Q c).
Proof. exact (EQ_MP (@lem19967 _3603 P Q c) (@lem19948 _3603 P Q c)). Qed.
Lemma lem19972 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem19973 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem19972 p q p' q'). Qed.
Lemma lem19974 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem19973 p q p'). Qed.
Lemma lem19975 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : term46 _3603 P Q c.
Proof. exact (@lem19974 (term1 _3603 c) (P = (Q c))). Qed.
Lemma lem19976 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (p' : Prop) : term47 _3603 P Q c p'.
Proof. exact (@lem19975 _3603 P Q c p'). Qed.
Lemma lem19977 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (p' : Prop) : (term47 _3603 P Q c p') = (term48 _3603 P Q c p').
Proof. exact (eq_refl (term47 _3603 P Q c p')). Qed.
Lemma lem19978 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (p' : Prop) : term48 _3603 P Q c p'.
Proof. exact (EQ_MP (@lem19977 _3603 P Q c p') (@lem19976 _3603 P Q c p')). Qed.
Lemma lem19979 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (p' : Prop) (q' : Prop) : term49 _3603 P Q c p' q'.
Proof. exact (@lem19978 _3603 P Q c p' q'). Qed.
Lemma lem19980 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (p' : Prop) (q' : Prop) : (term49 _3603 P Q c p' q') = (term50 _3603 P Q c p' q').
Proof. exact (eq_refl (term49 _3603 P Q c p' q')). Qed.
Lemma lem19981 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (p' : Prop) (q' : Prop) : term50 _3603 P Q c p' q'.
Proof. exact (EQ_MP (@lem19980 _3603 P Q c p' q') (@lem19979 _3603 P Q c p' q')). Qed.
Lemma lem19983 {A : Type'} (a : A) : (term1 A a) = True.
Proof. exact (EQ_MP (@lem19797 A a) (@lem19796 A a)). Qed.
Lemma lem19984 {_3603 : Type'} (a : _3603) : (term1 _3603 a) = True.
Proof. exact (@lem19983 _3603 a). Qed.
Lemma lem19985 {_3603 : Type'} (c : _3603) : (term1 _3603 c) = True.
Proof. exact (@lem19984 _3603 c). Qed.
Lemma lem19988 {_3603 : Type'} (c : _3603) : (term51 _3603 c) = (term51 _3603 c).
Proof. exact (eq_refl (term51 _3603 c)). Qed.
Lemma lem19989 {_3603 : Type'} (c : _3603) : (term51 _3603 c) = ((term1 _3603 c) = True).
Proof. exact (eq_refl (term51 _3603 c)). Qed.
Lemma lem19990 {_3603 : Type'} (c : _3603) : (term52 _3603 c) = (term52 _3603 c).
Proof. exact (eq_refl (term52 _3603 c)). Qed.
Lemma lem19991 {_3603 : Type'} (c : _3603) : ((term51 _3603 c) = (term51 _3603 c)) = ((term51 _3603 c) = ((term1 _3603 c) = True)).
Proof. exact (MK_COMB (@lem19990 _3603 c) (@lem19989 _3603 c)). Qed.
Lemma lem19992 {_3603 : Type'} (c : _3603) : (term51 _3603 c) = ((term1 _3603 c) = True).
Proof. exact (eq_refl (term51 _3603 c)). Qed.
Lemma lem19993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19994 {_3603 : Type'} (c : _3603) : (term52 _3603 c) = (term53 _3603 c).
Proof. exact (MK_COMB (@lem19993) (@lem19992 _3603 c)). Qed.
Lemma lem19995 {_3603 : Type'} (c : _3603) : ((term1 _3603 c) = True) = ((term1 _3603 c) = True).
Proof. exact (eq_refl ((term1 _3603 c) = True)). Qed.
Lemma lem19996 {_3603 : Type'} (c : _3603) : ((term51 _3603 c) = ((term1 _3603 c) = True)) = (((term1 _3603 c) = True) = ((term1 _3603 c) = True)).
Proof. exact (MK_COMB (@lem19994 _3603 c) (@lem19995 _3603 c)). Qed.
Lemma lem19997 {_3603 : Type'} (c : _3603) : ((term51 _3603 c) = (term51 _3603 c)) = (((term1 _3603 c) = True) = ((term1 _3603 c) = True)).
Proof. exact (TRANS (@lem19991 _3603 c) (@lem19996 _3603 c)). Qed.
Lemma lem19998 {_3603 : Type'} (c : _3603) : ((term1 _3603 c) = True) = ((term1 _3603 c) = True).
Proof. exact (EQ_MP (@lem19997 _3603 c) (@lem19988 _3603 c)). Qed.
Lemma lem19999 {_3603 : Type'} (c : _3603) : (term1 _3603 c) = True.
Proof. exact (EQ_MP (@lem19998 _3603 c) (@lem19985 _3603 c)). Qed.
Lemma lem20000 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (q' : Prop) : term54 _3603 P Q c q'.
Proof. exact (@lem19981 _3603 P Q c True q'). Qed.
Lemma lem20001 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (q' : Prop) : term55 _3603 P Q c q'.
Proof. exact (@lem20000 _3603 P Q c q' (@lem19999 _3603 c)). Qed.
Lemma lem20009 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (P = (Q c)) = (P = (Q c)).
Proof. exact (eq_refl (P = (Q c))). Qed.
Lemma lem20010 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : term56 _3603 P Q c.
Proof. exact (fun h0 : True => @lem20009 _3603 P Q c). Qed.
Lemma lem20011 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : term57 _3603 P Q c.
Proof. exact (@lem20001 _3603 P Q c (P = (Q c))). Qed.
Lemma lem20012 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term45 _3603 P Q c) = (term58 _3603 P Q c).
Proof. exact (@lem20011 _3603 P Q c (@lem20010 _3603 P Q c)). Qed.
Lemma lem20014 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem20015 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term58 _3603 P Q c) = (P = (Q c)).
Proof. exact (@lem20014 (P = (Q c))). Qed.
Lemma lem20018 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term45 _3603 P Q c) = (P = (Q c)).
Proof. exact (TRANS (@lem20012 _3603 P Q c) (@lem20015 _3603 P Q c)). Qed.
Lemma lem20019 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term30 _3603 P Q c) = (P = (Q c)).
Proof. exact (TRANS (@lem19968 _3603 P Q c) (@lem20018 _3603 P Q c)). Qed.
Lemma lem20020 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term11 _3603 c P Q) = (P = (Q c)).
Proof. exact (TRANS (@lem19944 _3603 P Q c) (@lem20019 _3603 P Q c)). Qed.
Lemma lem20021 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (q' : Prop) : term59 _3603 P Q c q'.
Proof. exact (@lem19817 _3603 P c Q (P = (Q c)) q'). Qed.
Lemma lem20022 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (q' : Prop) : term60 _3603 P Q c q'.
Proof. exact (@lem20021 _3603 P Q c q' (@lem20020 _3603 P Q c)). Qed.
Lemma lem20027 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (h1 : P = (Q c)) : P = (Q c).
Proof. exact (h1). Qed.
Lemma lem20028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20029 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (h1 : P = (Q c)) : (@eq Prop P) = (term61 _3603 Q c).
Proof. exact (MK_COMB (@lem20028) (@lem20027 _3603 P Q c h1)). Qed.
Lemma lem20063 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem20064 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem20063 p q p' q'). Qed.
Lemma lem20065 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem20064 p q p'). Qed.
Lemma lem20066 {_3603 : Type'} (c : _3603) (Q : _3603 -> Prop) (a : _3603) : term62 _3603 c Q a.
Proof. exact (@lem20065 (a = c) (Q a)). Qed.
Lemma lem20067 {_3603 : Type'} (c : _3603) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) : term63 _3603 c Q a p'.
Proof. exact (@lem20066 _3603 c Q a p'). Qed.
Lemma lem20068 {_3603 : Type'} (c : _3603) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) : (term63 _3603 c Q a p') = (term64 _3603 c Q a p').
Proof. exact (eq_refl (term63 _3603 c Q a p')). Qed.
Lemma lem20069 {_3603 : Type'} (c : _3603) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) : term64 _3603 c Q a p'.
Proof. exact (EQ_MP (@lem20068 _3603 c Q a p') (@lem20067 _3603 c Q a p')). Qed.
Lemma lem20070 {_3603 : Type'} (c : _3603) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) (q' : Prop) : term65 _3603 c Q a p' q'.
Proof. exact (@lem20069 _3603 c Q a p' q'). Qed.
Lemma lem20071 {_3603 : Type'} (c : _3603) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) (q' : Prop) : (term65 _3603 c Q a p' q') = (term66 _3603 c Q a p' q').
Proof. exact (eq_refl (term65 _3603 c Q a p' q')). Qed.
Lemma lem20072 {_3603 : Type'} (c : _3603) (Q : _3603 -> Prop) (a : _3603) (p' : Prop) (q' : Prop) : term66 _3603 c Q a p' q'.
Proof. exact (EQ_MP (@lem20071 _3603 c Q a p' q') (@lem20070 _3603 c Q a p' q')). Qed.
Lemma lem20075 {_3603 : Type'} (a : _3603) (c : _3603) : (a = c) = (a = c).
Proof. exact (eq_refl (a = c)). Qed.
Lemma lem20076 {_3603 : Type'} (Q : _3603 -> Prop) (a : _3603) (c : _3603) (q' : Prop) : term67 _3603 Q a c q'.
Proof. exact (@lem20072 _3603 c Q a (a = c) q'). Qed.
Lemma lem20077 {_3603 : Type'} (Q : _3603 -> Prop) (a : _3603) (c : _3603) (q' : Prop) : term68 _3603 Q a c q'.
Proof. exact (@lem20076 _3603 Q a c q' (@lem20075 _3603 a c)). Qed.
Lemma lem20080 {_3603 : Type'} (a : _3603) (c : _3603) (h1 : a = c) : a = c.
Proof. exact (h1). Qed.
Lemma lem20081 {_3603 : Type'} (Q : _3603 -> Prop) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem20082 {_3603 : Type'} (Q : _3603 -> Prop) (a : _3603) (c : _3603) (h1 : a = c) : (Q a) = (Q c).
Proof. exact (MK_COMB (@lem20081 _3603 Q) (@lem20080 _3603 a c h1)). Qed.
Lemma lem20083 {_3603 : Type'} (a : _3603) (Q : _3603 -> Prop) (c : _3603) : term69 _3603 a Q c.
Proof. exact (fun h0 : a = c => @lem20082 _3603 Q a c h0). Qed.
Lemma lem20084 {_3603 : Type'} (a : _3603) (Q : _3603 -> Prop) (c : _3603) : term70 _3603 a Q c.
Proof. exact (@lem20077 _3603 Q a c (Q c)). Qed.
Lemma lem20085 {_3603 : Type'} (a : _3603) (Q : _3603 -> Prop) (c : _3603) : (term71 _3603 c Q a) = (term72 _3603 a Q c).
Proof. exact (@lem20084 _3603 a Q c (@lem20083 _3603 a Q c)). Qed.
Lemma lem20113 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term73 _3603 c Q) = (term74 _3603 Q c).
Proof. exact (fun_ext (fun a : _3603 => @lem20085 _3603 a Q c)). Qed.
Lemma lem20141 {_3603 : Type'} : (@all _3603) = (@all _3603).
Proof. exact (eq_refl (@all _3603)). Qed.
Lemma lem20142 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term12 _3603 c Q) = (term75 _3603 Q c).
Proof. exact (MK_COMB (@lem20141 _3603) (@lem20113 _3603 Q c)). Qed.
Lemma lem20144 {A : Type'} (P : A -> Prop) (Q : Prop) : (term5 A P Q) = (term6 A P Q).
Proof. exact (EQ_MP (@lem19803 A P Q) (@lem19802 A P Q)). Qed.
Lemma lem20145 {_3603 : Type'} (P : _3603 -> Prop) (Q : Prop) : (term5 _3603 P Q) = (term6 _3603 P Q).
Proof. exact (@lem20144 _3603 P Q). Qed.
Lemma lem20146 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term76 _3603 Q c) = (term77 _3603 Q c).
Proof. exact (@lem20145 _3603 (term33 _3603 c) (Q c)). Qed.
Lemma lem20147 {_3603 : Type'} (a : _3603) (c : _3603) : (term34 _3603 c a) = (a = c).
Proof. exact (eq_refl (term34 _3603 c a)). Qed.
Lemma lem20148 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20149 {_3603 : Type'} (a : _3603) (c : _3603) : (term35 _3603 c a) = (term36 _3603 a c).
Proof. exact (MK_COMB (@lem20148) (@lem20147 _3603 a c)). Qed.
Lemma lem20150 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (Q c) = (Q c).
Proof. exact (eq_refl (Q c)). Qed.
Lemma lem20151 {_3603 : Type'} (a : _3603) (Q : _3603 -> Prop) (c : _3603) : (term78 _3603 a Q c) = (term72 _3603 a Q c).
Proof. exact (MK_COMB (@lem20149 _3603 a c) (@lem20150 _3603 Q c)). Qed.
Lemma lem20152 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term79 _3603 Q c) = (term74 _3603 Q c).
Proof. exact (fun_ext (fun a : _3603 => @lem20151 _3603 a Q c)). Qed.
Lemma lem20153 {_3603 : Type'} : (@all _3603) = (@all _3603).
Proof. exact (eq_refl (@all _3603)). Qed.
Lemma lem20154 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term76 _3603 Q c) = (term75 _3603 Q c).
Proof. exact (MK_COMB (@lem20153 _3603) (@lem20152 _3603 Q c)). Qed.
Lemma lem20155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20156 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term80 _3603 Q c) = (term81 _3603 Q c).
Proof. exact (MK_COMB (@lem20155) (@lem20154 _3603 Q c)). Qed.
Lemma lem20157 {_3603 : Type'} (a : _3603) (c : _3603) : (term34 _3603 c a) = (a = c).
Proof. exact (eq_refl (term34 _3603 c a)). Qed.
Lemma lem20158 {_3603 : Type'} (c : _3603) : (term41 _3603 c) = (term33 _3603 c).
Proof. exact (fun_ext (fun a : _3603 => @lem20157 _3603 a c)). Qed.
Lemma lem20159 {_3603 : Type'} : (@ex _3603) = (@ex _3603).
Proof. exact (eq_refl (@ex _3603)). Qed.
Lemma lem20160 {_3603 : Type'} (c : _3603) : (term42 _3603 c) = (term1 _3603 c).
Proof. exact (MK_COMB (@lem20159 _3603) (@lem20158 _3603 c)). Qed.
Lemma lem20161 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem20162 {_3603 : Type'} (c : _3603) : (term43 _3603 c) = (term44 _3603 c).
Proof. exact (MK_COMB (@lem20161) (@lem20160 _3603 c)). Qed.
Lemma lem20163 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (Q c) = (Q c).
Proof. exact (eq_refl (Q c)). Qed.
Lemma lem20164 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term77 _3603 Q c) = (term82 _3603 Q c).
Proof. exact (MK_COMB (@lem20162 _3603 c) (@lem20163 _3603 Q c)). Qed.
Lemma lem20165 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : ((term76 _3603 Q c) = (term77 _3603 Q c)) = ((term75 _3603 Q c) = (term82 _3603 Q c)).
Proof. exact (MK_COMB (@lem20156 _3603 Q c) (@lem20164 _3603 Q c)). Qed.
Lemma lem20166 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term75 _3603 Q c) = (term82 _3603 Q c).
Proof. exact (EQ_MP (@lem20165 _3603 Q c) (@lem20146 _3603 Q c)). Qed.
Lemma lem20170 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem20171 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem20170 p q p' q'). Qed.
Lemma lem20172 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem20171 p q p'). Qed.
Lemma lem20173 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : term83 _3603 Q c.
Proof. exact (@lem20172 (term1 _3603 c) (Q c)). Qed.
Lemma lem20174 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) (p' : Prop) : term84 _3603 Q c p'.
Proof. exact (@lem20173 _3603 Q c p'). Qed.
Lemma lem20175 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) (p' : Prop) : (term84 _3603 Q c p') = (term85 _3603 Q c p').
Proof. exact (eq_refl (term84 _3603 Q c p')). Qed.
Lemma lem20176 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) (p' : Prop) : term85 _3603 Q c p'.
Proof. exact (EQ_MP (@lem20175 _3603 Q c p') (@lem20174 _3603 Q c p')). Qed.
Lemma lem20177 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) (p' : Prop) (q' : Prop) : term86 _3603 Q c p' q'.
Proof. exact (@lem20176 _3603 Q c p' q'). Qed.
Lemma lem20178 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) (p' : Prop) (q' : Prop) : (term86 _3603 Q c p' q') = (term87 _3603 Q c p' q').
Proof. exact (eq_refl (term86 _3603 Q c p' q')). Qed.
Lemma lem20179 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) (p' : Prop) (q' : Prop) : term87 _3603 Q c p' q'.
Proof. exact (EQ_MP (@lem20178 _3603 Q c p' q') (@lem20177 _3603 Q c p' q')). Qed.
Lemma lem20181 {A : Type'} (a : A) : (term1 A a) = True.
Proof. exact (EQ_MP (@lem19797 A a) (@lem19796 A a)). Qed.
Lemma lem20182 {_3603 : Type'} (a : _3603) : (term1 _3603 a) = True.
Proof. exact (@lem20181 _3603 a). Qed.
Lemma lem20183 {_3603 : Type'} (c : _3603) : (term1 _3603 c) = True.
Proof. exact (@lem20182 _3603 c). Qed.
Lemma lem20186 {_3603 : Type'} (c : _3603) : (term51 _3603 c) = (term51 _3603 c).
Proof. exact (eq_refl (term51 _3603 c)). Qed.
Lemma lem20187 {_3603 : Type'} (c : _3603) : (term51 _3603 c) = ((term1 _3603 c) = True).
Proof. exact (eq_refl (term51 _3603 c)). Qed.
Lemma lem20188 {_3603 : Type'} (c : _3603) : (term52 _3603 c) = (term52 _3603 c).
Proof. exact (eq_refl (term52 _3603 c)). Qed.
Lemma lem20189 {_3603 : Type'} (c : _3603) : ((term51 _3603 c) = (term51 _3603 c)) = ((term51 _3603 c) = ((term1 _3603 c) = True)).
Proof. exact (MK_COMB (@lem20188 _3603 c) (@lem20187 _3603 c)). Qed.
Lemma lem20190 {_3603 : Type'} (c : _3603) : (term51 _3603 c) = ((term1 _3603 c) = True).
Proof. exact (eq_refl (term51 _3603 c)). Qed.
Lemma lem20191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20192 {_3603 : Type'} (c : _3603) : (term52 _3603 c) = (term53 _3603 c).
Proof. exact (MK_COMB (@lem20191) (@lem20190 _3603 c)). Qed.
Lemma lem20193 {_3603 : Type'} (c : _3603) : ((term1 _3603 c) = True) = ((term1 _3603 c) = True).
Proof. exact (eq_refl ((term1 _3603 c) = True)). Qed.
Lemma lem20194 {_3603 : Type'} (c : _3603) : ((term51 _3603 c) = ((term1 _3603 c) = True)) = (((term1 _3603 c) = True) = ((term1 _3603 c) = True)).
Proof. exact (MK_COMB (@lem20192 _3603 c) (@lem20193 _3603 c)). Qed.
Lemma lem20195 {_3603 : Type'} (c : _3603) : ((term51 _3603 c) = (term51 _3603 c)) = (((term1 _3603 c) = True) = ((term1 _3603 c) = True)).
Proof. exact (TRANS (@lem20189 _3603 c) (@lem20194 _3603 c)). Qed.
Lemma lem20196 {_3603 : Type'} (c : _3603) : ((term1 _3603 c) = True) = ((term1 _3603 c) = True).
Proof. exact (EQ_MP (@lem20195 _3603 c) (@lem20186 _3603 c)). Qed.
Lemma lem20197 {_3603 : Type'} (c : _3603) : (term1 _3603 c) = True.
Proof. exact (EQ_MP (@lem20196 _3603 c) (@lem20183 _3603 c)). Qed.
Lemma lem20198 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) (q' : Prop) : term88 _3603 Q c q'.
Proof. exact (@lem20179 _3603 Q c True q'). Qed.
Lemma lem20199 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) (q' : Prop) : term89 _3603 Q c q'.
Proof. exact (@lem20198 _3603 Q c q' (@lem20197 _3603 c)). Qed.
Lemma lem20205 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (Q c) = (Q c).
Proof. exact (eq_refl (Q c)). Qed.
Lemma lem20206 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : term90 _3603 Q c.
Proof. exact (fun h0 : True => @lem20205 _3603 Q c). Qed.
Lemma lem20207 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : term91 _3603 Q c.
Proof. exact (@lem20199 _3603 Q c (Q c)). Qed.
Lemma lem20208 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term82 _3603 Q c) = (term92 _3603 Q c).
Proof. exact (@lem20207 _3603 Q c (@lem20206 _3603 Q c)). Qed.
Lemma lem20210 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem20211 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term92 _3603 Q c) = (Q c).
Proof. exact (@lem20210 (Q c)). Qed.
Lemma lem20212 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term82 _3603 Q c) = (Q c).
Proof. exact (TRANS (@lem20208 _3603 Q c) (@lem20211 _3603 Q c)). Qed.
Lemma lem20213 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term75 _3603 Q c) = (Q c).
Proof. exact (TRANS (@lem20166 _3603 Q c) (@lem20212 _3603 Q c)). Qed.
Lemma lem20214 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : (term12 _3603 c Q) = (Q c).
Proof. exact (TRANS (@lem20142 _3603 Q c) (@lem20213 _3603 Q c)). Qed.
Lemma lem20215 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (h1 : P = (Q c)) : (P = (term12 _3603 c Q)) = ((Q c) = (Q c)).
Proof. exact (MK_COMB (@lem20029 _3603 P Q c h1) (@lem20214 _3603 Q c)). Qed.
Lemma lem20217 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem20218 (x : Prop) : (x = x) = True.
Proof. exact (@lem20217 Prop x). Qed.
Lemma lem20219 {_3603 : Type'} (Q : _3603 -> Prop) (c : _3603) : ((Q c) = (Q c)) = True.
Proof. exact (@lem20218 (Q c)). Qed.
Lemma lem20220 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) (h1 : P = (Q c)) : (P = (term12 _3603 c Q)) = True.
Proof. exact (TRANS (@lem20215 _3603 P Q c h1) (@lem20219 _3603 Q c)). Qed.
Lemma lem20221 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term93 _3603 P c Q.
Proof. exact (fun h0 : P = (Q c) => @lem20220 _3603 P Q c h0). Qed.
Lemma lem20222 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : term94 _3603 P Q c.
Proof. exact (@lem20022 _3603 P Q c True). Qed.
Lemma lem20223 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term95 _3603 P c Q) = (term96 _3603 P Q c).
Proof. exact (@lem20222 _3603 P Q c (@lem20221 _3603 P c Q)). Qed.
Lemma lem20227 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem20228 {_3603 : Type'} (P : Prop) (Q : _3603 -> Prop) (c : _3603) : (term96 _3603 P Q c) = True.
Proof. exact (@lem20227 (P = (Q c))). Qed.
Lemma lem20229 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : (term95 _3603 P c Q) = True.
Proof. exact (TRANS (@lem20223 _3603 P Q c) (@lem20228 _3603 P Q c)). Qed.
Lemma lem20230 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : True = (term95 _3603 P c Q).
Proof. exact (SYM (@lem20229 _3603 P c Q)). Qed.
