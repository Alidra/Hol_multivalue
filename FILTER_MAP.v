Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FILTER_MAP_term_abbrevs.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1106562_spec.
Require Import thm1106563_spec.
Require Import thm1106571_spec.
Require Import thm1106572_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1147888 {A B : Type'} : term0 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1147889 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem1147888 A B f). Qed.
Lemma lem1147890 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem1147891 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem1147890 A B f) (@lem1147889 A B f)). Qed.
Lemma lem1147892 {A B : Type'} (f : A -> B) (h : A) : term3 A B f h.
Proof. exact (@lem1147891 A B f h). Qed.
Lemma lem1147893 {A B : Type'} (h : A) (f : A -> B) : (term3 A B f h) = (term4 A B h f).
Proof. exact (eq_refl (term3 A B f h)). Qed.
Lemma lem1147894 {A B : Type'} (h : A) (f : A -> B) : term4 A B h f.
Proof. exact (EQ_MP (@lem1147893 A B h f) (@lem1147892 A B f h)). Qed.
Lemma lem1147895 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term5 A B h f t.
Proof. exact (@lem1147894 A B h f t). Qed.
Lemma lem1147896 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term5 A B h f t) = ((term6 A B f h t) = (term7 A B h f t)).
Proof. exact (eq_refl (term5 A B h f t)). Qed.
Lemma lem1147903 {A : Type'} (P : type1143 A) : term8 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1147904 {_27046 : Type'} (P : type1143 _27046) : term8 _27046 P.
Proof. exact (@lem1147903 _27046 P). Qed.
Lemma lem1147905 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : term9 _27039 _27046 P f.
Proof. exact (@lem1147904 _27046 (term10 _27039 _27046 P f)). Qed.
Lemma lem1147906 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term11 _27039 _27046 P f) = ((term12 _27039 _27046 P f) = (term13 _27039 _27046 P f)).
Proof. exact (eq_refl (term11 _27039 _27046 P f)). Qed.
Lemma lem1147907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1147908 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term14 _27039 _27046 P f) = (term15 _27039 _27046 P f).
Proof. exact (MK_COMB (@lem1147907) (@lem1147906 _27039 _27046 P f)). Qed.
Lemma lem1147909 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term16 _27039 _27046 P f t) = ((term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)).
Proof. exact (eq_refl (term16 _27039 _27046 P f t)). Qed.
Lemma lem1147910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1147911 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term19 _27039 _27046 P f t) = (term20 _27039 _27046 P f t).
Proof. exact (MK_COMB (@lem1147910) (@lem1147909 _27039 _27046 P f t)). Qed.
Lemma lem1147912 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (t : list _27046) : (term21 _27039 _27046 P f h t) = ((term22 _27039 _27046 P f h t) = (term23 _27039 _27046 P f h t)).
Proof. exact (eq_refl (term21 _27039 _27046 P f h t)). Qed.
Lemma lem1147913 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (t : list _27046) : (term24 _27039 _27046 P f h t) = (term25 _27039 _27046 P f h t).
Proof. exact (MK_COMB (@lem1147911 _27039 _27046 P f t) (@lem1147912 _27039 _27046 P f h t)). Qed.
Lemma lem1147914 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term26 _27039 _27046 P f h) = (term27 _27039 _27046 P f h).
Proof. exact (fun_ext (fun t : list _27046 => @lem1147913 _27039 _27046 P f h t)). Qed.
Lemma lem1147915 {_27046 : Type'} : (@all (list _27046)) = (@all (list _27046)).
Proof. exact (eq_refl (@all (list _27046))). Qed.
Lemma lem1147916 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term28 _27039 _27046 P f h) = (term29 _27039 _27046 P f h).
Proof. exact (MK_COMB (@lem1147915 _27046) (@lem1147914 _27039 _27046 P f h)). Qed.
Lemma lem1147917 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term30 _27039 _27046 P f) = (term31 _27039 _27046 P f).
Proof. exact (fun_ext (fun h : _27046 => @lem1147916 _27039 _27046 P f h)). Qed.
Lemma lem1147918 {_27046 : Type'} : (@all _27046) = (@all _27046).
Proof. exact (eq_refl (@all _27046)). Qed.
Lemma lem1147919 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term32 _27039 _27046 P f) = (term33 _27039 _27046 P f).
Proof. exact (MK_COMB (@lem1147918 _27046) (@lem1147917 _27039 _27046 P f)). Qed.
Lemma lem1147920 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term34 _27039 _27046 P f) = (term35 _27039 _27046 P f).
Proof. exact (MK_COMB (@lem1147908 _27039 _27046 P f) (@lem1147919 _27039 _27046 P f)). Qed.
Lemma lem1147921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1147922 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term36 _27039 _27046 P f) = (term37 _27039 _27046 P f).
Proof. exact (MK_COMB (@lem1147921) (@lem1147920 _27039 _27046 P f)). Qed.
Lemma lem1147923 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (l : list _27046) : (term16 _27039 _27046 P f l) = ((term17 _27039 _27046 P f l) = (term18 _27039 _27046 P f l)).
Proof. exact (eq_refl (term16 _27039 _27046 P f l)). Qed.
Lemma lem1147924 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term38 _27039 _27046 P f) = (term10 _27039 _27046 P f).
Proof. exact (fun_ext (fun l : list _27046 => @lem1147923 _27039 _27046 P f l)). Qed.
Lemma lem1147925 {_27046 : Type'} : (@all (list _27046)) = (@all (list _27046)).
Proof. exact (eq_refl (@all (list _27046))). Qed.
Lemma lem1147926 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term39 _27039 _27046 P f) = (term40 _27039 _27046 P f).
Proof. exact (MK_COMB (@lem1147925 _27046) (@lem1147924 _27039 _27046 P f)). Qed.
Lemma lem1147927 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term9 _27039 _27046 P f) = (term41 _27039 _27046 P f).
Proof. exact (MK_COMB (@lem1147922 _27039 _27046 P f) (@lem1147926 _27039 _27046 P f)). Qed.
Lemma lem1147928 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : term41 _27039 _27046 P f.
Proof. exact (EQ_MP (@lem1147927 _27039 _27046 P f) (@lem1147905 _27039 _27046 P f)). Qed.
Lemma lem1147951 {A B : Type'} : term42 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1147952 {A B : Type'} (f : A -> B) : term43 A B f.
Proof. exact (@lem1147951 A B f). Qed.
Lemma lem1147953 {A B : Type'} (f : A -> B) : (term43 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term43 A B f)). Qed.
Lemma lem1147958 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1147953 A B f) (@lem1147952 A B f)). Qed.
Lemma lem1147959 {_27039 _27046 : Type'} (f : _27046 -> _27039) : (@List.map _27046 _27039 f (@nil _27046)) = (@nil _27039).
Proof. exact (@lem1147958 _27046 _27039 f). Qed.
Lemma lem1147960 {_27039 : Type'} (P : _27039 -> Prop) : (@FILTER _27039 P) = (@FILTER _27039 P).
Proof. exact (eq_refl (@FILTER _27039 P)). Qed.
Lemma lem1147961 {_27039 _27046 : Type'} (f : _27046 -> _27039) (P : _27039 -> Prop) : (term12 _27039 _27046 P f) = (@FILTER _27039 P (@nil _27039)).
Proof. exact (MK_COMB (@lem1147960 _27039 P) (@lem1147959 _27039 _27046 f)). Qed.
Lemma lem1147963 {_25594 : Type'} (P : _25594 -> Prop) : (@FILTER _25594 P (@nil _25594)) = (@nil _25594).
Proof. exact (EQ_MP (@lem1106563 _25594 P) (@lem1106562 _25594 P)). Qed.
Lemma lem1147964 {_27039 : Type'} (P : _27039 -> Prop) : (@FILTER _27039 P (@nil _27039)) = (@nil _27039).
Proof. exact (@lem1147963 _27039 P). Qed.
Lemma lem1147965 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term12 _27039 _27046 P f) = (@nil _27039).
Proof. exact (TRANS (@lem1147961 _27039 _27046 f P) (@lem1147964 _27039 P)). Qed.
Lemma lem1147966 {_27039 : Type'} : (@eq (list _27039)) = (@eq (list _27039)).
Proof. exact (eq_refl (@eq (list _27039))). Qed.
Lemma lem1147967 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term44 _27039 _27046 P f) = (@eq (list _27039) (@nil _27039)).
Proof. exact (MK_COMB (@lem1147966 _27039) (@lem1147965 _27039 _27046 P f)). Qed.
Lemma lem1147969 {_25594 : Type'} (P : _25594 -> Prop) : (@FILTER _25594 P (@nil _25594)) = (@nil _25594).
Proof. exact (EQ_MP (@lem1106563 _25594 P) (@lem1106562 _25594 P)). Qed.
Lemma lem1147970 {_27046 : Type'} (P : _27046 -> Prop) : (@FILTER _27046 P (@nil _27046)) = (@nil _27046).
Proof. exact (@lem1147969 _27046 P). Qed.
Lemma lem1147971 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term45 _27039 _27046 P f) = (@nil _27046).
Proof. exact (@lem1147970 _27046 (@o _27046 _27039 Prop P f)). Qed.
Lemma lem1147972 {_27039 _27046 : Type'} (f : _27046 -> _27039) : (@List.map _27046 _27039 f) = (@List.map _27046 _27039 f).
Proof. exact (eq_refl (@List.map _27046 _27039 f)). Qed.
Lemma lem1147973 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term13 _27039 _27046 P f) = (@List.map _27046 _27039 f (@nil _27046)).
Proof. exact (MK_COMB (@lem1147972 _27039 _27046 f) (@lem1147971 _27039 _27046 P f)). Qed.
Lemma lem1147975 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1147953 A B f) (@lem1147952 A B f)). Qed.
Lemma lem1147976 {_27039 _27046 : Type'} (f : _27046 -> _27039) : (@List.map _27046 _27039 f (@nil _27046)) = (@nil _27039).
Proof. exact (@lem1147975 _27046 _27039 f). Qed.
Lemma lem1147977 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term13 _27039 _27046 P f) = (@nil _27039).
Proof. exact (TRANS (@lem1147973 _27039 _27046 P f) (@lem1147976 _27039 _27046 f)). Qed.
Lemma lem1147978 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : ((term12 _27039 _27046 P f) = (term13 _27039 _27046 P f)) = ((@nil _27039) = (@nil _27039)).
Proof. exact (MK_COMB (@lem1147967 _27039 _27046 P f) (@lem1147977 _27039 _27046 P f)). Qed.
Lemma lem1147980 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1147981 {_27039 : Type'} (x : list _27039) : (x = x) = True.
Proof. exact (@lem1147980 (list _27039) x). Qed.
Lemma lem1147982 {_27039 : Type'} : ((@nil _27039) = (@nil _27039)) = True.
Proof. exact (@lem1147981 _27039 (@nil _27039)). Qed.
Lemma lem1147983 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : ((term12 _27039 _27046 P f) = (term13 _27039 _27046 P f)) = True.
Proof. exact (TRANS (@lem1147978 _27039 _27046 P f) (@lem1147982 _27039)). Qed.
Lemma lem1147984 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : True = ((term12 _27039 _27046 P f) = (term13 _27039 _27046 P f)).
Proof. exact (SYM (@lem1147983 _27039 _27046 P f)). Qed.
Lemma lem1147985 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : (term12 _27039 _27046 P f) = (term13 _27039 _27046 P f).
Proof. exact (EQ_MP (@lem1147984 _27039 _27046 P f) (@lem0)). Qed.
Lemma lem1147986 {A B C : Type'} (f : B -> C) : term46 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem1147987 {A B C : Type'} (f : B -> C) : (term46 A B C f) = (term47 A B C f).
Proof. exact (eq_refl (term46 A B C f)). Qed.
Lemma lem1147988 {A B C : Type'} (f : B -> C) : term47 A B C f.
Proof. exact (EQ_MP (@lem1147987 A B C f) (@lem1147986 A B C f)). Qed.
Lemma lem1147989 {A B C : Type'} (f : B -> C) (g : A -> B) : term48 A B C f g.
Proof. exact (@lem1147988 A B C f g). Qed.
Lemma lem1147990 {A B C : Type'} (f : B -> C) (g : A -> B) : (term48 A B C f g) = (term49 A B C f g).
Proof. exact (eq_refl (term48 A B C f g)). Qed.
Lemma lem1147991 {A B C : Type'} (f : B -> C) (g : A -> B) : term49 A B C f g.
Proof. exact (EQ_MP (@lem1147990 A B C f g) (@lem1147989 A B C f g)). Qed.
Lemma lem1147992 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term50 A B C f g x.
Proof. exact (@lem1147991 A B C f g x). Qed.
Lemma lem1147993 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term50 A B C f g x) = ((@o A B C f g x) = (term51 A B C f g x)).
Proof. exact (eq_refl (term50 A B C f g x)). Qed.
Lemma lem1147997 {A B : Type'} : term0 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1147998 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem1147997 A B f). Qed.
Lemma lem1147999 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem1148000 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem1147999 A B f) (@lem1147998 A B f)). Qed.
Lemma lem1148001 {A B : Type'} (f : A -> B) (h : A) : term3 A B f h.
Proof. exact (@lem1148000 A B f h). Qed.
Lemma lem1148002 {A B : Type'} (h : A) (f : A -> B) : (term3 A B f h) = (term4 A B h f).
Proof. exact (eq_refl (term3 A B f h)). Qed.
Lemma lem1148003 {A B : Type'} (h : A) (f : A -> B) : term4 A B h f.
Proof. exact (EQ_MP (@lem1148002 A B h f) (@lem1148001 A B f h)). Qed.
Lemma lem1148004 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term5 A B h f t.
Proof. exact (@lem1148003 A B h f t). Qed.
Lemma lem1148005 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term5 A B h f t) = ((term6 A B f h t) = (term7 A B h f t)).
Proof. exact (eq_refl (term5 A B h f t)). Qed.
Lemma lem1148014 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term6 A B f h t) = (term7 A B h f t).
Proof. exact (EQ_MP (@lem1148005 A B h f t) (@lem1148004 A B h f t)). Qed.
Lemma lem1148015 {_27039 _27046 : Type'} (h : _27046) (f : _27046 -> _27039) (t : list _27046) : (term52 _27039 _27046 f h t) = (term53 _27039 _27046 h f t).
Proof. exact (@lem1148014 _27046 _27039 h f t). Qed.
Lemma lem1148016 {_27039 : Type'} (P : _27039 -> Prop) : (@FILTER _27039 P) = (@FILTER _27039 P).
Proof. exact (eq_refl (@FILTER _27039 P)). Qed.
Lemma lem1148017 {_27039 _27046 : Type'} (P : _27039 -> Prop) (h : _27046) (f : _27046 -> _27039) (t : list _27046) : (term22 _27039 _27046 P f h t) = (term54 _27039 _27046 P h f t).
Proof. exact (MK_COMB (@lem1148016 _27039 P) (@lem1148015 _27039 _27046 h f t)). Qed.
Lemma lem1148019 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term55 _25594 P h t) = (term56 _25594 h P t).
Proof. exact (EQ_MP (@lem1106572 _25594 h P t) (@lem1106571 _25594 h P t)). Qed.
Lemma lem1148020 {_27039 : Type'} (h : _27039) (P : _27039 -> Prop) (t : list _27039) : (term55 _27039 P h t) = (term56 _27039 h P t).
Proof. exact (@lem1148019 _27039 h P t). Qed.
Lemma lem1148021 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term54 _27039 _27046 P h f t) = (term57 _27039 _27046 h P f t).
Proof. exact (@lem1148020 _27039 (f h) P (@List.map _27046 _27039 f t)). Qed.
Lemma lem1148023 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t).
Proof. exact (h1). Qed.
Lemma lem1148024 {_27039 _27046 : Type'} (f : _27046 -> _27039) (h : _27046) : (term58 _27039 _27046 f h) = (term58 _27039 _27046 f h).
Proof. exact (eq_refl (term58 _27039 _27046 f h)). Qed.
Lemma lem1148025 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term59 _27039 _27046 h P f t) = (term60 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148024 _27039 _27046 f h) (@lem1148023 _27039 _27046 P f t h1)). Qed.
Lemma lem1148026 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term61 _27039 _27046 P f h) = (term61 _27039 _27046 P f h).
Proof. exact (eq_refl (term61 _27039 _27046 P f h)). Qed.
Lemma lem1148027 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term62 _27039 _27046 h P f t) = (term63 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148026 _27039 _27046 P f h) (@lem1148025 _27039 _27046 h P f t h1)). Qed.
Lemma lem1148029 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t).
Proof. exact (h1). Qed.
Lemma lem1148030 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term57 _27039 _27046 h P f t) = (term64 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148027 _27039 _27046 h P f t h1) (@lem1148029 _27039 _27046 P f t h1)). Qed.
Lemma lem1148031 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term54 _27039 _27046 P h f t) = (term64 _27039 _27046 h P f t).
Proof. exact (TRANS (@lem1148021 _27039 _27046 h P f t) (@lem1148030 _27039 _27046 h P f t h1)). Qed.
Lemma lem1148032 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term22 _27039 _27046 P f h t) = (term64 _27039 _27046 h P f t).
Proof. exact (TRANS (@lem1148017 _27039 _27046 P h f t) (@lem1148031 _27039 _27046 h P f t h1)). Qed.
Lemma lem1148033 {_27039 : Type'} : (@eq (list _27039)) = (@eq (list _27039)).
Proof. exact (eq_refl (@eq (list _27039))). Qed.
Lemma lem1148034 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term65 _27039 _27046 P f h t) = (term66 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148033 _27039) (@lem1148032 _27039 _27046 h P f t h1)). Qed.
Lemma lem1148036 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term55 _25594 P h t) = (term56 _25594 h P t).
Proof. exact (EQ_MP (@lem1106572 _25594 h P t) (@lem1106571 _25594 h P t)). Qed.
Lemma lem1148037 {_27046 : Type'} (h : _27046) (P : _27046 -> Prop) (t : list _27046) : (term55 _27046 P h t) = (term56 _27046 h P t).
Proof. exact (@lem1148036 _27046 h P t). Qed.
Lemma lem1148038 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term67 _27039 _27046 P f h t) = (term68 _27039 _27046 h P f t).
Proof. exact (@lem1148037 _27046 h (@o _27046 _27039 Prop P f) t). Qed.
Lemma lem1148040 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term51 A B C f g x).
Proof. exact (EQ_MP (@lem1147993 A B C f g x) (@lem1147992 A B C f g x)). Qed.
Lemma lem1148041 {_27039 _27046 : Type'} (f : _27039 -> Prop) (g : _27046 -> _27039) (x : _27046) : (@o _27046 _27039 Prop f g x) = (term69 _27039 _27046 f g x).
Proof. exact (@lem1148040 _27046 _27039 Prop f g x). Qed.
Lemma lem1148042 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (@o _27046 _27039 Prop P f h) = (term69 _27039 _27046 P f h).
Proof. exact (@lem1148041 _27039 _27046 P f h). Qed.
Lemma lem1148043 {_27046 : Type'} : (@COND (list _27046)) = (@COND (list _27046)).
Proof. exact (eq_refl (@COND (list _27046))). Qed.
Lemma lem1148044 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term70 _27039 _27046 P f h) = (term71 _27039 _27046 P f h).
Proof. exact (MK_COMB (@lem1148043 _27046) (@lem1148042 _27039 _27046 P f h)). Qed.
Lemma lem1148045 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term72 _27039 _27046 h P f t) = (term72 _27039 _27046 h P f t).
Proof. exact (eq_refl (term72 _27039 _27046 h P f t)). Qed.
Lemma lem1148046 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term73 _27039 _27046 h P f t) = (term74 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148044 _27039 _27046 P f h) (@lem1148045 _27039 _27046 h P f t)). Qed.
Lemma lem1148047 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term75 _27039 _27046 P f t) = (term75 _27039 _27046 P f t).
Proof. exact (eq_refl (term75 _27039 _27046 P f t)). Qed.
Lemma lem1148048 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term68 _27039 _27046 h P f t) = (term76 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148046 _27039 _27046 h P f t) (@lem1148047 _27039 _27046 P f t)). Qed.
Lemma lem1148049 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term67 _27039 _27046 P f h t) = (term76 _27039 _27046 h P f t).
Proof. exact (TRANS (@lem1148038 _27039 _27046 h P f t) (@lem1148048 _27039 _27046 h P f t)). Qed.
Lemma lem1148050 {_27039 _27046 : Type'} (f : _27046 -> _27039) : (@List.map _27046 _27039 f) = (@List.map _27046 _27039 f).
Proof. exact (eq_refl (@List.map _27046 _27039 f)). Qed.
Lemma lem1148051 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term23 _27039 _27046 P f h t) = (term77 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148050 _27039 _27046 f) (@lem1148049 _27039 _27046 h P f t)). Qed.
Lemma lem1148052 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : ((term22 _27039 _27046 P f h t) = (term23 _27039 _27046 P f h t)) = ((term64 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (MK_COMB (@lem1148034 _27039 _27046 h P f t h1) (@lem1148051 _27039 _27046 h P f t)). Qed.
Lemma lem1148055 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : ((term64 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)) = ((term22 _27039 _27046 P f h t) = (term23 _27039 _27046 P f h t)).
Proof. exact (SYM (@lem1148052 _27039 _27046 h P f t h1)). Qed.
Lemma lem1148056 {_27039 : Type'} (_474 : list _27039) (_475 : Prop) (_476 : type1143 _27039) (_477 : list _27039) : (term78 _27039 _476 _475 _474 _477) = (term79 _27039 _474 _475 _476 _477).
Proof. exact (@lem13473 (list _27039) _474 _475 _476 _477). Qed.
Lemma lem1148057 {_27039 _27046 : Type'} (_474 : list _27039) (_475 : Prop) (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (_477 : list _27039) : (term80 _27039 _27046 h P f t _475 _474 _477) = (term81 _27039 _27046 _474 _475 h P f t _477).
Proof. exact (@lem1148056 _27039 _474 _475 (term82 _27039 _27046 h P f t) _477). Qed.
Lemma lem1148058 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term83 _27039 _27046 h P f t) = (term84 _27039 _27046 h P f t).
Proof. exact (@lem1148057 _27039 _27046 (term60 _27039 _27046 h P f t) (term69 _27039 _27046 P f h) h P f t (term18 _27039 _27046 P f t)). Qed.
Lemma lem1148059 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term85 _27039 _27046 h P f t) = ((term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (eq_refl (term85 _27039 _27046 h P f t)). Qed.
Lemma lem1148060 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term86 _27039 _27046 P f h) = (term86 _27039 _27046 P f h).
Proof. exact (eq_refl (term86 _27039 _27046 P f h)). Qed.
Lemma lem1148061 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term87 _27039 _27046 h P f t) = (term88 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148060 _27039 _27046 P f h) (@lem1148059 _27039 _27046 h P f t)). Qed.
Lemma lem1148062 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term89 _27039 _27046 h P f t) = ((term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (eq_refl (term89 _27039 _27046 h P f t)). Qed.
Lemma lem1148063 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term90 _27039 _27046 P f h) = (term90 _27039 _27046 P f h).
Proof. exact (eq_refl (term90 _27039 _27046 P f h)). Qed.
Lemma lem1148064 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term91 _27039 _27046 h P f t) = (term92 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148063 _27039 _27046 P f h) (@lem1148062 _27039 _27046 h P f t)). Qed.
Lemma lem1148065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1148066 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term93 _27039 _27046 h P f t) = (term94 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148065) (@lem1148064 _27039 _27046 h P f t)). Qed.
Lemma lem1148067 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term84 _27039 _27046 h P f t) = (term95 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148066 _27039 _27046 h P f t) (@lem1148061 _27039 _27046 h P f t)). Qed.
Lemma lem1148068 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term83 _27039 _27046 h P f t) = ((term64 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (eq_refl (term83 _27039 _27046 h P f t)). Qed.
Lemma lem1148069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1148070 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term96 _27039 _27046 h P f t) = (term97 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148069) (@lem1148068 _27039 _27046 h P f t)). Qed.
Lemma lem1148071 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term83 _27039 _27046 h P f t) = (term84 _27039 _27046 h P f t)) = (((term64 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)) = (term95 _27039 _27046 h P f t)).
Proof. exact (MK_COMB (@lem1148070 _27039 _27046 h P f t) (@lem1148067 _27039 _27046 h P f t)). Qed.
Lemma lem1148072 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term64 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)) = (term95 _27039 _27046 h P f t).
Proof. exact (EQ_MP (@lem1148071 _27039 _27046 h P f t) (@lem1148058 _27039 _27046 h P f t)). Qed.
Lemma lem1148073 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term95 _27039 _27046 h P f t) = ((term64 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (SYM (@lem1148072 _27039 _27046 h P f t)). Qed.
Lemma lem1148074 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term69 _27039 _27046 P f h) : term69 _27039 _27046 P f h.
Proof. exact (h1). Qed.
Lemma lem1148075 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term69 _27039 _27046 P f h) = ((term69 _27039 _27046 P f h) = True).
Proof. exact (@lem7 (term69 _27039 _27046 P f h)). Qed.
Lemma lem1148076 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term69 _27039 _27046 P f h) : (term69 _27039 _27046 P f h) = True.
Proof. exact (EQ_MP (@lem1148075 _27039 _27046 P f h) (@lem1148074 _27039 _27046 P f h h1)). Qed.
Lemma lem1148077 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term98 _27039 _27046 h P f t) = (term98 _27039 _27046 h P f t).
Proof. exact (eq_refl (term98 _27039 _27046 h P f t)). Qed.
Lemma lem1148078 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term69 _27039 _27046 P f h) : (term99 _27039 _27046 t P f h) = (term100 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148077 _27039 _27046 h P f t) (@lem1148076 _27039 _27046 P f h h1)). Qed.
Lemma lem1148079 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term100 _27039 _27046 h P f t) = ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t)).
Proof. exact (eq_refl (term100 _27039 _27046 h P f t)). Qed.
Lemma lem1148080 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term102 _27039 _27046 t P f h) = (term102 _27039 _27046 t P f h).
Proof. exact (eq_refl (term102 _27039 _27046 t P f h)). Qed.
Lemma lem1148081 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term99 _27039 _27046 t P f h) = (term100 _27039 _27046 h P f t)) = ((term99 _27039 _27046 t P f h) = ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t))).
Proof. exact (MK_COMB (@lem1148080 _27039 _27046 t P f h) (@lem1148079 _27039 _27046 h P f t)). Qed.
Lemma lem1148082 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term99 _27039 _27046 t P f h) = ((term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (eq_refl (term99 _27039 _27046 t P f h)). Qed.
Lemma lem1148083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1148084 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term102 _27039 _27046 t P f h) = (term103 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148083) (@lem1148082 _27039 _27046 h P f t)). Qed.
Lemma lem1148085 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t)) = ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t)).
Proof. exact (eq_refl ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t))). Qed.
Lemma lem1148086 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term99 _27039 _27046 t P f h) = ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t))) = (((term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)) = ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t))).
Proof. exact (MK_COMB (@lem1148084 _27039 _27046 h P f t) (@lem1148085 _27039 _27046 h P f t)). Qed.
Lemma lem1148087 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term99 _27039 _27046 t P f h) = (term100 _27039 _27046 h P f t)) = (((term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)) = ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t))).
Proof. exact (TRANS (@lem1148081 _27039 _27046 h P f t) (@lem1148086 _27039 _27046 h P f t)). Qed.
Lemma lem1148088 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term69 _27039 _27046 P f h) : ((term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)) = ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t)).
Proof. exact (EQ_MP (@lem1148087 _27039 _27046 h P f t) (@lem1148078 _27039 _27046 t P f h h1)). Qed.
Lemma lem1148089 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term69 _27039 _27046 P f h) : ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t)) = ((term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (SYM (@lem1148088 _27039 _27046 t P f h h1)). Qed.
Lemma lem1148090 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term104 _27039 _27046 P f h) : term104 _27039 _27046 P f h.
Proof. exact (h1). Qed.
Lemma lem1148091 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : term105 _27039 _27046 P f h.
Proof. exact (@lem82 (term69 _27039 _27046 P f h)). Qed.
Lemma lem1148092 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term104 _27039 _27046 P f h) : (term69 _27039 _27046 P f h) = False.
Proof. exact (@lem1148091 _27039 _27046 P f h (@lem1148090 _27039 _27046 P f h h1)). Qed.
Lemma lem1148093 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term106 _27039 _27046 h P f t) = (term106 _27039 _27046 h P f t).
Proof. exact (eq_refl (term106 _27039 _27046 h P f t)). Qed.
Lemma lem1148094 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term104 _27039 _27046 P f h) : (term107 _27039 _27046 t P f h) = (term108 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148093 _27039 _27046 h P f t) (@lem1148092 _27039 _27046 P f h h1)). Qed.
Lemma lem1148095 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term108 _27039 _27046 h P f t) = ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t)).
Proof. exact (eq_refl (term108 _27039 _27046 h P f t)). Qed.
Lemma lem1148096 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : (term110 _27039 _27046 t P f h) = (term110 _27039 _27046 t P f h).
Proof. exact (eq_refl (term110 _27039 _27046 t P f h)). Qed.
Lemma lem1148097 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term107 _27039 _27046 t P f h) = (term108 _27039 _27046 h P f t)) = ((term107 _27039 _27046 t P f h) = ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t))).
Proof. exact (MK_COMB (@lem1148096 _27039 _27046 t P f h) (@lem1148095 _27039 _27046 h P f t)). Qed.
Lemma lem1148098 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term107 _27039 _27046 t P f h) = ((term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (eq_refl (term107 _27039 _27046 t P f h)). Qed.
Lemma lem1148099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1148100 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term110 _27039 _27046 t P f h) = (term111 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148099) (@lem1148098 _27039 _27046 h P f t)). Qed.
Lemma lem1148101 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t)) = ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t)).
Proof. exact (eq_refl ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t))). Qed.
Lemma lem1148102 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term107 _27039 _27046 t P f h) = ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t))) = (((term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t)) = ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t))).
Proof. exact (MK_COMB (@lem1148100 _27039 _27046 h P f t) (@lem1148101 _27039 _27046 h P f t)). Qed.
Lemma lem1148103 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term107 _27039 _27046 t P f h) = (term108 _27039 _27046 h P f t)) = (((term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t)) = ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t))).
Proof. exact (TRANS (@lem1148097 _27039 _27046 h P f t) (@lem1148102 _27039 _27046 h P f t)). Qed.
Lemma lem1148104 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term104 _27039 _27046 P f h) : ((term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t)) = ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t)).
Proof. exact (EQ_MP (@lem1148103 _27039 _27046 h P f t) (@lem1148094 _27039 _27046 t P f h h1)). Qed.
Lemma lem1148105 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term104 _27039 _27046 P f h) : ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t)) = ((term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (SYM (@lem1148104 _27039 _27046 t P f h h1)). Qed.
Lemma lem1148109 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1148110 {_27046 : Type'} (t2 : list _27046) (t1 : list _27046) : (@COND (list _27046) True t1 t2) = t1.
Proof. exact (@lem1148109 (list _27046) t2 t1). Qed.
Lemma lem1148111 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term112 _27039 _27046 h P f t) = (term72 _27039 _27046 h P f t).
Proof. exact (@lem1148110 _27046 (term75 _27039 _27046 P f t) (term72 _27039 _27046 h P f t)). Qed.
Lemma lem1148112 {_27039 _27046 : Type'} (f : _27046 -> _27039) : (@List.map _27046 _27039 f) = (@List.map _27046 _27039 f).
Proof. exact (eq_refl (@List.map _27046 _27039 f)). Qed.
Lemma lem1148113 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term101 _27039 _27046 h P f t) = (term113 _27039 _27046 h P f t).
Proof. exact (MK_COMB (@lem1148112 _27039 _27046 f) (@lem1148111 _27039 _27046 h P f t)). Qed.
Lemma lem1148115 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term6 A B f h t) = (term7 A B h f t).
Proof. exact (EQ_MP (@lem1147896 A B h f t) (@lem1147895 A B h f t)). Qed.
Lemma lem1148116 {_27039 _27046 : Type'} (h : _27046) (f : _27046 -> _27039) (t : list _27046) : (term52 _27039 _27046 f h t) = (term53 _27039 _27046 h f t).
Proof. exact (@lem1148115 _27046 _27039 h f t). Qed.
Lemma lem1148117 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term113 _27039 _27046 h P f t) = (term60 _27039 _27046 h P f t).
Proof. exact (@lem1148116 _27039 _27046 h f (term75 _27039 _27046 P f t)). Qed.
Lemma lem1148118 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term101 _27039 _27046 h P f t) = (term60 _27039 _27046 h P f t).
Proof. exact (TRANS (@lem1148113 _27039 _27046 h P f t) (@lem1148117 _27039 _27046 h P f t)). Qed.
Lemma lem1148119 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term114 _27039 _27046 h P f t) = (term114 _27039 _27046 h P f t).
Proof. exact (eq_refl (term114 _27039 _27046 h P f t)). Qed.
Lemma lem1148120 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t)) = ((term60 _27039 _27046 h P f t) = (term60 _27039 _27046 h P f t)).
Proof. exact (MK_COMB (@lem1148119 _27039 _27046 h P f t) (@lem1148118 _27039 _27046 h P f t)). Qed.
Lemma lem1148122 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1148123 {_27039 : Type'} (x : list _27039) : (x = x) = True.
Proof. exact (@lem1148122 (list _27039) x). Qed.
Lemma lem1148124 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term60 _27039 _27046 h P f t) = (term60 _27039 _27046 h P f t)) = True.
Proof. exact (@lem1148123 _27039 (term60 _27039 _27046 h P f t)). Qed.
Lemma lem1148125 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t)) = True.
Proof. exact (TRANS (@lem1148120 _27039 _27046 h P f t) (@lem1148124 _27039 _27046 h P f t)). Qed.
Lemma lem1148126 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : True = ((term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t)).
Proof. exact (SYM (@lem1148125 _27039 _27046 h P f t)). Qed.
Lemma lem1148127 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term60 _27039 _27046 h P f t) = (term101 _27039 _27046 h P f t).
Proof. exact (EQ_MP (@lem1148126 _27039 _27046 h P f t) (@lem0)). Qed.
Lemma lem1148131 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1148132 {_27046 : Type'} (t1 : list _27046) (t2 : list _27046) : (@COND (list _27046) False t1 t2) = t2.
Proof. exact (@lem1148131 (list _27046) t1 t2). Qed.
Lemma lem1148133 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term115 _27039 _27046 h P f t) = (term75 _27039 _27046 P f t).
Proof. exact (@lem1148132 _27046 (term72 _27039 _27046 h P f t) (term75 _27039 _27046 P f t)). Qed.
Lemma lem1148134 {_27039 _27046 : Type'} (f : _27046 -> _27039) : (@List.map _27046 _27039 f) = (@List.map _27046 _27039 f).
Proof. exact (eq_refl (@List.map _27046 _27039 f)). Qed.
Lemma lem1148135 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term109 _27039 _27046 h P f t) = (term18 _27039 _27046 P f t).
Proof. exact (MK_COMB (@lem1148134 _27039 _27046 f) (@lem1148133 _27039 _27046 h P f t)). Qed.
Lemma lem1148136 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term116 _27039 _27046 P f t) = (term116 _27039 _27046 P f t).
Proof. exact (eq_refl (term116 _27039 _27046 P f t)). Qed.
Lemma lem1148137 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t)) = ((term18 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)).
Proof. exact (MK_COMB (@lem1148136 _27039 _27046 P f t) (@lem1148135 _27039 _27046 h P f t)). Qed.
Lemma lem1148139 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1148140 {_27039 : Type'} (x : list _27039) : (x = x) = True.
Proof. exact (@lem1148139 (list _27039) x). Qed.
Lemma lem1148141 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term18 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) = True.
Proof. exact (@lem1148140 _27039 (term18 _27039 _27046 P f t)). Qed.
Lemma lem1148142 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t)) = True.
Proof. exact (TRANS (@lem1148137 _27039 _27046 h P f t) (@lem1148141 _27039 _27046 P f t)). Qed.
Lemma lem1148143 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : True = ((term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t)).
Proof. exact (SYM (@lem1148142 _27039 _27046 h P f t)). Qed.
Lemma lem1148144 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term18 _27039 _27046 P f t) = (term109 _27039 _27046 h P f t).
Proof. exact (EQ_MP (@lem1148143 _27039 _27046 h P f t) (@lem0)). Qed.
Lemma lem1148145 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term104 _27039 _27046 P f h) : (term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t).
Proof. exact (EQ_MP (@lem1148105 _27039 _27046 t P f h h1) (@lem1148144 _27039 _27046 h P f t)). Qed.
Lemma lem1148146 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term104 _27039 _27046 P f h) : (term104 _27039 _27046 P f h) = ((term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (prop_ext (fun h2 : term104 _27039 _27046 P f h => @lem1148145 _27039 _27046 t P f h h1) (fun h2 : (term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t) => @lem1148090 _27039 _27046 P f h h1)). Qed.
Lemma lem1148147 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term104 _27039 _27046 P f h) : (term18 _27039 _27046 P f t) = (term77 _27039 _27046 h P f t).
Proof. exact (EQ_MP (@lem1148146 _27039 _27046 t P f h h1) (@lem1148090 _27039 _27046 P f h h1)). Qed.
Lemma lem1148148 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : term88 _27039 _27046 h P f t.
Proof. exact (fun h0 : term104 _27039 _27046 P f h => @lem1148147 _27039 _27046 t P f h h0). Qed.
Lemma lem1148149 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term69 _27039 _27046 P f h) : (term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t).
Proof. exact (EQ_MP (@lem1148089 _27039 _27046 t P f h h1) (@lem1148127 _27039 _27046 h P f t)). Qed.
Lemma lem1148150 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term69 _27039 _27046 P f h) : (term69 _27039 _27046 P f h) = ((term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t)).
Proof. exact (prop_ext (fun h2 : term69 _27039 _27046 P f h => @lem1148149 _27039 _27046 t P f h h1) (fun h2 : (term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t) => @lem1148074 _27039 _27046 P f h h1)). Qed.
Lemma lem1148151 {_27039 _27046 : Type'} (t : list _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (h1 : term69 _27039 _27046 P f h) : (term60 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t).
Proof. exact (EQ_MP (@lem1148150 _27039 _27046 t P f h h1) (@lem1148074 _27039 _27046 P f h h1)). Qed.
Lemma lem1148152 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : term92 _27039 _27046 h P f t.
Proof. exact (fun h0 : term69 _27039 _27046 P f h => @lem1148151 _27039 _27046 t P f h h0). Qed.
Lemma lem1148153 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : term95 _27039 _27046 h P f t.
Proof. exact (conj (@lem1148152 _27039 _27046 h P f t) (@lem1148148 _27039 _27046 h P f t)). Qed.
Lemma lem1148154 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) : (term64 _27039 _27046 h P f t) = (term77 _27039 _27046 h P f t).
Proof. exact (EQ_MP (@lem1148073 _27039 _27046 h P f t) (@lem1148153 _27039 _27046 h P f t)). Qed.
Lemma lem1148155 {_27039 _27046 : Type'} (h : _27046) (P : _27039 -> Prop) (f : _27046 -> _27039) (t : list _27046) (h1 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t)) : (term22 _27039 _27046 P f h t) = (term23 _27039 _27046 P f h t).
Proof. exact (EQ_MP (@lem1148055 _27039 _27046 h P f t h1) (@lem1148154 _27039 _27046 h P f t)). Qed.
Lemma lem1148156 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) (t : list _27046) : term25 _27039 _27046 P f h t.
Proof. exact (fun h0 : (term17 _27039 _27046 P f t) = (term18 _27039 _27046 P f t) => @lem1148155 _27039 _27046 h P f t h0). Qed.
Lemma lem1148161 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) (h : _27046) : term29 _27039 _27046 P f h.
Proof. exact (fun t : list _27046 => @lem1148156 _27039 _27046 P f h t). Qed.
Lemma lem1148166 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : term33 _27039 _27046 P f.
Proof. exact (fun h : _27046 => @lem1148161 _27039 _27046 P f h). Qed.
Lemma lem1148167 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : term35 _27039 _27046 P f.
Proof. exact (conj (@lem1147985 _27039 _27046 P f) (@lem1148166 _27039 _27046 P f)). Qed.
Lemma lem1148168 {_27039 _27046 : Type'} (P : _27039 -> Prop) (f : _27046 -> _27039) : term40 _27039 _27046 P f.
Proof. exact (@lem1147928 _27039 _27046 P f (@lem1148167 _27039 _27046 P f)). Qed.
Lemma lem1148173 {_27039 _27046 : Type'} (P : _27039 -> Prop) : term117 _27039 _27046 P.
Proof. exact (fun f : _27046 -> _27039 => @lem1148168 _27039 _27046 P f). Qed.
Lemma lem1148178 {_27039 _27046 : Type'} : term118 _27039 _27046.
Proof. exact (fun P : _27039 -> Prop => @lem1148173 _27039 _27046 P). Qed.
