Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REVERSE_APPEND_term_abbrevs.
Require Import APPEND_ASSOC_spec.
Require Import APPEND_NIL_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1096517_spec.
Require Import thm1096523_spec.
Require Import thm1096524_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1111916 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1111917 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1111916 A P). Qed.
Lemma lem1111918 {A : Type'} : term1 A.
Proof. exact (@lem1111917 A (term2 A)). Qed.
Lemma lem1111919 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1111920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1111921 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem1111920) (@lem1111919 A)). Qed.
Lemma lem1111922 {A : Type'} (t : list A) : (term7 A t) = (term8 A t).
Proof. exact (eq_refl (term7 A t)). Qed.
Lemma lem1111923 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1111924 {A : Type'} (t : list A) : (term9 A t) = (term10 A t).
Proof. exact (MK_COMB (@lem1111923) (@lem1111922 A t)). Qed.
Lemma lem1111925 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A h t).
Proof. exact (eq_refl (term11 A h t)). Qed.
Lemma lem1111926 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A h t).
Proof. exact (MK_COMB (@lem1111924 A t) (@lem1111925 A h t)). Qed.
Lemma lem1111927 {A : Type'} (h : A) : (term15 A h) = (term16 A h).
Proof. exact (fun_ext (fun t : list A => @lem1111926 A h t)). Qed.
Lemma lem1111928 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111929 {A : Type'} (h : A) : (term17 A h) = (term18 A h).
Proof. exact (MK_COMB (@lem1111928 A) (@lem1111927 A h)). Qed.
Lemma lem1111930 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun h : A => @lem1111929 A h)). Qed.
Lemma lem1111931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1111932 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem1111931 A) (@lem1111930 A)). Qed.
Lemma lem1111933 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem1111921 A) (@lem1111932 A)). Qed.
Lemma lem1111934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1111935 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (MK_COMB (@lem1111934) (@lem1111933 A)). Qed.
Lemma lem1111936 {A : Type'} (l : list A) : (term7 A l) = (term8 A l).
Proof. exact (eq_refl (term7 A l)). Qed.
Lemma lem1111937 {A : Type'} : (term27 A) = (term2 A).
Proof. exact (fun_ext (fun l : list A => @lem1111936 A l)). Qed.
Lemma lem1111938 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111939 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem1111938 A) (@lem1111937 A)). Qed.
Lemma lem1111940 {A : Type'} : (term1 A) = (term30 A).
Proof. exact (MK_COMB (@lem1111935 A) (@lem1111939 A)). Qed.
Lemma lem1111941 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem1111940 A) (@lem1111918 A)). Qed.
Lemma lem1111942 {A : Type'} (t : list A) (h1 : term8 A t) : term8 A t.
Proof. exact (h1). Qed.
Lemma lem1111952 {A : Type'} (l : list A) : term31 A l.
Proof. exact (@lem1111732 A l). Qed.
Lemma lem1111953 {A : Type'} (l : list A) : (term31 A l) = ((@List.app A l (@nil A)) = l).
Proof. exact (eq_refl (term31 A l)). Qed.
Lemma lem1111967 {A : Type'} : term32 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1111968 {A : Type'} (l : list A) : term33 A l.
Proof. exact (@lem1111967 A l). Qed.
Lemma lem1111969 {A : Type'} (l : list A) : (term33 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term33 A l)). Qed.
Lemma lem1111978 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1111969 A l) (@lem1111968 A l)). Qed.
Lemma lem1111979 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1111978 A l). Qed.
Lemma lem1111980 {A : Type'} (m : list A) : (@List.app A (@nil A) m) = m.
Proof. exact (@lem1111979 A m). Qed.
Lemma lem1111981 {A : Type'} : (@List.rev A) = (@List.rev A).
Proof. exact (eq_refl (@List.rev A)). Qed.
Lemma lem1111982 {A : Type'} (m : list A) : (term34 A m) = (@List.rev A m).
Proof. exact (MK_COMB (@lem1111981 A) (@lem1111980 A m)). Qed.
Lemma lem1111983 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1111984 {A : Type'} (m : list A) : (term35 A m) = (term36 A m).
Proof. exact (MK_COMB (@lem1111983 A) (@lem1111982 A m)). Qed.
Lemma lem1111986 {A : Type'} : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096517 A)). Qed.
Lemma lem1111987 {A : Type'} (m : list A) : (term37 A m) = (term37 A m).
Proof. exact (eq_refl (term37 A m)). Qed.
Lemma lem1111988 {A : Type'} (m : list A) : (term38 A m) = (term39 A m).
Proof. exact (MK_COMB (@lem1111987 A m) (@lem1111986 A)). Qed.
Lemma lem1111990 {A : Type'} (l : list A) : (@List.app A l (@nil A)) = l.
Proof. exact (EQ_MP (@lem1111953 A l) (@lem1111952 A l)). Qed.
Lemma lem1111991 {A : Type'} (l : list A) : (@List.app A l (@nil A)) = l.
Proof. exact (@lem1111990 A l). Qed.
Lemma lem1111992 {A : Type'} (m : list A) : (term39 A m) = (@List.rev A m).
Proof. exact (@lem1111991 A (@List.rev A m)). Qed.
Lemma lem1111993 {A : Type'} (m : list A) : (term38 A m) = (@List.rev A m).
Proof. exact (TRANS (@lem1111988 A m) (@lem1111992 A m)). Qed.
Lemma lem1111994 {A : Type'} (m : list A) : ((term34 A m) = (term38 A m)) = ((@List.rev A m) = (@List.rev A m)).
Proof. exact (MK_COMB (@lem1111984 A m) (@lem1111993 A m)). Qed.
Lemma lem1111996 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1111997 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1111996 (list A) x). Qed.
Lemma lem1111998 {A : Type'} (m : list A) : ((@List.rev A m) = (@List.rev A m)) = True.
Proof. exact (@lem1111997 A (@List.rev A m)). Qed.
Lemma lem1111999 {A : Type'} (m : list A) : ((term34 A m) = (term38 A m)) = True.
Proof. exact (TRANS (@lem1111994 A m) (@lem1111998 A m)). Qed.
Lemma lem1112000 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (fun_ext (fun m : list A => @lem1111999 A m)). Qed.
Lemma lem1112001 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112002 {A : Type'} : (term4 A) = (term42 A).
Proof. exact (MK_COMB (@lem1112001 A) (@lem1112000 A)). Qed.
Lemma lem1112004 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1112005 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (@lem1112004 (list A) t). Qed.
Lemma lem1112006 {A : Type'} : (term42 A) = True.
Proof. exact (@lem1112005 A True). Qed.
Lemma lem1112007 {A : Type'} : (term4 A) = True.
Proof. exact (TRANS (@lem1112002 A) (@lem1112006 A)). Qed.
Lemma lem1112008 {A : Type'} : True = (term4 A).
Proof. exact (SYM (@lem1112007 A)). Qed.
Lemma lem1112009 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1112008 A) (@lem0)). Qed.
Lemma lem1112010 {A : Type'} (l : list A) : term45 A l.
Proof. exact (@lem1111914 A l). Qed.
Lemma lem1112011 {A : Type'} (l : list A) : (term45 A l) = (term46 A l).
Proof. exact (eq_refl (term45 A l)). Qed.
Lemma lem1112012 {A : Type'} (l : list A) : term46 A l.
Proof. exact (EQ_MP (@lem1112011 A l) (@lem1112010 A l)). Qed.
Lemma lem1112013 {A : Type'} (l : list A) (m : list A) : term47 A l m.
Proof. exact (@lem1112012 A l m). Qed.
Lemma lem1112014 {A : Type'} (l : list A) (m : list A) : (term47 A l m) = (term48 A l m).
Proof. exact (eq_refl (term47 A l m)). Qed.
Lemma lem1112015 {A : Type'} (l : list A) (m : list A) : term48 A l m.
Proof. exact (EQ_MP (@lem1112014 A l m) (@lem1112013 A l m)). Qed.
Lemma lem1112016 {A : Type'} (l : list A) (m : list A) (n : list A) : term49 A l m n.
Proof. exact (@lem1112015 A l m n). Qed.
Lemma lem1112017 {A : Type'} (l : list A) (m : list A) (n : list A) : (term49 A l m n) = ((term50 A l m n) = (term51 A l m n)).
Proof. exact (eq_refl (term49 A l m n)). Qed.
Lemma lem1112024 {A : Type'} : term52 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1112025 {A : Type'} (h : A) : term53 A h.
Proof. exact (@lem1112024 A h). Qed.
Lemma lem1112026 {A : Type'} (h : A) : (term53 A h) = (term54 A h).
Proof. exact (eq_refl (term53 A h)). Qed.
Lemma lem1112027 {A : Type'} (h : A) : term54 A h.
Proof. exact (EQ_MP (@lem1112026 A h) (@lem1112025 A h)). Qed.
Lemma lem1112028 {A : Type'} (h : A) (t : list A) : term55 A h t.
Proof. exact (@lem1112027 A h t). Qed.
Lemma lem1112029 {A : Type'} (h : A) (t : list A) : (term55 A h t) = (term56 A h t).
Proof. exact (eq_refl (term55 A h t)). Qed.
Lemma lem1112030 {A : Type'} (h : A) (t : list A) : term56 A h t.
Proof. exact (EQ_MP (@lem1112029 A h t) (@lem1112028 A h t)). Qed.
Lemma lem1112031 {A : Type'} (h : A) (t : list A) (l : list A) : term57 A h t l.
Proof. exact (@lem1112030 A h t l). Qed.
Lemma lem1112032 {A : Type'} (h : A) (t : list A) (l : list A) : (term57 A h t l) = ((term58 A h t l) = (term59 A h t l)).
Proof. exact (eq_refl (term57 A h t l)). Qed.
Lemma lem1112038 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : term60 A t m.
Proof. exact (@lem1111942 A t h1 m). Qed.
Lemma lem1112039 {A : Type'} (m : list A) (t : list A) : (term60 A t m) = ((term61 A t m) = (term62 A m t)).
Proof. exact (eq_refl (term60 A t m)). Qed.
Lemma lem1112048 {A : Type'} (h : A) (t : list A) (l : list A) : (term58 A h t l) = (term59 A h t l).
Proof. exact (EQ_MP (@lem1112032 A h t l) (@lem1112031 A h t l)). Qed.
Lemma lem1112049 {A : Type'} (h : A) (t : list A) (l : list A) : (term58 A h t l) = (term59 A h t l).
Proof. exact (@lem1112048 A h t l). Qed.
Lemma lem1112050 {A : Type'} (h : A) (t : list A) (m : list A) : (term58 A h t m) = (term59 A h t m).
Proof. exact (@lem1112049 A h t m). Qed.
Lemma lem1112051 {A : Type'} : (@List.rev A) = (@List.rev A).
Proof. exact (eq_refl (@List.rev A)). Qed.
Lemma lem1112052 {A : Type'} (h : A) (t : list A) (m : list A) : (term63 A h t m) = (term64 A h t m).
Proof. exact (MK_COMB (@lem1112051 A) (@lem1112050 A h t m)). Qed.
Lemma lem1112054 {A : Type'} (l : list A) (x : A) : (term65 A x l) = (term66 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1112055 {A : Type'} (l : list A) (x : A) : (term65 A x l) = (term66 A l x).
Proof. exact (@lem1112054 A l x). Qed.
Lemma lem1112056 {A : Type'} (t : list A) (m : list A) (h : A) : (term64 A h t m) = (term67 A t m h).
Proof. exact (@lem1112055 A (@List.app A t m) h). Qed.
Lemma lem1112058 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : (term61 A t m) = (term62 A m t).
Proof. exact (EQ_MP (@lem1112039 A m t) (@lem1112038 A m t h1)). Qed.
Lemma lem1112059 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : (term61 A t m) = (term62 A m t).
Proof. exact (@lem1112058 A m t h1). Qed.
Lemma lem1112060 {A : Type'} : (@List.app A) = (@List.app A).
Proof. exact (eq_refl (@List.app A)). Qed.
Lemma lem1112061 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : (term68 A t m) = (term69 A m t).
Proof. exact (MK_COMB (@lem1112060 A) (@lem1112059 A m t h1)). Qed.
Lemma lem1112062 {A : Type'} (h : A) : (@cons A h (@nil A)) = (@cons A h (@nil A)).
Proof. exact (eq_refl (@cons A h (@nil A))). Qed.
Lemma lem1112063 {A : Type'} (m : list A) (h : A) (t : list A) (h1 : term8 A t) : (term67 A t m h) = (term70 A m t h).
Proof. exact (MK_COMB (@lem1112061 A m t h1) (@lem1112062 A h)). Qed.
Lemma lem1112064 {A : Type'} (m : list A) (h : A) (t : list A) (h1 : term8 A t) : (term64 A h t m) = (term70 A m t h).
Proof. exact (TRANS (@lem1112056 A t m h) (@lem1112063 A m h t h1)). Qed.
Lemma lem1112065 {A : Type'} (m : list A) (h : A) (t : list A) (h1 : term8 A t) : (term63 A h t m) = (term70 A m t h).
Proof. exact (TRANS (@lem1112052 A h t m) (@lem1112064 A m h t h1)). Qed.
Lemma lem1112066 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1112067 {A : Type'} (m : list A) (h : A) (t : list A) (h1 : term8 A t) : (term71 A h t m) = (term72 A m t h).
Proof. exact (MK_COMB (@lem1112066 A) (@lem1112065 A m h t h1)). Qed.
Lemma lem1112069 {A : Type'} (l : list A) (x : A) : (term65 A x l) = (term66 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1112070 {A : Type'} (l : list A) (x : A) : (term65 A x l) = (term66 A l x).
Proof. exact (@lem1112069 A l x). Qed.
Lemma lem1112071 {A : Type'} (t : list A) (h : A) : (term65 A h t) = (term66 A t h).
Proof. exact (@lem1112070 A t h). Qed.
Lemma lem1112072 {A : Type'} (m : list A) : (term37 A m) = (term37 A m).
Proof. exact (eq_refl (term37 A m)). Qed.
Lemma lem1112073 {A : Type'} (m : list A) (t : list A) (h : A) : (term73 A m h t) = (term74 A m t h).
Proof. exact (MK_COMB (@lem1112072 A m) (@lem1112071 A t h)). Qed.
Lemma lem1112075 {A : Type'} (l : list A) (m : list A) (n : list A) : (term50 A l m n) = (term51 A l m n).
Proof. exact (EQ_MP (@lem1112017 A l m n) (@lem1112016 A l m n)). Qed.
Lemma lem1112076 {A : Type'} (l : list A) (m : list A) (n : list A) : (term50 A l m n) = (term51 A l m n).
Proof. exact (@lem1112075 A l m n). Qed.
Lemma lem1112077 {A : Type'} (m : list A) (t : list A) (h : A) : (term74 A m t h) = (term70 A m t h).
Proof. exact (@lem1112076 A (@List.rev A m) (@List.rev A t) (@cons A h (@nil A))). Qed.
Lemma lem1112078 {A : Type'} (m : list A) (t : list A) (h : A) : (term73 A m h t) = (term70 A m t h).
Proof. exact (TRANS (@lem1112073 A m t h) (@lem1112077 A m t h)). Qed.
Lemma lem1112079 {A : Type'} (m : list A) (h : A) (t : list A) (h1 : term8 A t) : ((term63 A h t m) = (term73 A m h t)) = ((term70 A m t h) = (term70 A m t h)).
Proof. exact (MK_COMB (@lem1112067 A m h t h1) (@lem1112078 A m t h)). Qed.
Lemma lem1112081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1112082 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1112081 (list A) x). Qed.
Lemma lem1112083 {A : Type'} (m : list A) (t : list A) (h : A) : ((term70 A m t h) = (term70 A m t h)) = True.
Proof. exact (@lem1112082 A (term70 A m t h)). Qed.
Lemma lem1112084 {A : Type'} (m : list A) (h : A) (t : list A) (h1 : term8 A t) : ((term63 A h t m) = (term73 A m h t)) = True.
Proof. exact (TRANS (@lem1112079 A m h t h1) (@lem1112083 A m t h)). Qed.
Lemma lem1112085 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term75 A h t) = (term41 A).
Proof. exact (fun_ext (fun m : list A => @lem1112084 A m h t h1)). Qed.
Lemma lem1112086 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112087 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term12 A h t) = (term42 A).
Proof. exact (MK_COMB (@lem1112086 A) (@lem1112085 A h t h1)). Qed.
Lemma lem1112089 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1112090 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (@lem1112089 (list A) t). Qed.
Lemma lem1112091 {A : Type'} : (term42 A) = True.
Proof. exact (@lem1112090 A True). Qed.
Lemma lem1112092 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term12 A h t) = True.
Proof. exact (TRANS (@lem1112087 A h t h1) (@lem1112091 A)). Qed.
Lemma lem1112093 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : True = (term12 A h t).
Proof. exact (SYM (@lem1112092 A h t h1)). Qed.
Lemma lem1112094 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : term12 A h t.
Proof. exact (EQ_MP (@lem1112093 A h t h1) (@lem0)). Qed.
Lemma lem1112095 {A : Type'} (h : A) (t : list A) : term14 A h t.
Proof. exact (fun h0 : term8 A t => @lem1112094 A h t h0). Qed.
Lemma lem1112100 {A : Type'} (h : A) : term18 A h.
Proof. exact (fun t : list A => @lem1112095 A h t). Qed.
Lemma lem1112105 {A : Type'} : term22 A.
Proof. exact (fun h : A => @lem1112100 A h). Qed.
Lemma lem1112106 {A : Type'} : term24 A.
Proof. exact (conj (@lem1112009 A) (@lem1112105 A)). Qed.
Lemma lem1112107 {A : Type'} : term29 A.
Proof. exact (@lem1111941 A (@lem1112106 A)). Qed.
