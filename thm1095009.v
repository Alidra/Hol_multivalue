Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1095009_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1094903 {A : Type'} (TL' : type1138 A) (h1 : term0 A TL') : term0 A TL'.
Proof. exact (h1). Qed.
Lemma lem1094904 {A : Type'} (h : A) (TL' : type1138 A) (h1 : term0 A TL') : term1 A TL' h.
Proof. exact (@lem1094903 A TL' h1 h). Qed.
Lemma lem1094905 {A : Type'} (TL' : type1138 A) (h : A) : (term1 A TL' h) = (term2 A TL' h).
Proof. exact (eq_refl (term1 A TL' h)). Qed.
Lemma lem1094906 {A : Type'} (h : A) (TL' : type1138 A) (h1 : term0 A TL') : term2 A TL' h.
Proof. exact (EQ_MP (@lem1094905 A TL' h) (@lem1094904 A h TL' h1)). Qed.
Lemma lem1094907 {A : Type'} (h : A) (t : list A) (TL' : type1138 A) (h1 : term0 A TL') : term3 A TL' h t.
Proof. exact (@lem1094906 A h TL' h1 t). Qed.
Lemma lem1094908 {A : Type'} (TL' : type1138 A) (h : A) (t : list A) : (term3 A TL' h t) = ((term4 A TL' h t) = t).
Proof. exact (eq_refl (term3 A TL' h t)). Qed.
Lemma lem1094909 {A : Type'} (h : A) (t : list A) (TL' : type1138 A) (h1 : term0 A TL') : (term4 A TL' h t) = t.
Proof. exact (EQ_MP (@lem1094908 A TL' h t) (@lem1094907 A h t TL' h1)). Qed.
Lemma lem1094910 {A : Type'} (h : A) (TL' : type1138 A) (h1 : term0 A TL') : term2 A TL' h.
Proof. exact (fun t : list A => @lem1094909 A h t TL' h1). Qed.
Lemma lem1094911 {A : Type'} (TL' : type1138 A) (h1 : term0 A TL') : term0 A TL'.
Proof. exact (fun h : A => @lem1094910 A h TL' h1). Qed.
Lemma lem1094912 {A : Type'} (TL' : type1138 A) (h1 : term0 A TL') : term0 A TL'.
Proof. exact (h1). Qed.
Lemma lem1094913 {A : Type'} (TL' : type1138 A) : (term0 A TL') = (term0 A TL').
Proof. exact (prop_ext (fun h1 : term0 A TL' => @lem1094911 A TL' h1) (fun h1 : term0 A TL' => @lem1094912 A TL' h1)). Qed.
Lemma lem1094914 {A : Type'} (TL' : type1138 A) (h1 : term0 A TL') : term0 A TL'.
Proof. exact (EQ_MP (@lem1094913 A TL') (@lem1094912 A TL' h1)). Qed.
Lemma lem1094915 {A Z : Type'} (NIL' : Z) : term5 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1094916 {A Z : Type'} (NIL' : Z) : (term5 A Z NIL') = (term6 A Z NIL').
Proof. exact (eq_refl (term5 A Z NIL')). Qed.
Lemma lem1094917 {A Z : Type'} (NIL' : Z) : term6 A Z NIL'.
Proof. exact (EQ_MP (@lem1094916 A Z NIL') (@lem1094915 A Z NIL')). Qed.
Lemma lem1094918 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term7 A Z NIL' CONS'.
Proof. exact (@lem1094917 A Z NIL' CONS'). Qed.
Lemma lem1094919 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term7 A Z NIL' CONS') = (term8 A Z NIL' CONS').
Proof. exact (eq_refl (term7 A Z NIL' CONS')). Qed.
Lemma lem1094920 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term8 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1094919 A Z NIL' CONS') (@lem1094918 A Z NIL' CONS')). Qed.
Lemma lem1094921 {A : Type'} (NIL' : list A) (CONS' : type1391 A) : term9 A NIL' CONS'.
Proof. exact (@lem1094920 A (list A) NIL' CONS'). Qed.
Lemma lem1094922 {A : Type'} (NIL' : list A) : term10 A NIL'.
Proof. exact (@lem1094921 A NIL' (term11 A)). Qed.
Lemma lem1094923 {A : Type'} (a0 : A) : (term12 A a0) = (term13 A).
Proof. exact (eq_refl (term12 A a0)). Qed.
Lemma lem1094924 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1094925 {A : Type'} (a0 : A) (a1 : list A) : (term14 A a0 a1) = (term15 A a1).
Proof. exact (MK_COMB (@lem1094923 A a0) (@lem1094924 A a1)). Qed.
Lemma lem1094926 {A : Type'} (a1 : list A) : (term15 A a1) = (term16 A a1).
Proof. exact (eq_refl (term15 A a1)). Qed.
Lemma lem1094927 {A : Type'} (a0 : A) (a1 : list A) : (term14 A a0 a1) = (term16 A a1).
Proof. exact (TRANS (@lem1094925 A a0 a1) (@lem1094926 A a1)). Qed.
Lemma lem1094928 {A : Type'} (fn : type1138 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1094929 {A : Type'} (a0 : A) (fn : type1138 A) (a1 : list A) : (term17 A a0 fn a1) = (term18 A fn a1).
Proof. exact (MK_COMB (@lem1094927 A a0 a1) (@lem1094928 A fn a1)). Qed.
Lemma lem1094930 {A : Type'} (fn : type1138 A) (a1 : list A) : (term18 A fn a1) = a1.
Proof. exact (eq_refl (term18 A fn a1)). Qed.
Lemma lem1094931 {A : Type'} (a0 : A) (fn : type1138 A) (a1 : list A) : (term17 A a0 fn a1) = a1.
Proof. exact (TRANS (@lem1094929 A a0 fn a1) (@lem1094930 A fn a1)). Qed.
Lemma lem1094932 {A : Type'} (fn : type1138 A) (a0 : A) (a1 : list A) : (term19 A fn a0 a1) = (term19 A fn a0 a1).
Proof. exact (eq_refl (term19 A fn a0 a1)). Qed.
Lemma lem1094933 {A : Type'} (fn : type1138 A) (a0 : A) (a1 : list A) : ((term4 A fn a0 a1) = (term17 A a0 fn a1)) = ((term4 A fn a0 a1) = a1).
Proof. exact (MK_COMB (@lem1094932 A fn a0 a1) (@lem1094931 A a0 fn a1)). Qed.
Lemma lem1094934 {A : Type'} (fn : type1138 A) (a0 : A) : (term20 A a0 fn) = (term21 A fn a0).
Proof. exact (fun_ext (fun a1 : list A => @lem1094933 A fn a0 a1)). Qed.
Lemma lem1094935 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1094936 {A : Type'} (fn : type1138 A) (a0 : A) : (term22 A a0 fn) = (term2 A fn a0).
Proof. exact (MK_COMB (@lem1094935 A) (@lem1094934 A fn a0)). Qed.
Lemma lem1094937 {A : Type'} (fn : type1138 A) : (term23 A fn) = (term24 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1094936 A fn a0)). Qed.
Lemma lem1094938 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1094939 {A : Type'} (fn : type1138 A) : (term25 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1094938 A) (@lem1094937 A fn)). Qed.
Lemma lem1094940 {A : Type'} (fn : type1138 A) (NIL' : list A) : (term26 A fn NIL') = (term26 A fn NIL').
Proof. exact (eq_refl (term26 A fn NIL')). Qed.
Lemma lem1094941 {A : Type'} (NIL' : list A) (fn : type1138 A) : (term27 A NIL' fn) = (term28 A NIL' fn).
Proof. exact (MK_COMB (@lem1094940 A fn NIL') (@lem1094939 A fn)). Qed.
Lemma lem1094942 {A : Type'} (NIL' : list A) : (term29 A NIL') = (term30 A NIL').
Proof. exact (fun_ext (fun fn : type1138 A => @lem1094941 A NIL' fn)). Qed.
Lemma lem1094943 {A : Type'} : (@ex ((list A) -> list A)) = (@ex ((list A) -> list A)).
Proof. exact (eq_refl (@ex ((list A) -> list A))). Qed.
Lemma lem1094944 {A : Type'} (NIL' : list A) : (term10 A NIL') = (term31 A NIL').
Proof. exact (MK_COMB (@lem1094943 A) (@lem1094942 A NIL')). Qed.
Lemma lem1094945 {A : Type'} (NIL' : list A) : term31 A NIL'.
Proof. exact (EQ_MP (@lem1094944 A NIL') (@lem1094922 A NIL')). Qed.
Lemma lem1094946 {A : Type'} (NIL' : list A) (TL' : type1138 A) (h1 : term28 A NIL' TL') : term28 A NIL' TL'.
Proof. exact (h1). Qed.
Lemma lem1094947 {A : Type'} (NIL' : list A) (TL' : type1138 A) (h1 : term28 A NIL' TL') : term0 A TL'.
Proof. exact (proj2 (@lem1094946 A NIL' TL' h1)). Qed.
Lemma lem1094949 {A : Type'} (NIL' : list A) (TL' : type1138 A) (h1 : term28 A NIL' TL') : term32 A.
Proof. exact (ex_intro (term33 A) TL' (@lem1094947 A NIL' TL' h1)). Qed.
Lemma lem1094950 {A : Type'} (NIL' : list A) (h1 : term31 A NIL') : term31 A NIL'.
Proof. exact (h1). Qed.
Lemma lem1094951 {A : Type'} (NIL' : list A) (h1 : term31 A NIL') : term32 A.
Proof. exact (ex_elim (@lem1094950 A NIL' h1) (fun TL' : type1138 A => fun h0 : term30 A NIL' TL' => @lem1094949 A NIL' TL' h0)). Qed.
Lemma lem1094952 {A : Type'} (NIL' : list A) : (term31 A NIL') = (term32 A).
Proof. exact (prop_ext (fun h1 : term31 A NIL' => @lem1094951 A NIL' h1) (fun h1 : term32 A => @lem1094945 A NIL')). Qed.
Lemma lem1094953 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1094952 A (@el (list A))) (@lem1094945 A (@el (list A)))). Qed.
Lemma lem1094954 {A : Type'} (TL' : type1138 A) (h1 : term0 A TL') : term32 A.
Proof. exact (ex_intro (term33 A) TL' (@lem1094914 A TL' h1)). Qed.
Lemma lem1094955 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1094956 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1094955 A h1) (fun TL' : type1138 A => fun h0 : term33 A TL' => @lem1094954 A TL' h0)). Qed.
Lemma lem1094957 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1094956 A h1) (fun h1 : term32 A => @lem1094953 A)). Qed.
Lemma lem1094958 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1094957 A) (@lem1094953 A)). Qed.
Lemma lem1094961 {A : Type'} (TL' : type1138 A) (h1 : term0 A TL') : term0 A TL'.
Proof. exact (h1). Qed.
Lemma lem1094962 {A : Type'} (TL' : type1138 A) (h1 : term0 A TL') : term32 A.
Proof. exact (ex_intro (term33 A) TL' (@lem1094961 A TL' h1)). Qed.
Lemma lem1094963 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1094964 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1094963 A h1) (fun TL' : type1138 A => fun h0 : term33 A TL' => @lem1094962 A TL' h0)). Qed.
Lemma lem1094965 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1094964 A h1) (fun h1 : term32 A => @lem1094958 A)). Qed.
Lemma lem1094966 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1094965 A) (@lem1094958 A)). Qed.
Lemma lem1094967 {A : Type'} : term34 A.
Proof. exact (fun _17931 : prod nat nat => @lem1094966 A). Qed.
Lemma lem1094968 {A B : Type'} (P : type1413 A B) : term35 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1094969 {A B : Type'} (P : type1413 A B) : (term35 A B P) = ((term36 A B P) = (term37 A B P)).
Proof. exact (eq_refl (term35 A B P)). Qed.
Lemma lem1094972 {A B : Type'} (P : type1413 A B) : (term36 A B P) = (term37 A B P).
Proof. exact (EQ_MP (@lem1094969 A B P) (@lem1094968 A B P)). Qed.
Lemma lem1094973 {A : Type'} (P : type1315 A) : (term38 A P) = (term39 A P).
Proof. exact (@lem1094972 (prod nat nat) (type1138 A) P). Qed.
Lemma lem1094974 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (@lem1094973 A (term42 A)). Qed.
Lemma lem1094975 {A : Type'} (_17931 : prod nat nat) : (term43 A _17931) = (term33 A).
Proof. exact (eq_refl (term43 A _17931)). Qed.
Lemma lem1094976 {A : Type'} (TL' : type1138 A) : TL' = TL'.
Proof. exact (eq_refl TL'). Qed.
Lemma lem1094977 {A : Type'} (_17931 : prod nat nat) (TL' : type1138 A) : (term44 A _17931 TL') = (term45 A TL').
Proof. exact (MK_COMB (@lem1094975 A _17931) (@lem1094976 A TL')). Qed.
Lemma lem1094978 {A : Type'} (TL' : type1138 A) : (term45 A TL') = (term0 A TL').
Proof. exact (eq_refl (term45 A TL')). Qed.
Lemma lem1094979 {A : Type'} (_17931 : prod nat nat) (TL' : type1138 A) : (term44 A _17931 TL') = (term0 A TL').
Proof. exact (TRANS (@lem1094977 A _17931 TL') (@lem1094978 A TL')). Qed.
Lemma lem1094980 {A : Type'} (_17931 : prod nat nat) : (term46 A _17931) = (term33 A).
Proof. exact (fun_ext (fun TL' : type1138 A => @lem1094979 A _17931 TL')). Qed.
Lemma lem1094981 {A : Type'} : (@ex ((list A) -> list A)) = (@ex ((list A) -> list A)).
Proof. exact (eq_refl (@ex ((list A) -> list A))). Qed.
Lemma lem1094982 {A : Type'} (_17931 : prod nat nat) : (term47 A _17931) = (term32 A).
Proof. exact (MK_COMB (@lem1094981 A) (@lem1094980 A _17931)). Qed.
Lemma lem1094983 {A : Type'} : (term48 A) = (term49 A).
Proof. exact (fun_ext (fun _17931 : prod nat nat => @lem1094982 A _17931)). Qed.
Lemma lem1094984 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem1094985 {A : Type'} : (term40 A) = (term34 A).
Proof. exact (MK_COMB (@lem1094984) (@lem1094983 A)). Qed.
Lemma lem1094986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1094987 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (MK_COMB (@lem1094986) (@lem1094985 A)). Qed.
Lemma lem1094988 {A : Type'} (_17931 : prod nat nat) : (term43 A _17931) = (term33 A).
Proof. exact (eq_refl (term43 A _17931)). Qed.
Lemma lem1094989 {A : Type'} (TL' : type1320 A) (_17931 : prod nat nat) : (TL' _17931) = (TL' _17931).
Proof. exact (eq_refl (TL' _17931)). Qed.
Lemma lem1094990 {A : Type'} (TL' : type1320 A) (_17931 : prod nat nat) : (term52 A TL' _17931) = (term53 A TL' _17931).
Proof. exact (MK_COMB (@lem1094988 A _17931) (@lem1094989 A TL' _17931)). Qed.
Lemma lem1094991 {A : Type'} (TL' : type1320 A) (_17931 : prod nat nat) : (term53 A TL' _17931) = (term54 A TL' _17931).
Proof. exact (eq_refl (term53 A TL' _17931)). Qed.
Lemma lem1094992 {A : Type'} (TL' : type1320 A) (_17931 : prod nat nat) : (term52 A TL' _17931) = (term54 A TL' _17931).
Proof. exact (TRANS (@lem1094990 A TL' _17931) (@lem1094991 A TL' _17931)). Qed.
Lemma lem1094993 {A : Type'} (TL' : type1320 A) : (term55 A TL') = (term56 A TL').
Proof. exact (fun_ext (fun _17931 : prod nat nat => @lem1094992 A TL' _17931)). Qed.
Lemma lem1094994 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem1094995 {A : Type'} (TL' : type1320 A) : (term57 A TL') = (term58 A TL').
Proof. exact (MK_COMB (@lem1094994) (@lem1094993 A TL')). Qed.
Lemma lem1094996 {A : Type'} : (term59 A) = (term60 A).
Proof. exact (fun_ext (fun TL' : type1320 A => @lem1094995 A TL')). Qed.
Lemma lem1094997 {A : Type'} : (@ex ((prod nat nat) -> (list A) -> list A)) = (@ex ((prod nat nat) -> (list A) -> list A)).
Proof. exact (eq_refl (@ex ((prod nat nat) -> (list A) -> list A))). Qed.
Lemma lem1094998 {A : Type'} : (term41 A) = (term61 A).
Proof. exact (MK_COMB (@lem1094997 A) (@lem1094996 A)). Qed.
Lemma lem1094999 {A : Type'} : ((term40 A) = (term41 A)) = ((term34 A) = (term61 A)).
Proof. exact (MK_COMB (@lem1094987 A) (@lem1094998 A)). Qed.
Lemma lem1095000 {A : Type'} : (term34 A) = (term61 A).
Proof. exact (EQ_MP (@lem1094999 A) (@lem1094974 A)). Qed.
Lemma lem1095001 {A : Type'} : term61 A.
Proof. exact (EQ_MP (@lem1095000 A) (@lem1094967 A)). Qed.
Lemma lem1095003 {A : Type'} : (@ex A) = (term62 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1095004 {A : Type'} : (@ex ((prod nat nat) -> (list A) -> list A)) = (term63 A).
Proof. exact (@lem1095003 (type1320 A)). Qed.
Lemma lem1095005 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem1095006 {A : Type'} : (term61 A) = (term64 A).
Proof. exact (MK_COMB (@lem1095004 A) (@lem1095005 A)). Qed.
Lemma lem1095007 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (eq_refl (term64 A)). Qed.
Lemma lem1095008 {A : Type'} : (term61 A) = (term65 A).
Proof. exact (TRANS (@lem1095006 A) (@lem1095007 A)). Qed.
Lemma lem1095009 {A : Type'} : term65 A.
Proof. exact (EQ_MP (@lem1095008 A) (@lem1095001 A)). Qed.
