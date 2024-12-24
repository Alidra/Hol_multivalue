Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1104037_term_abbrevs.
Require Import thm1103592_spec.
Require Import thm1103966_spec.
Lemma lem1103967 {_25409 _25416 : Type'} : (term0 _25409 _25416) = (term1 _25409 _25416).
Proof. exact (eq_refl (term0 _25409 _25416)). Qed.
Lemma lem1103968 {_25409 _25416 : Type'} : term1 _25409 _25416.
Proof. exact (EQ_MP (@lem1103967 _25409 _25416) (@lem1103592 _25409 _25416)). Qed.
Lemma lem1103969 {_25409 _25416 : Type'} : term2 _25409 _25416.
Proof. exact (@lem1103968 _25409 _25416 term3). Qed.
Lemma lem1103970 {_25409 _25416 : Type'} : (term2 _25409 _25416) = (term4 _25409 _25416).
Proof. exact (eq_refl (term2 _25409 _25416)). Qed.
Lemma lem1103971 {_25409 _25416 : Type'} : term4 _25409 _25416.
Proof. exact (EQ_MP (@lem1103970 _25409 _25416) (@lem1103969 _25409 _25416)). Qed.
Lemma lem1103972 {_25409 _25416 : Type'} (h1 : (@ALL2 _25409 _25416) = (term5 _25409 _25416)) : (@ALL2 _25409 _25416) = (term5 _25409 _25416).
Proof. exact (h1). Qed.
Lemma lem1103973 {_25409 _25416 : Type'} (h1 : (@ALL2 _25409 _25416) = (term5 _25409 _25416)) : (term5 _25409 _25416) = (@ALL2 _25409 _25416).
Proof. exact (SYM (@lem1103972 _25409 _25416 h1)). Qed.
Lemma lem1103974 {_25409 _25416 : Type'} (h1 : (term5 _25409 _25416) = (@ALL2 _25409 _25416)) : (term5 _25409 _25416) = (@ALL2 _25409 _25416).
Proof. exact (h1). Qed.
Lemma lem1103975 {_25409 _25416 : Type'} (h1 : (term5 _25409 _25416) = (@ALL2 _25409 _25416)) : (@ALL2 _25409 _25416) = (term5 _25409 _25416).
Proof. exact (SYM (@lem1103974 _25409 _25416 h1)). Qed.
Lemma lem1103976 {_25409 _25416 : Type'} : ((@ALL2 _25409 _25416) = (term5 _25409 _25416)) = ((term5 _25409 _25416) = (@ALL2 _25409 _25416)).
Proof. exact (prop_ext (fun h1 : (@ALL2 _25409 _25416) = (term5 _25409 _25416) => @lem1103973 _25409 _25416 h1) (fun h1 : (term5 _25409 _25416) = (@ALL2 _25409 _25416) => @lem1103975 _25409 _25416 h1)). Qed.
Lemma lem1103979 {_25409 _25416 : Type'} : (term5 _25409 _25416) = (@ALL2 _25409 _25416).
Proof. exact (EQ_MP (@lem1103976 _25409 _25416) (@lem1103966 _25409 _25416)). Qed.
Lemma lem1103980 {_25409 _25416 : Type'} : (term5 _25409 _25416) = (@ALL2 _25409 _25416).
Proof. exact (@lem1103979 _25409 _25416). Qed.
Lemma lem1103981 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1103982 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : (term6 _25409 _25416 P) = (@ALL2 _25409 _25416 P).
Proof. exact (MK_COMB (@lem1103980 _25409 _25416) (@lem1103981 _25409 _25416 P)). Qed.
Lemma lem1103983 {_25409 : Type'} : (@nil _25409) = (@nil _25409).
Proof. exact (eq_refl (@nil _25409)). Qed.
Lemma lem1103984 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : (term7 _25409 _25416 P) = (@ALL2 _25409 _25416 P (@nil _25409)).
Proof. exact (MK_COMB (@lem1103982 _25409 _25416 P) (@lem1103983 _25409)). Qed.
Lemma lem1103985 {_25416 : Type'} (l2 : list _25416) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1103986 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : (term8 _25409 _25416 P l2) = (@ALL2 _25409 _25416 P (@nil _25409) l2).
Proof. exact (MK_COMB (@lem1103984 _25409 _25416 P) (@lem1103985 _25416 l2)). Qed.
Lemma lem1103987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1103988 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : (term9 _25409 _25416 P l2) = (term10 _25409 _25416 P l2).
Proof. exact (MK_COMB (@lem1103987) (@lem1103986 _25409 _25416 P l2)). Qed.
Lemma lem1103989 {_25416 : Type'} (l2 : list _25416) : (l2 = (@nil _25416)) = (l2 = (@nil _25416)).
Proof. exact (eq_refl (l2 = (@nil _25416))). Qed.
Lemma lem1103990 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : ((term8 _25409 _25416 P l2) = (l2 = (@nil _25416))) = ((@ALL2 _25409 _25416 P (@nil _25409) l2) = (l2 = (@nil _25416))).
Proof. exact (MK_COMB (@lem1103988 _25409 _25416 P l2) (@lem1103989 _25416 l2)). Qed.
Lemma lem1103991 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : (term11 _25409 _25416 P) = (term12 _25409 _25416 P).
Proof. exact (fun_ext (fun l2 : list _25416 => @lem1103990 _25409 _25416 P l2)). Qed.
Lemma lem1103992 {_25416 : Type'} : (@all (list _25416)) = (@all (list _25416)).
Proof. exact (eq_refl (@all (list _25416))). Qed.
Lemma lem1103993 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : (term13 _25409 _25416 P) = (term14 _25409 _25416 P).
Proof. exact (MK_COMB (@lem1103992 _25416) (@lem1103991 _25409 _25416 P)). Qed.
Lemma lem1103994 {_25409 _25416 : Type'} : (term15 _25409 _25416) = (term16 _25409 _25416).
Proof. exact (fun_ext (fun P : type1413 _25409 _25416 => @lem1103993 _25409 _25416 P)). Qed.
Lemma lem1103995 {_25409 _25416 : Type'} : (@all (_25409 -> _25416 -> Prop)) = (@all (_25409 -> _25416 -> Prop)).
Proof. exact (eq_refl (@all (_25409 -> _25416 -> Prop))). Qed.
Lemma lem1103996 {_25409 _25416 : Type'} : (term17 _25409 _25416) = (term18 _25409 _25416).
Proof. exact (MK_COMB (@lem1103995 _25409 _25416) (@lem1103994 _25409 _25416)). Qed.
Lemma lem1103997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1103998 {_25409 _25416 : Type'} : (term19 _25409 _25416) = (term20 _25409 _25416).
Proof. exact (MK_COMB (@lem1103997) (@lem1103996 _25409 _25416)). Qed.
Lemma lem1104000 {_25409 _25416 : Type'} : (term5 _25409 _25416) = (@ALL2 _25409 _25416).
Proof. exact (EQ_MP (@lem1103976 _25409 _25416) (@lem1103966 _25409 _25416)). Qed.
Lemma lem1104001 {_25409 _25416 : Type'} : (term5 _25409 _25416) = (@ALL2 _25409 _25416).
Proof. exact (@lem1104000 _25409 _25416). Qed.
Lemma lem1104002 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1104003 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : (term6 _25409 _25416 P) = (@ALL2 _25409 _25416 P).
Proof. exact (MK_COMB (@lem1104001 _25409 _25416) (@lem1104002 _25409 _25416 P)). Qed.
Lemma lem1104004 {_25409 : Type'} (h1' : _25409) (t1 : list _25409) : (@cons _25409 h1' t1) = (@cons _25409 h1' t1).
Proof. exact (eq_refl (@cons _25409 h1' t1)). Qed.
Lemma lem1104005 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (h1' : _25409) (t1 : list _25409) : (term21 _25409 _25416 P h1' t1) = (term22 _25409 _25416 P h1' t1).
Proof. exact (MK_COMB (@lem1104003 _25409 _25416 P) (@lem1104004 _25409 h1' t1)). Qed.
Lemma lem1104006 {_25416 : Type'} (l2 : list _25416) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1104007 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (h1' : _25409) (t1 : list _25409) (l2 : list _25416) : (term23 _25409 _25416 P h1' t1 l2) = (term24 _25409 _25416 P h1' t1 l2).
Proof. exact (MK_COMB (@lem1104005 _25409 _25416 P h1' t1) (@lem1104006 _25416 l2)). Qed.
Lemma lem1104008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1104009 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (h1' : _25409) (t1 : list _25409) (l2 : list _25416) : (term25 _25409 _25416 P h1' t1 l2) = (term26 _25409 _25416 P h1' t1 l2).
Proof. exact (MK_COMB (@lem1104008) (@lem1104007 _25409 _25416 P h1' t1 l2)). Qed.
Lemma lem1104011 {_25409 _25416 : Type'} : (term5 _25409 _25416) = (@ALL2 _25409 _25416).
Proof. exact (EQ_MP (@lem1103976 _25409 _25416) (@lem1103966 _25409 _25416)). Qed.
Lemma lem1104012 {_25409 _25416 : Type'} : (term5 _25409 _25416) = (@ALL2 _25409 _25416).
Proof. exact (@lem1104011 _25409 _25416). Qed.
Lemma lem1104013 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1104014 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : (term6 _25409 _25416 P) = (@ALL2 _25409 _25416 P).
Proof. exact (MK_COMB (@lem1104012 _25409 _25416) (@lem1104013 _25409 _25416 P)). Qed.
Lemma lem1104015 {_25409 : Type'} (t1 : list _25409) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem1104016 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (t1 : list _25409) : (term27 _25409 _25416 P t1) = (@ALL2 _25409 _25416 P t1).
Proof. exact (MK_COMB (@lem1104014 _25409 _25416 P) (@lem1104015 _25409 t1)). Qed.
Lemma lem1104017 {_25416 : Type'} (l2 : list _25416) : (@tl _25416 l2) = (@tl _25416 l2).
Proof. exact (eq_refl (@tl _25416 l2)). Qed.
Lemma lem1104018 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term28 _25409 _25416 P t1 l2) = (term29 _25409 _25416 P t1 l2).
Proof. exact (MK_COMB (@lem1104016 _25409 _25416 P t1) (@lem1104017 _25416 l2)). Qed.
Lemma lem1104019 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (h1' : _25409) (l2 : list _25416) : (term30 _25409 _25416 P h1' l2) = (term30 _25409 _25416 P h1' l2).
Proof. exact (eq_refl (term30 _25409 _25416 P h1' l2)). Qed.
Lemma lem1104020 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term31 _25409 _25416 h1' P t1 l2) = (term32 _25409 _25416 h1' P t1 l2).
Proof. exact (MK_COMB (@lem1104019 _25409 _25416 P h1' l2) (@lem1104018 _25409 _25416 P t1 l2)). Qed.
Lemma lem1104021 {_25416 : Type'} (l2 : list _25416) : (term33 _25416 l2) = (term33 _25416 l2).
Proof. exact (eq_refl (term33 _25416 l2)). Qed.
Lemma lem1104022 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term34 _25409 _25416 h1' P t1 l2) = (term35 _25409 _25416 h1' P t1 l2).
Proof. exact (MK_COMB (@lem1104021 _25416 l2) (@lem1104020 _25409 _25416 h1' P t1 l2)). Qed.
Lemma lem1104023 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : ((term23 _25409 _25416 P h1' t1 l2) = (term34 _25409 _25416 h1' P t1 l2)) = ((term24 _25409 _25416 P h1' t1 l2) = (term35 _25409 _25416 h1' P t1 l2)).
Proof. exact (MK_COMB (@lem1104009 _25409 _25416 P h1' t1 l2) (@lem1104022 _25409 _25416 h1' P t1 l2)). Qed.
Lemma lem1104024 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) : (term36 _25409 _25416 h1' P t1) = (term37 _25409 _25416 h1' P t1).
Proof. exact (fun_ext (fun l2 : list _25416 => @lem1104023 _25409 _25416 h1' P t1 l2)). Qed.
Lemma lem1104025 {_25416 : Type'} : (@all (list _25416)) = (@all (list _25416)).
Proof. exact (eq_refl (@all (list _25416))). Qed.
Lemma lem1104026 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) : (term38 _25409 _25416 h1' P t1) = (term39 _25409 _25416 h1' P t1).
Proof. exact (MK_COMB (@lem1104025 _25416) (@lem1104024 _25409 _25416 h1' P t1)). Qed.
Lemma lem1104027 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) : (term40 _25409 _25416 h1' P) = (term41 _25409 _25416 h1' P).
Proof. exact (fun_ext (fun t1 : list _25409 => @lem1104026 _25409 _25416 h1' P t1)). Qed.
Lemma lem1104028 {_25409 : Type'} : (@all (list _25409)) = (@all (list _25409)).
Proof. exact (eq_refl (@all (list _25409))). Qed.
Lemma lem1104029 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) : (term42 _25409 _25416 h1' P) = (term43 _25409 _25416 h1' P).
Proof. exact (MK_COMB (@lem1104028 _25409) (@lem1104027 _25409 _25416 h1' P)). Qed.
Lemma lem1104030 {_25409 _25416 : Type'} (h1' : _25409) : (term44 _25409 _25416 h1') = (term45 _25409 _25416 h1').
Proof. exact (fun_ext (fun P : type1413 _25409 _25416 => @lem1104029 _25409 _25416 h1' P)). Qed.
Lemma lem1104031 {_25409 _25416 : Type'} : (@all (_25409 -> _25416 -> Prop)) = (@all (_25409 -> _25416 -> Prop)).
Proof. exact (eq_refl (@all (_25409 -> _25416 -> Prop))). Qed.
Lemma lem1104032 {_25409 _25416 : Type'} (h1' : _25409) : (term46 _25409 _25416 h1') = (term47 _25409 _25416 h1').
Proof. exact (MK_COMB (@lem1104031 _25409 _25416) (@lem1104030 _25409 _25416 h1')). Qed.
Lemma lem1104033 {_25409 _25416 : Type'} : (term48 _25409 _25416) = (term49 _25409 _25416).
Proof. exact (fun_ext (fun h1' : _25409 => @lem1104032 _25409 _25416 h1')). Qed.
Lemma lem1104034 {_25409 : Type'} : (@all _25409) = (@all _25409).
Proof. exact (eq_refl (@all _25409)). Qed.
Lemma lem1104035 {_25409 _25416 : Type'} : (term50 _25409 _25416) = (term51 _25409 _25416).
Proof. exact (MK_COMB (@lem1104034 _25409) (@lem1104033 _25409 _25416)). Qed.
Lemma lem1104036 {_25409 _25416 : Type'} : (term4 _25409 _25416) = (term52 _25409 _25416).
Proof. exact (MK_COMB (@lem1103998 _25409 _25416) (@lem1104035 _25409 _25416)). Qed.
Lemma lem1104037 {_25409 _25416 : Type'} : term52 _25409 _25416.
Proof. exact (EQ_MP (@lem1104036 _25409 _25416) (@lem1103971 _25409 _25416)). Qed.
