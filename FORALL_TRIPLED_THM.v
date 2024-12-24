Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_TRIPLED_THM_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import FUN_EQ_THM_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Lemma lem55946 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term0 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem55947 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term0 _5106 _5107 P) = ((term1 _5106 _5107 P) = (term2 _5106 _5107 P)).
Proof. exact (eq_refl (term0 _5106 _5107 P)). Qed.
Lemma lem55949 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem55950 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem55951 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem55950 A B f) (@lem55949 A B f)). Qed.
Lemma lem55952 {A B : Type'} (f : A -> B) (g : A -> B) : term5 A B f g.
Proof. exact (@lem55951 A B f g). Qed.
Lemma lem55953 {A B : Type'} (f : A -> B) (g : A -> B) : (term5 A B f g) = ((f = g) = (term6 A B f g)).
Proof. exact (eq_refl (term5 A B f g)). Qed.
Lemma lem55956 {A : Type'} : (@all A) = (term7 A).
Proof. exact (@all_def A). Qed.
Lemma lem55957 {_5805 _5806 _5807 : Type'} : (@all (prod _5807 (prod _5806 _5805))) = (term8 _5805 _5806 _5807).
Proof. exact (@lem55956 (type1659 _5805 _5806 _5807)). Qed.
Lemma lem55958 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term9 _5805 _5806 _5807 P) = (term9 _5805 _5806 _5807 P).
Proof. exact (eq_refl (term9 _5805 _5806 _5807 P)). Qed.
Lemma lem55959 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term10 _5805 _5806 _5807 P) = (term11 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem55957 _5805 _5806 _5807) (@lem55958 _5805 _5806 _5807 P)). Qed.
Lemma lem55960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55961 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term12 _5805 _5806 _5807 P) = (term13 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem55960) (@lem55959 _5805 _5806 _5807 P)). Qed.
Lemma lem55962 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P).
Proof. exact (eq_refl (term14 _5805 _5806 _5807 P)). Qed.
Lemma lem55963 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term10 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = ((term11 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)).
Proof. exact (MK_COMB (@lem55961 _5805 _5806 _5807 P) (@lem55962 _5805 _5806 _5807 P)). Qed.
Lemma lem55964 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term11 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = ((term10 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)).
Proof. exact (SYM (@lem55963 _5805 _5806 _5807 P)). Qed.
Lemma lem55970 {A B : Type'} (f : A -> B) (y : A) : (term15 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55971 {_5805 _5806 _5807 : Type'} (f : type332 _5805 _5806 _5807) (y : type1227 _5805 _5806 _5807) : (term16 _5805 _5806 _5807 f y) = (f y).
Proof. exact (@lem55970 (type1227 _5805 _5806 _5807) Prop f y). Qed.
Lemma lem55972 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term17 _5805 _5806 _5807 P) = (term11 _5805 _5806 _5807 P).
Proof. exact (@lem55971 _5805 _5806 _5807 (term8 _5805 _5806 _5807) (term9 _5805 _5806 _5807 P)). Qed.
Lemma lem55973 {_5805 _5806 _5807 : Type'} (P : type1227 _5805 _5806 _5807) : (term18 _5805 _5806 _5807 P) = (P = (term19 _5805 _5806 _5807)).
Proof. exact (eq_refl (term18 _5805 _5806 _5807 P)). Qed.
Lemma lem55974 {_5805 _5806 _5807 : Type'} : (term20 _5805 _5806 _5807) = (term8 _5805 _5806 _5807).
Proof. exact (fun_ext (fun P : type1227 _5805 _5806 _5807 => @lem55973 _5805 _5806 _5807 P)). Qed.
Lemma lem55975 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term9 _5805 _5806 _5807 P) = (term9 _5805 _5806 _5807 P).
Proof. exact (eq_refl (term9 _5805 _5806 _5807 P)). Qed.
Lemma lem55976 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term17 _5805 _5806 _5807 P) = (term11 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem55974 _5805 _5806 _5807) (@lem55975 _5805 _5806 _5807 P)). Qed.
Lemma lem55977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55978 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term21 _5805 _5806 _5807 P) = (term13 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem55977) (@lem55976 _5805 _5806 _5807 P)). Qed.
Lemma lem55979 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term11 _5805 _5806 _5807 P) = ((term9 _5805 _5806 _5807 P) = (term19 _5805 _5806 _5807)).
Proof. exact (eq_refl (term11 _5805 _5806 _5807 P)). Qed.
Lemma lem55980 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term17 _5805 _5806 _5807 P) = (term11 _5805 _5806 _5807 P)) = ((term11 _5805 _5806 _5807 P) = ((term9 _5805 _5806 _5807 P) = (term19 _5805 _5806 _5807))).
Proof. exact (MK_COMB (@lem55978 _5805 _5806 _5807 P) (@lem55979 _5805 _5806 _5807 P)). Qed.
Lemma lem55981 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term11 _5805 _5806 _5807 P) = ((term9 _5805 _5806 _5807 P) = (term19 _5805 _5806 _5807)).
Proof. exact (EQ_MP (@lem55980 _5805 _5806 _5807 P) (@lem55972 _5805 _5806 _5807 P)). Qed.
Lemma lem55985 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term6 A B f g).
Proof. exact (EQ_MP (@lem55953 A B f g) (@lem55952 A B f g)). Qed.
Lemma lem55986 {_5805 _5806 _5807 : Type'} (f : type1227 _5805 _5806 _5807) (g : type1227 _5805 _5806 _5807) : (f = g) = (term22 _5805 _5806 _5807 f g).
Proof. exact (@lem55985 (type1659 _5805 _5806 _5807) Prop f g). Qed.
Lemma lem55987 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term9 _5805 _5806 _5807 P) = (term19 _5805 _5806 _5807)) = (term23 _5805 _5806 _5807 P).
Proof. exact (@lem55986 _5805 _5806 _5807 (term9 _5805 _5806 _5807 P) (term19 _5805 _5806 _5807)). Qed.
Lemma lem55993 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term2 _5106 _5107 P).
Proof. exact (EQ_MP (@lem55947 _5106 _5107 P) (@lem55946 _5106 _5107 P)). Qed.
Lemma lem55994 {_5805 _5806 _5807 : Type'} (P : type1227 _5805 _5806 _5807) : (term24 _5805 _5806 _5807 P) = (term25 _5805 _5806 _5807 P).
Proof. exact (@lem55993 (prod _5806 _5805) _5807 P). Qed.
Lemma lem55995 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term26 _5805 _5806 _5807 P) = (term27 _5805 _5806 _5807 P).
Proof. exact (@lem55994 _5805 _5806 _5807 (term28 _5805 _5806 _5807 P)). Qed.
Lemma lem55996 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : type1659 _5805 _5806 _5807) : (term29 _5805 _5806 _5807 P x) = ((term30 _5805 _5806 _5807 P x) = (term31 _5805 _5806 _5807 x)).
Proof. exact (eq_refl (term29 _5805 _5806 _5807 P x)). Qed.
Lemma lem55997 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term32 _5805 _5806 _5807 P) = (term28 _5805 _5806 _5807 P).
Proof. exact (fun_ext (fun x : type1659 _5805 _5806 _5807 => @lem55996 _5805 _5806 _5807 P x)). Qed.
Lemma lem55998 {_5805 _5806 _5807 : Type'} : (@all (prod _5807 (prod _5806 _5805))) = (@all (prod _5807 (prod _5806 _5805))).
Proof. exact (eq_refl (@all (prod _5807 (prod _5806 _5805)))). Qed.
Lemma lem55999 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term26 _5805 _5806 _5807 P) = (term23 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem55998 _5805 _5806 _5807) (@lem55997 _5805 _5806 _5807 P)). Qed.
Lemma lem56000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56001 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term33 _5805 _5806 _5807 P) = (term34 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem56000) (@lem55999 _5805 _5806 _5807 P)). Qed.
Lemma lem56002 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p2 : prod _5806 _5805) : (term35 _5805 _5806 _5807 P p1 p2) = ((term36 _5805 _5806 _5807 P p1 p2) = (term37 _5805 _5806 _5807 p1 p2)).
Proof. exact (eq_refl (term35 _5805 _5806 _5807 P p1 p2)). Qed.
Lemma lem56003 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term38 _5805 _5806 _5807 P p1) = (term39 _5805 _5806 _5807 P p1).
Proof. exact (fun_ext (fun p2 : prod _5806 _5805 => @lem56002 _5805 _5806 _5807 P p1 p2)). Qed.
Lemma lem56004 {_5805 _5806 : Type'} : (@all (prod _5806 _5805)) = (@all (prod _5806 _5805)).
Proof. exact (eq_refl (@all (prod _5806 _5805))). Qed.
Lemma lem56005 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term40 _5805 _5806 _5807 P p1) = (term41 _5805 _5806 _5807 P p1).
Proof. exact (MK_COMB (@lem56004 _5805 _5806) (@lem56003 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56006 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term42 _5805 _5806 _5807 P) = (term43 _5805 _5806 _5807 P).
Proof. exact (fun_ext (fun p1 : _5807 => @lem56005 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56007 {_5807 : Type'} : (@all _5807) = (@all _5807).
Proof. exact (eq_refl (@all _5807)). Qed.
Lemma lem56008 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term27 _5805 _5806 _5807 P) = (term44 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem56007 _5807) (@lem56006 _5805 _5806 _5807 P)). Qed.
Lemma lem56009 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term26 _5805 _5806 _5807 P) = (term27 _5805 _5806 _5807 P)) = ((term23 _5805 _5806 _5807 P) = (term44 _5805 _5806 _5807 P)).
Proof. exact (MK_COMB (@lem56001 _5805 _5806 _5807 P) (@lem56008 _5805 _5806 _5807 P)). Qed.
Lemma lem56010 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term23 _5805 _5806 _5807 P) = (term44 _5805 _5806 _5807 P).
Proof. exact (EQ_MP (@lem56009 _5805 _5806 _5807 P) (@lem55995 _5805 _5806 _5807 P)). Qed.
Lemma lem56017 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term9 _5805 _5806 _5807 P) = (term19 _5805 _5806 _5807)) = (term44 _5805 _5806 _5807 P).
Proof. exact (TRANS (@lem55987 _5805 _5806 _5807 P) (@lem56010 _5805 _5806 _5807 P)). Qed.
Lemma lem56018 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term11 _5805 _5806 _5807 P) = (term44 _5805 _5806 _5807 P).
Proof. exact (TRANS (@lem55981 _5805 _5806 _5807 P) (@lem56017 _5805 _5806 _5807 P)). Qed.
Lemma lem56024 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term2 _5106 _5107 P).
Proof. exact (EQ_MP (@lem55947 _5106 _5107 P) (@lem55946 _5106 _5107 P)). Qed.
Lemma lem56025 {_5805 _5806 : Type'} (P : type1223 _5805 _5806) : (term1 _5805 _5806 P) = (term2 _5805 _5806 P).
Proof. exact (@lem56024 _5805 _5806 P). Qed.
Lemma lem56026 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term45 _5805 _5806 _5807 P p1) = (term46 _5805 _5806 _5807 P p1).
Proof. exact (@lem56025 _5805 _5806 (term39 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56027 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p2 : prod _5806 _5805) : (term47 _5805 _5806 _5807 P p1 p2) = ((term36 _5805 _5806 _5807 P p1 p2) = (term37 _5805 _5806 _5807 p1 p2)).
Proof. exact (eq_refl (term47 _5805 _5806 _5807 P p1 p2)). Qed.
Lemma lem56028 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term48 _5805 _5806 _5807 P p1) = (term39 _5805 _5806 _5807 P p1).
Proof. exact (fun_ext (fun p2 : prod _5806 _5805 => @lem56027 _5805 _5806 _5807 P p1 p2)). Qed.
Lemma lem56029 {_5805 _5806 : Type'} : (@all (prod _5806 _5805)) = (@all (prod _5806 _5805)).
Proof. exact (eq_refl (@all (prod _5806 _5805))). Qed.
Lemma lem56030 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term45 _5805 _5806 _5807 P p1) = (term41 _5805 _5806 _5807 P p1).
Proof. exact (MK_COMB (@lem56029 _5805 _5806) (@lem56028 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56032 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term49 _5805 _5806 _5807 P p1) = (term50 _5805 _5806 _5807 P p1).
Proof. exact (MK_COMB (@lem56031) (@lem56030 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56033 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term51 _5805 _5806 _5807 P p1 p1' p2) = ((term52 _5805 _5806 _5807 P p1 p1' p2) = (term53 _5805 _5806 _5807 p1 p1' p2)).
Proof. exact (eq_refl (term51 _5805 _5806 _5807 P p1 p1' p2)). Qed.
Lemma lem56034 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) : (term54 _5805 _5806 _5807 P p1 p1') = (term55 _5805 _5806 _5807 P p1 p1').
Proof. exact (fun_ext (fun p2 : _5805 => @lem56033 _5805 _5806 _5807 P p1 p1' p2)). Qed.
Lemma lem56035 {_5805 : Type'} : (@all _5805) = (@all _5805).
Proof. exact (eq_refl (@all _5805)). Qed.
Lemma lem56036 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) : (term56 _5805 _5806 _5807 P p1 p1') = (term57 _5805 _5806 _5807 P p1 p1').
Proof. exact (MK_COMB (@lem56035 _5805) (@lem56034 _5805 _5806 _5807 P p1 p1')). Qed.
Lemma lem56037 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term58 _5805 _5806 _5807 P p1) = (term59 _5805 _5806 _5807 P p1).
Proof. exact (fun_ext (fun p1' : _5806 => @lem56036 _5805 _5806 _5807 P p1 p1')). Qed.
Lemma lem56038 {_5806 : Type'} : (@all _5806) = (@all _5806).
Proof. exact (eq_refl (@all _5806)). Qed.
Lemma lem56039 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term46 _5805 _5806 _5807 P p1) = (term60 _5805 _5806 _5807 P p1).
Proof. exact (MK_COMB (@lem56038 _5806) (@lem56037 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56040 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : ((term45 _5805 _5806 _5807 P p1) = (term46 _5805 _5806 _5807 P p1)) = ((term41 _5805 _5806 _5807 P p1) = (term60 _5805 _5806 _5807 P p1)).
Proof. exact (MK_COMB (@lem56032 _5805 _5806 _5807 P p1) (@lem56039 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56041 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term41 _5805 _5806 _5807 P p1) = (term60 _5805 _5806 _5807 P p1).
Proof. exact (EQ_MP (@lem56040 _5805 _5806 _5807 P p1) (@lem56026 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56058 {_5805 _5806 _5807 : Type'} (a0 : _5807) (a1 : prod _5806 _5805) : a0 = (term61 _5805 _5806 _5807 a0 a1).
Proof. exact (@lem51128 _5807 (prod _5806 _5805) a0 a1). Qed.
Lemma lem56059 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : x = (term62 _5805 _5806 _5807 x y z).
Proof. exact (@lem56058 _5805 _5806 _5807 x (@pair _5806 _5805 y z)). Qed.
Lemma lem56060 {_5805 _5806 _5807 : Type'} (a0 : _5807) (a1 : prod _5806 _5805) : a1 = (term63 _5805 _5806 _5807 a0 a1).
Proof. exact (@lem51159 _5807 (prod _5806 _5805) a0 a1). Qed.
Lemma lem56061 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (@pair _5806 _5805 y z) = (term64 _5805 _5806 _5807 x y z).
Proof. exact (@lem56060 _5805 _5806 _5807 x (@pair _5806 _5805 y z)). Qed.
Lemma lem56062 {_5807 : Type'} (x : _5807) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem56063 {_5807 : Type'} : (term65 _5807) = (term65 _5807).
Proof. exact (eq_refl (term65 _5807)). Qed.
Lemma lem56064 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term66 _5807 x) = (term67 _5805 _5806 _5807 x y z).
Proof. exact (MK_COMB (@lem56063 _5807) (@lem56059 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56065 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term67 _5805 _5806 _5807 x y z) = (term62 _5805 _5806 _5807 x y z).
Proof. exact (eq_refl (term67 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56066 {_5807 : Type'} (x : _5807) : (term68 _5807 x) = (term68 _5807 x).
Proof. exact (eq_refl (term68 _5807 x)). Qed.
Lemma lem56067 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term66 _5807 x) = (term67 _5805 _5806 _5807 x y z)) = ((term66 _5807 x) = (term62 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56066 _5807 x) (@lem56065 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56068 {_5807 : Type'} (x : _5807) : (term66 _5807 x) = x.
Proof. exact (eq_refl (term66 _5807 x)). Qed.
Lemma lem56069 {_5807 : Type'} : (@eq _5807) = (@eq _5807).
Proof. exact (eq_refl (@eq _5807)). Qed.
Lemma lem56070 {_5807 : Type'} (x : _5807) : (term68 _5807 x) = (@eq _5807 x).
Proof. exact (MK_COMB (@lem56069 _5807) (@lem56068 _5807 x)). Qed.
Lemma lem56071 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term62 _5805 _5806 _5807 x y z) = (term62 _5805 _5806 _5807 x y z).
Proof. exact (eq_refl (term62 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56072 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term66 _5807 x) = (term62 _5805 _5806 _5807 x y z)) = (x = (term62 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56070 _5807 x) (@lem56071 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56073 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term66 _5807 x) = (term67 _5805 _5806 _5807 x y z)) = (x = (term62 _5805 _5806 _5807 x y z)).
Proof. exact (TRANS (@lem56067 _5805 _5806 _5807 x y z) (@lem56072 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56074 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : x = (term62 _5805 _5806 _5807 x y z).
Proof. exact (EQ_MP (@lem56073 _5805 _5806 _5807 x y z) (@lem56064 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56075 {_5807 : Type'} (x : _5807) : (@eq _5807 x) = (@eq _5807 x).
Proof. exact (eq_refl (@eq _5807 x)). Qed.
Lemma lem56076 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (x = x) = (x = (term62 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56075 _5807 x) (@lem56074 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56077 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : x = (term62 _5805 _5806 _5807 x y z).
Proof. exact (EQ_MP (@lem56076 _5805 _5806 _5807 x y z) (@lem56062 _5807 x)). Qed.
Lemma lem56078 {_5805 _5806 : Type'} (a0 : _5806) (a1 : _5805) : a0 = (term69 _5805 _5806 a0 a1).
Proof. exact (@lem51128 _5806 _5805 a0 a1). Qed.
Lemma lem56079 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : y = (term69 _5805 _5806 y z).
Proof. exact (@lem56078 _5805 _5806 y z). Qed.
Lemma lem56080 {_5805 _5806 : Type'} (a0 : _5806) (a1 : _5805) : a1 = (term70 _5805 _5806 a0 a1).
Proof. exact (@lem51159 _5806 _5805 a0 a1). Qed.
Lemma lem56081 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : z = (term70 _5805 _5806 y z).
Proof. exact (@lem56080 _5805 _5806 y z). Qed.
Lemma lem56082 {_5806 : Type'} (y : _5806) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem56083 {_5806 : Type'} : (term65 _5806) = (term65 _5806).
Proof. exact (eq_refl (term65 _5806)). Qed.
Lemma lem56084 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term66 _5806 y) = (term71 _5805 _5806 y z).
Proof. exact (MK_COMB (@lem56083 _5806) (@lem56079 _5805 _5806 y z)). Qed.
Lemma lem56085 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term71 _5805 _5806 y z) = (term69 _5805 _5806 y z).
Proof. exact (eq_refl (term71 _5805 _5806 y z)). Qed.
Lemma lem56086 {_5806 : Type'} (y : _5806) : (term68 _5806 y) = (term68 _5806 y).
Proof. exact (eq_refl (term68 _5806 y)). Qed.
Lemma lem56087 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : ((term66 _5806 y) = (term71 _5805 _5806 y z)) = ((term66 _5806 y) = (term69 _5805 _5806 y z)).
Proof. exact (MK_COMB (@lem56086 _5806 y) (@lem56085 _5805 _5806 y z)). Qed.
Lemma lem56088 {_5806 : Type'} (y : _5806) : (term66 _5806 y) = y.
Proof. exact (eq_refl (term66 _5806 y)). Qed.
Lemma lem56089 {_5806 : Type'} : (@eq _5806) = (@eq _5806).
Proof. exact (eq_refl (@eq _5806)). Qed.
Lemma lem56090 {_5806 : Type'} (y : _5806) : (term68 _5806 y) = (@eq _5806 y).
Proof. exact (MK_COMB (@lem56089 _5806) (@lem56088 _5806 y)). Qed.
Lemma lem56091 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term69 _5805 _5806 y z) = (term69 _5805 _5806 y z).
Proof. exact (eq_refl (term69 _5805 _5806 y z)). Qed.
Lemma lem56092 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : ((term66 _5806 y) = (term69 _5805 _5806 y z)) = (y = (term69 _5805 _5806 y z)).
Proof. exact (MK_COMB (@lem56090 _5806 y) (@lem56091 _5805 _5806 y z)). Qed.
Lemma lem56093 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : ((term66 _5806 y) = (term71 _5805 _5806 y z)) = (y = (term69 _5805 _5806 y z)).
Proof. exact (TRANS (@lem56087 _5805 _5806 y z) (@lem56092 _5805 _5806 y z)). Qed.
Lemma lem56094 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : y = (term69 _5805 _5806 y z).
Proof. exact (EQ_MP (@lem56093 _5805 _5806 y z) (@lem56084 _5805 _5806 y z)). Qed.
Lemma lem56095 {_5806 : Type'} (y : _5806) : (@eq _5806 y) = (@eq _5806 y).
Proof. exact (eq_refl (@eq _5806 y)). Qed.
Lemma lem56096 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (y = y) = (y = (term69 _5805 _5806 y z)).
Proof. exact (MK_COMB (@lem56095 _5806 y) (@lem56094 _5805 _5806 y z)). Qed.
Lemma lem56097 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : y = (term69 _5805 _5806 y z).
Proof. exact (EQ_MP (@lem56096 _5805 _5806 y z) (@lem56082 _5806 y)). Qed.
Lemma lem56098 {_5805 : Type'} (z : _5805) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem56099 {_5805 : Type'} : (term65 _5805) = (term65 _5805).
Proof. exact (eq_refl (term65 _5805)). Qed.
Lemma lem56100 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term66 _5805 z) = (term72 _5805 _5806 y z).
Proof. exact (MK_COMB (@lem56099 _5805) (@lem56081 _5805 _5806 y z)). Qed.
Lemma lem56101 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term72 _5805 _5806 y z) = (term70 _5805 _5806 y z).
Proof. exact (eq_refl (term72 _5805 _5806 y z)). Qed.
Lemma lem56102 {_5805 : Type'} (z : _5805) : (term68 _5805 z) = (term68 _5805 z).
Proof. exact (eq_refl (term68 _5805 z)). Qed.
Lemma lem56103 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : ((term66 _5805 z) = (term72 _5805 _5806 y z)) = ((term66 _5805 z) = (term70 _5805 _5806 y z)).
Proof. exact (MK_COMB (@lem56102 _5805 z) (@lem56101 _5805 _5806 y z)). Qed.
Lemma lem56104 {_5805 : Type'} (z : _5805) : (term66 _5805 z) = z.
Proof. exact (eq_refl (term66 _5805 z)). Qed.
Lemma lem56105 {_5805 : Type'} : (@eq _5805) = (@eq _5805).
Proof. exact (eq_refl (@eq _5805)). Qed.
Lemma lem56106 {_5805 : Type'} (z : _5805) : (term68 _5805 z) = (@eq _5805 z).
Proof. exact (MK_COMB (@lem56105 _5805) (@lem56104 _5805 z)). Qed.
Lemma lem56107 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term70 _5805 _5806 y z) = (term70 _5805 _5806 y z).
Proof. exact (eq_refl (term70 _5805 _5806 y z)). Qed.
Lemma lem56108 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : ((term66 _5805 z) = (term70 _5805 _5806 y z)) = (z = (term70 _5805 _5806 y z)).
Proof. exact (MK_COMB (@lem56106 _5805 z) (@lem56107 _5805 _5806 y z)). Qed.
Lemma lem56109 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : ((term66 _5805 z) = (term72 _5805 _5806 y z)) = (z = (term70 _5805 _5806 y z)).
Proof. exact (TRANS (@lem56103 _5805 _5806 y z) (@lem56108 _5805 _5806 y z)). Qed.
Lemma lem56110 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : z = (term70 _5805 _5806 y z).
Proof. exact (EQ_MP (@lem56109 _5805 _5806 y z) (@lem56100 _5805 _5806 y z)). Qed.
Lemma lem56111 {_5805 : Type'} (z : _5805) : (@eq _5805 z) = (@eq _5805 z).
Proof. exact (eq_refl (@eq _5805 z)). Qed.
Lemma lem56112 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (z = z) = (z = (term70 _5805 _5806 y z)).
Proof. exact (MK_COMB (@lem56111 _5805 z) (@lem56110 _5805 _5806 y z)). Qed.
Lemma lem56113 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : z = (term70 _5805 _5806 y z).
Proof. exact (EQ_MP (@lem56112 _5805 _5806 y z) (@lem56098 _5805 z)). Qed.
Lemma lem56114 {_5805 _5806 : Type'} : (term73 _5805 _5806) = (term73 _5805 _5806).
Proof. exact (eq_refl (term73 _5805 _5806)). Qed.
Lemma lem56115 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term74 _5805 _5806 y z) = (term75 _5805 _5806 _5807 x y z).
Proof. exact (MK_COMB (@lem56114 _5805 _5806) (@lem56061 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56116 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term75 _5805 _5806 _5807 x y z) = (term76 _5805 _5806 _5807 x y z).
Proof. exact (eq_refl (term75 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56117 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term77 _5805 _5806 y z) = (term77 _5805 _5806 y z).
Proof. exact (eq_refl (term77 _5805 _5806 y z)). Qed.
Lemma lem56118 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term74 _5805 _5806 y z) = (term75 _5805 _5806 _5807 x y z)) = ((term74 _5805 _5806 y z) = (term76 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56117 _5805 _5806 y z) (@lem56116 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56119 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term74 _5805 _5806 y z) = (term69 _5805 _5806 y z).
Proof. exact (eq_refl (term74 _5805 _5806 y z)). Qed.
Lemma lem56120 {_5806 : Type'} : (@eq _5806) = (@eq _5806).
Proof. exact (eq_refl (@eq _5806)). Qed.
Lemma lem56121 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term77 _5805 _5806 y z) = (term78 _5805 _5806 y z).
Proof. exact (MK_COMB (@lem56120 _5806) (@lem56119 _5805 _5806 y z)). Qed.
Lemma lem56122 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term76 _5805 _5806 _5807 x y z) = (term76 _5805 _5806 _5807 x y z).
Proof. exact (eq_refl (term76 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56123 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term74 _5805 _5806 y z) = (term76 _5805 _5806 _5807 x y z)) = ((term69 _5805 _5806 y z) = (term76 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56121 _5805 _5806 y z) (@lem56122 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56124 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term74 _5805 _5806 y z) = (term75 _5805 _5806 _5807 x y z)) = ((term69 _5805 _5806 y z) = (term76 _5805 _5806 _5807 x y z)).
Proof. exact (TRANS (@lem56118 _5805 _5806 _5807 x y z) (@lem56123 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56125 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term69 _5805 _5806 y z) = (term76 _5805 _5806 _5807 x y z).
Proof. exact (EQ_MP (@lem56124 _5805 _5806 _5807 x y z) (@lem56115 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56126 {_5806 : Type'} (y : _5806) : (@eq _5806 y) = (@eq _5806 y).
Proof. exact (eq_refl (@eq _5806 y)). Qed.
Lemma lem56127 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (y = (term69 _5805 _5806 y z)) = (y = (term76 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56126 _5806 y) (@lem56125 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56128 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : y = (term76 _5805 _5806 _5807 x y z).
Proof. exact (EQ_MP (@lem56127 _5805 _5806 _5807 x y z) (@lem56097 _5805 _5806 y z)). Qed.
Lemma lem56129 {_5805 _5806 : Type'} : (term79 _5805 _5806) = (term79 _5805 _5806).
Proof. exact (eq_refl (term79 _5805 _5806)). Qed.
Lemma lem56130 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term80 _5805 _5806 y z) = (term81 _5805 _5806 _5807 x y z).
Proof. exact (MK_COMB (@lem56129 _5805 _5806) (@lem56061 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56131 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term81 _5805 _5806 _5807 x y z) = (term82 _5805 _5806 _5807 x y z).
Proof. exact (eq_refl (term81 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56132 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term83 _5805 _5806 y z) = (term83 _5805 _5806 y z).
Proof. exact (eq_refl (term83 _5805 _5806 y z)). Qed.
Lemma lem56133 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term80 _5805 _5806 y z) = (term81 _5805 _5806 _5807 x y z)) = ((term80 _5805 _5806 y z) = (term82 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56132 _5805 _5806 y z) (@lem56131 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56134 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term80 _5805 _5806 y z) = (term70 _5805 _5806 y z).
Proof. exact (eq_refl (term80 _5805 _5806 y z)). Qed.
Lemma lem56135 {_5805 : Type'} : (@eq _5805) = (@eq _5805).
Proof. exact (eq_refl (@eq _5805)). Qed.
Lemma lem56136 {_5805 _5806 : Type'} (y : _5806) (z : _5805) : (term83 _5805 _5806 y z) = (term84 _5805 _5806 y z).
Proof. exact (MK_COMB (@lem56135 _5805) (@lem56134 _5805 _5806 y z)). Qed.
Lemma lem56137 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term82 _5805 _5806 _5807 x y z) = (term82 _5805 _5806 _5807 x y z).
Proof. exact (eq_refl (term82 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56138 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term80 _5805 _5806 y z) = (term82 _5805 _5806 _5807 x y z)) = ((term70 _5805 _5806 y z) = (term82 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56136 _5805 _5806 y z) (@lem56137 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56139 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : ((term80 _5805 _5806 y z) = (term81 _5805 _5806 _5807 x y z)) = ((term70 _5805 _5806 y z) = (term82 _5805 _5806 _5807 x y z)).
Proof. exact (TRANS (@lem56133 _5805 _5806 _5807 x y z) (@lem56138 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56140 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (term70 _5805 _5806 y z) = (term82 _5805 _5806 _5807 x y z).
Proof. exact (EQ_MP (@lem56139 _5805 _5806 _5807 x y z) (@lem56130 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56141 {_5805 : Type'} (z : _5805) : (@eq _5805 z) = (@eq _5805 z).
Proof. exact (eq_refl (@eq _5805 z)). Qed.
Lemma lem56142 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : (z = (term70 _5805 _5806 y z)) = (z = (term82 _5805 _5806 _5807 x y z)).
Proof. exact (MK_COMB (@lem56141 _5805 z) (@lem56140 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56143 {_5805 _5806 _5807 : Type'} (x : _5807) (y : _5806) (z : _5805) : z = (term82 _5805 _5806 _5807 x y z).
Proof. exact (EQ_MP (@lem56142 _5805 _5806 _5807 x y z) (@lem56113 _5805 _5806 y z)). Qed.
Lemma lem56144 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term85 _5805 _5806 _5807 P) = (term85 _5805 _5806 _5807 P).
Proof. exact (eq_refl (term85 _5805 _5806 _5807 P)). Qed.
Lemma lem56145 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term86 _5805 _5806 _5807 P x) = (term87 _5805 _5806 _5807 P x y z).
Proof. exact (MK_COMB (@lem56144 _5805 _5806 _5807 P) (@lem56077 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56146 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term87 _5805 _5806 _5807 P x y z) = (term88 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term87 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56147 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) : (term89 _5805 _5806 _5807 P x) = (term89 _5805 _5806 _5807 P x).
Proof. exact (eq_refl (term89 _5805 _5806 _5807 P x)). Qed.
Lemma lem56148 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term86 _5805 _5806 _5807 P x) = (term87 _5805 _5806 _5807 P x y z)) = ((term86 _5805 _5806 _5807 P x) = (term88 _5805 _5806 _5807 P x y z)).
Proof. exact (MK_COMB (@lem56147 _5805 _5806 _5807 P x) (@lem56146 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56149 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) : (term86 _5805 _5806 _5807 P x) = (term90 _5805 _5806 _5807 P x).
Proof. exact (eq_refl (term86 _5805 _5806 _5807 P x)). Qed.
Lemma lem56150 {_5805 _5806 : Type'} : (@eq (_5806 -> _5805 -> Prop)) = (@eq (_5806 -> _5805 -> Prop)).
Proof. exact (eq_refl (@eq (_5806 -> _5805 -> Prop))). Qed.
Lemma lem56151 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) : (term89 _5805 _5806 _5807 P x) = (term91 _5805 _5806 _5807 P x).
Proof. exact (MK_COMB (@lem56150 _5805 _5806) (@lem56149 _5805 _5806 _5807 P x)). Qed.
Lemma lem56152 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term88 _5805 _5806 _5807 P x y z) = (term88 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term88 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56153 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term86 _5805 _5806 _5807 P x) = (term88 _5805 _5806 _5807 P x y z)) = ((term90 _5805 _5806 _5807 P x) = (term88 _5805 _5806 _5807 P x y z)).
Proof. exact (MK_COMB (@lem56151 _5805 _5806 _5807 P x) (@lem56152 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56154 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term86 _5805 _5806 _5807 P x) = (term87 _5805 _5806 _5807 P x y z)) = ((term90 _5805 _5806 _5807 P x) = (term88 _5805 _5806 _5807 P x y z)).
Proof. exact (TRANS (@lem56148 _5805 _5806 _5807 P x y z) (@lem56153 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56155 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term90 _5805 _5806 _5807 P x) = (term88 _5805 _5806 _5807 P x y z).
Proof. exact (EQ_MP (@lem56154 _5805 _5806 _5807 P x y z) (@lem56145 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56156 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term92 _5805 _5806 _5807 P x y) = (term93 _5805 _5806 _5807 P x y z).
Proof. exact (MK_COMB (@lem56155 _5805 _5806 _5807 P x y z) (@lem56128 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56157 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term93 _5805 _5806 _5807 P x y z) = (term94 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term93 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56158 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : (term95 _5805 _5806 _5807 P x y) = (term95 _5805 _5806 _5807 P x y).
Proof. exact (eq_refl (term95 _5805 _5806 _5807 P x y)). Qed.
Lemma lem56159 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term92 _5805 _5806 _5807 P x y) = (term93 _5805 _5806 _5807 P x y z)) = ((term92 _5805 _5806 _5807 P x y) = (term94 _5805 _5806 _5807 P x y z)).
Proof. exact (MK_COMB (@lem56158 _5805 _5806 _5807 P x y) (@lem56157 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56160 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : (term92 _5805 _5806 _5807 P x y) = (term96 _5805 _5806 _5807 P x y).
Proof. exact (eq_refl (term92 _5805 _5806 _5807 P x y)). Qed.
Lemma lem56161 {_5805 : Type'} : (@eq (_5805 -> Prop)) = (@eq (_5805 -> Prop)).
Proof. exact (eq_refl (@eq (_5805 -> Prop))). Qed.
Lemma lem56162 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : (term95 _5805 _5806 _5807 P x y) = (term97 _5805 _5806 _5807 P x y).
Proof. exact (MK_COMB (@lem56161 _5805) (@lem56160 _5805 _5806 _5807 P x y)). Qed.
Lemma lem56163 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term94 _5805 _5806 _5807 P x y z) = (term94 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term94 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56164 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term92 _5805 _5806 _5807 P x y) = (term94 _5805 _5806 _5807 P x y z)) = ((term96 _5805 _5806 _5807 P x y) = (term94 _5805 _5806 _5807 P x y z)).
Proof. exact (MK_COMB (@lem56162 _5805 _5806 _5807 P x y) (@lem56163 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56165 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term92 _5805 _5806 _5807 P x y) = (term93 _5805 _5806 _5807 P x y z)) = ((term96 _5805 _5806 _5807 P x y) = (term94 _5805 _5806 _5807 P x y z)).
Proof. exact (TRANS (@lem56159 _5805 _5806 _5807 P x y z) (@lem56164 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56166 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term96 _5805 _5806 _5807 P x y) = (term94 _5805 _5806 _5807 P x y z).
Proof. exact (EQ_MP (@lem56165 _5805 _5806 _5807 P x y z) (@lem56156 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56167 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term98 _5805 _5806 _5807 P x y z) = (term99 _5805 _5806 _5807 P x y z).
Proof. exact (MK_COMB (@lem56166 _5805 _5806 _5807 P x y z) (@lem56143 _5805 _5806 _5807 x y z)). Qed.
Lemma lem56168 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term99 _5805 _5806 _5807 P x y z) = (term100 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term99 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56169 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term101 _5805 _5806 _5807 P x y z) = (term101 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term101 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56170 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term98 _5805 _5806 _5807 P x y z) = (term99 _5805 _5806 _5807 P x y z)) = ((term98 _5805 _5806 _5807 P x y z) = (term100 _5805 _5806 _5807 P x y z)).
Proof. exact (MK_COMB (@lem56169 _5805 _5806 _5807 P x y z) (@lem56168 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56171 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term98 _5805 _5806 _5807 P x y z) = (P x y z).
Proof. exact (eq_refl (term98 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56173 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term101 _5805 _5806 _5807 P x y z) = (term102 _5805 _5806 _5807 P x y z).
Proof. exact (MK_COMB (@lem56172) (@lem56171 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56174 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term100 _5805 _5806 _5807 P x y z) = (term100 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term100 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56175 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term98 _5805 _5806 _5807 P x y z) = (term100 _5805 _5806 _5807 P x y z)) = ((P x y z) = (term100 _5805 _5806 _5807 P x y z)).
Proof. exact (MK_COMB (@lem56173 _5805 _5806 _5807 P x y z) (@lem56174 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56176 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term98 _5805 _5806 _5807 P x y z) = (term99 _5805 _5806 _5807 P x y z)) = ((P x y z) = (term100 _5805 _5806 _5807 P x y z)).
Proof. exact (TRANS (@lem56170 _5805 _5806 _5807 P x y z) (@lem56175 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56177 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (P x y z) = (term100 _5805 _5806 _5807 P x y z).
Proof. exact (EQ_MP (@lem56176 _5805 _5806 _5807 P x y z) (@lem56167 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56178 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term100 _5805 _5806 _5807 P x y z) = (P x y z).
Proof. exact (SYM (@lem56177 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56179 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term103 _5805 _5806 _5807 P x y z) = (term100 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term103 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56180 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term103 _5805 _5806 _5807 P x y z) = (P x y z).
Proof. exact (TRANS (@lem56179 _5805 _5806 _5807 P x y z) (@lem56178 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56181 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : term104 _5805 _5806 _5807 P x y.
Proof. exact (fun z : _5805 => @lem56180 _5805 _5806 _5807 P x y z). Qed.
Lemma lem56182 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) : term105 _5805 _5806 _5807 P x.
Proof. exact (fun y : _5806 => @lem56181 _5805 _5806 _5807 P x y). Qed.
Lemma lem56183 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : term106 _5805 _5806 _5807 P.
Proof. exact (fun x : _5807 => @lem56182 _5805 _5806 _5807 P x). Qed.
Lemma lem56184 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : term107 _5805 _5806 _5807 P.
Proof. exact (ex_intro (term108 _5805 _5806 _5807 P) (term109 _5805 _5806 _5807 P) (@lem56183 _5805 _5806 _5807 P)). Qed.
Lemma lem56186 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem56187 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem56186 Prop a b). Qed.
Lemma lem56188 {_5805 _5806 _5807 : Type'} (_1568 : type1227 _5805 _5806 _5807) (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : ((term110 _5805 _5806 _5807 _1568 x y z) = (P x y z)) = (term111 _5805 _5806 _5807 _1568 P x y z).
Proof. exact (@lem56187 (term110 _5805 _5806 _5807 _1568 x y z) (P x y z)). Qed.
Lemma lem56189 {_5805 _5806 _5807 : Type'} (_1568 : type1227 _5805 _5806 _5807) (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : (term112 _5805 _5806 _5807 _1568 P x y) = (term113 _5805 _5806 _5807 _1568 P x y).
Proof. exact (fun_ext (fun z : _5805 => @lem56188 _5805 _5806 _5807 _1568 P x y z)). Qed.
Lemma lem56190 {_5805 : Type'} : (@all _5805) = (@all _5805).
Proof. exact (eq_refl (@all _5805)). Qed.
Lemma lem56191 {_5805 _5806 _5807 : Type'} (_1568 : type1227 _5805 _5806 _5807) (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : (term114 _5805 _5806 _5807 _1568 P x y) = (term115 _5805 _5806 _5807 _1568 P x y).
Proof. exact (MK_COMB (@lem56190 _5805) (@lem56189 _5805 _5806 _5807 _1568 P x y)). Qed.
Lemma lem56192 {_5805 _5806 _5807 : Type'} (_1568 : type1227 _5805 _5806 _5807) (P : type1517 _5805 _5806 _5807) (x : _5807) : (term116 _5805 _5806 _5807 _1568 P x) = (term117 _5805 _5806 _5807 _1568 P x).
Proof. exact (fun_ext (fun y : _5806 => @lem56191 _5805 _5806 _5807 _1568 P x y)). Qed.
Lemma lem56193 {_5806 : Type'} : (@all _5806) = (@all _5806).
Proof. exact (eq_refl (@all _5806)). Qed.
Lemma lem56194 {_5805 _5806 _5807 : Type'} (_1568 : type1227 _5805 _5806 _5807) (P : type1517 _5805 _5806 _5807) (x : _5807) : (term118 _5805 _5806 _5807 _1568 P x) = (term119 _5805 _5806 _5807 _1568 P x).
Proof. exact (MK_COMB (@lem56193 _5806) (@lem56192 _5805 _5806 _5807 _1568 P x)). Qed.
Lemma lem56195 {_5805 _5806 _5807 : Type'} (_1568 : type1227 _5805 _5806 _5807) (P : type1517 _5805 _5806 _5807) : (term120 _5805 _5806 _5807 _1568 P) = (term121 _5805 _5806 _5807 _1568 P).
Proof. exact (fun_ext (fun x : _5807 => @lem56194 _5805 _5806 _5807 _1568 P x)). Qed.
Lemma lem56196 {_5807 : Type'} : (@all _5807) = (@all _5807).
Proof. exact (eq_refl (@all _5807)). Qed.
Lemma lem56197 {_5805 _5806 _5807 : Type'} (_1568 : type1227 _5805 _5806 _5807) (P : type1517 _5805 _5806 _5807) : (term122 _5805 _5806 _5807 _1568 P) = (term123 _5805 _5806 _5807 _1568 P).
Proof. exact (MK_COMB (@lem56196 _5807) (@lem56195 _5805 _5806 _5807 _1568 P)). Qed.
Lemma lem56198 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term108 _5805 _5806 _5807 P) = (term124 _5805 _5806 _5807 P).
Proof. exact (fun_ext (fun _1568 : type1227 _5805 _5806 _5807 => @lem56197 _5805 _5806 _5807 _1568 P)). Qed.
Lemma lem56199 {_5805 _5806 _5807 : Type'} : (@ex ((prod _5807 (prod _5806 _5805)) -> Prop)) = (@ex ((prod _5807 (prod _5806 _5805)) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5807 (prod _5806 _5805)) -> Prop))). Qed.
Lemma lem56200 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term107 _5805 _5806 _5807 P) = (term125 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem56199 _5805 _5806 _5807) (@lem56198 _5805 _5806 _5807 P)). Qed.
Lemma lem56201 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : term125 _5805 _5806 _5807 P.
Proof. exact (EQ_MP (@lem56200 _5805 _5806 _5807 P) (@lem56184 _5805 _5806 _5807 P)). Qed.
Lemma lem56203 {_5076 : Type'} (P : _5076 -> Prop) : term126 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem56204 {_5805 _5806 _5807 : Type'} (P : type332 _5805 _5806 _5807) : term127 _5805 _5806 _5807 P.
Proof. exact (@lem56203 (type1227 _5805 _5806 _5807) P). Qed.
Lemma lem56205 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : term128 _5805 _5806 _5807 P.
Proof. exact (@lem56204 _5805 _5806 _5807 (term124 _5805 _5806 _5807 P)). Qed.
Lemma lem56206 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : term129 _5805 _5806 _5807 P.
Proof. exact (@lem56205 _5805 _5806 _5807 P (@lem56201 _5805 _5806 _5807 P)). Qed.
Lemma lem56207 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term129 _5805 _5806 _5807 P) = (term130 _5805 _5806 _5807 P).
Proof. exact (eq_refl (term129 _5805 _5806 _5807 P)). Qed.
Lemma lem56208 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : term130 _5805 _5806 _5807 P.
Proof. exact (EQ_MP (@lem56207 _5805 _5806 _5807 P) (@lem56206 _5805 _5806 _5807 P)). Qed.
Lemma lem56209 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) : term131 _5805 _5806 _5807 P x.
Proof. exact (@lem56208 _5805 _5806 _5807 P x). Qed.
Lemma lem56210 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) : (term131 _5805 _5806 _5807 P x) = (term132 _5805 _5806 _5807 P x).
Proof. exact (eq_refl (term131 _5805 _5806 _5807 P x)). Qed.
Lemma lem56211 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) : term132 _5805 _5806 _5807 P x.
Proof. exact (EQ_MP (@lem56210 _5805 _5806 _5807 P x) (@lem56209 _5805 _5806 _5807 P x)). Qed.
Lemma lem56212 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : term133 _5805 _5806 _5807 P x y.
Proof. exact (@lem56211 _5805 _5806 _5807 P x y). Qed.
Lemma lem56213 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : (term133 _5805 _5806 _5807 P x y) = (term134 _5805 _5806 _5807 P x y).
Proof. exact (eq_refl (term133 _5805 _5806 _5807 P x y)). Qed.
Lemma lem56214 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) : term134 _5805 _5806 _5807 P x y.
Proof. exact (EQ_MP (@lem56213 _5805 _5806 _5807 P x y) (@lem56212 _5805 _5806 _5807 P x y)). Qed.
Lemma lem56215 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : term135 _5805 _5806 _5807 P x y z.
Proof. exact (@lem56214 _5805 _5806 _5807 P x y z). Qed.
Lemma lem56216 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term135 _5805 _5806 _5807 P x y z) = (term136 _5805 _5806 _5807 P x y z).
Proof. exact (eq_refl (term135 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56217 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : term136 _5805 _5806 _5807 P x y z.
Proof. exact (EQ_MP (@lem56216 _5805 _5806 _5807 P x y z) (@lem56215 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56219 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem56220 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem56219 Prop a b). Qed.
Lemma lem56221 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term136 _5805 _5806 _5807 P x y z) = ((term52 _5805 _5806 _5807 P x y z) = (P x y z)).
Proof. exact (@lem56220 (term52 _5805 _5806 _5807 P x y z) (P x y z)). Qed.
Lemma lem56222 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term52 _5805 _5806 _5807 P x y z) = (P x y z).
Proof. exact (EQ_MP (@lem56221 _5805 _5806 _5807 P x y z) (@lem56217 _5805 _5806 _5807 P x y z)). Qed.
Lemma lem56223 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (x : _5807) (y : _5806) (z : _5805) : (term52 _5805 _5806 _5807 P x y z) = (P x y z).
Proof. exact (@lem56222 _5805 _5806 _5807 P x y z). Qed.
Lemma lem56224 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term52 _5805 _5806 _5807 P p1 p1' p2) = (P p1 p1' p2).
Proof. exact (@lem56223 _5805 _5806 _5807 P p1 p1' p2). Qed.
Lemma lem56225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56226 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term137 _5805 _5806 _5807 P p1 p1' p2) = (term102 _5805 _5806 _5807 P p1 p1' p2).
Proof. exact (MK_COMB (@lem56225) (@lem56224 _5805 _5806 _5807 P p1 p1' p2)). Qed.
Lemma lem56228 {A B : Type'} (f : A -> B) (y : A) : (term15 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem56229 {_5805 _5806 _5807 : Type'} (f : type1227 _5805 _5806 _5807) (y : type1659 _5805 _5806 _5807) : (term138 _5805 _5806 _5807 f y) = (f y).
Proof. exact (@lem56228 (type1659 _5805 _5806 _5807) Prop f y). Qed.
Lemma lem56230 {_5805 _5806 _5807 : Type'} (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term139 _5805 _5806 _5807 p1 p1' p2) = (term53 _5805 _5806 _5807 p1 p1' p2).
Proof. exact (@lem56229 _5805 _5806 _5807 (term19 _5805 _5806 _5807) (term140 _5805 _5806 _5807 p1 p1' p2)). Qed.
Lemma lem56231 {_5805 _5806 _5807 : Type'} (x : type1659 _5805 _5806 _5807) : (term31 _5805 _5806 _5807 x) = True.
Proof. exact (eq_refl (term31 _5805 _5806 _5807 x)). Qed.
Lemma lem56232 {_5805 _5806 _5807 : Type'} : (term141 _5805 _5806 _5807) = (term19 _5805 _5806 _5807).
Proof. exact (fun_ext (fun x : type1659 _5805 _5806 _5807 => @lem56231 _5805 _5806 _5807 x)). Qed.
Lemma lem56233 {_5805 _5806 _5807 : Type'} (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term140 _5805 _5806 _5807 p1 p1' p2) = (term140 _5805 _5806 _5807 p1 p1' p2).
Proof. exact (eq_refl (term140 _5805 _5806 _5807 p1 p1' p2)). Qed.
Lemma lem56234 {_5805 _5806 _5807 : Type'} (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term139 _5805 _5806 _5807 p1 p1' p2) = (term53 _5805 _5806 _5807 p1 p1' p2).
Proof. exact (MK_COMB (@lem56232 _5805 _5806 _5807) (@lem56233 _5805 _5806 _5807 p1 p1' p2)). Qed.
Lemma lem56235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56236 {_5805 _5806 _5807 : Type'} (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term142 _5805 _5806 _5807 p1 p1' p2) = (term143 _5805 _5806 _5807 p1 p1' p2).
Proof. exact (MK_COMB (@lem56235) (@lem56234 _5805 _5806 _5807 p1 p1' p2)). Qed.
Lemma lem56237 {_5805 _5806 _5807 : Type'} (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term53 _5805 _5806 _5807 p1 p1' p2) = True.
Proof. exact (eq_refl (term53 _5805 _5806 _5807 p1 p1' p2)). Qed.
Lemma lem56238 {_5805 _5806 _5807 : Type'} (p1 : _5807) (p1' : _5806) (p2 : _5805) : ((term139 _5805 _5806 _5807 p1 p1' p2) = (term53 _5805 _5806 _5807 p1 p1' p2)) = ((term53 _5805 _5806 _5807 p1 p1' p2) = True).
Proof. exact (MK_COMB (@lem56236 _5805 _5806 _5807 p1 p1' p2) (@lem56237 _5805 _5806 _5807 p1 p1' p2)). Qed.
Lemma lem56239 {_5805 _5806 _5807 : Type'} (p1 : _5807) (p1' : _5806) (p2 : _5805) : (term53 _5805 _5806 _5807 p1 p1' p2) = True.
Proof. exact (EQ_MP (@lem56238 _5805 _5806 _5807 p1 p1' p2) (@lem56230 _5805 _5806 _5807 p1 p1' p2)). Qed.
Lemma lem56240 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) (p2 : _5805) : ((term52 _5805 _5806 _5807 P p1 p1' p2) = (term53 _5805 _5806 _5807 p1 p1' p2)) = ((P p1 p1' p2) = True).
Proof. exact (MK_COMB (@lem56226 _5805 _5806 _5807 P p1 p1' p2) (@lem56239 _5805 _5806 _5807 p1 p1' p2)). Qed.
Lemma lem56242 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem56243 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) (p2 : _5805) : ((P p1 p1' p2) = True) = (P p1 p1' p2).
Proof. exact (@lem56242 (P p1 p1' p2)). Qed.
Lemma lem56244 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) (p2 : _5805) : ((term52 _5805 _5806 _5807 P p1 p1' p2) = (term53 _5805 _5806 _5807 p1 p1' p2)) = (P p1 p1' p2).
Proof. exact (TRANS (@lem56240 _5805 _5806 _5807 P p1 p1' p2) (@lem56243 _5805 _5806 _5807 P p1 p1' p2)). Qed.
Lemma lem56245 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) : (term55 _5805 _5806 _5807 P p1 p1') = (term96 _5805 _5806 _5807 P p1 p1').
Proof. exact (fun_ext (fun p2 : _5805 => @lem56244 _5805 _5806 _5807 P p1 p1' p2)). Qed.
Lemma lem56246 {_5805 : Type'} : (@all _5805) = (@all _5805).
Proof. exact (eq_refl (@all _5805)). Qed.
Lemma lem56247 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) (p1' : _5806) : (term57 _5805 _5806 _5807 P p1 p1') = (term144 _5805 _5806 _5807 P p1 p1').
Proof. exact (MK_COMB (@lem56246 _5805) (@lem56245 _5805 _5806 _5807 P p1 p1')). Qed.
Lemma lem56254 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term59 _5805 _5806 _5807 P p1) = (term145 _5805 _5806 _5807 P p1).
Proof. exact (fun_ext (fun p1' : _5806 => @lem56247 _5805 _5806 _5807 P p1 p1')). Qed.
Lemma lem56255 {_5806 : Type'} : (@all _5806) = (@all _5806).
Proof. exact (eq_refl (@all _5806)). Qed.
Lemma lem56256 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term60 _5805 _5806 _5807 P p1) = (term146 _5805 _5806 _5807 P p1).
Proof. exact (MK_COMB (@lem56255 _5806) (@lem56254 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56263 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) (p1 : _5807) : (term41 _5805 _5806 _5807 P p1) = (term146 _5805 _5806 _5807 P p1).
Proof. exact (TRANS (@lem56041 _5805 _5806 _5807 P p1) (@lem56256 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56264 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term43 _5805 _5806 _5807 P) = (term147 _5805 _5806 _5807 P).
Proof. exact (fun_ext (fun p1 : _5807 => @lem56263 _5805 _5806 _5807 P p1)). Qed.
Lemma lem56265 {_5807 : Type'} : (@all _5807) = (@all _5807).
Proof. exact (eq_refl (@all _5807)). Qed.
Lemma lem56266 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term44 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem56265 _5807) (@lem56264 _5805 _5806 _5807 P)). Qed.
Lemma lem56273 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term11 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P).
Proof. exact (TRANS (@lem56018 _5805 _5806 _5807 P) (@lem56266 _5805 _5806 _5807 P)). Qed.
Lemma lem56274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56275 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term13 _5805 _5806 _5807 P) = (term148 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem56274) (@lem56273 _5805 _5806 _5807 P)). Qed.
Lemma lem56294 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P).
Proof. exact (eq_refl (term14 _5805 _5806 _5807 P)). Qed.
Lemma lem56295 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term11 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = ((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)).
Proof. exact (MK_COMB (@lem56275 _5805 _5806 _5807 P) (@lem56294 _5805 _5806 _5807 P)). Qed.
Lemma lem56297 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem56298 (x : Prop) : (x = x) = True.
Proof. exact (@lem56297 Prop x). Qed.
Lemma lem56299 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True.
Proof. exact (@lem56298 (term14 _5805 _5806 _5807 P)). Qed.
Lemma lem56302 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term149 _5805 _5806 _5807 P) = (term149 _5805 _5806 _5807 P).
Proof. exact (eq_refl (term149 _5805 _5806 _5807 P)). Qed.
Lemma lem56303 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term149 _5805 _5806 _5807 P) = (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True).
Proof. exact (eq_refl (term149 _5805 _5806 _5807 P)). Qed.
Lemma lem56304 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term150 _5805 _5806 _5807 P) = (term150 _5805 _5806 _5807 P).
Proof. exact (eq_refl (term150 _5805 _5806 _5807 P)). Qed.
Lemma lem56305 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term149 _5805 _5806 _5807 P) = (term149 _5805 _5806 _5807 P)) = ((term149 _5805 _5806 _5807 P) = (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True)).
Proof. exact (MK_COMB (@lem56304 _5805 _5806 _5807 P) (@lem56303 _5805 _5806 _5807 P)). Qed.
Lemma lem56306 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term149 _5805 _5806 _5807 P) = (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True).
Proof. exact (eq_refl (term149 _5805 _5806 _5807 P)). Qed.
Lemma lem56307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem56308 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term150 _5805 _5806 _5807 P) = (term151 _5805 _5806 _5807 P).
Proof. exact (MK_COMB (@lem56307) (@lem56306 _5805 _5806 _5807 P)). Qed.
Lemma lem56309 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True) = (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True).
Proof. exact (eq_refl (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True)). Qed.
Lemma lem56310 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term149 _5805 _5806 _5807 P) = (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True)) = ((((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True) = (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True)).
Proof. exact (MK_COMB (@lem56308 _5805 _5806 _5807 P) (@lem56309 _5805 _5806 _5807 P)). Qed.
Lemma lem56311 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term149 _5805 _5806 _5807 P) = (term149 _5805 _5806 _5807 P)) = ((((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True) = (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True)).
Proof. exact (TRANS (@lem56305 _5805 _5806 _5807 P) (@lem56310 _5805 _5806 _5807 P)). Qed.
Lemma lem56312 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True) = (((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True).
Proof. exact (EQ_MP (@lem56311 _5805 _5806 _5807 P) (@lem56302 _5805 _5806 _5807 P)). Qed.
Lemma lem56313 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term14 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True.
Proof. exact (EQ_MP (@lem56312 _5805 _5806 _5807 P) (@lem56299 _5805 _5806 _5807 P)). Qed.
Lemma lem56314 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : ((term11 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)) = True.
Proof. exact (TRANS (@lem56295 _5805 _5806 _5807 P) (@lem56313 _5805 _5806 _5807 P)). Qed.
Lemma lem56315 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : True = ((term11 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P)).
Proof. exact (SYM (@lem56314 _5805 _5806 _5807 P)). Qed.
Lemma lem56316 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term11 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P).
Proof. exact (EQ_MP (@lem56315 _5805 _5806 _5807 P) (@lem0)). Qed.
Lemma lem56317 {_5805 _5806 _5807 : Type'} (P : type1517 _5805 _5806 _5807) : (term10 _5805 _5806 _5807 P) = (term14 _5805 _5806 _5807 P).
Proof. exact (EQ_MP (@lem55964 _5805 _5806 _5807 P) (@lem56316 _5805 _5806 _5807 P)). Qed.
Lemma lem56322 {_5805 _5806 _5807 : Type'} : term152 _5805 _5806 _5807.
Proof. exact (fun P : type1517 _5805 _5806 _5807 => @lem56317 _5805 _5806 _5807 P). Qed.
