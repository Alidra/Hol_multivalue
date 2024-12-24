Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_UNION_NONZERO_term_abbrevs.
Require Import DISJOINT_spec.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import FINITE_SUPPORT_spec.
Require Import IN_INTER_spec.
Require Import IN_SUPPORT_spec.
Require Import ITERATE_SUPPORT_spec.
Require Import ITERATE_UNION_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUPPORT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem6003913 {_120592 _120607 : Type'} (op : type1400 _120607) : term0 _120592 _120607 op.
Proof. exact (@lem5764203 _120592 _120607 op). Qed.
Lemma lem6003914 {_120592 _120607 : Type'} (op : type1400 _120607) : (term0 _120592 _120607 op) = (term1 _120592 _120607 op).
Proof. exact (eq_refl (term0 _120592 _120607 op)). Qed.
Lemma lem6003916 {_120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term2 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5736505 Prop _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem6003917 {_120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term3 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem6003916 Prop _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem6003918 {_120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term4 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem6003917 Prop _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem6003951 {_120082 _120196 : Type'} (op : type1400 _120196) : term5 _120082 _120196 op.
Proof. exact (proj1 (@lem6003918 _120082 Prop Prop Prop Prop _120196 op)). Qed.
Lemma lem6003952 {_120082 _120196 : Type'} (op : type1400 _120196) (f : _120082 -> _120196) : term6 _120082 _120196 op f.
Proof. exact (@lem6003951 _120082 _120196 op f). Qed.
Lemma lem6003953 {_120082 _120196 : Type'} (op : type1400 _120196) (f : _120082 -> _120196) : (term6 _120082 _120196 op f) = (term7 _120082 _120196 op f).
Proof. exact (eq_refl (term6 _120082 _120196 op f)). Qed.
Lemma lem6003954 {_120082 _120196 : Type'} (op : type1400 _120196) (f : _120082 -> _120196) : term7 _120082 _120196 op f.
Proof. exact (EQ_MP (@lem6003953 _120082 _120196 op f) (@lem6003952 _120082 _120196 op f)). Qed.
Lemma lem6003955 {_120082 _120196 : Type'} (op : type1400 _120196) (f : _120082 -> _120196) (s : _120082 -> Prop) : term8 _120082 _120196 op f s.
Proof. exact (@lem6003954 _120082 _120196 op f s). Qed.
Lemma lem6003956 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) : (term8 _120082 _120196 op f s) = (term9 _120082 _120196 s op f).
Proof. exact (eq_refl (term8 _120082 _120196 op f s)). Qed.
Lemma lem6003957 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) : term9 _120082 _120196 s op f.
Proof. exact (EQ_MP (@lem6003956 _120082 _120196 s op f) (@lem6003955 _120082 _120196 op f s)). Qed.
Lemma lem6003958 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) (t : _120082 -> Prop) : term10 _120082 _120196 s op f t.
Proof. exact (@lem6003957 _120082 _120196 s op f t). Qed.
Lemma lem6003959 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) (t : _120082 -> Prop) : (term10 _120082 _120196 s op f t) = ((term11 _120082 _120196 op f s t) = (term12 _120082 _120196 s op f t)).
Proof. exact (eq_refl (term10 _120082 _120196 s op f t)). Qed.
Lemma lem6003988 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term13 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (term13 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem6003989 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term13 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f).
Proof. exact (SYM (@lem6003988 _120296 _120308 op s f h1)). Qed.
Lemma lem6003990 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem6003991 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f)) : (term13 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (SYM (@lem6003990 _120296 _120308 op s f h1)). Qed.
Lemma lem6003992 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term13 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f)).
Proof. exact (prop_ext (fun h1 : (term13 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f) => @lem6003989 _120296 _120308 op s f h1) (fun h1 : (@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f) => @lem6003991 _120296 _120308 op s f h1)). Qed.
Lemma lem6003993 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term14 _120296 _120308 op f) = (term15 _120296 _120308 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem6003992 _120296 _120308 op s f)). Qed.
Lemma lem6003994 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem6003995 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term16 _120296 _120308 op f) = (term17 _120296 _120308 op f).
Proof. exact (MK_COMB (@lem6003994 _120308) (@lem6003993 _120296 _120308 op f)). Qed.
Lemma lem6003996 {_120296 _120308 : Type'} (op : type1400 _120296) : (term18 _120296 _120308 op) = (term19 _120296 _120308 op).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem6003995 _120296 _120308 op f)). Qed.
Lemma lem6003997 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem6003998 {_120296 _120308 : Type'} (op : type1400 _120296) : (term20 _120296 _120308 op) = (term21 _120296 _120308 op).
Proof. exact (MK_COMB (@lem6003997 _120296 _120308) (@lem6003996 _120296 _120308 op)). Qed.
Lemma lem6003999 {_120296 _120308 : Type'} : (term22 _120296 _120308) = (term23 _120296 _120308).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem6003998 _120296 _120308 op)). Qed.
Lemma lem6004000 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem6004001 {_120296 _120308 : Type'} : (term24 _120296 _120308) = (term25 _120296 _120308).
Proof. exact (MK_COMB (@lem6004000 _120296) (@lem6003999 _120296 _120308)). Qed.
Lemma lem6004002 {_120296 _120308 : Type'} : term25 _120296 _120308.
Proof. exact (EQ_MP (@lem6004001 _120296 _120308) (@lem5737860 _120296 _120308)). Qed.
Lemma lem6004003 {_120296 _120308 : Type'} (op : type1400 _120296) : term26 _120296 _120308 op.
Proof. exact (@lem6004002 _120296 _120308 op). Qed.
Lemma lem6004004 {_120296 _120308 : Type'} (op : type1400 _120296) : (term26 _120296 _120308 op) = (term21 _120296 _120308 op).
Proof. exact (eq_refl (term26 _120296 _120308 op)). Qed.
Lemma lem6004005 {_120296 _120308 : Type'} (op : type1400 _120296) : term21 _120296 _120308 op.
Proof. exact (EQ_MP (@lem6004004 _120296 _120308 op) (@lem6004003 _120296 _120308 op)). Qed.
Lemma lem6004006 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term27 _120296 _120308 op f.
Proof. exact (@lem6004005 _120296 _120308 op f). Qed.
Lemma lem6004007 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term27 _120296 _120308 op f) = (term17 _120296 _120308 op f).
Proof. exact (eq_refl (term27 _120296 _120308 op f)). Qed.
Lemma lem6004008 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term17 _120296 _120308 op f.
Proof. exact (EQ_MP (@lem6004007 _120296 _120308 op f) (@lem6004006 _120296 _120308 op f)). Qed.
Lemma lem6004009 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : term28 _120296 _120308 op f s.
Proof. exact (@lem6004008 _120296 _120308 op f s). Qed.
Lemma lem6004010 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (term28 _120296 _120308 op f s) = ((@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f)).
Proof. exact (eq_refl (term28 _120296 _120308 op f s)). Qed.
Lemma lem6004012 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6004013 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term29 A B s t f op) : term29 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004014 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term30 A B s t f op) : term30 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004015 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6004016 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term31 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004017 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem6004021 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6004010 _120296 _120308 op s f) (@lem6004009 _120296 _120308 op f s)). Qed.
Lemma lem6004022 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term32 A B op s f).
Proof. exact (@lem6004021 B A op s f). Qed.
Lemma lem6004023 {A B : Type'} (op : type1400 B) (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term33 A B op s t f) = (term34 A B op s t f).
Proof. exact (@lem6004022 A B op (@UNION A s t) f). Qed.
Lemma lem6004024 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6004025 {A B : Type'} (op : type1400 B) (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term35 A B op s t f) = (term36 A B op s t f).
Proof. exact (MK_COMB (@lem6004024 B) (@lem6004023 A B op s t f)). Qed.
Lemma lem6004027 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6004010 _120296 _120308 op s f) (@lem6004009 _120296 _120308 op f s)). Qed.
Lemma lem6004028 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term32 A B op s f).
Proof. exact (@lem6004027 B A op s f). Qed.
Lemma lem6004029 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6004030 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term37 A B op s f) = (term38 A B op s f).
Proof. exact (MK_COMB (@lem6004029 B op) (@lem6004028 A B op s f)). Qed.
Lemma lem6004032 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term13 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6004010 _120296 _120308 op s f) (@lem6004009 _120296 _120308 op f s)). Qed.
Lemma lem6004033 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term32 A B op s f).
Proof. exact (@lem6004032 B A op s f). Qed.
Lemma lem6004034 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (@iterate B A op t f) = (term32 A B op t f).
Proof. exact (@lem6004033 A B op t f). Qed.
Lemma lem6004035 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term39 A B s op t f) = (term40 A B s op t f).
Proof. exact (MK_COMB (@lem6004030 A B op s f) (@lem6004034 A B op t f)). Qed.
Lemma lem6004036 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : ((term33 A B op s t f) = (term39 A B s op t f)) = ((term34 A B op s t f) = (term40 A B s op t f)).
Proof. exact (MK_COMB (@lem6004025 A B op s t f) (@lem6004035 A B s op t f)). Qed.
Lemma lem6004037 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : ((term34 A B op s t f) = (term40 A B s op t f)) = ((term33 A B op s t f) = (term39 A B s op t f)).
Proof. exact (SYM (@lem6004036 A B s op t f)). Qed.
Lemma lem6004041 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) (t : _120082 -> Prop) : (term11 _120082 _120196 op f s t) = (term12 _120082 _120196 s op f t).
Proof. exact (EQ_MP (@lem6003959 _120082 _120196 s op f t) (@lem6003958 _120082 _120196 s op f t)). Qed.
Lemma lem6004042 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term11 A B op f s t) = (term12 A B s op f t).
Proof. exact (@lem6004041 A B s op f t). Qed.
Lemma lem6004043 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem6004044 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term41 A B op f s t) = (term42 A B s op f t).
Proof. exact (MK_COMB (@lem6004043 A B op) (@lem6004042 A B s op f t)). Qed.
Lemma lem6004045 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6004046 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term34 A B op s t f) = (term43 A B s op t f).
Proof. exact (MK_COMB (@lem6004044 A B s op f t) (@lem6004045 A B f)). Qed.
Lemma lem6004047 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem6004048 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term36 A B op s t f) = (term44 A B s op t f).
Proof. exact (MK_COMB (@lem6004047 B) (@lem6004046 A B s op t f)). Qed.
Lemma lem6004049 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term40 A B s op t f) = (term40 A B s op t f).
Proof. exact (eq_refl (term40 A B s op t f)). Qed.
Lemma lem6004050 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : ((term34 A B op s t f) = (term40 A B s op t f)) = ((term43 A B s op t f) = (term40 A B s op t f)).
Proof. exact (MK_COMB (@lem6004048 A B s op t f) (@lem6004049 A B s op t f)). Qed.
Lemma lem6004053 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : ((term43 A B s op t f) = (term40 A B s op t f)) = ((term34 A B op s t f) = (term40 A B s op t f)).
Proof. exact (SYM (@lem6004050 A B s op t f)). Qed.
Lemma lem6004061 {_120592 _120607 : Type'} (op : type1400 _120607) : term1 _120592 _120607 op.
Proof. exact (EQ_MP (@lem6003914 _120592 _120607 op) (@lem6003913 _120592 _120607 op)). Qed.
Lemma lem6004062 {_120592 B : Type'} (op : type1400 B) : term1 _120592 B op.
Proof. exact (@lem6004061 _120592 B op). Qed.
Lemma lem6004063 {_120592 B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term45 _120592 B op.
Proof. exact (@lem6004062 _120592 B op (@lem6004012 B op h1)). Qed.
Lemma lem6004064 {_120592 B : Type'} (op : type1400 B) (h1 : term45 _120592 B op) : term45 _120592 B op.
Proof. exact (h1). Qed.
Lemma lem6004065 {_120592 B : Type'} (f : _120592 -> B) (op : type1400 B) (h1 : term45 _120592 B op) : term46 _120592 B op f.
Proof. exact (@lem6004064 _120592 B op h1 f). Qed.
Lemma lem6004066 {_120592 B : Type'} (op : type1400 B) (f : _120592 -> B) : (term46 _120592 B op f) = (term47 _120592 B op f).
Proof. exact (eq_refl (term46 _120592 B op f)). Qed.
Lemma lem6004067 {_120592 B : Type'} (f : _120592 -> B) (op : type1400 B) (h1 : term45 _120592 B op) : term47 _120592 B op f.
Proof. exact (EQ_MP (@lem6004066 _120592 B op f) (@lem6004065 _120592 B f op h1)). Qed.
Lemma lem6004068 {_120592 B : Type'} (f : _120592 -> B) (s : _120592 -> Prop) (op : type1400 B) (h1 : term45 _120592 B op) : term48 _120592 B op f s.
Proof. exact (@lem6004067 _120592 B f op h1 s). Qed.
Lemma lem6004069 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (f : _120592 -> B) : (term48 _120592 B op f s) = (term49 _120592 B s op f).
Proof. exact (eq_refl (term48 _120592 B op f s)). Qed.
Lemma lem6004070 {_120592 B : Type'} (s : _120592 -> Prop) (f : _120592 -> B) (op : type1400 B) (h1 : term45 _120592 B op) : term49 _120592 B s op f.
Proof. exact (EQ_MP (@lem6004069 _120592 B s op f) (@lem6004068 _120592 B f s op h1)). Qed.
Lemma lem6004071 {_120592 B : Type'} (s : _120592 -> Prop) (f : _120592 -> B) (t : _120592 -> Prop) (op : type1400 B) (h1 : term45 _120592 B op) : term50 _120592 B s op f t.
Proof. exact (@lem6004070 _120592 B s f op h1 t). Qed.
Lemma lem6004072 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (t : _120592 -> Prop) (f : _120592 -> B) : (term50 _120592 B s op f t) = (term51 _120592 B s op t f).
Proof. exact (eq_refl (term50 _120592 B s op f t)). Qed.
Lemma lem6004073 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) (op : type1400 B) (h1 : term45 _120592 B op) : term51 _120592 B s op t f.
Proof. exact (EQ_MP (@lem6004072 _120592 B s op t f) (@lem6004071 _120592 B s f t op h1)). Qed.
Lemma lem6004074 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term52 _120592 s t) : term52 _120592 s t.
Proof. exact (h1). Qed.
Lemma lem6004075 {_120592 B : Type'} (f : _120592 -> B) (op : type1400 B) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term45 _120592 B op) (h2 : term52 _120592 s t) : (term33 _120592 B op s t f) = (term39 _120592 B s op t f).
Proof. exact (@lem6004073 _120592 B s t f op h1 (@lem6004074 _120592 s t h2)). Qed.
Lemma lem6004076 {_120592 B : Type'} (op : type1400 B) (f : _120592 -> B) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term52 _120592 s t) : term53 _120592 B s op t f.
Proof. exact (fun h0 : term45 _120592 B op => @lem6004075 _120592 B f op s t h0 h1). Qed.
Lemma lem6004077 {_120592 B : Type'} (op : type1400 B) (h1 : term45 _120592 B op) : term45 _120592 B op.
Proof. exact (h1). Qed.
Lemma lem6004078 {_120592 B : Type'} (f : _120592 -> B) (op : type1400 B) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term45 _120592 B op) (h2 : term52 _120592 s t) : (term33 _120592 B op s t f) = (term39 _120592 B s op t f).
Proof. exact (@lem6004076 _120592 B op f s t h2 (@lem6004077 _120592 B op h1)). Qed.
Lemma lem6004079 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) (op : type1400 B) (h1 : term45 _120592 B op) : term51 _120592 B s op t f.
Proof. exact (fun h0 : term52 _120592 s t => @lem6004078 _120592 B f op s t h1 h0). Qed.
Lemma lem6004080 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (op : type1400 B) (h1 : term45 _120592 B op) : term54 _120592 B s op t.
Proof. exact (fun f : _120592 -> B => @lem6004079 _120592 B s t f op h1). Qed.
Lemma lem6004081 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (h1 : term45 _120592 B op) : term55 _120592 B s op.
Proof. exact (fun t : _120592 -> Prop => @lem6004080 _120592 B s t op h1). Qed.
Lemma lem6004082 {_120592 B : Type'} (op : type1400 B) (h1 : term45 _120592 B op) : term56 _120592 B op.
Proof. exact (fun s : _120592 -> Prop => @lem6004081 _120592 B s op h1). Qed.
Lemma lem6004083 {_120592 B : Type'} (op : type1400 B) : term57 _120592 B op.
Proof. exact (fun h0 : term45 _120592 B op => @lem6004082 _120592 B op h0). Qed.
Lemma lem6004084 {_120592 B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term56 _120592 B op.
Proof. exact (@lem6004083 _120592 B op (@lem6004063 _120592 B op h1)). Qed.
Lemma lem6004085 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term58 _120592 B op s.
Proof. exact (@lem6004084 _120592 B op h1 s). Qed.
Lemma lem6004086 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) : (term58 _120592 B op s) = (term55 _120592 B s op).
Proof. exact (eq_refl (term58 _120592 B op s)). Qed.
Lemma lem6004087 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term55 _120592 B s op.
Proof. exact (EQ_MP (@lem6004086 _120592 B s op) (@lem6004085 _120592 B s op h1)). Qed.
Lemma lem6004088 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term59 _120592 B s op t.
Proof. exact (@lem6004087 _120592 B s op h1 t). Qed.
Lemma lem6004089 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (t : _120592 -> Prop) : (term59 _120592 B s op t) = (term54 _120592 B s op t).
Proof. exact (eq_refl (term59 _120592 B s op t)). Qed.
Lemma lem6004090 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term54 _120592 B s op t.
Proof. exact (EQ_MP (@lem6004089 _120592 B s op t) (@lem6004088 _120592 B s t op h1)). Qed.
Lemma lem6004091 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) (op : type1400 B) (h1 : @monoidal B op) : term60 _120592 B s op t f.
Proof. exact (@lem6004090 _120592 B s t op h1 f). Qed.
Lemma lem6004092 {_120592 B : Type'} (s : _120592 -> Prop) (op : type1400 B) (t : _120592 -> Prop) (f : _120592 -> B) : (term60 _120592 B s op t f) = (term51 _120592 B s op t f).
Proof. exact (eq_refl (term60 _120592 B s op t f)). Qed.
Lemma lem6004095 {_120592 B : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> B) (op : type1400 B) (h1 : @monoidal B op) : term51 _120592 B s op t f.
Proof. exact (EQ_MP (@lem6004092 _120592 B s op t f) (@lem6004091 _120592 B s t f op h1)). Qed.
Lemma lem6004096 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term51 A B s op t f.
Proof. exact (@lem6004095 A B s t f op h1). Qed.
Lemma lem6004097 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term61 A B s op t f.
Proof. exact (@lem6004096 A B (@support A B op f s) (@support A B op f t) f op h1). Qed.
Lemma lem6004098 {A : Type'} (s : A -> Prop) : term62 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem6004099 {A : Type'} (s : A -> Prop) : (term62 A s) = (term63 A s).
Proof. exact (eq_refl (term62 A s)). Qed.
Lemma lem6004100 {A : Type'} (s : A -> Prop) : term63 A s.
Proof. exact (EQ_MP (@lem6004099 A s) (@lem6004098 A s)). Qed.
Lemma lem6004101 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term64 A s t.
Proof. exact (@lem6004100 A s t). Qed.
Lemma lem6004102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = ((s = t) = (term65 A s t)).
Proof. exact (eq_refl (term64 A s t)). Qed.
Lemma lem6004104 {_119826 _119829 : Type'} (op : type1400 _119826) : term66 _119826 _119829 op.
Proof. exact (@lem5718201 _119826 _119829 op). Qed.
Lemma lem6004105 {_119826 _119829 : Type'} (op : type1400 _119826) : (term66 _119826 _119829 op) = (term67 _119826 _119829 op).
Proof. exact (eq_refl (term66 _119826 _119829 op)). Qed.
Lemma lem6004106 {_119826 _119829 : Type'} (op : type1400 _119826) : term67 _119826 _119829 op.
Proof. exact (EQ_MP (@lem6004105 _119826 _119829 op) (@lem6004104 _119826 _119829 op)). Qed.
Lemma lem6004107 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : term68 _119826 _119829 op f.
Proof. exact (@lem6004106 _119826 _119829 op f). Qed.
Lemma lem6004108 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : (term68 _119826 _119829 op f) = (term69 _119826 _119829 f op).
Proof. exact (eq_refl (term68 _119826 _119829 op f)). Qed.
Lemma lem6004109 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : term69 _119826 _119829 f op.
Proof. exact (EQ_MP (@lem6004108 _119826 _119829 f op) (@lem6004107 _119826 _119829 op f)). Qed.
Lemma lem6004110 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) (x : _119829) : term70 _119826 _119829 f op x.
Proof. exact (@lem6004109 _119826 _119829 f op x). Qed.
Lemma lem6004111 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term70 _119826 _119829 f op x) = (term71 _119826 _119829 f x op).
Proof. exact (eq_refl (term70 _119826 _119829 f op x)). Qed.
Lemma lem6004112 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : term71 _119826 _119829 f x op.
Proof. exact (EQ_MP (@lem6004111 _119826 _119829 f x op) (@lem6004110 _119826 _119829 f op x)). Qed.
Lemma lem6004113 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) (s : _119829 -> Prop) : term72 _119826 _119829 f x op s.
Proof. exact (@lem6004112 _119826 _119829 f x op s). Qed.
Lemma lem6004114 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term72 _119826 _119829 f x op s) = ((term73 _119826 _119829 x op f s) = (term74 _119826 _119829 s f x op)).
Proof. exact (eq_refl (term72 _119826 _119829 f x op s)). Qed.
Lemma lem6004116 {A : Type'} (s : A -> Prop) : term75 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem6004117 {A : Type'} (s : A -> Prop) : (term75 A s) = (term76 A s).
Proof. exact (eq_refl (term75 A s)). Qed.
Lemma lem6004118 {A : Type'} (s : A -> Prop) : term76 A s.
Proof. exact (EQ_MP (@lem6004117 A s) (@lem6004116 A s)). Qed.
Lemma lem6004119 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term77 A s t.
Proof. exact (@lem6004118 A s t). Qed.
Lemma lem6004120 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term78 A s t).
Proof. exact (eq_refl (term77 A s t)). Qed.
Lemma lem6004121 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term78 A s t.
Proof. exact (EQ_MP (@lem6004120 A s t) (@lem6004119 A s t)). Qed.
Lemma lem6004122 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term79 A s t x.
Proof. exact (@lem6004121 A s t x). Qed.
Lemma lem6004123 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term79 A s t x) = ((term80 A x s t) = (term81 A s x t)).
Proof. exact (eq_refl (term79 A s t x)). Qed.
Lemma lem6004125 {A : Type'} (s : A -> Prop) : term82 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem6004126 {A : Type'} (s : A -> Prop) : (term82 A s) = (term83 A s).
Proof. exact (eq_refl (term82 A s)). Qed.
Lemma lem6004127 {A : Type'} (s : A -> Prop) : term83 A s.
Proof. exact (EQ_MP (@lem6004126 A s) (@lem6004125 A s)). Qed.
Lemma lem6004128 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term84 A s t.
Proof. exact (@lem6004127 A s t). Qed.
Lemma lem6004129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term84 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term84 A s t)). Qed.
Lemma lem6004131 {_119939 _119945 : Type'} (op : type1400 _119945) : term85 _119939 _119945 op.
Proof. exact (@lem5720601 _119939 _119945 op). Qed.
Lemma lem6004132 {_119939 _119945 : Type'} (op : type1400 _119945) : (term85 _119939 _119945 op) = (term86 _119939 _119945 op).
Proof. exact (eq_refl (term85 _119939 _119945 op)). Qed.
Lemma lem6004133 {_119939 _119945 : Type'} (op : type1400 _119945) : term86 _119939 _119945 op.
Proof. exact (EQ_MP (@lem6004132 _119939 _119945 op) (@lem6004131 _119939 _119945 op)). Qed.
Lemma lem6004134 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : term87 _119939 _119945 op f.
Proof. exact (@lem6004133 _119939 _119945 op f). Qed.
Lemma lem6004135 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term87 _119939 _119945 op f) = (term88 _119939 _119945 op f).
Proof. exact (eq_refl (term87 _119939 _119945 op f)). Qed.
Lemma lem6004136 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : term88 _119939 _119945 op f.
Proof. exact (EQ_MP (@lem6004135 _119939 _119945 op f) (@lem6004134 _119939 _119945 op f)). Qed.
Lemma lem6004137 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term89 _119939 _119945 op f s.
Proof. exact (@lem6004136 _119939 _119945 op f s). Qed.
Lemma lem6004138 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term89 _119939 _119945 op f s) = (term90 _119939 _119945 op f s).
Proof. exact (eq_refl (term89 _119939 _119945 op f s)). Qed.
Lemma lem6004139 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term90 _119939 _119945 op f s.
Proof. exact (EQ_MP (@lem6004138 _119939 _119945 op f s) (@lem6004137 _119939 _119945 op f s)). Qed.
Lemma lem6004140 {_119939 : Type'} (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : @FINITE _119939 s.
Proof. exact (h1). Qed.
Lemma lem6004141 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : term91 _119939 _119945 op f s.
Proof. exact (@lem6004139 _119939 _119945 op f s (@lem6004140 _119939 s h1)). Qed.
Lemma lem6004142 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term91 _119939 _119945 op f s) = ((term91 _119939 _119945 op f s) = True).
Proof. exact (@lem7 (term91 _119939 _119945 op f s)). Qed.
Lemma lem6004143 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : (term91 _119939 _119945 op f s) = True.
Proof. exact (EQ_MP (@lem6004142 _119939 _119945 op f s) (@lem6004141 _119939 _119945 op f s h1)). Qed.
Lemma lem6004151 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6004153 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem6004168 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term92 _119939 _119945 op f s.
Proof. exact (fun h0 : @FINITE _119939 s => @lem6004143 _119939 _119945 op f s h0). Qed.
Lemma lem6004169 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term92 A B op f s.
Proof. exact (@lem6004168 A B op f s). Qed.
Lemma lem6004171 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6004151 A s) (@lem6004015 A s h1)). Qed.
Lemma lem6004172 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6004171 A s h1)). Qed.
Lemma lem6004173 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6004172 A s h1) (@lem0)). Qed.
Lemma lem6004174 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term91 A B op f s) = True.
Proof. exact (@lem6004169 A B op f s (@lem6004173 A s h1)). Qed.
Lemma lem6004175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6004176 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term93 A B op f s) = (and True).
Proof. exact (MK_COMB (@lem6004175) (@lem6004174 A B op f s h1)). Qed.
Lemma lem6004180 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term92 _119939 _119945 op f s.
Proof. exact (fun h0 : @FINITE _119939 s => @lem6004143 _119939 _119945 op f s h0). Qed.
Lemma lem6004181 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term92 A B op f s.
Proof. exact (@lem6004180 A B op f s). Qed.
Lemma lem6004182 {A B : Type'} (op : type1400 B) (f : A -> B) (t : A -> Prop) : term92 A B op f t.
Proof. exact (@lem6004181 A B op f t). Qed.
Lemma lem6004184 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem6004153 A t) (@lem6004017 A t h1)). Qed.
Lemma lem6004185 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : True = (@FINITE A t).
Proof. exact (SYM (@lem6004184 A t h1)). Qed.
Lemma lem6004186 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (EQ_MP (@lem6004185 A t h1) (@lem0)). Qed.
Lemma lem6004187 {A B : Type'} (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @FINITE A t) : (term91 A B op f t) = True.
Proof. exact (@lem6004182 A B op f t (@lem6004186 A t h1)). Qed.
Lemma lem6004188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6004189 {A B : Type'} (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @FINITE A t) : (term93 A B op f t) = (and True).
Proof. exact (MK_COMB (@lem6004188) (@lem6004187 A B op f t h1)). Qed.
Lemma lem6004191 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem6004129 A s t) (@lem6004128 A s t)). Qed.
Lemma lem6004192 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem6004191 A s t). Qed.
Lemma lem6004193 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term94 A B s op f t) = ((term95 A B s op f t) = (@EMPTY A)).
Proof. exact (@lem6004192 A (@support A B op f s) (@support A B op f t)). Qed.
Lemma lem6004197 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term65 A s t).
Proof. exact (EQ_MP (@lem6004102 A s t) (@lem6004101 A s t)). Qed.
Lemma lem6004198 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term65 A s t).
Proof. exact (@lem6004197 A s t). Qed.
Lemma lem6004199 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : ((term95 A B s op f t) = (@EMPTY A)) = (term96 A B s op f t).
Proof. exact (@lem6004198 A (term95 A B s op f t) (@EMPTY A)). Qed.
Lemma lem6004209 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term80 A x s t) = (term81 A s x t).
Proof. exact (EQ_MP (@lem6004123 A s x t) (@lem6004122 A s t x)). Qed.
Lemma lem6004210 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term80 A x s t) = (term81 A s x t).
Proof. exact (@lem6004209 A s x t). Qed.
Lemma lem6004211 {A B : Type'} (s : A -> Prop) (x : A) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term97 A B x s op f t) = (term98 A B s x op f t).
Proof. exact (@lem6004210 A (@support A B op f s) x (@support A B op f t)). Qed.
Lemma lem6004215 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term73 _119826 _119829 x op f s) = (term74 _119826 _119829 s f x op).
Proof. exact (EQ_MP (@lem6004114 _119826 _119829 s f x op) (@lem6004113 _119826 _119829 f x op s)). Qed.
Lemma lem6004216 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term99 A B x op f s) = (term100 A B s f x op).
Proof. exact (@lem6004215 B A s f x op). Qed.
Lemma lem6004232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6004233 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term101 A B x op f s) = (term102 A B s f x op).
Proof. exact (MK_COMB (@lem6004232) (@lem6004216 A B s f x op)). Qed.
Lemma lem6004250 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term73 _119826 _119829 x op f s) = (term74 _119826 _119829 s f x op).
Proof. exact (EQ_MP (@lem6004114 _119826 _119829 s f x op) (@lem6004113 _119826 _119829 f x op s)). Qed.
Lemma lem6004251 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term99 A B x op f s) = (term100 A B s f x op).
Proof. exact (@lem6004250 B A s f x op). Qed.
Lemma lem6004252 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term99 A B x op f t) = (term100 A B t f x op).
Proof. exact (@lem6004251 A B t f x op). Qed.
Lemma lem6004268 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term98 A B s x op f t) = (term103 A B s t f x op).
Proof. exact (MK_COMB (@lem6004233 A B s f x op) (@lem6004252 A B t f x op)). Qed.
Lemma lem6004301 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term97 A B x s op f t) = (term103 A B s t f x op).
Proof. exact (TRANS (@lem6004211 A B s x op f t) (@lem6004268 A B s t f x op)). Qed.
Lemma lem6004302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6004303 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term104 A B x s op f t) = (term105 A B s t f x op).
Proof. exact (MK_COMB (@lem6004302) (@lem6004301 A B s t f x op)). Qed.
Lemma lem6004336 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (@IN A x (@EMPTY A))). Qed.
Lemma lem6004337 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : ((term97 A B x s op f t) = (@IN A x (@EMPTY A))) = ((term103 A B s t f x op) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem6004303 A B s t f x op) (@lem6004336 A x)). Qed.
Lemma lem6004374 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term106 A B s op f t) = (term107 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6004337 A B s t f op x)). Qed.
Lemma lem6004411 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6004412 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term96 A B s op f t) = (term108 A B s t f op).
Proof. exact (MK_COMB (@lem6004411 A) (@lem6004374 A B s t f op)). Qed.
Lemma lem6004453 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : ((term95 A B s op f t) = (@EMPTY A)) = (term108 A B s t f op).
Proof. exact (TRANS (@lem6004199 A B s op f t) (@lem6004412 A B s t f op)). Qed.
Lemma lem6004454 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term94 A B s op f t) = (term108 A B s t f op).
Proof. exact (TRANS (@lem6004193 A B s op f t) (@lem6004453 A B s t f op)). Qed.
Lemma lem6004455 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @FINITE A t) : (term109 A B s op f t) = (term110 A B s t f op).
Proof. exact (MK_COMB (@lem6004189 A B op f t h1) (@lem6004454 A B s t f op)). Qed.
Lemma lem6004457 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6004458 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term110 A B s t f op) = (term108 A B s t f op).
Proof. exact (@lem6004457 (term108 A B s t f op)). Qed.
Lemma lem6004499 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @FINITE A t) : (term109 A B s op f t) = (term108 A B s t f op).
Proof. exact (TRANS (@lem6004455 A B s f op t h1) (@lem6004458 A B s t f op)). Qed.
Lemma lem6004500 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term111 A B s op f t) = (term110 A B s t f op).
Proof. exact (MK_COMB (@lem6004176 A B op f s h1) (@lem6004499 A B s f op t h2)). Qed.
Lemma lem6004502 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6004503 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term110 A B s t f op) = (term108 A B s t f op).
Proof. exact (@lem6004502 (term108 A B s t f op)). Qed.
Lemma lem6004544 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term111 A B s op f t) = (term108 A B s t f op).
Proof. exact (TRANS (@lem6004500 A B f op s t h1 h2) (@lem6004503 A B s t f op)). Qed.
Lemma lem6004545 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term108 A B s t f op) = (term111 A B s op f t).
Proof. exact (SYM (@lem6004544 A B f op s t h1 h2)). Qed.
Lemma lem6004547 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6004548 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term108 A B s t f op) = (term113 A B s t f op).
Proof. exact (@lem6004547 (term108 A B s t f op)). Qed.
Lemma lem6004549 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term113 A B s t f op) = (term108 A B s t f op).
Proof. exact (SYM (@lem6004548 A B s t f op)). Qed.
Lemma lem6004550 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term114 A B s t f op) : term114 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004551 {A : Type'} : term115 A.
Proof. exact (@lem3205222 A). Qed.
Lemma lem6004553 {A : Type'} : term116 A.
Proof. exact (@lem3204775 A). Qed.
Lemma lem6004557 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term117 A B s t f op) : term117 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004558 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term118 A B s t f op.
Proof. exact (fun h0 : term117 A B s t f op => @lem6004557 A B s t f op h0). Qed.
Lemma lem6004559 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term118 A B s t f op) : term118 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004560 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term117 A B s t f op) : term117 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004561 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term117 A B s t f op) (h2 : term118 A B s t f op) : term117 A B s t f op.
Proof. exact (@lem6004559 A B s t f op h2 (@lem6004560 A B s t f op h1)). Qed.
Lemma lem6004562 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term117 A B s t f op) : term119 A B s t f op.
Proof. exact (fun h0 : term118 A B s t f op => @lem6004561 A B s t f op h1 h0). Qed.
Lemma lem6004563 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term118 A B s t f op) : term118 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004564 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term117 A B s t f op) (h2 : term118 A B s t f op) : term117 A B s t f op.
Proof. exact (@lem6004562 A B s t f op h1 (@lem6004563 A B s t f op h2)). Qed.
Lemma lem6004565 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term118 A B s t f op) : term118 A B s t f op.
Proof. exact (fun h0 : term117 A B s t f op => @lem6004564 A B s t f op h0 h1). Qed.
Lemma lem6004566 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term120 A B s t f op.
Proof. exact (fun h0 : term118 A B s t f op => @lem6004565 A B s t f op h0). Qed.
Lemma lem6004569 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term118 A B s t f op.
Proof. exact (@lem6004566 A B s t f op (@lem6004558 A B s t f op)). Qed.
Lemma lem6004570 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term118 A B s t f op.
Proof. exact (@lem6004569 A B s t f op). Qed.
Lemma lem6004620 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6004621 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (@lem6004620 (term115 A)). Qed.
Lemma lem6004636 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem6004637 {A : Type'} : (term124 A) = (term125 A).
Proof. exact (MK_COMB (@lem6004636 A) (@lem6004621 A)). Qed.
Lemma lem6004640 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term126 A B s t f op) = (term126 A B s t f op).
Proof. exact (eq_refl (term126 A B s t f op)). Qed.
Lemma lem6004641 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term127 A B s t f op) = (term128 A B s t f op).
Proof. exact (MK_COMB (@lem6004640 A B s t f op) (@lem6004637 A)). Qed.
Lemma lem6004644 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term129 A B s t f op) = (term129 A B s t f op).
Proof. exact (eq_refl (term129 A B s t f op)). Qed.
Lemma lem6004645 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term130 A B s t f op) = (term131 A B s t f op).
Proof. exact (MK_COMB (@lem6004644 A B s t f op) (@lem6004641 A B s t f op)). Qed.
Lemma lem6004648 {A : Type'} (t : A -> Prop) : (term132 A t) = (term132 A t).
Proof. exact (eq_refl (term132 A t)). Qed.
Lemma lem6004649 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term133 A B s t f op) = (term134 A B s t f op).
Proof. exact (MK_COMB (@lem6004648 A t) (@lem6004645 A B s t f op)). Qed.
Lemma lem6004652 {A : Type'} (s : A -> Prop) : (term132 A s) = (term132 A s).
Proof. exact (eq_refl (term132 A s)). Qed.
Lemma lem6004653 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term135 A B s t f op) = (term136 A B s t f op).
Proof. exact (MK_COMB (@lem6004652 A s) (@lem6004649 A B s t f op)). Qed.
Lemma lem6004656 {B : Type'} (op : type1400 B) : (term137 B op) = (term137 B op).
Proof. exact (eq_refl (term137 B op)). Qed.
Lemma lem6004657 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term117 A B s t f op) = (term138 A B s t f op).
Proof. exact (MK_COMB (@lem6004656 B op) (@lem6004653 A B s t f op)). Qed.
Lemma lem6004660 {A B : Type'} (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term139 A B t f op) = (term140 A B t f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6004657 A B s t f op)). Qed.
Lemma lem6004661 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6004662 {A B : Type'} (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term141 A B t f op) = (term142 A B t f op).
Proof. exact (MK_COMB (@lem6004661 A) (@lem6004660 A B t f op)). Qed.
Lemma lem6004667 {A B : Type'} (f : A -> B) (op : type1400 B) : (term143 A B f op) = (term144 A B f op).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6004662 A B t f op)). Qed.
Lemma lem6004668 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6004669 {A B : Type'} (f : A -> B) (op : type1400 B) : (term145 A B f op) = (term146 A B f op).
Proof. exact (MK_COMB (@lem6004668 A) (@lem6004667 A B f op)). Qed.
Lemma lem6004674 {A B : Type'} (op : type1400 B) : (term147 A B op) = (term148 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6004669 A B f op)). Qed.
Lemma lem6004675 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6004676 {A B : Type'} (op : type1400 B) : (term149 A B op) = (term150 A B op).
Proof. exact (MK_COMB (@lem6004675 A B) (@lem6004674 A B op)). Qed.
Lemma lem6004681 {A B : Type'} : (term151 A B) = (term152 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6004676 A B op)). Qed.
Lemma lem6004682 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6004691 {A B : Type'} : (term153 A B) = (term154 A B).
Proof. exact (MK_COMB (@lem6004682 B) (@lem6004681 A B)). Qed.
Lemma lem6004700 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term80 A x s t) = (term81 A s x t)) = ((term80 A x s t) = (term81 A s x t)).
Proof. exact (eq_refl ((term80 A x s t) = (term81 A s x t))). Qed.
Lemma lem6004701 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term155 A s t) = (term155 A s t).
Proof. exact (fun_ext (fun x : A => @lem6004700 A s x t)). Qed.
Lemma lem6004702 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6004703 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (MK_COMB (@lem6004702 A) (@lem6004701 A s t)). Qed.
Lemma lem6004704 {A : Type'} (s : A -> Prop) : (term156 A s) = (term156 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6004703 A s t)). Qed.
Lemma lem6004705 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6004706 {A : Type'} (s : A -> Prop) : (term76 A s) = (term76 A s).
Proof. exact (MK_COMB (@lem6004705 A) (@lem6004704 A s)). Qed.
Lemma lem6004707 {A : Type'} : (term157 A) = (term157 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6004706 A s)). Qed.
Lemma lem6004708 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6004709 {A : Type'} : (term115 A) = (term115 A).
Proof. exact (MK_COMB (@lem6004708 A) (@lem6004707 A)). Qed.
Lemma lem6004710 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6004711 {A : Type'} : (term122 A) = (term122 A).
Proof. exact (MK_COMB (@lem6004710) (@lem6004709 A)). Qed.
Lemma lem6004714 {A : Type'} (x : A) : (term158 A x) = (term158 A x).
Proof. exact (eq_refl (term158 A x)). Qed.
Lemma lem6004715 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (fun_ext (fun x : A => @lem6004714 A x)). Qed.
Lemma lem6004716 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6004717 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem6004716 A) (@lem6004715 A)). Qed.
Lemma lem6004718 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6004719 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem6004718) (@lem6004717 A)). Qed.
Lemma lem6004720 {A : Type'} : (term125 A) = (term125 A).
Proof. exact (MK_COMB (@lem6004719 A) (@lem6004711 A)). Qed.
Lemma lem6004741 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : ((term103 A B s t f x op) = (@IN A x (@EMPTY A))) = ((term103 A B s t f x op) = (@IN A x (@EMPTY A))).
Proof. exact (eq_refl ((term103 A B s t f x op) = (@IN A x (@EMPTY A)))). Qed.
Lemma lem6004742 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term107 A B s t f op) = (term107 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6004741 A B s t f op x)). Qed.
Lemma lem6004743 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6004744 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term108 A B s t f op) = (term108 A B s t f op).
Proof. exact (MK_COMB (@lem6004743 A) (@lem6004742 A B s t f op)). Qed.
Lemma lem6004745 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6004746 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term114 A B s t f op) = (term114 A B s t f op).
Proof. exact (MK_COMB (@lem6004745) (@lem6004744 A B s t f op)). Qed.
Lemma lem6004747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6004748 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term126 A B s t f op) = (term126 A B s t f op).
Proof. exact (MK_COMB (@lem6004747) (@lem6004746 A B s t f op)). Qed.
Lemma lem6004749 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term128 A B s t f op) = (term128 A B s t f op).
Proof. exact (MK_COMB (@lem6004748 A B s t f op) (@lem6004720 A)). Qed.
Lemma lem6004754 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term160 A B s t f x op) = (term160 A B s t f x op).
Proof. exact (eq_refl (term160 A B s t f x op)). Qed.
Lemma lem6004755 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term161 A B s t f op) = (term161 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6004754 A B s t f x op)). Qed.
Lemma lem6004756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6004757 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term31 A B s t f op) = (term31 A B s t f op).
Proof. exact (MK_COMB (@lem6004756 A) (@lem6004755 A B s t f op)). Qed.
Lemma lem6004758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6004759 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term129 A B s t f op) = (term129 A B s t f op).
Proof. exact (MK_COMB (@lem6004758) (@lem6004757 A B s t f op)). Qed.
Lemma lem6004760 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term131 A B s t f op) = (term131 A B s t f op).
Proof. exact (MK_COMB (@lem6004759 A B s t f op) (@lem6004749 A B s t f op)). Qed.
Lemma lem6004763 {A : Type'} (t : A -> Prop) : (term132 A t) = (term132 A t).
Proof. exact (eq_refl (term132 A t)). Qed.
Lemma lem6004764 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term134 A B s t f op) = (term134 A B s t f op).
Proof. exact (MK_COMB (@lem6004763 A t) (@lem6004760 A B s t f op)). Qed.
Lemma lem6004767 {A : Type'} (s : A -> Prop) : (term132 A s) = (term132 A s).
Proof. exact (eq_refl (term132 A s)). Qed.
Lemma lem6004768 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term136 A B s t f op) = (term136 A B s t f op).
Proof. exact (MK_COMB (@lem6004767 A s) (@lem6004764 A B s t f op)). Qed.
Lemma lem6004771 {B : Type'} (op : type1400 B) : (term137 B op) = (term137 B op).
Proof. exact (eq_refl (term137 B op)). Qed.
Lemma lem6004772 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term138 A B s t f op) = (term138 A B s t f op).
Proof. exact (MK_COMB (@lem6004771 B op) (@lem6004768 A B s t f op)). Qed.
Lemma lem6004773 {A B : Type'} (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term140 A B t f op) = (term140 A B t f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6004772 A B s t f op)). Qed.
Lemma lem6004774 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6004775 {A B : Type'} (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term142 A B t f op) = (term142 A B t f op).
Proof. exact (MK_COMB (@lem6004774 A) (@lem6004773 A B t f op)). Qed.
Lemma lem6004776 {A B : Type'} (f : A -> B) (op : type1400 B) : (term144 A B f op) = (term144 A B f op).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6004775 A B t f op)). Qed.
Lemma lem6004777 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6004778 {A B : Type'} (f : A -> B) (op : type1400 B) : (term146 A B f op) = (term146 A B f op).
Proof. exact (MK_COMB (@lem6004777 A) (@lem6004776 A B f op)). Qed.
Lemma lem6004779 {A B : Type'} (op : type1400 B) : (term148 A B op) = (term148 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem6004778 A B f op)). Qed.
Lemma lem6004780 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6004781 {A B : Type'} (op : type1400 B) : (term150 A B op) = (term150 A B op).
Proof. exact (MK_COMB (@lem6004780 A B) (@lem6004779 A B op)). Qed.
Lemma lem6004782 {A B : Type'} : (term152 A B) = (term152 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem6004781 A B op)). Qed.
Lemma lem6004783 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem6004784 {A B : Type'} : (term154 A B) = (term154 A B).
Proof. exact (MK_COMB (@lem6004783 B) (@lem6004782 A B)). Qed.
Lemma lem6004869 {A B : Type'} : (term153 A B) = (term154 A B).
Proof. exact (TRANS (@lem6004691 A B) (@lem6004784 A B)). Qed.
Lemma lem6004870 {A B : Type'} : (term154 A B) = (term153 A B).
Proof. exact (SYM (@lem6004869 A B)). Qed.
Lemma lem6004874 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term31 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004875 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term114 A B s t f op) : term114 A B s t f op.
Proof. exact (h1). Qed.
Lemma lem6004876 {A : Type'} (h1 : term116 A) : term116 A.
Proof. exact (h1). Qed.
Lemma lem6004877 {A : Type'} (h1 : term115 A) : term115 A.
Proof. exact (h1). Qed.
Lemma lem6004902 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term160 A B s t f x op) = (term162 A B s t f x op).
Proof. exact (@lem17265 (term80 A x s t) ((f x) = (@neutral B op))). Qed.
Lemma lem6004903 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term161 A B s t f op) = (term163 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6004902 A B s t f x op)). Qed.
Lemma lem6004904 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6004957 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term31 A B s t f op) = (term164 A B s t f op).
Proof. exact (MK_COMB (@lem6004904 A) (@lem6004903 A B s t f op)). Qed.
Lemma lem6004958 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term164 A B s t f op.
Proof. exact (EQ_MP (@lem6004957 A B s t f op) (@lem6004874 A B s t f op h1)). Qed.
Lemma lem6004964 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term165 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6004966 {A : Type'} (x : A) (s : A -> Prop) : (term166 A x s) = (term166 A x s).
Proof. exact (eq_refl (term166 A x s)). Qed.
Lemma lem6004967 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term167 A B s f x op) = (term168 A B s f x op).
Proof. exact (MK_COMB (@lem6004966 A x s) (@lem6004964 A B f x op)). Qed.
Lemma lem6004968 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B s f x op) = (term167 A B s f x op).
Proof. exact (@lem17045 (@IN A x s) (term170 A B f x op)). Qed.
Lemma lem6004969 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B s f x op) = (term168 A B s f x op).
Proof. exact (TRANS (@lem6004968 A B s f x op) (@lem6004967 A B s f x op)). Qed.
Lemma lem6004978 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term165 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem6004980 {A : Type'} (x : A) (t : A -> Prop) : (term166 A x t) = (term166 A x t).
Proof. exact (eq_refl (term166 A x t)). Qed.
Lemma lem6004981 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term167 A B t f x op) = (term168 A B t f x op).
Proof. exact (MK_COMB (@lem6004980 A x t) (@lem6004978 A B f x op)). Qed.
Lemma lem6004982 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B t f x op) = (term167 A B t f x op).
Proof. exact (@lem17045 (@IN A x t) (term170 A B f x op)). Qed.
Lemma lem6004983 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term169 A B t f x op) = (term168 A B t f x op).
Proof. exact (TRANS (@lem6004982 A B t f x op) (@lem6004981 A B t f x op)). Qed.
Lemma lem6004987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6004988 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term171 A B s f x op) = (term172 A B s f x op).
Proof. exact (MK_COMB (@lem6004987) (@lem6004969 A B s f x op)). Qed.
Lemma lem6004989 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term173 A B s t f x op) = (term174 A B s t f x op).
Proof. exact (MK_COMB (@lem6004988 A B s f x op) (@lem6004983 A B t f x op)). Qed.
Lemma lem6004990 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term175 A B s t f x op) = (term173 A B s t f x op).
Proof. exact (@lem17045 (term100 A B s f x op) (term100 A B t f x op)). Qed.
Lemma lem6004991 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term175 A B s t f x op) = (term174 A B s t f x op).
Proof. exact (TRANS (@lem6004990 A B s t f x op) (@lem6004989 A B s t f x op)). Qed.
Lemma lem6004996 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (@IN A x (@EMPTY A))). Qed.
Lemma lem6004997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6004998 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term176 A B s t f x op) = (term177 A B s t f x op).
Proof. exact (MK_COMB (@lem6004997) (@lem6004991 A B s t f x op)). Qed.
Lemma lem6004999 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term178 A B s t f op x) = (term179 A B s t f op x).
Proof. exact (MK_COMB (@lem6004998 A B s t f x op) (@lem6004996 A x)). Qed.
Lemma lem6005004 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term180 A B s t f op x) = (term180 A B s t f op x).
Proof. exact (eq_refl (term180 A B s t f op x)). Qed.
Lemma lem6005005 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term181 A B s t f op x) = (term182 A B s t f op x).
Proof. exact (MK_COMB (@lem6005004 A B s t f op x) (@lem6004999 A B s t f op x)). Qed.
Lemma lem6005006 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term183 A B s t f op x) = (term181 A B s t f op x).
Proof. exact (@lem17646 (term103 A B s t f x op) (@IN A x (@EMPTY A))). Qed.
Lemma lem6005007 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term183 A B s t f op x) = (term182 A B s t f op x).
Proof. exact (TRANS (@lem6005006 A B s t f op x) (@lem6005005 A B s t f op x)). Qed.
Lemma lem6005008 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6005009 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term114 A B s t f op) = (term186 A B s t f op).
Proof. exact (@lem6005008 A (term107 A B s t f op)). Qed.
Lemma lem6005010 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term187 A B s t f op x) = ((term103 A B s t f x op) = (@IN A x (@EMPTY A))).
Proof. exact (eq_refl (term187 A B s t f op x)). Qed.
Lemma lem6005011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6005012 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term188 A B s t f op x) = (term183 A B s t f op x).
Proof. exact (MK_COMB (@lem6005011) (@lem6005010 A B s t f op x)). Qed.
Lemma lem6005013 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term188 A B s t f op x) = (term182 A B s t f op x).
Proof. exact (TRANS (@lem6005012 A B s t f op x) (@lem6005007 A B s t f op x)). Qed.
Lemma lem6005014 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term189 A B s t f op) = (term190 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005013 A B s t f op x)). Qed.
Lemma lem6005015 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6005016 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term186 A B s t f op) = (term191 A B s t f op).
Proof. exact (MK_COMB (@lem6005015 A) (@lem6005014 A B s t f op)). Qed.
Lemma lem6005017 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term114 A B s t f op) = (term191 A B s t f op).
Proof. exact (TRANS (@lem6005009 A B s t f op) (@lem6005016 A B s t f op)). Qed.
Lemma lem6005019 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6005020 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (@lem6005019 A P Q). Qed.
Lemma lem6005021 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term194 A B s t f op) = (term195 A B s t f op).
Proof. exact (@lem6005020 A (term196 A B s t f op) (term197 A B s t f op)). Qed.
Lemma lem6005022 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term198 A B s t f op x) = (term199 A B s t f op x).
Proof. exact (eq_refl (term198 A B s t f op x)). Qed.
Lemma lem6005023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6005024 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term200 A B s t f op x) = (term180 A B s t f op x).
Proof. exact (MK_COMB (@lem6005023) (@lem6005022 A B s t f op x)). Qed.
Lemma lem6005025 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term201 A B s t f op x) = (term179 A B s t f op x).
Proof. exact (eq_refl (term201 A B s t f op x)). Qed.
Lemma lem6005026 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term202 A B s t f op x) = (term182 A B s t f op x).
Proof. exact (MK_COMB (@lem6005024 A B s t f op x) (@lem6005025 A B s t f op x)). Qed.
Lemma lem6005027 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term203 A B s t f op) = (term190 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005026 A B s t f op x)). Qed.
Lemma lem6005028 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6005029 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term194 A B s t f op) = (term191 A B s t f op).
Proof. exact (MK_COMB (@lem6005028 A) (@lem6005027 A B s t f op)). Qed.
Lemma lem6005030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6005031 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term204 A B s t f op) = (term205 A B s t f op).
Proof. exact (MK_COMB (@lem6005030) (@lem6005029 A B s t f op)). Qed.
Lemma lem6005032 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term198 A B s t f op x) = (term199 A B s t f op x).
Proof. exact (eq_refl (term198 A B s t f op x)). Qed.
Lemma lem6005033 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term206 A B s t f op) = (term196 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005032 A B s t f op x)). Qed.
Lemma lem6005034 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6005035 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term207 A B s t f op) = (term208 A B s t f op).
Proof. exact (MK_COMB (@lem6005034 A) (@lem6005033 A B s t f op)). Qed.
Lemma lem6005036 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6005037 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term209 A B s t f op) = (term210 A B s t f op).
Proof. exact (MK_COMB (@lem6005036) (@lem6005035 A B s t f op)). Qed.
Lemma lem6005038 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term201 A B s t f op x) = (term179 A B s t f op x).
Proof. exact (eq_refl (term201 A B s t f op x)). Qed.
Lemma lem6005039 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term211 A B s t f op) = (term197 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005038 A B s t f op x)). Qed.
Lemma lem6005040 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6005041 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term212 A B s t f op) = (term213 A B s t f op).
Proof. exact (MK_COMB (@lem6005040 A) (@lem6005039 A B s t f op)). Qed.
Lemma lem6005042 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term195 A B s t f op) = (term214 A B s t f op).
Proof. exact (MK_COMB (@lem6005037 A B s t f op) (@lem6005041 A B s t f op)). Qed.
Lemma lem6005043 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : ((term194 A B s t f op) = (term195 A B s t f op)) = ((term191 A B s t f op) = (term214 A B s t f op)).
Proof. exact (MK_COMB (@lem6005031 A B s t f op) (@lem6005042 A B s t f op)). Qed.
Lemma lem6005044 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term191 A B s t f op) = (term214 A B s t f op).
Proof. exact (EQ_MP (@lem6005043 A B s t f op) (@lem6005021 A B s t f op)). Qed.
Lemma lem6005142 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6005143 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term192 A P Q).
Proof. exact (@lem6005142 A P Q). Qed.
Lemma lem6005144 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term195 A B s t f op) = (term194 A B s t f op).
Proof. exact (@lem6005143 A (term196 A B s t f op) (term197 A B s t f op)). Qed.
Lemma lem6005145 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term198 A B s t f op x) = (term199 A B s t f op x).
Proof. exact (eq_refl (term198 A B s t f op x)). Qed.
Lemma lem6005146 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term206 A B s t f op) = (term196 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005145 A B s t f op x)). Qed.
Lemma lem6005147 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6005148 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term207 A B s t f op) = (term208 A B s t f op).
Proof. exact (MK_COMB (@lem6005147 A) (@lem6005146 A B s t f op)). Qed.
Lemma lem6005149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6005150 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term209 A B s t f op) = (term210 A B s t f op).
Proof. exact (MK_COMB (@lem6005149) (@lem6005148 A B s t f op)). Qed.
Lemma lem6005151 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term201 A B s t f op x) = (term179 A B s t f op x).
Proof. exact (eq_refl (term201 A B s t f op x)). Qed.
Lemma lem6005152 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term211 A B s t f op) = (term197 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005151 A B s t f op x)). Qed.
Lemma lem6005153 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6005154 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term212 A B s t f op) = (term213 A B s t f op).
Proof. exact (MK_COMB (@lem6005153 A) (@lem6005152 A B s t f op)). Qed.
Lemma lem6005155 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term195 A B s t f op) = (term214 A B s t f op).
Proof. exact (MK_COMB (@lem6005150 A B s t f op) (@lem6005154 A B s t f op)). Qed.
Lemma lem6005156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6005157 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term215 A B s t f op) = (term216 A B s t f op).
Proof. exact (MK_COMB (@lem6005156) (@lem6005155 A B s t f op)). Qed.
Lemma lem6005158 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term198 A B s t f op x) = (term199 A B s t f op x).
Proof. exact (eq_refl (term198 A B s t f op x)). Qed.
Lemma lem6005159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6005160 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term200 A B s t f op x) = (term180 A B s t f op x).
Proof. exact (MK_COMB (@lem6005159) (@lem6005158 A B s t f op x)). Qed.
Lemma lem6005161 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term201 A B s t f op x) = (term179 A B s t f op x).
Proof. exact (eq_refl (term201 A B s t f op x)). Qed.
Lemma lem6005162 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) : (term202 A B s t f op x) = (term182 A B s t f op x).
Proof. exact (MK_COMB (@lem6005160 A B s t f op x) (@lem6005161 A B s t f op x)). Qed.
Lemma lem6005163 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term203 A B s t f op) = (term190 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005162 A B s t f op x)). Qed.
Lemma lem6005164 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6005165 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term194 A B s t f op) = (term191 A B s t f op).
Proof. exact (MK_COMB (@lem6005164 A) (@lem6005163 A B s t f op)). Qed.
Lemma lem6005166 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : ((term195 A B s t f op) = (term194 A B s t f op)) = ((term214 A B s t f op) = (term191 A B s t f op)).
Proof. exact (MK_COMB (@lem6005157 A B s t f op) (@lem6005165 A B s t f op)). Qed.
Lemma lem6005167 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term214 A B s t f op) = (term191 A B s t f op).
Proof. exact (EQ_MP (@lem6005166 A B s t f op) (@lem6005144 A B s t f op)). Qed.
Lemma lem6005168 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term191 A B s t f op) = (term191 A B s t f op).
Proof. exact (TRANS (@lem6005044 A B s t f op) (@lem6005167 A B s t f op)). Qed.
Lemma lem6005169 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term114 A B s t f op) = (term191 A B s t f op).
Proof. exact (TRANS (@lem6005017 A B s t f op) (@lem6005168 A B s t f op)). Qed.
Lemma lem6005170 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term114 A B s t f op) : term191 A B s t f op.
Proof. exact (EQ_MP (@lem6005169 A B s t f op) (@lem6004875 A B s t f op h1)). Qed.
Lemma lem6005171 {A : Type'} (x : A) : (term158 A x) = (term158 A x).
Proof. exact (eq_refl (term158 A x)). Qed.
Lemma lem6005172 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (fun_ext (fun x : A => @lem6005171 A x)). Qed.
Lemma lem6005173 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005182 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem6005173 A) (@lem6005172 A)). Qed.
Lemma lem6005183 {A : Type'} (h1 : term116 A) : term116 A.
Proof. exact (EQ_MP (@lem6005182 A) (@lem6004876 A h1)). Qed.
Lemma lem6005194 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term217 A s x t) = (term218 A s x t).
Proof. exact (@lem17045 (@IN A x s) (@IN A x t)). Qed.
Lemma lem6005200 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term219 A s x t) = (term219 A s x t).
Proof. exact (eq_refl (term219 A s x t)). Qed.
Lemma lem6005202 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term220 A x s t) = (term220 A x s t).
Proof. exact (eq_refl (term220 A x s t)). Qed.
Lemma lem6005203 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term221 A s x t) = (term222 A s x t).
Proof. exact (MK_COMB (@lem6005202 A x s t) (@lem6005194 A s x t)). Qed.
Lemma lem6005204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6005205 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term223 A s x t) = (term224 A s x t).
Proof. exact (MK_COMB (@lem6005204) (@lem6005203 A s x t)). Qed.
Lemma lem6005206 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term225 A s x t) = (term226 A s x t).
Proof. exact (MK_COMB (@lem6005205 A s x t) (@lem6005200 A s x t)). Qed.
Lemma lem6005207 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term80 A x s t) = (term81 A s x t)) = (term225 A s x t).
Proof. exact (@lem17784 (term80 A x s t) (term81 A s x t)). Qed.
Lemma lem6005208 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term80 A x s t) = (term81 A s x t)) = (term226 A s x t).
Proof. exact (TRANS (@lem6005207 A s x t) (@lem6005206 A s x t)). Qed.
Lemma lem6005209 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term155 A s t) = (term227 A s t).
Proof. exact (fun_ext (fun x : A => @lem6005208 A s x t)). Qed.
Lemma lem6005210 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005211 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term228 A s t).
Proof. exact (MK_COMB (@lem6005210 A) (@lem6005209 A s t)). Qed.
Lemma lem6005212 {A : Type'} (s : A -> Prop) : (term156 A s) = (term229 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6005211 A s t)). Qed.
Lemma lem6005213 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005214 {A : Type'} (s : A -> Prop) : (term76 A s) = (term230 A s).
Proof. exact (MK_COMB (@lem6005213 A) (@lem6005212 A s)). Qed.
Lemma lem6005215 {A : Type'} : (term157 A) = (term231 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6005214 A s)). Qed.
Lemma lem6005216 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005217 {A : Type'} : (term115 A) = (term232 A).
Proof. exact (MK_COMB (@lem6005216 A) (@lem6005215 A)). Qed.
Lemma lem6005227 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term233 A P Q) = (term234 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6005228 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term233 A P Q) = (term234 A P Q).
Proof. exact (@lem6005227 A P Q). Qed.
Lemma lem6005229 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term235 A s t) = (term236 A s t).
Proof. exact (@lem6005228 A (term237 A s t) (term238 A s t)). Qed.
Lemma lem6005230 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term239 A s t x) = (term222 A s x t).
Proof. exact (eq_refl (term239 A s t x)). Qed.
Lemma lem6005231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6005232 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term240 A s t x) = (term224 A s x t).
Proof. exact (MK_COMB (@lem6005231) (@lem6005230 A s x t)). Qed.
Lemma lem6005233 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term241 A s t x) = (term219 A s x t).
Proof. exact (eq_refl (term241 A s t x)). Qed.
Lemma lem6005234 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term242 A s t x) = (term226 A s x t).
Proof. exact (MK_COMB (@lem6005232 A s x t) (@lem6005233 A s x t)). Qed.
Lemma lem6005235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term243 A s t) = (term227 A s t).
Proof. exact (fun_ext (fun x : A => @lem6005234 A s x t)). Qed.
Lemma lem6005236 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005237 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term235 A s t) = (term228 A s t).
Proof. exact (MK_COMB (@lem6005236 A) (@lem6005235 A s t)). Qed.
Lemma lem6005238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6005239 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term244 A s t) = (term245 A s t).
Proof. exact (MK_COMB (@lem6005238) (@lem6005237 A s t)). Qed.
Lemma lem6005240 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term239 A s t x) = (term222 A s x t).
Proof. exact (eq_refl (term239 A s t x)). Qed.
Lemma lem6005241 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term246 A s t) = (term237 A s t).
Proof. exact (fun_ext (fun x : A => @lem6005240 A s x t)). Qed.
Lemma lem6005242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005243 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term247 A s t) = (term248 A s t).
Proof. exact (MK_COMB (@lem6005242 A) (@lem6005241 A s t)). Qed.
Lemma lem6005244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6005245 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term249 A s t) = (term250 A s t).
Proof. exact (MK_COMB (@lem6005244) (@lem6005243 A s t)). Qed.
Lemma lem6005246 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term241 A s t x) = (term219 A s x t).
Proof. exact (eq_refl (term241 A s t x)). Qed.
Lemma lem6005247 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term251 A s t) = (term238 A s t).
Proof. exact (fun_ext (fun x : A => @lem6005246 A s x t)). Qed.
Lemma lem6005248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005249 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term252 A s t) = (term253 A s t).
Proof. exact (MK_COMB (@lem6005248 A) (@lem6005247 A s t)). Qed.
Lemma lem6005250 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term236 A s t) = (term254 A s t).
Proof. exact (MK_COMB (@lem6005245 A s t) (@lem6005249 A s t)). Qed.
Lemma lem6005251 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term235 A s t) = (term236 A s t)) = ((term228 A s t) = (term254 A s t)).
Proof. exact (MK_COMB (@lem6005239 A s t) (@lem6005250 A s t)). Qed.
Lemma lem6005252 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term228 A s t) = (term254 A s t).
Proof. exact (EQ_MP (@lem6005251 A s t) (@lem6005229 A s t)). Qed.
Lemma lem6005349 {A : Type'} (s : A -> Prop) : (term229 A s) = (term255 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6005252 A s t)). Qed.
Lemma lem6005350 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005351 {A : Type'} (s : A -> Prop) : (term230 A s) = (term256 A s).
Proof. exact (MK_COMB (@lem6005350 A) (@lem6005349 A s)). Qed.
Lemma lem6005353 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term233 A P Q) = (term234 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6005354 {A : Type'} (P : type686 A) (Q : type686 A) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem6005353 (A -> Prop) P Q). Qed.
Lemma lem6005355 {A : Type'} (s : A -> Prop) : (term259 A s) = (term260 A s).
Proof. exact (@lem6005354 A (term261 A s) (term262 A s)). Qed.
Lemma lem6005356 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term263 A s t) = (term248 A s t).
Proof. exact (eq_refl (term263 A s t)). Qed.
Lemma lem6005357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6005358 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term264 A s t) = (term250 A s t).
Proof. exact (MK_COMB (@lem6005357) (@lem6005356 A s t)). Qed.
Lemma lem6005359 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term265 A s t) = (term253 A s t).
Proof. exact (eq_refl (term265 A s t)). Qed.
Lemma lem6005360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term266 A s t) = (term254 A s t).
Proof. exact (MK_COMB (@lem6005358 A s t) (@lem6005359 A s t)). Qed.
Lemma lem6005361 {A : Type'} (s : A -> Prop) : (term267 A s) = (term255 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6005360 A s t)). Qed.
Lemma lem6005362 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005363 {A : Type'} (s : A -> Prop) : (term259 A s) = (term256 A s).
Proof. exact (MK_COMB (@lem6005362 A) (@lem6005361 A s)). Qed.
Lemma lem6005364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6005365 {A : Type'} (s : A -> Prop) : (term268 A s) = (term269 A s).
Proof. exact (MK_COMB (@lem6005364) (@lem6005363 A s)). Qed.
Lemma lem6005366 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term263 A s t) = (term248 A s t).
Proof. exact (eq_refl (term263 A s t)). Qed.
Lemma lem6005367 {A : Type'} (s : A -> Prop) : (term270 A s) = (term261 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6005366 A s t)). Qed.
Lemma lem6005368 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005369 {A : Type'} (s : A -> Prop) : (term271 A s) = (term272 A s).
Proof. exact (MK_COMB (@lem6005368 A) (@lem6005367 A s)). Qed.
Lemma lem6005370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6005371 {A : Type'} (s : A -> Prop) : (term273 A s) = (term274 A s).
Proof. exact (MK_COMB (@lem6005370) (@lem6005369 A s)). Qed.
Lemma lem6005372 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term265 A s t) = (term253 A s t).
Proof. exact (eq_refl (term265 A s t)). Qed.
Lemma lem6005373 {A : Type'} (s : A -> Prop) : (term275 A s) = (term262 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6005372 A s t)). Qed.
Lemma lem6005374 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005375 {A : Type'} (s : A -> Prop) : (term276 A s) = (term277 A s).
Proof. exact (MK_COMB (@lem6005374 A) (@lem6005373 A s)). Qed.
Lemma lem6005376 {A : Type'} (s : A -> Prop) : (term260 A s) = (term278 A s).
Proof. exact (MK_COMB (@lem6005371 A s) (@lem6005375 A s)). Qed.
Lemma lem6005377 {A : Type'} (s : A -> Prop) : ((term259 A s) = (term260 A s)) = ((term256 A s) = (term278 A s)).
Proof. exact (MK_COMB (@lem6005365 A s) (@lem6005376 A s)). Qed.
Lemma lem6005378 {A : Type'} (s : A -> Prop) : (term256 A s) = (term278 A s).
Proof. exact (EQ_MP (@lem6005377 A s) (@lem6005355 A s)). Qed.
Lemma lem6005483 {A : Type'} (s : A -> Prop) : (term230 A s) = (term278 A s).
Proof. exact (TRANS (@lem6005351 A s) (@lem6005378 A s)). Qed.
Lemma lem6005484 {A : Type'} : (term231 A) = (term279 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6005483 A s)). Qed.
Lemma lem6005485 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005486 {A : Type'} : (term232 A) = (term280 A).
Proof. exact (MK_COMB (@lem6005485 A) (@lem6005484 A)). Qed.
Lemma lem6005488 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term233 A P Q) = (term234 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6005489 {A : Type'} (P : type686 A) (Q : type686 A) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem6005488 (A -> Prop) P Q). Qed.
Lemma lem6005490 {A : Type'} : (term281 A) = (term282 A).
Proof. exact (@lem6005489 A (term283 A) (term284 A)). Qed.
Lemma lem6005491 {A : Type'} (s : A -> Prop) : (term285 A s) = (term272 A s).
Proof. exact (eq_refl (term285 A s)). Qed.
Lemma lem6005492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6005493 {A : Type'} (s : A -> Prop) : (term286 A s) = (term274 A s).
Proof. exact (MK_COMB (@lem6005492) (@lem6005491 A s)). Qed.
Lemma lem6005494 {A : Type'} (s : A -> Prop) : (term287 A s) = (term277 A s).
Proof. exact (eq_refl (term287 A s)). Qed.
Lemma lem6005495 {A : Type'} (s : A -> Prop) : (term288 A s) = (term278 A s).
Proof. exact (MK_COMB (@lem6005493 A s) (@lem6005494 A s)). Qed.
Lemma lem6005496 {A : Type'} : (term289 A) = (term279 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6005495 A s)). Qed.
Lemma lem6005497 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005498 {A : Type'} : (term281 A) = (term280 A).
Proof. exact (MK_COMB (@lem6005497 A) (@lem6005496 A)). Qed.
Lemma lem6005499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6005500 {A : Type'} : (term290 A) = (term291 A).
Proof. exact (MK_COMB (@lem6005499) (@lem6005498 A)). Qed.
Lemma lem6005501 {A : Type'} (s : A -> Prop) : (term285 A s) = (term272 A s).
Proof. exact (eq_refl (term285 A s)). Qed.
Lemma lem6005502 {A : Type'} : (term292 A) = (term283 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6005501 A s)). Qed.
Lemma lem6005503 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005504 {A : Type'} : (term293 A) = (term294 A).
Proof. exact (MK_COMB (@lem6005503 A) (@lem6005502 A)). Qed.
Lemma lem6005505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6005506 {A : Type'} : (term295 A) = (term296 A).
Proof. exact (MK_COMB (@lem6005505) (@lem6005504 A)). Qed.
Lemma lem6005507 {A : Type'} (s : A -> Prop) : (term287 A s) = (term277 A s).
Proof. exact (eq_refl (term287 A s)). Qed.
Lemma lem6005508 {A : Type'} : (term297 A) = (term284 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6005507 A s)). Qed.
Lemma lem6005509 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005510 {A : Type'} : (term298 A) = (term299 A).
Proof. exact (MK_COMB (@lem6005509 A) (@lem6005508 A)). Qed.
Lemma lem6005511 {A : Type'} : (term282 A) = (term300 A).
Proof. exact (MK_COMB (@lem6005506 A) (@lem6005510 A)). Qed.
Lemma lem6005512 {A : Type'} : ((term281 A) = (term282 A)) = ((term280 A) = (term300 A)).
Proof. exact (MK_COMB (@lem6005500 A) (@lem6005511 A)). Qed.
Lemma lem6005513 {A : Type'} : (term280 A) = (term300 A).
Proof. exact (EQ_MP (@lem6005512 A) (@lem6005490 A)). Qed.
Lemma lem6005628 {A : Type'} : (term232 A) = (term300 A).
Proof. exact (TRANS (@lem6005486 A) (@lem6005513 A)). Qed.
Lemma lem6005629 {A : Type'} : (term115 A) = (term300 A).
Proof. exact (TRANS (@lem6005217 A) (@lem6005628 A)). Qed.
Lemma lem6005630 {A : Type'} (h1 : term115 A) : term300 A.
Proof. exact (EQ_MP (@lem6005629 A) (@lem6004877 A h1)). Qed.
Lemma lem6005666 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term162 A B s t f x op) = (term162 A B s t f x op).
Proof. exact (eq_refl (term162 A B s t f x op)). Qed.
Lemma lem6005667 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B s t f op) = (term163 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005666 A B s t f x op)). Qed.
Lemma lem6005668 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005669 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term164 A B s t f op) = (term164 A B s t f op).
Proof. exact (MK_COMB (@lem6005668 A) (@lem6005667 A B s t f op)). Qed.
Lemma lem6005670 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term164 A B s t f op.
Proof. exact (EQ_MP (@lem6005669 A B s t f op) (@lem6004958 A B s t f op h1)). Qed.
Lemma lem6005677 {A : Type'} (x : A) : (term158 A x) = (term158 A x).
Proof. exact (eq_refl (term158 A x)). Qed.
Lemma lem6005678 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (fun_ext (fun x : A => @lem6005677 A x)). Qed.
Lemma lem6005679 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005680 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem6005679 A) (@lem6005678 A)). Qed.
Lemma lem6005681 {A : Type'} (h1 : term116 A) : term116 A.
Proof. exact (EQ_MP (@lem6005680 A) (@lem6005183 A h1)). Qed.
Lemma lem6005708 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term219 A s x t) = (term219 A s x t).
Proof. exact (eq_refl (term219 A s x t)). Qed.
Lemma lem6005709 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term238 A s t) = (term238 A s t).
Proof. exact (fun_ext (fun x : A => @lem6005708 A s x t)). Qed.
Lemma lem6005710 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005711 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term253 A s t) = (term253 A s t).
Proof. exact (MK_COMB (@lem6005710 A) (@lem6005709 A s t)). Qed.
Lemma lem6005712 {A : Type'} (s : A -> Prop) : (term262 A s) = (term262 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6005711 A s t)). Qed.
Lemma lem6005713 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005714 {A : Type'} (s : A -> Prop) : (term277 A s) = (term277 A s).
Proof. exact (MK_COMB (@lem6005713 A) (@lem6005712 A s)). Qed.
Lemma lem6005715 {A : Type'} : (term284 A) = (term284 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6005714 A s)). Qed.
Lemma lem6005716 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005717 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (MK_COMB (@lem6005716 A) (@lem6005715 A)). Qed.
Lemma lem6005746 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term222 A s x t) = (term222 A s x t).
Proof. exact (eq_refl (term222 A s x t)). Qed.
Lemma lem6005747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term237 A s t) = (term237 A s t).
Proof. exact (fun_ext (fun x : A => @lem6005746 A s x t)). Qed.
Lemma lem6005748 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005749 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term248 A s t) = (term248 A s t).
Proof. exact (MK_COMB (@lem6005748 A) (@lem6005747 A s t)). Qed.
Lemma lem6005750 {A : Type'} (s : A -> Prop) : (term261 A s) = (term261 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6005749 A s t)). Qed.
Lemma lem6005751 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005752 {A : Type'} (s : A -> Prop) : (term272 A s) = (term272 A s).
Proof. exact (MK_COMB (@lem6005751 A) (@lem6005750 A s)). Qed.
Lemma lem6005753 {A : Type'} : (term283 A) = (term283 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6005752 A s)). Qed.
Lemma lem6005754 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005755 {A : Type'} : (term294 A) = (term294 A).
Proof. exact (MK_COMB (@lem6005754 A) (@lem6005753 A)). Qed.
Lemma lem6005756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6005757 {A : Type'} : (term296 A) = (term296 A).
Proof. exact (MK_COMB (@lem6005756) (@lem6005755 A)). Qed.
Lemma lem6005758 {A : Type'} : (term300 A) = (term300 A).
Proof. exact (MK_COMB (@lem6005757 A) (@lem6005717 A)). Qed.
Lemma lem6005759 {A : Type'} (h1 : term115 A) : term300 A.
Proof. exact (EQ_MP (@lem6005758 A) (@lem6005630 A h1)). Qed.
Lemma lem6005863 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term182 A B s t f op x) : term182 A B s t f op x.
Proof. exact (h1). Qed.
Lemma lem6005865 {A : Type'} (h1 : term115 A) : term294 A.
Proof. exact (proj1 (@lem6005759 A h1)). Qed.
Lemma lem6005866 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term199 A B s t f op x.
Proof. exact (h1). Qed.
Lemma lem6005867 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : term179 A B s t f op x.
Proof. exact (h1). Qed.
Lemma lem6005869 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term103 A B s t f x op.
Proof. exact (proj1 (@lem6005866 A B s t f op x h1)). Qed.
Lemma lem6005870 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term100 A B t f x op.
Proof. exact (proj2 (@lem6005869 A B s t f op x h1)). Qed.
Lemma lem6005871 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term100 A B s f x op.
Proof. exact (proj1 (@lem6005869 A B s t f op x h1)). Qed.
Lemma lem6005877 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : term174 A B s t f x op.
Proof. exact (proj1 (@lem6005867 A B s t f op x h1)). Qed.
Lemma lem6005878 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term168 A B s f x op) : term168 A B s f x op.
Proof. exact (h1). Qed.
Lemma lem6005879 {A B : Type'} (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term168 A B t f x op) : term168 A B t f x op.
Proof. exact (h1). Qed.
Lemma lem6005903 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term162 A B s t f x op) = (term162 A B s t f x op).
Proof. exact (eq_refl (term162 A B s t f x op)). Qed.
Lemma lem6005904 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term163 A B s t f op) = (term163 A B s t f op).
Proof. exact (fun_ext (fun x : A => @lem6005903 A B s t f x op)). Qed.
Lemma lem6005905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005907 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term164 A B s t f op) = (term164 A B s t f op).
Proof. exact (MK_COMB (@lem6005905 A) (@lem6005904 A B s t f op)). Qed.
Lemma lem6005908 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term164 A B s t f op.
Proof. exact (EQ_MP (@lem6005907 A B s t f op) (@lem6005670 A B s t f op h1)). Qed.
Lemma lem6005929 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term222 A s x t) = (term222 A s x t).
Proof. exact (eq_refl (term222 A s x t)). Qed.
Lemma lem6005930 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term237 A s t) = (term237 A s t).
Proof. exact (fun_ext (fun x : A => @lem6005929 A s x t)). Qed.
Lemma lem6005931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6005932 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term248 A s t) = (term248 A s t).
Proof. exact (MK_COMB (@lem6005931 A) (@lem6005930 A s t)). Qed.
Lemma lem6005933 {A : Type'} (s : A -> Prop) : (term261 A s) = (term261 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6005932 A s t)). Qed.
Lemma lem6005934 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005935 {A : Type'} (s : A -> Prop) : (term272 A s) = (term272 A s).
Proof. exact (MK_COMB (@lem6005934 A) (@lem6005933 A s)). Qed.
Lemma lem6005936 {A : Type'} : (term283 A) = (term283 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6005935 A s)). Qed.
Lemma lem6005937 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6005939 {A : Type'} : (term294 A) = (term294 A).
Proof. exact (MK_COMB (@lem6005937 A) (@lem6005936 A)). Qed.
Lemma lem6005940 {A : Type'} (h1 : term115 A) : term294 A.
Proof. exact (EQ_MP (@lem6005939 A) (@lem6005865 A h1)). Qed.
Lemma lem6006016 {A : Type'} (x : A) : (term158 A x) = (term158 A x).
Proof. exact (eq_refl (term158 A x)). Qed.
Lemma lem6006017 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (fun_ext (fun x : A => @lem6006016 A x)). Qed.
Lemma lem6006018 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6006020 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem6006018 A) (@lem6006017 A)). Qed.
Lemma lem6006021 {A : Type'} (h1 : term116 A) : term116 A.
Proof. exact (EQ_MP (@lem6006020 A) (@lem6005681 A h1)). Qed.
Lemma lem6006110 {A : Type'} (x : A) : (term158 A x) = (term158 A x).
Proof. exact (eq_refl (term158 A x)). Qed.
Lemma lem6006111 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (fun_ext (fun x : A => @lem6006110 A x)). Qed.
Lemma lem6006112 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6006114 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem6006112 A) (@lem6006111 A)). Qed.
Lemma lem6006115 {A : Type'} (h1 : term116 A) : term116 A.
Proof. exact (EQ_MP (@lem6006114 A) (@lem6005681 A h1)). Qed.
Lemma lem6006204 {A : Type'} (x : A) : (term158 A x) = (term158 A x).
Proof. exact (eq_refl (term158 A x)). Qed.
Lemma lem6006205 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (fun_ext (fun x : A => @lem6006204 A x)). Qed.
Lemma lem6006206 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6006208 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem6006206 A) (@lem6006205 A)). Qed.
Lemma lem6006209 {A : Type'} (h1 : term116 A) : term116 A.
Proof. exact (EQ_MP (@lem6006208 A) (@lem6005681 A h1)). Qed.
Lemma lem6006298 {A : Type'} (x : A) : (term158 A x) = (term158 A x).
Proof. exact (eq_refl (term158 A x)). Qed.
Lemma lem6006299 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (fun_ext (fun x : A => @lem6006298 A x)). Qed.
Lemma lem6006300 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6006302 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem6006300 A) (@lem6006299 A)). Qed.
Lemma lem6006303 {A : Type'} (h1 : term116 A) : term116 A.
Proof. exact (EQ_MP (@lem6006302 A) (@lem6005681 A h1)). Qed.
Lemma lem6006366 {A B : Type'} (_76522 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term301 A B s t f op _76522.
Proof. exact (@lem6005908 A B s t f op h1 _76522). Qed.
Lemma lem6006367 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_76522 : A) (op : type1400 B) : (term301 A B s t f op _76522) = (term162 A B s t f _76522 op).
Proof. exact (eq_refl (term301 A B s t f op _76522)). Qed.
Lemma lem6006372 {A : Type'} (_76524 : A -> Prop) (h1 : term115 A) : term285 A _76524.
Proof. exact (@lem6005940 A h1 _76524). Qed.
Lemma lem6006373 {A : Type'} (_76524 : A -> Prop) : (term285 A _76524) = (term272 A _76524).
Proof. exact (eq_refl (term285 A _76524)). Qed.
Lemma lem6006374 {A : Type'} (_76524 : A -> Prop) (h1 : term115 A) : term272 A _76524.
Proof. exact (EQ_MP (@lem6006373 A _76524) (@lem6006372 A _76524 h1)). Qed.
Lemma lem6006375 {A : Type'} (_76524 : A -> Prop) (_76525 : A -> Prop) (h1 : term115 A) : term263 A _76524 _76525.
Proof. exact (@lem6006374 A _76524 h1 _76525). Qed.
Lemma lem6006376 {A : Type'} (_76524 : A -> Prop) (_76525 : A -> Prop) : (term263 A _76524 _76525) = (term248 A _76524 _76525).
Proof. exact (eq_refl (term263 A _76524 _76525)). Qed.
Lemma lem6006377 {A : Type'} (_76524 : A -> Prop) (_76525 : A -> Prop) (h1 : term115 A) : term248 A _76524 _76525.
Proof. exact (EQ_MP (@lem6006376 A _76524 _76525) (@lem6006375 A _76524 _76525 h1)). Qed.
Lemma lem6006378 {A : Type'} (_76524 : A -> Prop) (_76525 : A -> Prop) (_76526 : A) (h1 : term115 A) : term239 A _76524 _76525 _76526.
Proof. exact (@lem6006377 A _76524 _76525 h1 _76526). Qed.
Lemma lem6006379 {A : Type'} (_76524 : A -> Prop) (_76526 : A) (_76525 : A -> Prop) : (term239 A _76524 _76525 _76526) = (term222 A _76524 _76526 _76525).
Proof. exact (eq_refl (term239 A _76524 _76525 _76526)). Qed.
Lemma lem6006393 {A : Type'} (_76531 : A) (h1 : term116 A) : term302 A _76531.
Proof. exact (@lem6006021 A h1 _76531). Qed.
Lemma lem6006394 {A : Type'} (_76531 : A) : (term302 A _76531) = (term158 A _76531).
Proof. exact (eq_refl (term302 A _76531)). Qed.
Lemma lem6006417 {A : Type'} (_76539 : A) (h1 : term116 A) : term302 A _76539.
Proof. exact (@lem6006115 A h1 _76539). Qed.
Lemma lem6006418 {A : Type'} (_76539 : A) : (term302 A _76539) = (term158 A _76539).
Proof. exact (eq_refl (term302 A _76539)). Qed.
Lemma lem6006441 {A : Type'} (_76547 : A) (h1 : term116 A) : term302 A _76547.
Proof. exact (@lem6006209 A h1 _76547). Qed.
Lemma lem6006442 {A : Type'} (_76547 : A) : (term302 A _76547) = (term158 A _76547).
Proof. exact (eq_refl (term302 A _76547)). Qed.
Lemma lem6006465 {A : Type'} (_76555 : A) (h1 : term116 A) : term302 A _76555.
Proof. exact (@lem6006303 A h1 _76555). Qed.
Lemma lem6006466 {A : Type'} (_76555 : A) : (term302 A _76555) = (term158 A _76555).
Proof. exact (eq_refl (term302 A _76555)). Qed.
Lemma lem6006507 {A B : Type'} (_76522 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term162 A B s t f _76522 op.
Proof. exact (EQ_MP (@lem6006367 A B s t f _76522 op) (@lem6006366 A B _76522 s t f op h1)). Qed.
Lemma lem6006519 {A : Type'} (_76524 : A -> Prop) (_76526 : A) (_76525 : A -> Prop) (h1 : term115 A) : term222 A _76524 _76526 _76525.
Proof. exact (EQ_MP (@lem6006379 A _76524 _76526 _76525) (@lem6006378 A _76524 _76525 _76526 h1)). Qed.
Lemma lem6006525 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term170 A B f x op.
Proof. exact (proj2 (@lem6005870 A B s t f op x h1)). Qed.
Lemma lem6006555 {A : Type'} (_76531 : A) (h1 : term116 A) : term158 A _76531.
Proof. exact (EQ_MP (@lem6006394 A _76531) (@lem6006393 A _76531 h1)). Qed.
Lemma lem6006595 {A : Type'} (_76539 : A) (h1 : term116 A) : term158 A _76539.
Proof. exact (EQ_MP (@lem6006418 A _76539) (@lem6006417 A _76539 h1)). Qed.
Lemma lem6006635 {A : Type'} (_76547 : A) (h1 : term116 A) : term158 A _76547.
Proof. exact (EQ_MP (@lem6006442 A _76547) (@lem6006441 A _76547 h1)). Qed.
Lemma lem6006675 {A : Type'} (_76555 : A) (h1 : term116 A) : term158 A _76555.
Proof. exact (EQ_MP (@lem6006466 A _76555) (@lem6006465 A _76555 h1)). Qed.
Lemma lem6006785 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : @IN A x s.
Proof. exact (proj1 (@lem6005871 A B s t f op x h1)). Qed.
Lemma lem6006786 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term303 A x s.
Proof. exact (fun h0 : term304 A x s => @lem6006785 A B s t f op x h1). Qed.
Lemma lem6006788 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6006789 {A : Type'} (x : A) (s : A -> Prop) : (term303 A x s) = (@IN A x s).
Proof. exact (@lem6006788 (@IN A x s)). Qed.
Lemma lem6006790 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : @IN A x s.
Proof. exact (EQ_MP (@lem6006789 A x s) (@lem6006786 A B s t f op x h1)). Qed.
Lemma lem6006792 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : @IN A x t.
Proof. exact (proj1 (@lem6005870 A B s t f op x h1)). Qed.
Lemma lem6006793 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term303 A x t.
Proof. exact (fun h0 : term304 A x t => @lem6006792 A B s t f op x h1). Qed.
Lemma lem6006795 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6006796 {A : Type'} (x : A) (t : A -> Prop) : (term303 A x t) = (@IN A x t).
Proof. exact (@lem6006795 (@IN A x t)). Qed.
Lemma lem6006797 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : @IN A x t.
Proof. exact (EQ_MP (@lem6006796 A x t) (@lem6006793 A B s t f op x h1)). Qed.
Lemma lem6006799 (b : Prop) (a : Prop) : (a \/ b) = (term306 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6006800 {A : Type'} (_76526 : A) (_76524 : A -> Prop) (_76525 : A -> Prop) : (term222 A _76524 _76526 _76525) = (term307 A _76526 _76524 _76525).
Proof. exact (@lem6006799 (term218 A _76524 _76526 _76525) (term80 A _76526 _76524 _76525)). Qed.
Lemma lem6006802 (a : Prop) (b : Prop) : (term308 a b) = (term309 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6006803 {A : Type'} (_76524 : A -> Prop) (_76526 : A) (_76525 : A -> Prop) : (term310 A _76524 _76526 _76525) = (term311 A _76524 _76526 _76525).
Proof. exact (@lem6006802 (term304 A _76526 _76524) (term304 A _76526 _76525)). Qed.
Lemma lem6006805 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6006806 {A : Type'} (_76526 : A) (_76524 : A -> Prop) : (term313 A _76526 _76524) = (@IN A _76526 _76524).
Proof. exact (@lem6006805 (@IN A _76526 _76524)). Qed.
Lemma lem6006807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6006808 {A : Type'} (_76526 : A) (_76524 : A -> Prop) : (term314 A _76526 _76524) = (term315 A _76526 _76524).
Proof. exact (MK_COMB (@lem6006807) (@lem6006806 A _76526 _76524)). Qed.
Lemma lem6006810 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6006811 {A : Type'} (_76526 : A) (_76525 : A -> Prop) : (term313 A _76526 _76525) = (@IN A _76526 _76525).
Proof. exact (@lem6006810 (@IN A _76526 _76525)). Qed.
Lemma lem6006812 {A : Type'} (_76524 : A -> Prop) (_76526 : A) (_76525 : A -> Prop) : (term311 A _76524 _76526 _76525) = (term81 A _76524 _76526 _76525).
Proof. exact (MK_COMB (@lem6006808 A _76526 _76524) (@lem6006811 A _76526 _76525)). Qed.
Lemma lem6006813 {A : Type'} (_76524 : A -> Prop) (_76526 : A) (_76525 : A -> Prop) : (term310 A _76524 _76526 _76525) = (term81 A _76524 _76526 _76525).
Proof. exact (TRANS (@lem6006803 A _76524 _76526 _76525) (@lem6006812 A _76524 _76526 _76525)). Qed.
Lemma lem6006814 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6006815 {A : Type'} (_76524 : A -> Prop) (_76526 : A) (_76525 : A -> Prop) : (term316 A _76524 _76526 _76525) = (term317 A _76524 _76526 _76525).
Proof. exact (MK_COMB (@lem6006814) (@lem6006813 A _76524 _76526 _76525)). Qed.
Lemma lem6006816 {A : Type'} (_76526 : A) (_76524 : A -> Prop) (_76525 : A -> Prop) : (term80 A _76526 _76524 _76525) = (term80 A _76526 _76524 _76525).
Proof. exact (eq_refl (term80 A _76526 _76524 _76525)). Qed.
Lemma lem6006817 {A : Type'} (_76526 : A) (_76524 : A -> Prop) (_76525 : A -> Prop) : (term307 A _76526 _76524 _76525) = (term318 A _76526 _76524 _76525).
Proof. exact (MK_COMB (@lem6006815 A _76524 _76526 _76525) (@lem6006816 A _76526 _76524 _76525)). Qed.
Lemma lem6006818 {A : Type'} (_76526 : A) (_76524 : A -> Prop) (_76525 : A -> Prop) : (term222 A _76524 _76526 _76525) = (term318 A _76526 _76524 _76525).
Proof. exact (TRANS (@lem6006800 A _76526 _76524 _76525) (@lem6006817 A _76526 _76524 _76525)). Qed.
Lemma lem6006820 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term81 A s x t.
Proof. exact (conj (@lem6006790 A B s t f op x h1) (@lem6006797 A B s t f op x h1)). Qed.
Lemma lem6006822 {A : Type'} (_76526 : A) (_76524 : A -> Prop) (_76525 : A -> Prop) (h1 : term115 A) : term318 A _76526 _76524 _76525.
Proof. exact (EQ_MP (@lem6006818 A _76526 _76524 _76525) (@lem6006519 A _76524 _76526 _76525 h1)). Qed.
Lemma lem6006823 {A : Type'} (_76526 : A) (_76524 : A -> Prop) (_76525 : A -> Prop) (h1 : term115 A) : term318 A _76526 _76524 _76525.
Proof. exact (@lem6006822 A _76526 _76524 _76525 h1). Qed.
Lemma lem6006824 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term115 A) : term318 A x s t.
Proof. exact (@lem6006823 A x s t h1). Qed.
Lemma lem6006827 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term115 A) (h2 : term199 A B s t f op x) : term80 A x s t.
Proof. exact (@lem6006824 A x s t h1 (@lem6006820 A B s t f op x h2)). Qed.
Lemma lem6006828 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term115 A) (h2 : term199 A B s t f op x) : term319 A x s t.
Proof. exact (fun h0 : term320 A x s t => @lem6006827 A B s t f op x h1 h2). Qed.
Lemma lem6006830 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6006831 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term319 A x s t) = (term80 A x s t).
Proof. exact (@lem6006830 (term80 A x s t)). Qed.
Lemma lem6006832 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term115 A) (h2 : term199 A B s t f op x) : term80 A x s t.
Proof. exact (EQ_MP (@lem6006831 A x s t) (@lem6006828 A B s t f op x h1 h2)). Qed.
Lemma lem6006838 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6006839 {A B : Type'} (f : A -> B) (op : type1400 B) (_76522 : A) (s : A -> Prop) (t : A -> Prop) : (term162 A B s t f _76522 op) = (term321 A B f op _76522 s t).
Proof. exact (@lem6006838 ((f _76522) = (@neutral B op)) (term320 A _76522 s t)). Qed.
Lemma lem6006847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6006848 {A B : Type'} (f : A -> B) (op : type1400 B) (_76522 : A) (s : A -> Prop) (t : A -> Prop) : (term322 A B s t f _76522 op) = (term323 A B f op _76522 s t).
Proof. exact (MK_COMB (@lem6006847) (@lem6006839 A B f op _76522 s t)). Qed.
Lemma lem6006856 {A B : Type'} (f : A -> B) (op : type1400 B) (_76522 : A) (s : A -> Prop) (t : A -> Prop) : (term321 A B f op _76522 s t) = (term321 A B f op _76522 s t).
Proof. exact (eq_refl (term321 A B f op _76522 s t)). Qed.
Lemma lem6006857 {A B : Type'} (f : A -> B) (op : type1400 B) (_76522 : A) (s : A -> Prop) (t : A -> Prop) : ((term162 A B s t f _76522 op) = (term321 A B f op _76522 s t)) = ((term321 A B f op _76522 s t) = (term321 A B f op _76522 s t)).
Proof. exact (MK_COMB (@lem6006848 A B f op _76522 s t) (@lem6006856 A B f op _76522 s t)). Qed.
Lemma lem6006859 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6006860 (x : Prop) : (x = x) = True.
Proof. exact (@lem6006859 Prop x). Qed.
Lemma lem6006861 {A B : Type'} (f : A -> B) (op : type1400 B) (_76522 : A) (s : A -> Prop) (t : A -> Prop) : ((term321 A B f op _76522 s t) = (term321 A B f op _76522 s t)) = True.
Proof. exact (@lem6006860 (term321 A B f op _76522 s t)). Qed.
Lemma lem6006862 {A B : Type'} (f : A -> B) (op : type1400 B) (_76522 : A) (s : A -> Prop) (t : A -> Prop) : ((term162 A B s t f _76522 op) = (term321 A B f op _76522 s t)) = True.
Proof. exact (TRANS (@lem6006857 A B f op _76522 s t) (@lem6006861 A B f op _76522 s t)). Qed.
Lemma lem6006863 {A B : Type'} (f : A -> B) (op : type1400 B) (_76522 : A) (s : A -> Prop) (t : A -> Prop) : True = ((term162 A B s t f _76522 op) = (term321 A B f op _76522 s t)).
Proof. exact (SYM (@lem6006862 A B f op _76522 s t)). Qed.
Lemma lem6006864 {A B : Type'} (f : A -> B) (op : type1400 B) (_76522 : A) (s : A -> Prop) (t : A -> Prop) : (term162 A B s t f _76522 op) = (term321 A B f op _76522 s t).
Proof. exact (EQ_MP (@lem6006863 A B f op _76522 s t) (@lem0)). Qed.
Lemma lem6006865 {A B : Type'} (_76522 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term321 A B f op _76522 s t.
Proof. exact (EQ_MP (@lem6006864 A B f op _76522 s t) (@lem6006507 A B _76522 s t f op h1)). Qed.
Lemma lem6006867 (b : Prop) (a : Prop) : (a \/ b) = (term306 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6006868 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_76522 : A) (op : type1400 B) : (term321 A B f op _76522 s t) = (term324 A B s t f _76522 op).
Proof. exact (@lem6006867 (term320 A _76522 s t) ((f _76522) = (@neutral B op))). Qed.
Lemma lem6006870 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6006871 {A : Type'} (_76522 : A) (s : A -> Prop) (t : A -> Prop) : (term325 A _76522 s t) = (term80 A _76522 s t).
Proof. exact (@lem6006870 (term80 A _76522 s t)). Qed.
Lemma lem6006872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6006873 {A : Type'} (_76522 : A) (s : A -> Prop) (t : A -> Prop) : (term326 A _76522 s t) = (term327 A _76522 s t).
Proof. exact (MK_COMB (@lem6006872) (@lem6006871 A _76522 s t)). Qed.
Lemma lem6006874 {A B : Type'} (f : A -> B) (_76522 : A) (op : type1400 B) : ((f _76522) = (@neutral B op)) = ((f _76522) = (@neutral B op)).
Proof. exact (eq_refl ((f _76522) = (@neutral B op))). Qed.
Lemma lem6006875 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_76522 : A) (op : type1400 B) : (term324 A B s t f _76522 op) = (term160 A B s t f _76522 op).
Proof. exact (MK_COMB (@lem6006873 A _76522 s t) (@lem6006874 A B f _76522 op)). Qed.
Lemma lem6006876 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_76522 : A) (op : type1400 B) : (term321 A B f op _76522 s t) = (term160 A B s t f _76522 op).
Proof. exact (TRANS (@lem6006868 A B s t f _76522 op) (@lem6006875 A B s t f _76522 op)). Qed.
Lemma lem6006879 {A B : Type'} (_76522 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term160 A B s t f _76522 op.
Proof. exact (EQ_MP (@lem6006876 A B s t f _76522 op) (@lem6006865 A B _76522 s t f op h1)). Qed.
Lemma lem6006880 {A B : Type'} (_76522 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term160 A B s t f _76522 op.
Proof. exact (@lem6006879 A B _76522 s t f op h1). Qed.
Lemma lem6006881 {A B : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term160 A B s t f x op.
Proof. exact (@lem6006880 A B x s t f op h1). Qed.
Lemma lem6006884 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term31 A B s t f op) (h2 : term115 A) (h3 : term199 A B s t f op x) : (f x) = (@neutral B op).
Proof. exact (@lem6006881 A B x s t f op h1 (@lem6006832 A B s t f op x h2 h3)). Qed.
Lemma lem6006885 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term31 A B s t f op) (h2 : term115 A) (h3 : term199 A B s t f op x) : term328 A B f x op.
Proof. exact (fun h0 : term170 A B f x op => @lem6006884 A B s t f op x h1 h2 h3). Qed.
Lemma lem6006887 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6006888 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term328 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem6006887 ((f x) = (@neutral B op))). Qed.
Lemma lem6006889 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term31 A B s t f op) (h2 : term115 A) (h3 : term199 A B s t f op x) : (f x) = (@neutral B op).
Proof. exact (EQ_MP (@lem6006888 A B f x op) (@lem6006885 A B s t f op x h1 h2 h3)). Qed.
Lemma lem6006892 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6006894 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term170 A B f x op) = (term329 A B f x op).
Proof. exact (@lem6006892 ((f x) = (@neutral B op))). Qed.
Lemma lem6006897 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term199 A B s t f op x) : term329 A B f x op.
Proof. exact (EQ_MP (@lem6006894 A B f x op) (@lem6006525 A B s t f op x h1)). Qed.
Lemma lem6006900 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term31 A B s t f op) (h2 : term115 A) (h3 : term199 A B s t f op x) : False.
Proof. exact (@lem6006897 A B s t f op x h3 (@lem6006889 A B s t f op x h1 h2 h3)). Qed.
Lemma lem6006901 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term31 A B s t f op) (h2 : term115 A) (h3 : term199 A B s t f op x) : term330.
Proof. exact (fun h0 : ~ False => @lem6006900 A B s t f op x h1 h2 h3). Qed.
Lemma lem6006903 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6006904 : term330 = False.
Proof. exact (@lem6006903 False). Qed.
Lemma lem6006905 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term31 A B s t f op) (h2 : term115 A) (h3 : term199 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6006904) (@lem6006901 A B s t f op x h1 h2 h3)). Qed.
Lemma lem6006989 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : @IN A x (@EMPTY A).
Proof. exact (proj2 (@lem6005867 A B s t f op x h1)). Qed.
Lemma lem6006990 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : term331 A x.
Proof. exact (fun h0 : term158 A x => @lem6006989 A B s t f op x h1). Qed.
Lemma lem6006992 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6006993 {A : Type'} (x : A) : (term331 A x) = (@IN A x (@EMPTY A)).
Proof. exact (@lem6006992 (@IN A x (@EMPTY A))). Qed.
Lemma lem6006994 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem6006993 A x) (@lem6006990 A B s t f op x h1)). Qed.
Lemma lem6006997 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6006999 {A : Type'} (_76531 : A) : (term158 A _76531) = (term332 A _76531).
Proof. exact (@lem6006997 (@IN A _76531 (@EMPTY A))). Qed.
Lemma lem6007002 {A : Type'} (_76531 : A) (h1 : term116 A) : term332 A _76531.
Proof. exact (EQ_MP (@lem6006999 A _76531) (@lem6006555 A _76531 h1)). Qed.
Lemma lem6007003 {A : Type'} (_76531 : A) (h1 : term116 A) : term332 A _76531.
Proof. exact (@lem6007002 A _76531 h1). Qed.
Lemma lem6007004 {A : Type'} (x : A) (h1 : term116 A) : term332 A x.
Proof. exact (@lem6007003 A x h1). Qed.
Lemma lem6007007 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (@lem6007004 A x h1 (@lem6006994 A B s t f op x h2)). Qed.
Lemma lem6007008 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : term330.
Proof. exact (fun h0 : ~ False => @lem6007007 A B s t f op x h1 h2). Qed.
Lemma lem6007010 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6007011 : term330 = False.
Proof. exact (@lem6007010 False). Qed.
Lemma lem6007012 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007011) (@lem6007008 A B s t f op x h1 h2)). Qed.
Lemma lem6007096 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : @IN A x (@EMPTY A).
Proof. exact (proj2 (@lem6005867 A B s t f op x h1)). Qed.
Lemma lem6007097 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : term331 A x.
Proof. exact (fun h0 : term158 A x => @lem6007096 A B s t f op x h1). Qed.
Lemma lem6007099 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6007100 {A : Type'} (x : A) : (term331 A x) = (@IN A x (@EMPTY A)).
Proof. exact (@lem6007099 (@IN A x (@EMPTY A))). Qed.
Lemma lem6007101 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem6007100 A x) (@lem6007097 A B s t f op x h1)). Qed.
Lemma lem6007104 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6007106 {A : Type'} (_76539 : A) : (term158 A _76539) = (term332 A _76539).
Proof. exact (@lem6007104 (@IN A _76539 (@EMPTY A))). Qed.
Lemma lem6007109 {A : Type'} (_76539 : A) (h1 : term116 A) : term332 A _76539.
Proof. exact (EQ_MP (@lem6007106 A _76539) (@lem6006595 A _76539 h1)). Qed.
Lemma lem6007110 {A : Type'} (_76539 : A) (h1 : term116 A) : term332 A _76539.
Proof. exact (@lem6007109 A _76539 h1). Qed.
Lemma lem6007111 {A : Type'} (x : A) (h1 : term116 A) : term332 A x.
Proof. exact (@lem6007110 A x h1). Qed.
Lemma lem6007114 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (@lem6007111 A x h1 (@lem6007101 A B s t f op x h2)). Qed.
Lemma lem6007115 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : term330.
Proof. exact (fun h0 : ~ False => @lem6007114 A B s t f op x h1 h2). Qed.
Lemma lem6007117 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6007118 : term330 = False.
Proof. exact (@lem6007117 False). Qed.
Lemma lem6007119 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007118) (@lem6007115 A B s t f op x h1 h2)). Qed.
Lemma lem6007203 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : @IN A x (@EMPTY A).
Proof. exact (proj2 (@lem6005867 A B s t f op x h1)). Qed.
Lemma lem6007204 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : term331 A x.
Proof. exact (fun h0 : term158 A x => @lem6007203 A B s t f op x h1). Qed.
Lemma lem6007206 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6007207 {A : Type'} (x : A) : (term331 A x) = (@IN A x (@EMPTY A)).
Proof. exact (@lem6007206 (@IN A x (@EMPTY A))). Qed.
Lemma lem6007208 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem6007207 A x) (@lem6007204 A B s t f op x h1)). Qed.
Lemma lem6007211 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6007213 {A : Type'} (_76547 : A) : (term158 A _76547) = (term332 A _76547).
Proof. exact (@lem6007211 (@IN A _76547 (@EMPTY A))). Qed.
Lemma lem6007216 {A : Type'} (_76547 : A) (h1 : term116 A) : term332 A _76547.
Proof. exact (EQ_MP (@lem6007213 A _76547) (@lem6006635 A _76547 h1)). Qed.
Lemma lem6007217 {A : Type'} (_76547 : A) (h1 : term116 A) : term332 A _76547.
Proof. exact (@lem6007216 A _76547 h1). Qed.
Lemma lem6007218 {A : Type'} (x : A) (h1 : term116 A) : term332 A x.
Proof. exact (@lem6007217 A x h1). Qed.
Lemma lem6007221 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (@lem6007218 A x h1 (@lem6007208 A B s t f op x h2)). Qed.
Lemma lem6007222 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : term330.
Proof. exact (fun h0 : ~ False => @lem6007221 A B s t f op x h1 h2). Qed.
Lemma lem6007224 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6007225 : term330 = False.
Proof. exact (@lem6007224 False). Qed.
Lemma lem6007226 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007225) (@lem6007222 A B s t f op x h1 h2)). Qed.
Lemma lem6007310 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : @IN A x (@EMPTY A).
Proof. exact (proj2 (@lem6005867 A B s t f op x h1)). Qed.
Lemma lem6007311 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : term331 A x.
Proof. exact (fun h0 : term158 A x => @lem6007310 A B s t f op x h1). Qed.
Lemma lem6007313 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6007314 {A : Type'} (x : A) : (term331 A x) = (@IN A x (@EMPTY A)).
Proof. exact (@lem6007313 (@IN A x (@EMPTY A))). Qed.
Lemma lem6007315 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term179 A B s t f op x) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem6007314 A x) (@lem6007311 A B s t f op x h1)). Qed.
Lemma lem6007318 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6007320 {A : Type'} (_76555 : A) : (term158 A _76555) = (term332 A _76555).
Proof. exact (@lem6007318 (@IN A _76555 (@EMPTY A))). Qed.
Lemma lem6007323 {A : Type'} (_76555 : A) (h1 : term116 A) : term332 A _76555.
Proof. exact (EQ_MP (@lem6007320 A _76555) (@lem6006675 A _76555 h1)). Qed.
Lemma lem6007324 {A : Type'} (_76555 : A) (h1 : term116 A) : term332 A _76555.
Proof. exact (@lem6007323 A _76555 h1). Qed.
Lemma lem6007325 {A : Type'} (x : A) (h1 : term116 A) : term332 A x.
Proof. exact (@lem6007324 A x h1). Qed.
Lemma lem6007328 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (@lem6007325 A x h1 (@lem6007315 A B s t f op x h2)). Qed.
Lemma lem6007329 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : term330.
Proof. exact (fun h0 : ~ False => @lem6007328 A B s t f op x h1 h2). Qed.
Lemma lem6007331 (p : Prop) : (term305 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6007332 : term330 = False.
Proof. exact (@lem6007331 False). Qed.
Lemma lem6007333 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007332) (@lem6007329 A B s t f op x h1 h2)). Qed.
Lemma lem6007334 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : (term116 A) = False.
Proof. exact (prop_ext (fun h3 : term116 A => @lem6007333 A B s t f op x h1 h2) (fun h3 : False => @lem6006303 A h1)). Qed.
Lemma lem6007335 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007334 A B s t f op x h1 h2) (@lem6006303 A h1)). Qed.
Lemma lem6007336 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : (term116 A) = False.
Proof. exact (prop_ext (fun h3 : term116 A => @lem6007226 A B s t f op x h1 h2) (fun h3 : False => @lem6006209 A h1)). Qed.
Lemma lem6007337 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007336 A B s t f op x h1 h2) (@lem6006209 A h1)). Qed.
Lemma lem6007338 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : (term116 A) = False.
Proof. exact (prop_ext (fun h3 : term116 A => @lem6007119 A B s t f op x h1 h2) (fun h3 : False => @lem6006115 A h1)). Qed.
Lemma lem6007339 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007338 A B s t f op x h1 h2) (@lem6006115 A h1)). Qed.
Lemma lem6007340 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : (term116 A) = False.
Proof. exact (prop_ext (fun h3 : term116 A => @lem6007012 A B s t f op x h1 h2) (fun h3 : False => @lem6006021 A h1)). Qed.
Lemma lem6007341 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007340 A B s t f op x h1 h2) (@lem6006021 A h1)). Qed.
Lemma lem6007342 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term116 A) (h2 : term179 A B s t f op x) (h3 : term168 A B t f x op) : False.
Proof. exact (or_elim (@lem6005879 A B t f x op h3) (fun h0 : term304 A x t => @lem6007337 A B s t f op x h1 h2) (fun h0 : (f x) = (@neutral B op) => @lem6007335 A B s t f op x h1 h2)). Qed.
Lemma lem6007343 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term116 A) (h2 : term179 A B s t f op x) (h3 : term168 A B s f x op) : False.
Proof. exact (or_elim (@lem6005878 A B s f x op h3) (fun h0 : term304 A x s => @lem6007341 A B s t f op x h1 h2) (fun h0 : (f x) = (@neutral B op) => @lem6007339 A B s t f op x h1 h2)). Qed.
Lemma lem6007344 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term179 A B s t f op x) : False.
Proof. exact (or_elim (@lem6005877 A B s t f op x h2) (fun h0 : term168 A B s f x op => @lem6007343 A B t s f x op h1 h2 h0) (fun h0 : term168 A B t f x op => @lem6007342 A B s t f x op h1 h2 h0)). Qed.
Lemma lem6007345 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term115 A) (h4 : term182 A B s t f op x) : False.
Proof. exact (or_elim (@lem6005863 A B s t f op x h4) (fun h0 : term199 A B s t f op x => @lem6006905 A B s t f op x h2 h3 h0) (fun h0 : term179 A B s t f op x => @lem6007344 A B s t f op x h1 h0)). Qed.
Lemma lem6007346 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term115 A) (h4 : term182 A B s t f op x) : (term182 A B s t f op x) = False.
Proof. exact (prop_ext (fun h5 : term182 A B s t f op x => @lem6007345 A B s t f op x h1 h2 h3 h4) (fun h5 : False => @lem6005863 A B s t f op x h4)). Qed.
Lemma lem6007347 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term115 A) (h4 : term182 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007346 A B s t f op x h1 h2 h3 h4) (@lem6005863 A B s t f op x h4)). Qed.
Lemma lem6007348 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term115 A) (h4 : term182 A B s t f op x) : (term116 A) = False.
Proof. exact (prop_ext (fun h5 : term116 A => @lem6007347 A B s t f op x h1 h2 h3 h4) (fun h5 : False => @lem6005681 A h1)). Qed.
Lemma lem6007349 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (x : A) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term115 A) (h4 : term182 A B s t f op x) : False.
Proof. exact (EQ_MP (@lem6007348 A B s t f op x h1 h2 h3 h4) (@lem6005681 A h1)). Qed.
Lemma lem6007350 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term115 A) (h4 : term114 A B s t f op) : False.
Proof. exact (ex_elim (@lem6005170 A B s t f op h4) (fun x : A => fun h0 : term190 A B s t f op x => @lem6007349 A B s t f op x h1 h2 h3 h0)). Qed.
Lemma lem6007351 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term115 A) (h4 : term114 A B s t f op) : (term116 A) = False.
Proof. exact (prop_ext (fun h5 : term116 A => @lem6007350 A B s t f op h1 h2 h3 h4) (fun h5 : False => @lem6005183 A h1)). Qed.
Lemma lem6007352 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term115 A) (h4 : term114 A B s t f op) : False.
Proof. exact (EQ_MP (@lem6007351 A B s t f op h1 h2 h3 h4) (@lem6005183 A h1)). Qed.
Lemma lem6007353 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term114 A B s t f op) : term121 A.
Proof. exact (fun h0 : term115 A => @lem6007352 A B s t f op h1 h2 h0 h3). Qed.
Lemma lem6007354 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (@lem69 (term115 A)). Qed.
Lemma lem6007355 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term116 A) (h2 : term31 A B s t f op) (h3 : term114 A B s t f op) : term122 A.
Proof. exact (EQ_MP (@lem6007354 A) (@lem6007353 A B s t f op h1 h2 h3)). Qed.
Lemma lem6007356 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : term114 A B s t f op) : term125 A.
Proof. exact (fun h0 : term116 A => @lem6007355 A B s t f op h0 h1 h2). Qed.
Lemma lem6007357 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) : term128 A B s t f op.
Proof. exact (fun h0 : term114 A B s t f op => @lem6007356 A B s t f op h1 h0). Qed.
Lemma lem6007358 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term131 A B s t f op.
Proof. exact (fun h0 : term31 A B s t f op => @lem6007357 A B s t f op h0). Qed.
Lemma lem6007359 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term134 A B s t f op.
Proof. exact (fun h0 : @FINITE A t => @lem6007358 A B s t f op). Qed.
Lemma lem6007360 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term136 A B s t f op.
Proof. exact (fun h0 : @FINITE A s => @lem6007359 A B s t f op). Qed.
Lemma lem6007361 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term138 A B s t f op.
Proof. exact (fun h0 : @monoidal B op => @lem6007360 A B s t f op). Qed.
Lemma lem6007366 {A B : Type'} (t : A -> Prop) (f : A -> B) (op : type1400 B) : term142 A B t f op.
Proof. exact (fun s : A -> Prop => @lem6007361 A B s t f op). Qed.
Lemma lem6007371 {A B : Type'} (f : A -> B) (op : type1400 B) : term146 A B f op.
Proof. exact (fun t : A -> Prop => @lem6007366 A B t f op). Qed.
Lemma lem6007376 {A B : Type'} (op : type1400 B) : term150 A B op.
Proof. exact (fun f : A -> B => @lem6007371 A B f op). Qed.
Lemma lem6007381 {A B : Type'} : term154 A B.
Proof. exact (fun op : type1400 B => @lem6007376 A B op). Qed.
Lemma lem6007382 {A B : Type'} : term153 A B.
Proof. exact (EQ_MP (@lem6004870 A B) (@lem6007381 A B)). Qed.
Lemma lem6007383 {A B : Type'} (op : type1400 B) : term333 A B op.
Proof. exact (@lem6007382 A B op). Qed.
Lemma lem6007384 {A B : Type'} (op : type1400 B) : (term333 A B op) = (term149 A B op).
Proof. exact (eq_refl (term333 A B op)). Qed.
Lemma lem6007385 {A B : Type'} (op : type1400 B) : term149 A B op.
Proof. exact (EQ_MP (@lem6007384 A B op) (@lem6007383 A B op)). Qed.
Lemma lem6007386 {A B : Type'} (op : type1400 B) (f : A -> B) : term334 A B op f.
Proof. exact (@lem6007385 A B op f). Qed.
Lemma lem6007387 {A B : Type'} (f : A -> B) (op : type1400 B) : (term334 A B op f) = (term145 A B f op).
Proof. exact (eq_refl (term334 A B op f)). Qed.
Lemma lem6007388 {A B : Type'} (f : A -> B) (op : type1400 B) : term145 A B f op.
Proof. exact (EQ_MP (@lem6007387 A B f op) (@lem6007386 A B op f)). Qed.
Lemma lem6007389 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) : term335 A B f op t.
Proof. exact (@lem6007388 A B f op t). Qed.
Lemma lem6007390 {A B : Type'} (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term335 A B f op t) = (term141 A B t f op).
Proof. exact (eq_refl (term335 A B f op t)). Qed.
Lemma lem6007391 {A B : Type'} (t : A -> Prop) (f : A -> B) (op : type1400 B) : term141 A B t f op.
Proof. exact (EQ_MP (@lem6007390 A B t f op) (@lem6007389 A B f op t)). Qed.
Lemma lem6007392 {A B : Type'} (t : A -> Prop) (f : A -> B) (op : type1400 B) (s : A -> Prop) : term336 A B t f op s.
Proof. exact (@lem6007391 A B t f op s). Qed.
Lemma lem6007393 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : (term336 A B t f op s) = (term117 A B s t f op).
Proof. exact (eq_refl (term336 A B t f op s)). Qed.
Lemma lem6007394 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term117 A B s t f op.
Proof. exact (EQ_MP (@lem6007393 A B s t f op) (@lem6007392 A B t f op s)). Qed.
Lemma lem6007396 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) : term117 A B s t f op.
Proof. exact (@lem6004570 A B s t f op (@lem6007394 A B s t f op)). Qed.
Lemma lem6007397 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term135 A B s t f op.
Proof. exact (@lem6007396 A B s t f op (@lem6004012 B op h1)). Qed.
Lemma lem6007398 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) : term133 A B s t f op.
Proof. exact (@lem6007397 A B s t f op h2 (@lem6004015 A s h1)). Qed.
Lemma lem6007399 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : @FINITE A s) (h2 : @FINITE A t) (h3 : @monoidal B op) : term130 A B s t f op.
Proof. exact (@lem6007398 A B t f s op h1 h3 (@lem6004017 A t h2)). Qed.
Lemma lem6007400 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : term127 A B s t f op.
Proof. exact (@lem6007399 A B f s t op h2 h3 h4 (@lem6004016 A B s t f op h1)). Qed.
Lemma lem6007401 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) (h5 : term114 A B s t f op) : term124 A.
Proof. exact (@lem6007400 A B f s t op h1 h2 h3 h4 (@lem6004550 A B s t f op h5)). Qed.
Lemma lem6007402 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) (h5 : term114 A B s t f op) : term121 A.
Proof. exact (@lem6007401 A B s t f op h1 h2 h3 h4 h5 (@lem6004553 A)). Qed.
Lemma lem6007403 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) (h5 : term114 A B s t f op) : False.
Proof. exact (@lem6007402 A B s t f op h1 h2 h3 h4 h5 (@lem6004551 A)). Qed.
Lemma lem6007404 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) (h5 : term114 A B s t f op) : (term114 A B s t f op) = False.
Proof. exact (prop_ext (fun h6 : term114 A B s t f op => @lem6007403 A B s t f op h1 h2 h3 h4 h5) (fun h6 : False => @lem6004550 A B s t f op h5)). Qed.
Lemma lem6007405 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) (h5 : term114 A B s t f op) : False.
Proof. exact (EQ_MP (@lem6007404 A B s t f op h1 h2 h3 h4 h5) (@lem6004550 A B s t f op h5)). Qed.
Lemma lem6007406 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : term113 A B s t f op.
Proof. exact (fun h0 : term114 A B s t f op => @lem6007405 A B s t f op h1 h2 h3 h4 h0). Qed.
Lemma lem6007407 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : term108 A B s t f op.
Proof. exact (EQ_MP (@lem6004549 A B s t f op) (@lem6007406 A B f s t op h1 h2 h3 h4)). Qed.
Lemma lem6007408 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : term111 A B s op f t.
Proof. exact (EQ_MP (@lem6004545 A B op f s t h2 h3) (@lem6007407 A B f s t op h1 h2 h3 h4)). Qed.
Lemma lem6007409 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : (term43 A B s op t f) = (term40 A B s op t f).
Proof. exact (@lem6004097 A B s t f op h4 (@lem6007408 A B f s t op h1 h2 h3 h4)). Qed.
Lemma lem6007410 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : (term34 A B op s t f) = (term40 A B s op t f).
Proof. exact (EQ_MP (@lem6004053 A B s op t f) (@lem6007409 A B f s t op h1 h2 h3 h4)). Qed.
Lemma lem6007411 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : (term33 A B op s t f) = (term39 A B s op t f).
Proof. exact (EQ_MP (@lem6004037 A B s op t f) (@lem6007410 A B f s t op h1 h2 h3 h4)). Qed.
Lemma lem6007412 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term29 A B s t f op) : term30 A B s t f op.
Proof. exact (proj2 (@lem6004013 A B s t f op h1)). Qed.
Lemma lem6007413 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term29 A B s t f op) : @FINITE A s.
Proof. exact (proj1 (@lem6004013 A B s t f op h1)). Qed.
Lemma lem6007414 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term30 A B s t f op) : term31 A B s t f op.
Proof. exact (proj2 (@lem6004014 A B s t f op h1)). Qed.
Lemma lem6007415 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term30 A B s t f op) : @FINITE A t.
Proof. exact (proj1 (@lem6004014 A B s t f op h1)). Qed.
Lemma lem6007416 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : (term31 A B s t f op) = ((term33 A B op s t f) = (term39 A B s op t f)).
Proof. exact (prop_ext (fun h5 : term31 A B s t f op => @lem6007411 A B f s t op h1 h2 h3 h4) (fun h5 : (term33 A B op s t f) = (term39 A B s op t f) => @lem6004016 A B s t f op h1)). Qed.
Lemma lem6007417 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : (term33 A B op s t f) = (term39 A B s op t f).
Proof. exact (EQ_MP (@lem6007416 A B f s t op h1 h2 h3 h4) (@lem6004016 A B s t f op h1)). Qed.
Lemma lem6007418 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : (@FINITE A t) = ((term33 A B op s t f) = (term39 A B s op t f)).
Proof. exact (prop_ext (fun h5 : @FINITE A t => @lem6007417 A B f s t op h1 h2 h3 h4) (fun h5 : (term33 A B op s t f) = (term39 A B s op t f) => @lem6004017 A t h3)). Qed.
Lemma lem6007419 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (op : type1400 B) (h1 : term31 A B s t f op) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : @monoidal B op) : (term33 A B op s t f) = (term39 A B s op t f).
Proof. exact (EQ_MP (@lem6007418 A B f s t op h1 h2 h3 h4) (@lem6004017 A t h3)). Qed.
Lemma lem6007420 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @FINITE A s) (h2 : @FINITE A t) (h3 : @monoidal B op) (h4 : term30 A B s t f op) : (term31 A B s t f op) = ((term33 A B op s t f) = (term39 A B s op t f)).
Proof. exact (prop_ext (fun h5 : term31 A B s t f op => @lem6007419 A B f s t op h5 h1 h2 h3) (fun h5 : (term33 A B op s t f) = (term39 A B s op t f) => @lem6007414 A B s t f op h4)). Qed.
Lemma lem6007421 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @FINITE A s) (h2 : @FINITE A t) (h3 : @monoidal B op) (h4 : term30 A B s t f op) : (term33 A B op s t f) = (term39 A B s op t f).
Proof. exact (EQ_MP (@lem6007420 A B s t f op h1 h2 h3 h4) (@lem6007414 A B s t f op h4)). Qed.
Lemma lem6007422 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term30 A B s t f op) : (@FINITE A t) = ((term33 A B op s t f) = (term39 A B s op t f)).
Proof. exact (prop_ext (fun h4 : @FINITE A t => @lem6007421 A B s t f op h1 h4 h2 h3) (fun h4 : (term33 A B op s t f) = (term39 A B s op t f) => @lem6007415 A B s t f op h3)). Qed.
Lemma lem6007423 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term30 A B s t f op) : (term33 A B op s t f) = (term39 A B s op t f).
Proof. exact (EQ_MP (@lem6007422 A B s t f op h1 h2 h3) (@lem6007415 A B s t f op h3)). Qed.
Lemma lem6007424 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term30 A B s t f op) : (@FINITE A s) = ((term33 A B op s t f) = (term39 A B s op t f)).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem6007423 A B s t f op h1 h2 h3) (fun h4 : (term33 A B op s t f) = (term39 A B s op t f) => @lem6004015 A s h1)). Qed.
Lemma lem6007425 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term30 A B s t f op) : (term33 A B op s t f) = (term39 A B s op t f).
Proof. exact (EQ_MP (@lem6007424 A B s t f op h1 h2 h3) (@lem6004015 A s h1)). Qed.
Lemma lem6007426 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term29 A B s t f op) : (term30 A B s t f op) = ((term33 A B op s t f) = (term39 A B s op t f)).
Proof. exact (prop_ext (fun h4 : term30 A B s t f op => @lem6007425 A B s t f op h1 h2 h4) (fun h4 : (term33 A B op s t f) = (term39 A B s op t f) => @lem6007412 A B s t f op h3)). Qed.
Lemma lem6007427 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @FINITE A s) (h2 : @monoidal B op) (h3 : term29 A B s t f op) : (term33 A B op s t f) = (term39 A B s op t f).
Proof. exact (EQ_MP (@lem6007426 A B s t f op h1 h2 h3) (@lem6007412 A B s t f op h3)). Qed.
Lemma lem6007428 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term29 A B s t f op) : (@FINITE A s) = ((term33 A B op s t f) = (term39 A B s op t f)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6007427 A B s t f op h3 h1 h2) (fun h3 : (term33 A B op s t f) = (term39 A B s op t f) => @lem6007413 A B s t f op h2)). Qed.
Lemma lem6007429 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term29 A B s t f op) : (term33 A B op s t f) = (term39 A B s op t f).
Proof. exact (EQ_MP (@lem6007428 A B s t f op h1 h2) (@lem6007413 A B s t f op h2)). Qed.
Lemma lem6007430 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term337 A B s op t f.
Proof. exact (fun h0 : term29 A B s t f op => @lem6007429 A B s t f op h1 h0). Qed.
Lemma lem6007435 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term338 A B s op f.
Proof. exact (fun t : A -> Prop => @lem6007430 A B s t f op h1). Qed.
Lemma lem6007440 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term339 A B op f.
Proof. exact (fun s : A -> Prop => @lem6007435 A B s f op h1). Qed.
Lemma lem6007445 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term340 A B op.
Proof. exact (fun f : A -> B => @lem6007440 A B f op h1). Qed.
Lemma lem6007446 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term340 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem6007445 A B op h1) (fun h2 : term340 A B op => @lem6004012 B op h1)). Qed.
Lemma lem6007447 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term340 A B op.
Proof. exact (EQ_MP (@lem6007446 A B op h1) (@lem6004012 B op h1)). Qed.
Lemma lem6007448 {A B : Type'} (op : type1400 B) : term341 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6007447 A B op h0). Qed.
Lemma lem6007453 {A B : Type'} : term342 A B.
Proof. exact (fun op : type1400 B => @lem6007448 A B op). Qed.
