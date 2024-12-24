Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_UNPAIR_FUN_THM_term_abbrevs.
Require Import ETA_AX_spec.
Require Import EXISTS_PAIR_FUN_THM_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Lemma lem54978 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem54979 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem54980 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem54979 A B t) (@lem54978 A B t)). Qed.
Lemma lem54981 {A B C : Type'} (f : B -> C) : term2 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem54982 {A B C : Type'} (f : B -> C) : (term2 A B C f) = (term3 A B C f).
Proof. exact (eq_refl (term2 A B C f)). Qed.
Lemma lem54983 {A B C : Type'} (f : B -> C) : term3 A B C f.
Proof. exact (EQ_MP (@lem54982 A B C f) (@lem54981 A B C f)). Qed.
Lemma lem54984 {A B C : Type'} (f : B -> C) (g : A -> B) : term4 A B C f g.
Proof. exact (@lem54983 A B C f g). Qed.
Lemma lem54985 {A B C : Type'} (f : B -> C) (g : A -> B) : (term4 A B C f g) = ((@o A B C f g) = (term5 A B C f g)).
Proof. exact (eq_refl (term4 A B C f g)). Qed.
Lemma lem54987 {A B C : Type'} (P : type478 A B C) : term6 A B C P.
Proof. exact (@lem54786 A B C P). Qed.
Lemma lem54988 {A B C : Type'} (P : type478 A B C) : (term6 A B C P) = ((term7 A B C P) = (term8 A B C P)).
Proof. exact (eq_refl (term6 A B C P)). Qed.
Lemma lem55008 {_5658 _5668 : Type'} (t : type572 _5658 _5668) : (term9 _5658 _5668 t) = t.
Proof. exact (@lem54980 (_5658 -> _5668) Prop t). Qed.
Lemma lem55009 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (f : _5658 -> _5667) : (term10 _5658 _5667 _5668 P f) = (P f).
Proof. exact (@lem55008 _5658 _5668 (P f)). Qed.
Lemma lem55010 {_5658 _5668 : Type'} : (@ex (_5658 -> _5668)) = (@ex (_5658 -> _5668)).
Proof. exact (eq_refl (@ex (_5658 -> _5668))). Qed.
Lemma lem55011 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (f : _5658 -> _5667) : (term11 _5658 _5667 _5668 P f) = (term12 _5658 _5667 _5668 P f).
Proof. exact (MK_COMB (@lem55010 _5658 _5668) (@lem55009 _5658 _5667 _5668 P f)). Qed.
Lemma lem55012 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term13 _5658 _5667 _5668 P) = (term14 _5658 _5667 _5668 P).
Proof. exact (fun_ext (fun f : _5658 -> _5667 => @lem55011 _5658 _5667 _5668 P f)). Qed.
Lemma lem55013 {_5658 _5667 : Type'} : (@ex (_5658 -> _5667)) = (@ex (_5658 -> _5667)).
Proof. exact (eq_refl (@ex (_5658 -> _5667))). Qed.
Lemma lem55014 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term15 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P).
Proof. exact (MK_COMB (@lem55013 _5658 _5667) (@lem55012 _5658 _5667 _5668 P)). Qed.
Lemma lem55021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55022 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term17 _5658 _5667 _5668 P) = (term18 _5658 _5667 _5668 P).
Proof. exact (MK_COMB (@lem55021) (@lem55014 _5658 _5667 _5668 P)). Qed.
Lemma lem55028 {A B C : Type'} (P : type478 A B C) : (term7 A B C P) = (term8 A B C P).
Proof. exact (EQ_MP (@lem54988 A B C P) (@lem54987 A B C P)). Qed.
Lemma lem55029 {_5658 _5667 _5668 : Type'} (P : type478 _5658 _5667 _5668) : (term7 _5658 _5667 _5668 P) = (term8 _5658 _5667 _5668 P).
Proof. exact (@lem55028 _5658 _5667 _5668 P). Qed.
Lemma lem55030 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term19 _5658 _5667 _5668 P) = (term20 _5658 _5667 _5668 P).
Proof. exact (@lem55029 _5658 _5667 _5668 (term21 _5658 _5667 _5668 P)). Qed.
Lemma lem55031 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (h : type1430 _5658 _5667 _5668) : (term22 _5658 _5667 _5668 P h) = (term23 _5658 _5667 _5668 P h).
Proof. exact (eq_refl (term22 _5658 _5667 _5668 P h)). Qed.
Lemma lem55032 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term24 _5658 _5667 _5668 P) = (term21 _5658 _5667 _5668 P).
Proof. exact (fun_ext (fun h : type1430 _5658 _5667 _5668 => @lem55031 _5658 _5667 _5668 P h)). Qed.
Lemma lem55033 {_5658 _5667 _5668 : Type'} : (@ex (_5658 -> prod _5667 _5668)) = (@ex (_5658 -> prod _5667 _5668)).
Proof. exact (eq_refl (@ex (_5658 -> prod _5667 _5668))). Qed.
Lemma lem55034 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term19 _5658 _5667 _5668 P) = (term25 _5658 _5667 _5668 P).
Proof. exact (MK_COMB (@lem55033 _5658 _5667 _5668) (@lem55032 _5658 _5667 _5668 P)). Qed.
Lemma lem55035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55036 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term26 _5658 _5667 _5668 P) = (term27 _5658 _5667 _5668 P).
Proof. exact (MK_COMB (@lem55035) (@lem55034 _5658 _5667 _5668 P)). Qed.
Lemma lem55037 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) (h : _5658 -> _5668) : (term28 _5658 _5667 _5668 P g h) = (term29 _5658 _5667 _5668 P g h).
Proof. exact (eq_refl (term28 _5658 _5667 _5668 P g h)). Qed.
Lemma lem55038 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) : (term30 _5658 _5667 _5668 P g) = (term31 _5658 _5667 _5668 P g).
Proof. exact (fun_ext (fun h : _5658 -> _5668 => @lem55037 _5658 _5667 _5668 P g h)). Qed.
Lemma lem55039 {_5658 _5668 : Type'} : (@ex (_5658 -> _5668)) = (@ex (_5658 -> _5668)).
Proof. exact (eq_refl (@ex (_5658 -> _5668))). Qed.
Lemma lem55040 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) : (term32 _5658 _5667 _5668 P g) = (term33 _5658 _5667 _5668 P g).
Proof. exact (MK_COMB (@lem55039 _5658 _5668) (@lem55038 _5658 _5667 _5668 P g)). Qed.
Lemma lem55041 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term34 _5658 _5667 _5668 P) = (term35 _5658 _5667 _5668 P).
Proof. exact (fun_ext (fun g : _5658 -> _5667 => @lem55040 _5658 _5667 _5668 P g)). Qed.
Lemma lem55042 {_5658 _5667 : Type'} : (@ex (_5658 -> _5667)) = (@ex (_5658 -> _5667)).
Proof. exact (eq_refl (@ex (_5658 -> _5667))). Qed.
Lemma lem55043 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term20 _5658 _5667 _5668 P) = (term36 _5658 _5667 _5668 P).
Proof. exact (MK_COMB (@lem55042 _5658 _5667) (@lem55041 _5658 _5667 _5668 P)). Qed.
Lemma lem55044 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : ((term19 _5658 _5667 _5668 P) = (term20 _5658 _5667 _5668 P)) = ((term25 _5658 _5667 _5668 P) = (term36 _5658 _5667 _5668 P)).
Proof. exact (MK_COMB (@lem55036 _5658 _5667 _5668 P) (@lem55043 _5658 _5667 _5668 P)). Qed.
Lemma lem55045 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term25 _5658 _5667 _5668 P) = (term36 _5658 _5667 _5668 P).
Proof. exact (EQ_MP (@lem55044 _5658 _5667 _5668 P) (@lem55030 _5658 _5667 _5668 P)). Qed.
Lemma lem55059 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term5 A B C f g).
Proof. exact (EQ_MP (@lem54985 A B C f g) (@lem54984 A B C f g)). Qed.
Lemma lem55060 {_5658 _5667 _5668 : Type'} (f : type1207 _5667 _5668) (g : type1430 _5658 _5667 _5668) : (@o _5658 (prod _5667 _5668) _5667 f g) = (term37 _5658 _5667 _5668 f g).
Proof. exact (@lem55059 _5658 (prod _5667 _5668) _5667 f g). Qed.
Lemma lem55061 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) : (term38 _5658 _5667 _5668 g h) = (term39 _5658 _5667 _5668 g h).
Proof. exact (@lem55060 _5658 _5667 _5668 (@fst _5667 _5668) (term40 _5658 _5667 _5668 g h)). Qed.
Lemma lem55063 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55064 {_5658 _5667 _5668 : Type'} (f : type1430 _5658 _5667 _5668) (y : _5658) : (term42 _5658 _5667 _5668 f y) = (f y).
Proof. exact (@lem55063 _5658 (prod _5667 _5668) f y). Qed.
Lemma lem55065 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term43 _5658 _5667 _5668 g h x) = (term44 _5658 _5667 _5668 g h x).
Proof. exact (@lem55064 _5658 _5667 _5668 (term40 _5658 _5667 _5668 g h) x). Qed.
Lemma lem55066 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (a : _5658) : (term44 _5658 _5667 _5668 g h a) = (term45 _5658 _5667 _5668 g h a).
Proof. exact (eq_refl (term44 _5658 _5667 _5668 g h a)). Qed.
Lemma lem55067 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) : (term46 _5658 _5667 _5668 g h) = (term40 _5658 _5667 _5668 g h).
Proof. exact (fun_ext (fun a : _5658 => @lem55066 _5658 _5667 _5668 g h a)). Qed.
Lemma lem55068 {_5658 : Type'} (x : _5658) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem55069 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term43 _5658 _5667 _5668 g h x) = (term44 _5658 _5667 _5668 g h x).
Proof. exact (MK_COMB (@lem55067 _5658 _5667 _5668 g h) (@lem55068 _5658 x)). Qed.
Lemma lem55070 {_5667 _5668 : Type'} : (@eq (prod _5667 _5668)) = (@eq (prod _5667 _5668)).
Proof. exact (eq_refl (@eq (prod _5667 _5668))). Qed.
Lemma lem55071 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term47 _5658 _5667 _5668 g h x) = (term48 _5658 _5667 _5668 g h x).
Proof. exact (MK_COMB (@lem55070 _5667 _5668) (@lem55069 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55072 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term44 _5658 _5667 _5668 g h x) = (term45 _5658 _5667 _5668 g h x).
Proof. exact (eq_refl (term44 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55073 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : ((term43 _5658 _5667 _5668 g h x) = (term44 _5658 _5667 _5668 g h x)) = ((term44 _5658 _5667 _5668 g h x) = (term45 _5658 _5667 _5668 g h x)).
Proof. exact (MK_COMB (@lem55071 _5658 _5667 _5668 g h x) (@lem55072 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55074 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term44 _5658 _5667 _5668 g h x) = (term45 _5658 _5667 _5668 g h x).
Proof. exact (EQ_MP (@lem55073 _5658 _5667 _5668 g h x) (@lem55065 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55075 {_5667 _5668 : Type'} : (@fst _5667 _5668) = (@fst _5667 _5668).
Proof. exact (eq_refl (@fst _5667 _5668)). Qed.
Lemma lem55076 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term49 _5658 _5667 _5668 g h x) = (term50 _5658 _5667 _5668 g h x).
Proof. exact (MK_COMB (@lem55075 _5667 _5668) (@lem55074 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55078 {A B : Type'} (y : B) (x : A) : (term51 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem55079 {_5667 _5668 : Type'} (y : _5668) (x : _5667) : (term51 _5667 _5668 x y) = x.
Proof. exact (@lem55078 _5667 _5668 y x). Qed.
Lemma lem55080 {_5658 _5667 _5668 : Type'} (h : _5658 -> _5668) (g : _5658 -> _5667) (x : _5658) : (term50 _5658 _5667 _5668 g h x) = (g x).
Proof. exact (@lem55079 _5667 _5668 (h x) (g x)). Qed.
Lemma lem55081 {_5658 _5667 _5668 : Type'} (h : _5658 -> _5668) (g : _5658 -> _5667) (x : _5658) : (term49 _5658 _5667 _5668 g h x) = (g x).
Proof. exact (TRANS (@lem55076 _5658 _5667 _5668 g h x) (@lem55080 _5658 _5667 _5668 h g x)). Qed.
Lemma lem55082 {_5658 _5667 _5668 : Type'} (h : _5658 -> _5668) (g : _5658 -> _5667) : (term39 _5658 _5667 _5668 g h) = (term1 _5658 _5667 g).
Proof. exact (fun_ext (fun x : _5658 => @lem55081 _5658 _5667 _5668 h g x)). Qed.
Lemma lem55083 {_5658 _5667 : Type'} (t : _5658 -> _5667) : (term1 _5658 _5667 t) = t.
Proof. exact (@lem54980 _5658 _5667 t). Qed.
Lemma lem55084 {_5658 _5667 : Type'} (g : _5658 -> _5667) : (term1 _5658 _5667 g) = g.
Proof. exact (@lem55083 _5658 _5667 g). Qed.
Lemma lem55085 {_5658 _5667 _5668 : Type'} (h : _5658 -> _5668) (g : _5658 -> _5667) : (term39 _5658 _5667 _5668 g h) = g.
Proof. exact (TRANS (@lem55082 _5658 _5667 _5668 h g) (@lem55084 _5658 _5667 g)). Qed.
Lemma lem55086 {_5658 _5667 _5668 : Type'} (h : _5658 -> _5668) (g : _5658 -> _5667) : (term38 _5658 _5667 _5668 g h) = g.
Proof. exact (TRANS (@lem55061 _5658 _5667 _5668 g h) (@lem55085 _5658 _5667 _5668 h g)). Qed.
Lemma lem55087 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem55088 {_5658 _5667 _5668 : Type'} (h : _5658 -> _5668) (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) : (term52 _5658 _5667 _5668 P g h) = (P g).
Proof. exact (MK_COMB (@lem55087 _5658 _5667 _5668 P) (@lem55086 _5658 _5667 _5668 h g)). Qed.
Lemma lem55090 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term5 A B C f g).
Proof. exact (EQ_MP (@lem54985 A B C f g) (@lem54984 A B C f g)). Qed.
Lemma lem55091 {_5658 _5667 _5668 : Type'} (f : type1208 _5667 _5668) (g : type1430 _5658 _5667 _5668) : (@o _5658 (prod _5667 _5668) _5668 f g) = (term53 _5658 _5667 _5668 f g).
Proof. exact (@lem55090 _5658 (prod _5667 _5668) _5668 f g). Qed.
Lemma lem55092 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) : (term54 _5658 _5667 _5668 g h) = (term55 _5658 _5667 _5668 g h).
Proof. exact (@lem55091 _5658 _5667 _5668 (@snd _5667 _5668) (term40 _5658 _5667 _5668 g h)). Qed.
Lemma lem55094 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55095 {_5658 _5667 _5668 : Type'} (f : type1430 _5658 _5667 _5668) (y : _5658) : (term42 _5658 _5667 _5668 f y) = (f y).
Proof. exact (@lem55094 _5658 (prod _5667 _5668) f y). Qed.
Lemma lem55096 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term43 _5658 _5667 _5668 g h x) = (term44 _5658 _5667 _5668 g h x).
Proof. exact (@lem55095 _5658 _5667 _5668 (term40 _5658 _5667 _5668 g h) x). Qed.
Lemma lem55097 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (a : _5658) : (term44 _5658 _5667 _5668 g h a) = (term45 _5658 _5667 _5668 g h a).
Proof. exact (eq_refl (term44 _5658 _5667 _5668 g h a)). Qed.
Lemma lem55098 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) : (term46 _5658 _5667 _5668 g h) = (term40 _5658 _5667 _5668 g h).
Proof. exact (fun_ext (fun a : _5658 => @lem55097 _5658 _5667 _5668 g h a)). Qed.
Lemma lem55099 {_5658 : Type'} (x : _5658) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem55100 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term43 _5658 _5667 _5668 g h x) = (term44 _5658 _5667 _5668 g h x).
Proof. exact (MK_COMB (@lem55098 _5658 _5667 _5668 g h) (@lem55099 _5658 x)). Qed.
Lemma lem55101 {_5667 _5668 : Type'} : (@eq (prod _5667 _5668)) = (@eq (prod _5667 _5668)).
Proof. exact (eq_refl (@eq (prod _5667 _5668))). Qed.
Lemma lem55102 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term47 _5658 _5667 _5668 g h x) = (term48 _5658 _5667 _5668 g h x).
Proof. exact (MK_COMB (@lem55101 _5667 _5668) (@lem55100 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55103 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term44 _5658 _5667 _5668 g h x) = (term45 _5658 _5667 _5668 g h x).
Proof. exact (eq_refl (term44 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55104 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : ((term43 _5658 _5667 _5668 g h x) = (term44 _5658 _5667 _5668 g h x)) = ((term44 _5658 _5667 _5668 g h x) = (term45 _5658 _5667 _5668 g h x)).
Proof. exact (MK_COMB (@lem55102 _5658 _5667 _5668 g h x) (@lem55103 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55105 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term44 _5658 _5667 _5668 g h x) = (term45 _5658 _5667 _5668 g h x).
Proof. exact (EQ_MP (@lem55104 _5658 _5667 _5668 g h x) (@lem55096 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55106 {_5667 _5668 : Type'} : (@snd _5667 _5668) = (@snd _5667 _5668).
Proof. exact (eq_refl (@snd _5667 _5668)). Qed.
Lemma lem55107 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term56 _5658 _5667 _5668 g h x) = (term57 _5658 _5667 _5668 g h x).
Proof. exact (MK_COMB (@lem55106 _5667 _5668) (@lem55105 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55109 {A B : Type'} (x : A) (y : B) : (term58 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem55110 {_5667 _5668 : Type'} (x : _5667) (y : _5668) : (term58 _5667 _5668 x y) = y.
Proof. exact (@lem55109 _5667 _5668 x y). Qed.
Lemma lem55111 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term57 _5658 _5667 _5668 g h x) = (h x).
Proof. exact (@lem55110 _5667 _5668 (g x) (h x)). Qed.
Lemma lem55112 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) (x : _5658) : (term56 _5658 _5667 _5668 g h x) = (h x).
Proof. exact (TRANS (@lem55107 _5658 _5667 _5668 g h x) (@lem55111 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55113 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) : (term55 _5658 _5667 _5668 g h) = (term1 _5658 _5668 h).
Proof. exact (fun_ext (fun x : _5658 => @lem55112 _5658 _5667 _5668 g h x)). Qed.
Lemma lem55114 {_5658 _5668 : Type'} (t : _5658 -> _5668) : (term1 _5658 _5668 t) = t.
Proof. exact (@lem54980 _5658 _5668 t). Qed.
Lemma lem55115 {_5658 _5668 : Type'} (h : _5658 -> _5668) : (term1 _5658 _5668 h) = h.
Proof. exact (@lem55114 _5658 _5668 h). Qed.
Lemma lem55116 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) : (term55 _5658 _5667 _5668 g h) = h.
Proof. exact (TRANS (@lem55113 _5658 _5667 _5668 g h) (@lem55115 _5658 _5668 h)). Qed.
Lemma lem55117 {_5658 _5667 _5668 : Type'} (g : _5658 -> _5667) (h : _5658 -> _5668) : (term54 _5658 _5667 _5668 g h) = h.
Proof. exact (TRANS (@lem55092 _5658 _5667 _5668 g h) (@lem55116 _5658 _5667 _5668 g h)). Qed.
Lemma lem55118 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) (h : _5658 -> _5668) : (term29 _5658 _5667 _5668 P g h) = (P g h).
Proof. exact (MK_COMB (@lem55088 _5658 _5667 _5668 h P g) (@lem55117 _5658 _5667 _5668 g h)). Qed.
Lemma lem55119 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) : (term31 _5658 _5667 _5668 P g) = (term10 _5658 _5667 _5668 P g).
Proof. exact (fun_ext (fun h : _5658 -> _5668 => @lem55118 _5658 _5667 _5668 P g h)). Qed.
Lemma lem55120 {_5658 _5668 : Type'} (t : type572 _5658 _5668) : (term9 _5658 _5668 t) = t.
Proof. exact (@lem54980 (_5658 -> _5668) Prop t). Qed.
Lemma lem55121 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) : (term10 _5658 _5667 _5668 P g) = (P g).
Proof. exact (@lem55120 _5658 _5668 (P g)). Qed.
Lemma lem55122 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) : (term31 _5658 _5667 _5668 P g) = (P g).
Proof. exact (TRANS (@lem55119 _5658 _5667 _5668 P g) (@lem55121 _5658 _5667 _5668 P g)). Qed.
Lemma lem55123 {_5658 _5668 : Type'} : (@ex (_5658 -> _5668)) = (@ex (_5658 -> _5668)).
Proof. exact (eq_refl (@ex (_5658 -> _5668))). Qed.
Lemma lem55124 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) (g : _5658 -> _5667) : (term33 _5658 _5667 _5668 P g) = (term12 _5658 _5667 _5668 P g).
Proof. exact (MK_COMB (@lem55123 _5658 _5668) (@lem55122 _5658 _5667 _5668 P g)). Qed.
Lemma lem55125 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term35 _5658 _5667 _5668 P) = (term14 _5658 _5667 _5668 P).
Proof. exact (fun_ext (fun g : _5658 -> _5667 => @lem55124 _5658 _5667 _5668 P g)). Qed.
Lemma lem55126 {_5658 _5667 : Type'} : (@ex (_5658 -> _5667)) = (@ex (_5658 -> _5667)).
Proof. exact (eq_refl (@ex (_5658 -> _5667))). Qed.
Lemma lem55127 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term36 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P).
Proof. exact (MK_COMB (@lem55126 _5658 _5667) (@lem55125 _5658 _5667 _5668 P)). Qed.
Lemma lem55134 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term25 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P).
Proof. exact (TRANS (@lem55045 _5658 _5667 _5668 P) (@lem55127 _5658 _5667 _5668 P)). Qed.
Lemma lem55135 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : ((term15 _5658 _5667 _5668 P) = (term25 _5658 _5667 _5668 P)) = ((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)).
Proof. exact (MK_COMB (@lem55022 _5658 _5667 _5668 P) (@lem55134 _5658 _5667 _5668 P)). Qed.
Lemma lem55137 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem55138 (x : Prop) : (x = x) = True.
Proof. exact (@lem55137 Prop x). Qed.
Lemma lem55139 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : ((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True.
Proof. exact (@lem55138 (term16 _5658 _5667 _5668 P)). Qed.
Lemma lem55142 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term59 _5658 _5667 _5668 P) = (term59 _5658 _5667 _5668 P).
Proof. exact (eq_refl (term59 _5658 _5667 _5668 P)). Qed.
Lemma lem55143 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term59 _5658 _5667 _5668 P) = (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True).
Proof. exact (eq_refl (term59 _5658 _5667 _5668 P)). Qed.
Lemma lem55144 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term60 _5658 _5667 _5668 P) = (term60 _5658 _5667 _5668 P).
Proof. exact (eq_refl (term60 _5658 _5667 _5668 P)). Qed.
Lemma lem55145 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : ((term59 _5658 _5667 _5668 P) = (term59 _5658 _5667 _5668 P)) = ((term59 _5658 _5667 _5668 P) = (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True)).
Proof. exact (MK_COMB (@lem55144 _5658 _5667 _5668 P) (@lem55143 _5658 _5667 _5668 P)). Qed.
Lemma lem55146 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term59 _5658 _5667 _5668 P) = (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True).
Proof. exact (eq_refl (term59 _5658 _5667 _5668 P)). Qed.
Lemma lem55147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55148 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (term60 _5658 _5667 _5668 P) = (term61 _5658 _5667 _5668 P).
Proof. exact (MK_COMB (@lem55147) (@lem55146 _5658 _5667 _5668 P)). Qed.
Lemma lem55149 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True) = (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True).
Proof. exact (eq_refl (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True)). Qed.
Lemma lem55150 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : ((term59 _5658 _5667 _5668 P) = (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True)) = ((((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True) = (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True)).
Proof. exact (MK_COMB (@lem55148 _5658 _5667 _5668 P) (@lem55149 _5658 _5667 _5668 P)). Qed.
Lemma lem55151 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : ((term59 _5658 _5667 _5668 P) = (term59 _5658 _5667 _5668 P)) = ((((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True) = (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True)).
Proof. exact (TRANS (@lem55145 _5658 _5667 _5668 P) (@lem55150 _5658 _5667 _5668 P)). Qed.
Lemma lem55152 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True) = (((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True).
Proof. exact (EQ_MP (@lem55151 _5658 _5667 _5668 P) (@lem55142 _5658 _5667 _5668 P)). Qed.
Lemma lem55153 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : ((term16 _5658 _5667 _5668 P) = (term16 _5658 _5667 _5668 P)) = True.
Proof. exact (EQ_MP (@lem55152 _5658 _5667 _5668 P) (@lem55139 _5658 _5667 _5668 P)). Qed.
Lemma lem55154 {_5658 _5667 _5668 : Type'} (P : type524 _5658 _5667 _5668) : ((term15 _5658 _5667 _5668 P) = (term25 _5658 _5667 _5668 P)) = True.
Proof. exact (TRANS (@lem55135 _5658 _5667 _5668 P) (@lem55153 _5658 _5667 _5668 P)). Qed.
Lemma lem55155 {_5658 _5667 _5668 : Type'} : (term62 _5658 _5667 _5668) = (term63 _5658 _5667 _5668).
Proof. exact (fun_ext (fun P : type524 _5658 _5667 _5668 => @lem55154 _5658 _5667 _5668 P)). Qed.
Lemma lem55156 {_5658 _5667 _5668 : Type'} : (@all ((_5658 -> _5667) -> (_5658 -> _5668) -> Prop)) = (@all ((_5658 -> _5667) -> (_5658 -> _5668) -> Prop)).
Proof. exact (eq_refl (@all ((_5658 -> _5667) -> (_5658 -> _5668) -> Prop))). Qed.
Lemma lem55157 {_5658 _5667 _5668 : Type'} : (term64 _5658 _5667 _5668) = (term65 _5658 _5667 _5668).
Proof. exact (MK_COMB (@lem55156 _5658 _5667 _5668) (@lem55155 _5658 _5667 _5668)). Qed.
Lemma lem55159 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem55160 {_5658 _5667 _5668 : Type'} (t : Prop) : (term67 _5658 _5667 _5668 t) = t.
Proof. exact (@lem55159 (type524 _5658 _5667 _5668) t). Qed.
Lemma lem55161 {_5658 _5667 _5668 : Type'} : (term65 _5658 _5667 _5668) = True.
Proof. exact (@lem55160 _5658 _5667 _5668 True). Qed.
Lemma lem55162 {_5658 _5667 _5668 : Type'} : (term64 _5658 _5667 _5668) = True.
Proof. exact (TRANS (@lem55157 _5658 _5667 _5668) (@lem55161 _5658 _5667 _5668)). Qed.
Lemma lem55163 {_5658 _5667 _5668 : Type'} : True = (term64 _5658 _5667 _5668).
Proof. exact (SYM (@lem55162 _5658 _5667 _5668)). Qed.
Lemma lem55166 {_5658 _5667 _5668 : Type'} : term64 _5658 _5667 _5668.
Proof. exact (EQ_MP (@lem55163 _5658 _5667 _5668) (@lem0)). Qed.
