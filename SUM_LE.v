Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_LE_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import REAL_LE_ADD2_spec.
Require Import SUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1339240_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7071001 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem7071002 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem7071003 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem7071002 A x) (@lem7071001 A x)). Qed.
Lemma lem7071004 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem7071003 A x y). Qed.
Lemma lem7071005 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem7071006 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem7071005 A y x) (@lem7071004 A x y)). Qed.
Lemma lem7071007 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term4 A y x s.
Proof. exact (@lem7071006 A y x s). Qed.
Lemma lem7071008 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A y x s) = ((term5 A x y s) = (term6 A y x s)).
Proof. exact (eq_refl (term4 A y x s)). Qed.
Lemma lem7071010 (w : real) : term7 w.
Proof. exact (@lem1502113 w). Qed.
Lemma lem7071011 (w : real) : (term7 w) = (term8 w).
Proof. exact (eq_refl (term7 w)). Qed.
Lemma lem7071012 (w : real) : term8 w.
Proof. exact (EQ_MP (@lem7071011 w) (@lem7071010 w)). Qed.
Lemma lem7071013 (w : real) (x : real) : term9 w x.
Proof. exact (@lem7071012 w x). Qed.
Lemma lem7071014 (w : real) (x : real) : (term9 w x) = (term10 w x).
Proof. exact (eq_refl (term9 w x)). Qed.
Lemma lem7071015 (w : real) (x : real) : term10 w x.
Proof. exact (EQ_MP (@lem7071014 w x) (@lem7071013 w x)). Qed.
Lemma lem7071016 (w : real) (x : real) (y : real) : term11 w x y.
Proof. exact (@lem7071015 w x y). Qed.
Lemma lem7071017 (w : real) (y : real) (x : real) : (term11 w x y) = (term12 w y x).
Proof. exact (eq_refl (term11 w x y)). Qed.
Lemma lem7071018 (w : real) (y : real) (x : real) : term12 w y x.
Proof. exact (EQ_MP (@lem7071017 w y x) (@lem7071016 w x y)). Qed.
Lemma lem7071019 (w : real) (y : real) (x : real) (z : real) : term13 w y x z.
Proof. exact (@lem7071018 w y x z). Qed.
Lemma lem7071020 (w : real) (y : real) (x : real) (z : real) : (term13 w y x z) = (term14 w y x z).
Proof. exact (eq_refl (term13 w y x z)). Qed.
Lemma lem7071021 (w : real) (y : real) (x : real) (z : real) : term14 w y x z.
Proof. exact (EQ_MP (@lem7071020 w y x z) (@lem7071019 w y x z)). Qed.
Lemma lem7071022 (w : real) (x : real) (y : real) (z : real) (h1 : term15 w x y z) : term15 w x y z.
Proof. exact (h1). Qed.
Lemma lem7071023 (w : real) (x : real) (y : real) (z : real) (h1 : term15 w x y z) : term16 w y x z.
Proof. exact (@lem7071021 w y x z (@lem7071022 w x y z h1)). Qed.
Lemma lem7071024 (w : real) (y : real) (x : real) (z : real) : (term16 w y x z) = ((term16 w y x z) = True).
Proof. exact (@lem7 (term16 w y x z)). Qed.
Lemma lem7071025 (w : real) (x : real) (y : real) (z : real) (h1 : term15 w x y z) : (term16 w y x z) = True.
Proof. exact (EQ_MP (@lem7071024 w y x z) (@lem7071023 w x y z h1)). Qed.
Lemma lem7071031 (x : real) : term17 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem7071032 (x : real) : (term17 x) = (real_le x x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem7071033 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem7071032 x) (@lem7071031 x)). Qed.
Lemma lem7071034 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem7071036 {_131524 : Type'} : term18 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7071037 {_131524 : Type'} (x : _131524) : term19 _131524 x.
Proof. exact (@lem7071036 _131524 x). Qed.
Lemma lem7071038 {_131524 : Type'} (x : _131524) : (term19 _131524 x) = (term20 _131524 x).
Proof. exact (eq_refl (term19 _131524 x)). Qed.
Lemma lem7071039 {_131524 : Type'} (x : _131524) : term20 _131524 x.
Proof. exact (EQ_MP (@lem7071038 _131524 x) (@lem7071037 _131524 x)). Qed.
Lemma lem7071040 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term21 _131524 x f.
Proof. exact (@lem7071039 _131524 x f). Qed.
Lemma lem7071041 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term21 _131524 x f) = (term22 _131524 x f).
Proof. exact (eq_refl (term21 _131524 x f)). Qed.
Lemma lem7071042 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term22 _131524 x f.
Proof. exact (EQ_MP (@lem7071041 _131524 x f) (@lem7071040 _131524 x f)). Qed.
Lemma lem7071043 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term23 _131524 x f s.
Proof. exact (@lem7071042 _131524 x f s). Qed.
Lemma lem7071044 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term23 _131524 x f s) = (term24 _131524 x s f).
Proof. exact (eq_refl (term23 _131524 x f s)). Qed.
Lemma lem7071045 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term24 _131524 x s f.
Proof. exact (EQ_MP (@lem7071044 _131524 x s f) (@lem7071043 _131524 x f s)). Qed.
Lemma lem7071046 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7071047 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term25 _131524 x s f) = (term26 _131524 x s f).
Proof. exact (@lem7071045 _131524 x s f (@lem7071046 _131524 s h1)). Qed.
Lemma lem7071053 {_131483 : Type'} : term27 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7071054 {_131483 : Type'} (f : _131483 -> real) : term28 _131483 f.
Proof. exact (@lem7071053 _131483 f). Qed.
Lemma lem7071055 {_131483 : Type'} (f : _131483 -> real) : (term28 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term29).
Proof. exact (eq_refl (term28 _131483 f)). Qed.
Lemma lem7071057 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem7071058 {A : Type'} (P : type686 A) (h1 : term30 A) : term31 A P.
Proof. exact (@lem7071057 A h1 P). Qed.
Lemma lem7071059 {A : Type'} (P : type686 A) : (term31 A P) = (term32 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem7071060 {A : Type'} (P : type686 A) (h1 : term30 A) : term32 A P.
Proof. exact (EQ_MP (@lem7071059 A P) (@lem7071058 A P h1)). Qed.
Lemma lem7071061 {A : Type'} (P : type686 A) (h1 : term33 A P) : term33 A P.
Proof. exact (h1). Qed.
Lemma lem7071062 {A : Type'} (P : type686 A) (h1 : term30 A) (h2 : term33 A P) : term34 A P.
Proof. exact (@lem7071060 A P h1 (@lem7071061 A P h2)). Qed.
Lemma lem7071063 {A : Type'} (P : type686 A) (h1 : term33 A P) : term35 A P.
Proof. exact (fun h0 : term30 A => @lem7071062 A P h0 h1). Qed.
Lemma lem7071064 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem7071065 {A : Type'} (P : type686 A) (h1 : term30 A) (h2 : term33 A P) : term34 A P.
Proof. exact (@lem7071063 A P h2 (@lem7071064 A h1)). Qed.
Lemma lem7071066 {A : Type'} (P : type686 A) (h1 : term30 A) : term32 A P.
Proof. exact (fun h0 : term33 A P => @lem7071065 A P h1 h0). Qed.
Lemma lem7071067 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (fun P : type686 A => @lem7071066 A P h1). Qed.
Lemma lem7071068 {A : Type'} : term36 A.
Proof. exact (fun h0 : term30 A => @lem7071067 A h0). Qed.
Lemma lem7071069 {A : Type'} : term30 A.
Proof. exact (@lem7071068 A (@lem3558722 A)). Qed.
Lemma lem7071070 {A : Type'} (P : type686 A) : term31 A P.
Proof. exact (@lem7071069 A P). Qed.
Lemma lem7071071 {A : Type'} (P : type686 A) : (term31 A P) = (term32 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem7071086 (p : Prop) (q : Prop) (r : Prop) : (term37 p q r) = (term38 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7071087 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term39 _132081 f s g) = (term40 _132081 f s g).
Proof. exact (@lem7071086 (@FINITE _132081 s) (term41 _132081 s f g) (term42 _132081 f s g)). Qed.
Lemma lem7071088 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term43 _132081 f g) = (term44 _132081 f g).
Proof. exact (fun_ext (fun s : _132081 -> Prop => @lem7071087 _132081 f s g)). Qed.
Lemma lem7071089 {_132081 : Type'} : (@all (_132081 -> Prop)) = (@all (_132081 -> Prop)).
Proof. exact (eq_refl (@all (_132081 -> Prop))). Qed.
Lemma lem7071090 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term45 _132081 f g) = (term46 _132081 f g).
Proof. exact (MK_COMB (@lem7071089 _132081) (@lem7071088 _132081 f g)). Qed.
Lemma lem7071091 {_132081 : Type'} (f : _132081 -> real) : (term47 _132081 f) = (term48 _132081 f).
Proof. exact (fun_ext (fun g : _132081 -> real => @lem7071090 _132081 f g)). Qed.
Lemma lem7071092 {_132081 : Type'} : (@all (_132081 -> real)) = (@all (_132081 -> real)).
Proof. exact (eq_refl (@all (_132081 -> real))). Qed.
Lemma lem7071093 {_132081 : Type'} (f : _132081 -> real) : (term49 _132081 f) = (term50 _132081 f).
Proof. exact (MK_COMB (@lem7071092 _132081) (@lem7071091 _132081 f)). Qed.
Lemma lem7071094 {_132081 : Type'} : (term51 _132081) = (term52 _132081).
Proof. exact (fun_ext (fun f : _132081 -> real => @lem7071093 _132081 f)). Qed.
Lemma lem7071095 {_132081 : Type'} : (@all (_132081 -> real)) = (@all (_132081 -> real)).
Proof. exact (eq_refl (@all (_132081 -> real))). Qed.
Lemma lem7071096 {_132081 : Type'} : (term53 _132081) = (term54 _132081).
Proof. exact (MK_COMB (@lem7071095 _132081) (@lem7071094 _132081)). Qed.
Lemma lem7071097 {_132081 : Type'} : (term54 _132081) = (term53 _132081).
Proof. exact (SYM (@lem7071096 _132081)). Qed.
Lemma lem7071099 {A : Type'} (P : type686 A) : term32 A P.
Proof. exact (EQ_MP (@lem7071071 A P) (@lem7071070 A P)). Qed.
Lemma lem7071100 {_132081 : Type'} (P : type686 _132081) : term32 _132081 P.
Proof. exact (@lem7071099 _132081 P). Qed.
Lemma lem7071101 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term55 _132081 f g.
Proof. exact (@lem7071100 _132081 (term56 _132081 f g)). Qed.
Lemma lem7071102 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term57 _132081 f g) = (term58 _132081 f g).
Proof. exact (eq_refl (term57 _132081 f g)). Qed.
Lemma lem7071103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7071104 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term59 _132081 f g) = (term60 _132081 f g).
Proof. exact (MK_COMB (@lem7071103) (@lem7071102 _132081 f g)). Qed.
Lemma lem7071105 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term61 _132081 f g s) = (term62 _132081 f s g).
Proof. exact (eq_refl (term61 _132081 f g s)). Qed.
Lemma lem7071106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7071107 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term63 _132081 f g s) = (term64 _132081 f s g).
Proof. exact (MK_COMB (@lem7071106) (@lem7071105 _132081 f s g)). Qed.
Lemma lem7071108 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) : (term65 _132081 x s) = (term65 _132081 x s).
Proof. exact (eq_refl (term65 _132081 x s)). Qed.
Lemma lem7071109 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) : (term66 _132081 f g x s) = (term67 _132081 f g x s).
Proof. exact (MK_COMB (@lem7071107 _132081 f s g) (@lem7071108 _132081 x s)). Qed.
Lemma lem7071110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7071111 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) : (term68 _132081 f g x s) = (term69 _132081 f g x s).
Proof. exact (MK_COMB (@lem7071110) (@lem7071109 _132081 f g x s)). Qed.
Lemma lem7071112 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : (term70 _132081 f g x s) = (term71 _132081 f x s g).
Proof. exact (eq_refl (term70 _132081 f g x s)). Qed.
Lemma lem7071113 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : (term72 _132081 f g x s) = (term73 _132081 f x s g).
Proof. exact (MK_COMB (@lem7071111 _132081 f g x s) (@lem7071112 _132081 f x s g)). Qed.
Lemma lem7071114 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (g : _132081 -> real) : (term74 _132081 f g x) = (term75 _132081 f x g).
Proof. exact (fun_ext (fun s : _132081 -> Prop => @lem7071113 _132081 f x s g)). Qed.
Lemma lem7071115 {_132081 : Type'} : (@all (_132081 -> Prop)) = (@all (_132081 -> Prop)).
Proof. exact (eq_refl (@all (_132081 -> Prop))). Qed.
Lemma lem7071116 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (g : _132081 -> real) : (term76 _132081 f g x) = (term77 _132081 f x g).
Proof. exact (MK_COMB (@lem7071115 _132081) (@lem7071114 _132081 f x g)). Qed.
Lemma lem7071117 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term78 _132081 f g) = (term79 _132081 f g).
Proof. exact (fun_ext (fun x : _132081 => @lem7071116 _132081 f x g)). Qed.
Lemma lem7071118 {_132081 : Type'} : (@all _132081) = (@all _132081).
Proof. exact (eq_refl (@all _132081)). Qed.
Lemma lem7071119 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term80 _132081 f g) = (term81 _132081 f g).
Proof. exact (MK_COMB (@lem7071118 _132081) (@lem7071117 _132081 f g)). Qed.
Lemma lem7071120 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term82 _132081 f g) = (term83 _132081 f g).
Proof. exact (MK_COMB (@lem7071104 _132081 f g) (@lem7071119 _132081 f g)). Qed.
Lemma lem7071121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7071122 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term84 _132081 f g) = (term85 _132081 f g).
Proof. exact (MK_COMB (@lem7071121) (@lem7071120 _132081 f g)). Qed.
Lemma lem7071123 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term61 _132081 f g s) = (term62 _132081 f s g).
Proof. exact (eq_refl (term61 _132081 f g s)). Qed.
Lemma lem7071124 {_132081 : Type'} (s : _132081 -> Prop) : (term86 _132081 s) = (term86 _132081 s).
Proof. exact (eq_refl (term86 _132081 s)). Qed.
Lemma lem7071125 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term87 _132081 f g s) = (term40 _132081 f s g).
Proof. exact (MK_COMB (@lem7071124 _132081 s) (@lem7071123 _132081 f s g)). Qed.
Lemma lem7071126 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term88 _132081 f g) = (term44 _132081 f g).
Proof. exact (fun_ext (fun s : _132081 -> Prop => @lem7071125 _132081 f s g)). Qed.
Lemma lem7071127 {_132081 : Type'} : (@all (_132081 -> Prop)) = (@all (_132081 -> Prop)).
Proof. exact (eq_refl (@all (_132081 -> Prop))). Qed.
Lemma lem7071128 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term89 _132081 f g) = (term46 _132081 f g).
Proof. exact (MK_COMB (@lem7071127 _132081) (@lem7071126 _132081 f g)). Qed.
Lemma lem7071129 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term55 _132081 f g) = (term90 _132081 f g).
Proof. exact (MK_COMB (@lem7071122 _132081 f g) (@lem7071128 _132081 f g)). Qed.
Lemma lem7071130 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term90 _132081 f g.
Proof. exact (EQ_MP (@lem7071129 _132081 f g) (@lem7071101 _132081 f g)). Qed.
Lemma lem7071136 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7071137 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem7071136 p q p' q'). Qed.
Lemma lem7071138 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem7071137 p q p'). Qed.
Lemma lem7071139 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term94 _132081 f g.
Proof. exact (@lem7071138 (term95 _132081 f g) (term96 _132081 f g)). Qed.
Lemma lem7071140 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (p' : Prop) : term97 _132081 f g p'.
Proof. exact (@lem7071139 _132081 f g p'). Qed.
Lemma lem7071141 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (p' : Prop) : (term97 _132081 f g p') = (term98 _132081 f g p').
Proof. exact (eq_refl (term97 _132081 f g p')). Qed.
Lemma lem7071142 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (p' : Prop) : term98 _132081 f g p'.
Proof. exact (EQ_MP (@lem7071141 _132081 f g p') (@lem7071140 _132081 f g p')). Qed.
Lemma lem7071143 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (p' : Prop) (q' : Prop) : term99 _132081 f g p' q'.
Proof. exact (@lem7071142 _132081 f g p' q'). Qed.
Lemma lem7071144 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (p' : Prop) (q' : Prop) : (term99 _132081 f g p' q') = (term100 _132081 f g p' q').
Proof. exact (eq_refl (term99 _132081 f g p' q')). Qed.
Lemma lem7071145 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (p' : Prop) (q' : Prop) : term100 _132081 f g p' q'.
Proof. exact (EQ_MP (@lem7071144 _132081 f g p' q') (@lem7071143 _132081 f g p' q')). Qed.
Lemma lem7071177 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term95 _132081 f g) = (term95 _132081 f g).
Proof. exact (eq_refl (term95 _132081 f g)). Qed.
Lemma lem7071178 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (q' : Prop) : term101 _132081 f g q'.
Proof. exact (@lem7071145 _132081 f g (term95 _132081 f g) q'). Qed.
Lemma lem7071179 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (q' : Prop) : term102 _132081 f g q'.
Proof. exact (@lem7071178 _132081 f g q' (@lem7071177 _132081 f g)). Qed.
Lemma lem7071196 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term29.
Proof. exact (EQ_MP (@lem7071055 _131483 f) (@lem7071054 _131483 f)). Qed.
Lemma lem7071197 {_132081 : Type'} (f : _132081 -> real) : (@sum _132081 (@EMPTY _132081) f) = term29.
Proof. exact (@lem7071196 _132081 f). Qed.
Lemma lem7071198 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7071199 {_132081 : Type'} (f : _132081 -> real) : (term103 _132081 f) = term104.
Proof. exact (MK_COMB (@lem7071198) (@lem7071197 _132081 f)). Qed.
Lemma lem7071201 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term29.
Proof. exact (EQ_MP (@lem7071055 _131483 f) (@lem7071054 _131483 f)). Qed.
Lemma lem7071202 {_132081 : Type'} (f : _132081 -> real) : (@sum _132081 (@EMPTY _132081) f) = term29.
Proof. exact (@lem7071201 _132081 f). Qed.
Lemma lem7071203 {_132081 : Type'} (g : _132081 -> real) : (@sum _132081 (@EMPTY _132081) g) = term29.
Proof. exact (@lem7071202 _132081 g). Qed.
Lemma lem7071204 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term96 _132081 f g) = term105.
Proof. exact (MK_COMB (@lem7071199 _132081 f) (@lem7071203 _132081 g)). Qed.
Lemma lem7071206 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem7071034 x) (@lem7071033 x)). Qed.
Lemma lem7071207 : term105 = True.
Proof. exact (@lem7071206 term29). Qed.
Lemma lem7071208 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term96 _132081 f g) = True.
Proof. exact (TRANS (@lem7071204 _132081 f g) (@lem7071207)). Qed.
Lemma lem7071209 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term106 _132081 f g.
Proof. exact (fun h0 : term95 _132081 f g => @lem7071208 _132081 f g). Qed.
Lemma lem7071210 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term107 _132081 f g.
Proof. exact (@lem7071179 _132081 f g True). Qed.
Lemma lem7071211 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term58 _132081 f g) = (term108 _132081 f g).
Proof. exact (@lem7071210 _132081 f g (@lem7071209 _132081 f g)). Qed.
Lemma lem7071213 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7071214 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term108 _132081 f g) = True.
Proof. exact (@lem7071213 (term95 _132081 f g)). Qed.
Lemma lem7071215 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term58 _132081 f g) = True.
Proof. exact (TRANS (@lem7071211 _132081 f g) (@lem7071214 _132081 f g)). Qed.
Lemma lem7071216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7071217 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term60 _132081 f g) = (and True).
Proof. exact (MK_COMB (@lem7071216) (@lem7071215 _132081 f g)). Qed.
Lemma lem7071229 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7071230 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem7071229 p q p' q'). Qed.
Lemma lem7071231 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem7071230 p q p'). Qed.
Lemma lem7071232 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : term109 _132081 f x s g.
Proof. exact (@lem7071231 (term67 _132081 f g x s) (term71 _132081 f x s g)). Qed.
Lemma lem7071233 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) : term110 _132081 f x s g p'.
Proof. exact (@lem7071232 _132081 f x s g p'). Qed.
Lemma lem7071234 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) : (term110 _132081 f x s g p') = (term111 _132081 f x s g p').
Proof. exact (eq_refl (term110 _132081 f x s g p')). Qed.
Lemma lem7071235 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) : term111 _132081 f x s g p'.
Proof. exact (EQ_MP (@lem7071234 _132081 f x s g p') (@lem7071233 _132081 f x s g p')). Qed.
Lemma lem7071236 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) (q' : Prop) : term112 _132081 f x s g p' q'.
Proof. exact (@lem7071235 _132081 f x s g p' q'). Qed.
Lemma lem7071237 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) (q' : Prop) : (term112 _132081 f x s g p' q') = (term113 _132081 f x s g p' q').
Proof. exact (eq_refl (term112 _132081 f x s g p' q')). Qed.
Lemma lem7071238 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) (q' : Prop) : term113 _132081 f x s g p' q'.
Proof. exact (EQ_MP (@lem7071237 _132081 f x s g p' q') (@lem7071236 _132081 f x s g p' q')). Qed.
Lemma lem7071342 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) : (term67 _132081 f g x s) = (term67 _132081 f g x s).
Proof. exact (eq_refl (term67 _132081 f g x s)). Qed.
Lemma lem7071343 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (q' : Prop) : term114 _132081 f g x s q'.
Proof. exact (@lem7071238 _132081 f x s g (term67 _132081 f g x s) q'). Qed.
Lemma lem7071344 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (q' : Prop) : term115 _132081 f g x s q'.
Proof. exact (@lem7071343 _132081 f g x s q' (@lem7071342 _132081 f g x s)). Qed.
Lemma lem7071345 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term67 _132081 f g x s.
Proof. exact (h1). Qed.
Lemma lem7071346 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term65 _132081 x s.
Proof. exact (proj2 (@lem7071345 _132081 f g x s h1)). Qed.
Lemma lem7071347 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : @FINITE _132081 s.
Proof. exact (proj2 (@lem7071346 _132081 f g x s h1)). Qed.
Lemma lem7071348 {_132081 : Type'} (s : _132081 -> Prop) : (@FINITE _132081 s) = ((@FINITE _132081 s) = True).
Proof. exact (@lem7 (@FINITE _132081 s)). Qed.
Lemma lem7071350 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term116 _132081 x s.
Proof. exact (proj1 (@lem7071346 _132081 f g x s h1)). Qed.
Lemma lem7071351 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) : term117 _132081 x s.
Proof. exact (@lem82 (@IN _132081 x s)). Qed.
Lemma lem7071353 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term62 _132081 f s g.
Proof. exact (proj1 (@lem7071345 _132081 f g x s h1)). Qed.
Lemma lem7071354 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term41 _132081 s f g) : term41 _132081 s f g.
Proof. exact (h1). Qed.
Lemma lem7071355 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term41 _132081 s f g) (h2 : term67 _132081 f g x s) : term42 _132081 f s g.
Proof. exact (@lem7071353 _132081 f g x s h2 (@lem7071354 _132081 s f g h1)). Qed.
Lemma lem7071356 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term42 _132081 f s g) = ((term42 _132081 f s g) = True).
Proof. exact (@lem7 (term42 _132081 f s g)). Qed.
Lemma lem7071357 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term41 _132081 s f g) (h2 : term67 _132081 f g x s) : (term42 _132081 f s g) = True.
Proof. exact (EQ_MP (@lem7071356 _132081 f s g) (@lem7071355 _132081 f g x s h1 h2)). Qed.
Lemma lem7071366 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7071367 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem7071366 p q p' q'). Qed.
Lemma lem7071368 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem7071367 p q p'). Qed.
Lemma lem7071369 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : term118 _132081 f x s g.
Proof. exact (@lem7071368 (term119 _132081 x s f g) (term120 _132081 f x s g)). Qed.
Lemma lem7071370 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) : term121 _132081 f x s g p'.
Proof. exact (@lem7071369 _132081 f x s g p'). Qed.
Lemma lem7071371 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) : (term121 _132081 f x s g p') = (term122 _132081 f x s g p').
Proof. exact (eq_refl (term121 _132081 f x s g p')). Qed.
Lemma lem7071372 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) : term122 _132081 f x s g p'.
Proof. exact (EQ_MP (@lem7071371 _132081 f x s g p') (@lem7071370 _132081 f x s g p')). Qed.
Lemma lem7071373 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) (q' : Prop) : term123 _132081 f x s g p' q'.
Proof. exact (@lem7071372 _132081 f x s g p' q'). Qed.
Lemma lem7071374 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) (q' : Prop) : (term123 _132081 f x s g p' q') = (term124 _132081 f x s g p' q').
Proof. exact (eq_refl (term123 _132081 f x s g p' q')). Qed.
Lemma lem7071375 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (p' : Prop) (q' : Prop) : term124 _132081 f x s g p' q'.
Proof. exact (EQ_MP (@lem7071374 _132081 f x s g p' q') (@lem7071373 _132081 f x s g p' q')). Qed.
Lemma lem7071383 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7071384 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem7071383 p q p' q'). Qed.
Lemma lem7071385 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem7071384 p q p'). Qed.
Lemma lem7071386 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) : term125 _132081 x s f g x'.
Proof. exact (@lem7071385 (term5 _132081 x' x s) (term126 _132081 f g x')). Qed.
Lemma lem7071387 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) (p' : Prop) : term127 _132081 x s f g x' p'.
Proof. exact (@lem7071386 _132081 x s f g x' p'). Qed.
Lemma lem7071388 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) (p' : Prop) : (term127 _132081 x s f g x' p') = (term128 _132081 x s f g x' p').
Proof. exact (eq_refl (term127 _132081 x s f g x' p')). Qed.
Lemma lem7071389 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) (p' : Prop) : term128 _132081 x s f g x' p'.
Proof. exact (EQ_MP (@lem7071388 _132081 x s f g x' p') (@lem7071387 _132081 x s f g x' p')). Qed.
Lemma lem7071390 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) (p' : Prop) (q' : Prop) : term129 _132081 x s f g x' p' q'.
Proof. exact (@lem7071389 _132081 x s f g x' p' q'). Qed.
Lemma lem7071391 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) (p' : Prop) (q' : Prop) : (term129 _132081 x s f g x' p' q') = (term130 _132081 x s f g x' p' q').
Proof. exact (eq_refl (term129 _132081 x s f g x' p' q')). Qed.
Lemma lem7071392 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) (p' : Prop) (q' : Prop) : term130 _132081 x s f g x' p' q'.
Proof. exact (EQ_MP (@lem7071391 _132081 x s f g x' p' q') (@lem7071390 _132081 x s f g x' p' q')). Qed.
Lemma lem7071394 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem7071008 A y x s) (@lem7071007 A y x s)). Qed.
Lemma lem7071395 {_132081 : Type'} (y : _132081) (x : _132081) (s : _132081 -> Prop) : (term5 _132081 x y s) = (term6 _132081 y x s).
Proof. exact (@lem7071394 _132081 y x s). Qed.
Lemma lem7071396 {_132081 : Type'} (x : _132081) (x' : _132081) (s : _132081 -> Prop) : (term5 _132081 x' x s) = (term6 _132081 x x' s).
Proof. exact (@lem7071395 _132081 x x' s). Qed.
Lemma lem7071401 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (x' : _132081) (s : _132081 -> Prop) (q' : Prop) : term131 _132081 f g x x' s q'.
Proof. exact (@lem7071392 _132081 x s f g x' (term6 _132081 x x' s) q'). Qed.
Lemma lem7071402 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (x' : _132081) (s : _132081 -> Prop) (q' : Prop) : term132 _132081 f g x x' s q'.
Proof. exact (@lem7071401 _132081 f g x x' s q' (@lem7071396 _132081 x x' s)). Qed.
Lemma lem7071408 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) : (term126 _132081 f g x') = (term126 _132081 f g x').
Proof. exact (eq_refl (term126 _132081 f g x')). Qed.
Lemma lem7071409 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) : term133 _132081 x s f g x'.
Proof. exact (fun h0 : term6 _132081 x x' s => @lem7071408 _132081 f g x'). Qed.
Lemma lem7071410 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) : term134 _132081 x s f g x'.
Proof. exact (@lem7071402 _132081 f g x x' s (term126 _132081 f g x')). Qed.
Lemma lem7071411 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) : (term135 _132081 x s f g x') = (term136 _132081 x s f g x').
Proof. exact (@lem7071410 _132081 x s f g x' (@lem7071409 _132081 x s f g x')). Qed.
Lemma lem7071447 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) : (term137 _132081 x s f g) = (term138 _132081 x s f g).
Proof. exact (fun_ext (fun x' : _132081 => @lem7071411 _132081 x s f g x')). Qed.
Lemma lem7071483 {_132081 : Type'} : (@all _132081) = (@all _132081).
Proof. exact (eq_refl (@all _132081)). Qed.
Lemma lem7071484 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) : (term119 _132081 x s f g) = (term139 _132081 x s f g).
Proof. exact (MK_COMB (@lem7071483 _132081) (@lem7071447 _132081 x s f g)). Qed.
Lemma lem7071524 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (q' : Prop) : term140 _132081 x s f g q'.
Proof. exact (@lem7071375 _132081 f x s g (term139 _132081 x s f g) q'). Qed.
Lemma lem7071525 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (q' : Prop) : term141 _132081 x s f g q'.
Proof. exact (@lem7071524 _132081 x s f g q' (@lem7071484 _132081 x s f g)). Qed.
Lemma lem7071526 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term139 _132081 x s f g.
Proof. exact (h1). Qed.
Lemma lem7071527 {_132081 : Type'} (x' : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term142 _132081 x s f g x'.
Proof. exact (@lem7071526 _132081 x s f g h1 x'). Qed.
Lemma lem7071528 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) : (term142 _132081 x s f g x') = (term136 _132081 x s f g x').
Proof. exact (eq_refl (term142 _132081 x s f g x')). Qed.
Lemma lem7071529 {_132081 : Type'} (x' : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term136 _132081 x s f g x'.
Proof. exact (EQ_MP (@lem7071528 _132081 x s f g x') (@lem7071527 _132081 x' x s f g h1)). Qed.
Lemma lem7071530 {_132081 : Type'} (x : _132081) (x' : _132081) (s : _132081 -> Prop) (h1 : term6 _132081 x x' s) : term6 _132081 x x' s.
Proof. exact (h1). Qed.
Lemma lem7071531 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (x' : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term6 _132081 x x' s) : term126 _132081 f g x'.
Proof. exact (@lem7071529 _132081 x' x s f g h1 (@lem7071530 _132081 x x' s h2)). Qed.
Lemma lem7071532 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x' : _132081) : (term126 _132081 f g x') = ((term126 _132081 f g x') = True).
Proof. exact (@lem7 (term126 _132081 f g x')). Qed.
Lemma lem7071533 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (x' : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term6 _132081 x x' s) : (term126 _132081 f g x') = True.
Proof. exact (EQ_MP (@lem7071532 _132081 f g x') (@lem7071531 _132081 f g x x' s h1 h2)). Qed.
Lemma lem7071542 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term24 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7071047 _131524 x f s h0). Qed.
Lemma lem7071543 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) : term24 _132081 x s f.
Proof. exact (@lem7071542 _132081 x s f). Qed.
Lemma lem7071545 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (@FINITE _132081 s) = True.
Proof. exact (EQ_MP (@lem7071348 _132081 s) (@lem7071347 _132081 f g x s h1)). Qed.
Lemma lem7071546 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : True = (@FINITE _132081 s).
Proof. exact (SYM (@lem7071545 _132081 f g x s h1)). Qed.
Lemma lem7071547 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : @FINITE _132081 s.
Proof. exact (EQ_MP (@lem7071546 _132081 f g x s h1) (@lem0)). Qed.
Lemma lem7071548 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term25 _132081 x s f) = (term26 _132081 x s f).
Proof. exact (@lem7071543 _132081 x s f (@lem7071547 _132081 f g x s h1)). Qed.
Lemma lem7071550 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term143 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7071551 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term144 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7071550 _2963 g t e g' t' e'). Qed.
Lemma lem7071552 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term145 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7071551 _2963 g t e g' t'). Qed.
Lemma lem7071553 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term146 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7071552 _2963 g t e g'). Qed.
Lemma lem7071554 (g : Prop) (t : real) (e : real) : term147 g t e.
Proof. exact (@lem7071553 real g t e). Qed.
Lemma lem7071555 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) : term148 _132081 x s f.
Proof. exact (@lem7071554 (@IN _132081 x s) (@sum _132081 s f) (term149 _132081 x s f)). Qed.
Lemma lem7071556 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) : term150 _132081 x s f g'.
Proof. exact (@lem7071555 _132081 x s f g'). Qed.
Lemma lem7071557 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) : (term150 _132081 x s f g') = (term151 _132081 x s f g').
Proof. exact (eq_refl (term150 _132081 x s f g')). Qed.
Lemma lem7071558 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) : term151 _132081 x s f g'.
Proof. exact (EQ_MP (@lem7071557 _132081 x s f g') (@lem7071556 _132081 x s f g')). Qed.
Lemma lem7071559 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) (t' : real) : term152 _132081 x s f g' t'.
Proof. exact (@lem7071558 _132081 x s f g' t'). Qed.
Lemma lem7071560 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) (t' : real) : (term152 _132081 x s f g' t') = (term153 _132081 x s f g' t').
Proof. exact (eq_refl (term152 _132081 x s f g' t')). Qed.
Lemma lem7071561 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) (t' : real) : term153 _132081 x s f g' t'.
Proof. exact (EQ_MP (@lem7071560 _132081 x s f g' t') (@lem7071559 _132081 x s f g' t')). Qed.
Lemma lem7071562 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) (t' : real) (e' : real) : term154 _132081 x s f g' t' e'.
Proof. exact (@lem7071561 _132081 x s f g' t' e'). Qed.
Lemma lem7071563 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) (t' : real) (e' : real) : (term154 _132081 x s f g' t' e') = (term155 _132081 x s f g' t' e').
Proof. exact (eq_refl (term154 _132081 x s f g' t' e')). Qed.
Lemma lem7071564 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g' : Prop) (t' : real) (e' : real) : term155 _132081 x s f g' t' e'.
Proof. exact (EQ_MP (@lem7071563 _132081 x s f g' t' e') (@lem7071562 _132081 x s f g' t' e')). Qed.
Lemma lem7071566 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (@IN _132081 x s) = False.
Proof. exact (@lem7071351 _132081 x s (@lem7071350 _132081 f g x s h1)). Qed.
Lemma lem7071567 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (t' : real) (e' : real) : term156 _132081 x s f t' e'.
Proof. exact (@lem7071564 _132081 x s f False t' e'). Qed.
Lemma lem7071568 {_132081 : Type'} (t' : real) (e' : real) (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term157 _132081 x s f t' e'.
Proof. exact (@lem7071567 _132081 x s f t' e' (@lem7071566 _132081 f g x s h1)). Qed.
Lemma lem7071572 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) : (@sum _132081 s f) = (@sum _132081 s f).
Proof. exact (eq_refl (@sum _132081 s f)). Qed.
Lemma lem7071573 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) : term158 _132081 s f.
Proof. exact (fun h0 : False => @lem7071572 _132081 s f). Qed.
Lemma lem7071574 {_132081 : Type'} (e' : real) (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term159 _132081 x s f e'.
Proof. exact (@lem7071568 _132081 (@sum _132081 s f) e' f g x s h1). Qed.
Lemma lem7071575 {_132081 : Type'} (e' : real) (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term160 _132081 x s f e'.
Proof. exact (@lem7071574 _132081 e' f g x s h1 (@lem7071573 _132081 s f)). Qed.
Lemma lem7071581 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) : (term149 _132081 x s f) = (term149 _132081 x s f).
Proof. exact (eq_refl (term149 _132081 x s f)). Qed.
Lemma lem7071582 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) : term161 _132081 x s f.
Proof. exact (fun h0 : ~ False => @lem7071581 _132081 x s f). Qed.
Lemma lem7071583 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term162 _132081 x s f.
Proof. exact (@lem7071575 _132081 (term149 _132081 x s f) f g x s h1). Qed.
Lemma lem7071584 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term26 _132081 x s f) = (term163 _132081 x s f).
Proof. exact (@lem7071583 _132081 f g x s h1 (@lem7071582 _132081 x s f)). Qed.
Lemma lem7071586 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7071587 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7071586 real t1 t2). Qed.
Lemma lem7071588 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) : (term163 _132081 x s f) = (term149 _132081 x s f).
Proof. exact (@lem7071587 (@sum _132081 s f) (term149 _132081 x s f)). Qed.
Lemma lem7071589 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term26 _132081 x s f) = (term149 _132081 x s f).
Proof. exact (TRANS (@lem7071584 _132081 f g x s h1) (@lem7071588 _132081 x s f)). Qed.
Lemma lem7071590 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term25 _132081 x s f) = (term149 _132081 x s f).
Proof. exact (TRANS (@lem7071548 _132081 f g x s h1) (@lem7071589 _132081 f g x s h1)). Qed.
Lemma lem7071591 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7071592 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term164 _132081 x s f) = (term165 _132081 x s f).
Proof. exact (MK_COMB (@lem7071591) (@lem7071590 _132081 f g x s h1)). Qed.
Lemma lem7071594 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term24 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7071047 _131524 x f s h0). Qed.
Lemma lem7071595 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) : term24 _132081 x s f.
Proof. exact (@lem7071594 _132081 x s f). Qed.
Lemma lem7071596 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : term24 _132081 x s g.
Proof. exact (@lem7071595 _132081 x s g). Qed.
Lemma lem7071598 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (@FINITE _132081 s) = True.
Proof. exact (EQ_MP (@lem7071348 _132081 s) (@lem7071347 _132081 f g x s h1)). Qed.
Lemma lem7071599 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : True = (@FINITE _132081 s).
Proof. exact (SYM (@lem7071598 _132081 f g x s h1)). Qed.
Lemma lem7071600 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : @FINITE _132081 s.
Proof. exact (EQ_MP (@lem7071599 _132081 f g x s h1) (@lem0)). Qed.
Lemma lem7071601 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term25 _132081 x s g) = (term26 _132081 x s g).
Proof. exact (@lem7071596 _132081 x s g (@lem7071600 _132081 f g x s h1)). Qed.
Lemma lem7071603 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term143 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7071604 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term144 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7071603 _2963 g t e g' t' e'). Qed.
Lemma lem7071605 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term145 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7071604 _2963 g t e g' t'). Qed.
Lemma lem7071606 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term146 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7071605 _2963 g t e g'). Qed.
Lemma lem7071607 (g : Prop) (t : real) (e : real) : term147 g t e.
Proof. exact (@lem7071606 real g t e). Qed.
Lemma lem7071608 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : term148 _132081 x s g.
Proof. exact (@lem7071607 (@IN _132081 x s) (@sum _132081 s g) (term149 _132081 x s g)). Qed.
Lemma lem7071609 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) : term150 _132081 x s g g'.
Proof. exact (@lem7071608 _132081 x s g g'). Qed.
Lemma lem7071610 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) : (term150 _132081 x s g g') = (term151 _132081 x s g g').
Proof. exact (eq_refl (term150 _132081 x s g g')). Qed.
Lemma lem7071611 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) : term151 _132081 x s g g'.
Proof. exact (EQ_MP (@lem7071610 _132081 x s g g') (@lem7071609 _132081 x s g g')). Qed.
Lemma lem7071612 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) (t' : real) : term152 _132081 x s g g' t'.
Proof. exact (@lem7071611 _132081 x s g g' t'). Qed.
Lemma lem7071613 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) (t' : real) : (term152 _132081 x s g g' t') = (term153 _132081 x s g g' t').
Proof. exact (eq_refl (term152 _132081 x s g g' t')). Qed.
Lemma lem7071614 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) (t' : real) : term153 _132081 x s g g' t'.
Proof. exact (EQ_MP (@lem7071613 _132081 x s g g' t') (@lem7071612 _132081 x s g g' t')). Qed.
Lemma lem7071615 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) (t' : real) (e' : real) : term154 _132081 x s g g' t' e'.
Proof. exact (@lem7071614 _132081 x s g g' t' e'). Qed.
Lemma lem7071616 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) (t' : real) (e' : real) : (term154 _132081 x s g g' t' e') = (term155 _132081 x s g g' t' e').
Proof. exact (eq_refl (term154 _132081 x s g g' t' e')). Qed.
Lemma lem7071617 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (g' : Prop) (t' : real) (e' : real) : term155 _132081 x s g g' t' e'.
Proof. exact (EQ_MP (@lem7071616 _132081 x s g g' t' e') (@lem7071615 _132081 x s g g' t' e')). Qed.
Lemma lem7071619 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (@IN _132081 x s) = False.
Proof. exact (@lem7071351 _132081 x s (@lem7071350 _132081 f g x s h1)). Qed.
Lemma lem7071620 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) (t' : real) (e' : real) : term156 _132081 x s g t' e'.
Proof. exact (@lem7071617 _132081 x s g False t' e'). Qed.
Lemma lem7071621 {_132081 : Type'} (t' : real) (e' : real) (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term157 _132081 x s g t' e'.
Proof. exact (@lem7071620 _132081 x s g t' e' (@lem7071619 _132081 f g x s h1)). Qed.
Lemma lem7071625 {_132081 : Type'} (s : _132081 -> Prop) (g : _132081 -> real) : (@sum _132081 s g) = (@sum _132081 s g).
Proof. exact (eq_refl (@sum _132081 s g)). Qed.
Lemma lem7071626 {_132081 : Type'} (s : _132081 -> Prop) (g : _132081 -> real) : term158 _132081 s g.
Proof. exact (fun h0 : False => @lem7071625 _132081 s g). Qed.
Lemma lem7071627 {_132081 : Type'} (e' : real) (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term159 _132081 x s g e'.
Proof. exact (@lem7071621 _132081 (@sum _132081 s g) e' f g x s h1). Qed.
Lemma lem7071628 {_132081 : Type'} (e' : real) (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term160 _132081 x s g e'.
Proof. exact (@lem7071627 _132081 e' f g x s h1 (@lem7071626 _132081 s g)). Qed.
Lemma lem7071634 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : (term149 _132081 x s g) = (term149 _132081 x s g).
Proof. exact (eq_refl (term149 _132081 x s g)). Qed.
Lemma lem7071635 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : term161 _132081 x s g.
Proof. exact (fun h0 : ~ False => @lem7071634 _132081 x s g). Qed.
Lemma lem7071636 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term162 _132081 x s g.
Proof. exact (@lem7071628 _132081 (term149 _132081 x s g) f g x s h1). Qed.
Lemma lem7071637 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term26 _132081 x s g) = (term163 _132081 x s g).
Proof. exact (@lem7071636 _132081 f g x s h1 (@lem7071635 _132081 x s g)). Qed.
Lemma lem7071639 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7071640 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7071639 real t1 t2). Qed.
Lemma lem7071641 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : (term163 _132081 x s g) = (term149 _132081 x s g).
Proof. exact (@lem7071640 (@sum _132081 s g) (term149 _132081 x s g)). Qed.
Lemma lem7071642 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term26 _132081 x s g) = (term149 _132081 x s g).
Proof. exact (TRANS (@lem7071637 _132081 f g x s h1) (@lem7071641 _132081 x s g)). Qed.
Lemma lem7071643 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term25 _132081 x s g) = (term149 _132081 x s g).
Proof. exact (TRANS (@lem7071601 _132081 f g x s h1) (@lem7071642 _132081 f g x s h1)). Qed.
Lemma lem7071644 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term120 _132081 f x s g) = (term166 _132081 f x s g).
Proof. exact (MK_COMB (@lem7071592 _132081 f g x s h1) (@lem7071643 _132081 f g x s h1)). Qed.
Lemma lem7071646 (w : real) (y : real) (x : real) (z : real) : term167 w y x z.
Proof. exact (fun h0 : term15 w x y z => @lem7071025 w x y z h0). Qed.
Lemma lem7071647 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : term168 _132081 f x s g.
Proof. exact (@lem7071646 (f x) (@sum _132081 s f) (g x) (@sum _132081 s g)). Qed.
Lemma lem7071651 {_132081 : Type'} (x' : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term169 _132081 x s f g x'.
Proof. exact (fun h0 : term6 _132081 x x' s => @lem7071533 _132081 f g x x' s h1 h0). Qed.
Lemma lem7071652 {_132081 : Type'} (x' : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term169 _132081 x s f g x'.
Proof. exact (@lem7071651 _132081 x' x s f g h1). Qed.
Lemma lem7071653 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term170 _132081 s f g x.
Proof. exact (@lem7071652 _132081 x x s f g h1). Qed.
Lemma lem7071657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7071658 {_132081 : Type'} (x : _132081) : (x = x) = True.
Proof. exact (@lem7071657 _132081 x). Qed.
Lemma lem7071659 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7071660 {_132081 : Type'} (x : _132081) : (term171 _132081 x) = (or True).
Proof. exact (MK_COMB (@lem7071659) (@lem7071658 _132081 x)). Qed.
Lemma lem7071662 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (@IN _132081 x s) = False.
Proof. exact (@lem7071351 _132081 x s (@lem7071350 _132081 f g x s h1)). Qed.
Lemma lem7071663 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term172 _132081 x s) = (True \/ False).
Proof. exact (MK_COMB (@lem7071660 _132081 x) (@lem7071662 _132081 f g x s h1)). Qed.
Lemma lem7071665 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7071666 : (True \/ False) = True.
Proof. exact (@lem7071665 False). Qed.
Lemma lem7071667 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term172 _132081 x s) = True.
Proof. exact (TRANS (@lem7071663 _132081 f g x s h1) (@lem7071666)). Qed.
Lemma lem7071668 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : True = (term172 _132081 x s).
Proof. exact (SYM (@lem7071667 _132081 f g x s h1)). Qed.
Lemma lem7071669 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term172 _132081 x s.
Proof. exact (EQ_MP (@lem7071668 _132081 f g x s h1) (@lem0)). Qed.
Lemma lem7071670 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : (term126 _132081 f g x) = True.
Proof. exact (@lem7071653 _132081 x s f g h1 (@lem7071669 _132081 f g x s h2)). Qed.
Lemma lem7071671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7071672 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : (term173 _132081 f g x) = (and True).
Proof. exact (MK_COMB (@lem7071671) (@lem7071670 _132081 f g x s h1 h2)). Qed.
Lemma lem7071674 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term174 _132081 f s g.
Proof. exact (fun h0 : term41 _132081 s f g => @lem7071357 _132081 f g x s h0 h1). Qed.
Lemma lem7071733 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7071734 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem7071733 p q p' q'). Qed.
Lemma lem7071735 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem7071734 p q p'). Qed.
Lemma lem7071736 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) : term175 _132081 s f g _94346.
Proof. exact (@lem7071735 (@IN _132081 _94346 s) (term126 _132081 f g _94346)). Qed.
Lemma lem7071737 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (p' : Prop) : term176 _132081 s f g _94346 p'.
Proof. exact (@lem7071736 _132081 s f g _94346 p'). Qed.
Lemma lem7071738 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (p' : Prop) : (term176 _132081 s f g _94346 p') = (term177 _132081 s f g _94346 p').
Proof. exact (eq_refl (term176 _132081 s f g _94346 p')). Qed.
Lemma lem7071739 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (p' : Prop) : term177 _132081 s f g _94346 p'.
Proof. exact (EQ_MP (@lem7071738 _132081 s f g _94346 p') (@lem7071737 _132081 s f g _94346 p')). Qed.
Lemma lem7071740 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (p' : Prop) (q' : Prop) : term178 _132081 s f g _94346 p' q'.
Proof. exact (@lem7071739 _132081 s f g _94346 p' q'). Qed.
Lemma lem7071741 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (p' : Prop) (q' : Prop) : (term178 _132081 s f g _94346 p' q') = (term179 _132081 s f g _94346 p' q').
Proof. exact (eq_refl (term178 _132081 s f g _94346 p' q')). Qed.
Lemma lem7071742 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (p' : Prop) (q' : Prop) : term179 _132081 s f g _94346 p' q'.
Proof. exact (EQ_MP (@lem7071741 _132081 s f g _94346 p' q') (@lem7071740 _132081 s f g _94346 p' q')). Qed.
Lemma lem7071743 {_132081 : Type'} (_94346 : _132081) (s : _132081 -> Prop) : (@IN _132081 _94346 s) = (@IN _132081 _94346 s).
Proof. exact (eq_refl (@IN _132081 _94346 s)). Qed.
Lemma lem7071744 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (s : _132081 -> Prop) (q' : Prop) : term180 _132081 f g _94346 s q'.
Proof. exact (@lem7071742 _132081 s f g _94346 (@IN _132081 _94346 s) q'). Qed.
Lemma lem7071745 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (s : _132081 -> Prop) (q' : Prop) : term181 _132081 f g _94346 s q'.
Proof. exact (@lem7071744 _132081 f g _94346 s q' (@lem7071743 _132081 _94346 s)). Qed.
Lemma lem7071746 {_132081 : Type'} (_94346 : _132081) (s : _132081 -> Prop) (h1 : @IN _132081 _94346 s) : @IN _132081 _94346 s.
Proof. exact (h1). Qed.
Lemma lem7071747 {_132081 : Type'} (_94346 : _132081) (s : _132081 -> Prop) : (@IN _132081 _94346 s) = ((@IN _132081 _94346 s) = True).
Proof. exact (@lem7 (@IN _132081 _94346 s)). Qed.
Lemma lem7071750 {_132081 : Type'} (x' : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term169 _132081 x s f g x'.
Proof. exact (fun h0 : term6 _132081 x x' s => @lem7071533 _132081 f g x x' s h1 h0). Qed.
Lemma lem7071751 {_132081 : Type'} (x' : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term169 _132081 x s f g x'.
Proof. exact (@lem7071750 _132081 x' x s f g h1). Qed.
Lemma lem7071752 {_132081 : Type'} (_94346 : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term169 _132081 x s f g _94346.
Proof. exact (@lem7071751 _132081 _94346 x s f g h1). Qed.
Lemma lem7071758 {_132081 : Type'} (_94346 : _132081) (s : _132081 -> Prop) (h1 : @IN _132081 _94346 s) : (@IN _132081 _94346 s) = True.
Proof. exact (EQ_MP (@lem7071747 _132081 _94346 s) (@lem7071746 _132081 _94346 s h1)). Qed.
Lemma lem7071759 {_132081 : Type'} (_94346 : _132081) (x : _132081) : (term182 _132081 _94346 x) = (term182 _132081 _94346 x).
Proof. exact (eq_refl (term182 _132081 _94346 x)). Qed.
Lemma lem7071760 {_132081 : Type'} (x : _132081) (_94346 : _132081) (s : _132081 -> Prop) (h1 : @IN _132081 _94346 s) : (term6 _132081 x _94346 s) = (term183 _132081 _94346 x).
Proof. exact (MK_COMB (@lem7071759 _132081 _94346 x) (@lem7071758 _132081 _94346 s h1)). Qed.
Lemma lem7071762 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7071763 {_132081 : Type'} (_94346 : _132081) (x : _132081) : (term183 _132081 _94346 x) = True.
Proof. exact (@lem7071762 (_94346 = x)). Qed.
Lemma lem7071764 {_132081 : Type'} (x : _132081) (_94346 : _132081) (s : _132081 -> Prop) (h1 : @IN _132081 _94346 s) : (term6 _132081 x _94346 s) = True.
Proof. exact (TRANS (@lem7071760 _132081 x _94346 s h1) (@lem7071763 _132081 _94346 x)). Qed.
Lemma lem7071765 {_132081 : Type'} (x : _132081) (_94346 : _132081) (s : _132081 -> Prop) (h1 : @IN _132081 _94346 s) : True = (term6 _132081 x _94346 s).
Proof. exact (SYM (@lem7071764 _132081 x _94346 s h1)). Qed.
Lemma lem7071766 {_132081 : Type'} (x : _132081) (_94346 : _132081) (s : _132081 -> Prop) (h1 : @IN _132081 _94346 s) : term6 _132081 x _94346 s.
Proof. exact (EQ_MP (@lem7071765 _132081 x _94346 s h1) (@lem0)). Qed.
Lemma lem7071767 {_132081 : Type'} (x : _132081) (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : @IN _132081 _94346 s) : (term126 _132081 f g _94346) = True.
Proof. exact (@lem7071752 _132081 _94346 x s f g h1 (@lem7071766 _132081 x _94346 s h2)). Qed.
Lemma lem7071768 {_132081 : Type'} (_94346 : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term184 _132081 s f g _94346.
Proof. exact (fun h0 : @IN _132081 _94346 s => @lem7071767 _132081 x f g _94346 s h1 h0). Qed.
Lemma lem7071769 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (_94346 : _132081) (s : _132081 -> Prop) : term185 _132081 f g _94346 s.
Proof. exact (@lem7071745 _132081 f g _94346 s True). Qed.
Lemma lem7071770 {_132081 : Type'} (_94346 : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : (term186 _132081 s f g _94346) = (term187 _132081 _94346 s).
Proof. exact (@lem7071769 _132081 f g _94346 s (@lem7071768 _132081 _94346 x s f g h1)). Qed.
Lemma lem7071772 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7071773 {_132081 : Type'} (_94346 : _132081) (s : _132081 -> Prop) : (term187 _132081 _94346 s) = True.
Proof. exact (@lem7071772 (@IN _132081 _94346 s)). Qed.
Lemma lem7071774 {_132081 : Type'} (_94346 : _132081) (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : (term186 _132081 s f g _94346) = True.
Proof. exact (TRANS (@lem7071770 _132081 _94346 x s f g h1) (@lem7071773 _132081 _94346 s)). Qed.
Lemma lem7071777 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : (term188 _132081 s f g) = (term189 _132081).
Proof. exact (fun_ext (fun _94346 : _132081 => @lem7071774 _132081 _94346 x s f g h1)). Qed.
Lemma lem7071778 {_132081 : Type'} : (@all _132081) = (@all _132081).
Proof. exact (eq_refl (@all _132081)). Qed.
Lemma lem7071779 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : (term41 _132081 s f g) = (term190 _132081).
Proof. exact (MK_COMB (@lem7071778 _132081) (@lem7071777 _132081 x s f g h1)). Qed.
Lemma lem7071781 {A : Type'} (t : Prop) : (term191 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7071782 {_132081 : Type'} (t : Prop) : (term191 _132081 t) = t.
Proof. exact (@lem7071781 _132081 t). Qed.
Lemma lem7071783 {_132081 : Type'} : (term190 _132081) = True.
Proof. exact (@lem7071782 _132081 True). Qed.
Lemma lem7071784 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : (term41 _132081 s f g) = True.
Proof. exact (TRANS (@lem7071779 _132081 x s f g h1) (@lem7071783 _132081)). Qed.
Lemma lem7071785 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : True = (term41 _132081 s f g).
Proof. exact (SYM (@lem7071784 _132081 x s f g h1)). Qed.
Lemma lem7071786 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term139 _132081 x s f g) : term41 _132081 s f g.
Proof. exact (EQ_MP (@lem7071785 _132081 x s f g h1) (@lem0)). Qed.
Lemma lem7071787 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : (term42 _132081 f s g) = True.
Proof. exact (@lem7071674 _132081 f g x s h2 (@lem7071786 _132081 x s f g h1)). Qed.
Lemma lem7071788 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : (term192 _132081 x f s g) = (True /\ True).
Proof. exact (MK_COMB (@lem7071672 _132081 f g x s h1 h2) (@lem7071787 _132081 f g x s h1 h2)). Qed.
Lemma lem7071790 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7071791 : (True /\ True) = True.
Proof. exact (@lem7071790 True). Qed.
Lemma lem7071792 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : (term192 _132081 x f s g) = True.
Proof. exact (TRANS (@lem7071788 _132081 f g x s h1 h2) (@lem7071791)). Qed.
Lemma lem7071793 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : True = (term192 _132081 x f s g).
Proof. exact (SYM (@lem7071792 _132081 f g x s h1 h2)). Qed.
Lemma lem7071794 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : term192 _132081 x f s g.
Proof. exact (EQ_MP (@lem7071793 _132081 f g x s h1 h2) (@lem0)). Qed.
Lemma lem7071795 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : (term166 _132081 f x s g) = True.
Proof. exact (@lem7071647 _132081 f x s g (@lem7071794 _132081 f g x s h1 h2)). Qed.
Lemma lem7071796 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term139 _132081 x s f g) (h2 : term67 _132081 f g x s) : (term120 _132081 f x s g) = True.
Proof. exact (TRANS (@lem7071644 _132081 f g x s h2) (@lem7071795 _132081 f g x s h1 h2)). Qed.
Lemma lem7071797 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : term193 _132081 f x s g.
Proof. exact (fun h0 : term139 _132081 x s f g => @lem7071796 _132081 f g x s h0 h1). Qed.
Lemma lem7071798 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) : term194 _132081 x s f g.
Proof. exact (@lem7071525 _132081 x s f g True). Qed.
Lemma lem7071799 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term71 _132081 f x s g) = (term195 _132081 x s f g).
Proof. exact (@lem7071798 _132081 x s f g (@lem7071797 _132081 f g x s h1)). Qed.
Lemma lem7071801 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7071802 {_132081 : Type'} (x : _132081) (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) : (term195 _132081 x s f g) = True.
Proof. exact (@lem7071801 (term139 _132081 x s f g)). Qed.
Lemma lem7071803 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (h1 : term67 _132081 f g x s) : (term71 _132081 f x s g) = True.
Proof. exact (TRANS (@lem7071799 _132081 f g x s h1) (@lem7071802 _132081 x s f g)). Qed.
Lemma lem7071804 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : term196 _132081 f x s g.
Proof. exact (fun h0 : term67 _132081 f g x s => @lem7071803 _132081 f g x s h0). Qed.
Lemma lem7071805 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) : term197 _132081 f g x s.
Proof. exact (@lem7071344 _132081 f g x s True). Qed.
Lemma lem7071806 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) : (term73 _132081 f x s g) = (term198 _132081 f g x s).
Proof. exact (@lem7071805 _132081 f g x s (@lem7071804 _132081 f x s g)). Qed.
Lemma lem7071808 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7071809 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (x : _132081) (s : _132081 -> Prop) : (term198 _132081 f g x s) = True.
Proof. exact (@lem7071808 (term67 _132081 f g x s)). Qed.
Lemma lem7071810 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (s : _132081 -> Prop) (g : _132081 -> real) : (term73 _132081 f x s g) = True.
Proof. exact (TRANS (@lem7071806 _132081 f g x s) (@lem7071809 _132081 f g x s)). Qed.
Lemma lem7071811 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (g : _132081 -> real) : (term75 _132081 f x g) = (term199 _132081).
Proof. exact (fun_ext (fun s : _132081 -> Prop => @lem7071810 _132081 f x s g)). Qed.
Lemma lem7071812 {_132081 : Type'} : (@all (_132081 -> Prop)) = (@all (_132081 -> Prop)).
Proof. exact (eq_refl (@all (_132081 -> Prop))). Qed.
Lemma lem7071813 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (g : _132081 -> real) : (term77 _132081 f x g) = (term200 _132081).
Proof. exact (MK_COMB (@lem7071812 _132081) (@lem7071811 _132081 f x g)). Qed.
Lemma lem7071815 {A : Type'} (t : Prop) : (term191 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7071816 {_132081 : Type'} (t : Prop) : (term201 _132081 t) = t.
Proof. exact (@lem7071815 (_132081 -> Prop) t). Qed.
Lemma lem7071817 {_132081 : Type'} : (term200 _132081) = True.
Proof. exact (@lem7071816 _132081 True). Qed.
Lemma lem7071818 {_132081 : Type'} (f : _132081 -> real) (x : _132081) (g : _132081 -> real) : (term77 _132081 f x g) = True.
Proof. exact (TRANS (@lem7071813 _132081 f x g) (@lem7071817 _132081)). Qed.
Lemma lem7071819 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term79 _132081 f g) = (term189 _132081).
Proof. exact (fun_ext (fun x : _132081 => @lem7071818 _132081 f x g)). Qed.
Lemma lem7071820 {_132081 : Type'} : (@all _132081) = (@all _132081).
Proof. exact (eq_refl (@all _132081)). Qed.
Lemma lem7071821 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term81 _132081 f g) = (term190 _132081).
Proof. exact (MK_COMB (@lem7071820 _132081) (@lem7071819 _132081 f g)). Qed.
Lemma lem7071823 {A : Type'} (t : Prop) : (term191 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7071824 {_132081 : Type'} (t : Prop) : (term191 _132081 t) = t.
Proof. exact (@lem7071823 _132081 t). Qed.
Lemma lem7071825 {_132081 : Type'} : (term190 _132081) = True.
Proof. exact (@lem7071824 _132081 True). Qed.
Lemma lem7071826 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term81 _132081 f g) = True.
Proof. exact (TRANS (@lem7071821 _132081 f g) (@lem7071825 _132081)). Qed.
Lemma lem7071827 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term83 _132081 f g) = (True /\ True).
Proof. exact (MK_COMB (@lem7071217 _132081 f g) (@lem7071826 _132081 f g)). Qed.
Lemma lem7071829 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7071830 : (True /\ True) = True.
Proof. exact (@lem7071829 True). Qed.
Lemma lem7071831 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term83 _132081 f g) = True.
Proof. exact (TRANS (@lem7071827 _132081 f g) (@lem7071830)). Qed.
Lemma lem7071832 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : True = (term83 _132081 f g).
Proof. exact (SYM (@lem7071831 _132081 f g)). Qed.
Lemma lem7071833 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term83 _132081 f g.
Proof. exact (EQ_MP (@lem7071832 _132081 f g) (@lem0)). Qed.
Lemma lem7071834 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : term46 _132081 f g.
Proof. exact (@lem7071130 _132081 f g (@lem7071833 _132081 f g)). Qed.
Lemma lem7071839 {_132081 : Type'} (f : _132081 -> real) : term50 _132081 f.
Proof. exact (fun g : _132081 -> real => @lem7071834 _132081 f g). Qed.
Lemma lem7071844 {_132081 : Type'} : term54 _132081.
Proof. exact (fun f : _132081 -> real => @lem7071839 _132081 f). Qed.
Lemma lem7071845 {_132081 : Type'} : term53 _132081.
Proof. exact (EQ_MP (@lem7071097 _132081) (@lem7071844 _132081)). Qed.
