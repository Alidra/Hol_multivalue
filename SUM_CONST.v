Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CONST_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import REAL_OF_NUM_SUC_spec.
Require Import SUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982725_spec.
Require Import thm1982729_spec.
Require Import thm1982747_spec.
Require Import thm1982753_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7083954 (n : nat) (h1 : (term0 n) = (term1 n)) : (term0 n) = (term1 n).
Proof. exact (h1). Qed.
Lemma lem7083955 (n : nat) (h1 : (term0 n) = (term1 n)) : (term1 n) = (term0 n).
Proof. exact (SYM (@lem7083954 n h1)). Qed.
Lemma lem7083956 (n : nat) (h1 : (term1 n) = (term0 n)) : (term1 n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem7083957 (n : nat) (h1 : (term1 n) = (term0 n)) : (term0 n) = (term1 n).
Proof. exact (SYM (@lem7083956 n h1)). Qed.
Lemma lem7083958 (n : nat) : ((term0 n) = (term1 n)) = ((term1 n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (term1 n) => @lem7083955 n h1) (fun h1 : (term1 n) = (term0 n) => @lem7083957 n h1)). Qed.
Lemma lem7083959 : term2 = term3.
Proof. exact (fun_ext (fun n : nat => @lem7083958 n)). Qed.
Lemma lem7083960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7083961 : term4 = term5.
Proof. exact (MK_COMB (@lem7083960) (@lem7083959)). Qed.
Lemma lem7083962 : term5.
Proof. exact (EQ_MP (@lem7083961) (@lem1484068)). Qed.
Lemma lem7083963 (n : nat) : term6 n.
Proof. exact (@lem7083962 n). Qed.
Lemma lem7083964 (n : nat) : (term6 n) = ((term1 n) = (term0 n)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem7083966 {A : Type'} : term7 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem7083967 {A : Type'} (x : A) : term8 A x.
Proof. exact (@lem7083966 A x). Qed.
Lemma lem7083968 {A : Type'} (x : A) : (term8 A x) = (term9 A x).
Proof. exact (eq_refl (term8 A x)). Qed.
Lemma lem7083969 {A : Type'} (x : A) : term9 A x.
Proof. exact (EQ_MP (@lem7083968 A x) (@lem7083967 A x)). Qed.
Lemma lem7083970 {A : Type'} (x : A) (s : A -> Prop) : term10 A x s.
Proof. exact (@lem7083969 A x s). Qed.
Lemma lem7083971 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term11 A x s).
Proof. exact (eq_refl (term10 A x s)). Qed.
Lemma lem7083972 {A : Type'} (x : A) (s : A -> Prop) : term11 A x s.
Proof. exact (EQ_MP (@lem7083971 A x s) (@lem7083970 A x s)). Qed.
Lemma lem7083973 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7083974 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term12 A x s) = (term13 A x s).
Proof. exact (@lem7083972 A x s (@lem7083973 A s h1)). Qed.
Lemma lem7083981 {_131524 : Type'} : term14 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7083982 {_131524 : Type'} (x : _131524) : term15 _131524 x.
Proof. exact (@lem7083981 _131524 x). Qed.
Lemma lem7083983 {_131524 : Type'} (x : _131524) : (term15 _131524 x) = (term16 _131524 x).
Proof. exact (eq_refl (term15 _131524 x)). Qed.
Lemma lem7083984 {_131524 : Type'} (x : _131524) : term16 _131524 x.
Proof. exact (EQ_MP (@lem7083983 _131524 x) (@lem7083982 _131524 x)). Qed.
Lemma lem7083985 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term17 _131524 x f.
Proof. exact (@lem7083984 _131524 x f). Qed.
Lemma lem7083986 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term17 _131524 x f) = (term18 _131524 x f).
Proof. exact (eq_refl (term17 _131524 x f)). Qed.
Lemma lem7083987 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term18 _131524 x f.
Proof. exact (EQ_MP (@lem7083986 _131524 x f) (@lem7083985 _131524 x f)). Qed.
Lemma lem7083988 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term19 _131524 x f s.
Proof. exact (@lem7083987 _131524 x f s). Qed.
Lemma lem7083989 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term19 _131524 x f s) = (term20 _131524 x s f).
Proof. exact (eq_refl (term19 _131524 x f s)). Qed.
Lemma lem7083990 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term20 _131524 x s f.
Proof. exact (EQ_MP (@lem7083989 _131524 x s f) (@lem7083988 _131524 x f s)). Qed.
Lemma lem7083991 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7083992 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term21 _131524 x s f) = (term22 _131524 x s f).
Proof. exact (@lem7083990 _131524 x s f (@lem7083991 _131524 s h1)). Qed.
Lemma lem7083998 {_131483 : Type'} : term23 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7083999 {_131483 : Type'} (f : _131483 -> real) : term24 _131483 f.
Proof. exact (@lem7083998 _131483 f). Qed.
Lemma lem7084000 {_131483 : Type'} (f : _131483 -> real) : (term24 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term25).
Proof. exact (eq_refl (term24 _131483 f)). Qed.
Lemma lem7084002 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem7084003 {A : Type'} (P : type686 A) (h1 : term26 A) : term27 A P.
Proof. exact (@lem7084002 A h1 P). Qed.
Lemma lem7084004 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (eq_refl (term27 A P)). Qed.
Lemma lem7084005 {A : Type'} (P : type686 A) (h1 : term26 A) : term28 A P.
Proof. exact (EQ_MP (@lem7084004 A P) (@lem7084003 A P h1)). Qed.
Lemma lem7084006 {A : Type'} (P : type686 A) (h1 : term29 A P) : term29 A P.
Proof. exact (h1). Qed.
Lemma lem7084007 {A : Type'} (P : type686 A) (h1 : term26 A) (h2 : term29 A P) : term30 A P.
Proof. exact (@lem7084005 A P h1 (@lem7084006 A P h2)). Qed.
Lemma lem7084008 {A : Type'} (P : type686 A) (h1 : term29 A P) : term31 A P.
Proof. exact (fun h0 : term26 A => @lem7084007 A P h0 h1). Qed.
Lemma lem7084009 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem7084010 {A : Type'} (P : type686 A) (h1 : term26 A) (h2 : term29 A P) : term30 A P.
Proof. exact (@lem7084008 A P h2 (@lem7084009 A h1)). Qed.
Lemma lem7084011 {A : Type'} (P : type686 A) (h1 : term26 A) : term28 A P.
Proof. exact (fun h0 : term29 A P => @lem7084010 A P h1 h0). Qed.
Lemma lem7084012 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (fun P : type686 A => @lem7084011 A P h1). Qed.
Lemma lem7084013 {A : Type'} : term32 A.
Proof. exact (fun h0 : term26 A => @lem7084012 A h0). Qed.
Lemma lem7084014 {A : Type'} : term26 A.
Proof. exact (@lem7084013 A (@lem3558722 A)). Qed.
Lemma lem7084015 {A : Type'} (P : type686 A) : term27 A P.
Proof. exact (@lem7084014 A P). Qed.
Lemma lem7084016 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (eq_refl (term27 A P)). Qed.
Lemma lem7084019 {A : Type'} (P : type686 A) : term28 A P.
Proof. exact (EQ_MP (@lem7084016 A P) (@lem7084015 A P)). Qed.
Lemma lem7084020 {_132484 : Type'} (P : type686 _132484) : term28 _132484 P.
Proof. exact (@lem7084019 _132484 P). Qed.
Lemma lem7084021 {_132484 : Type'} (c : real) : term33 _132484 c.
Proof. exact (@lem7084020 _132484 (term34 _132484 c)). Qed.
Lemma lem7084022 {_132484 : Type'} (c : real) : (term35 _132484 c) = ((term36 _132484 c) = (term37 _132484 c)).
Proof. exact (eq_refl (term35 _132484 c)). Qed.
Lemma lem7084023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7084024 {_132484 : Type'} (c : real) : (term38 _132484 c) = (term39 _132484 c).
Proof. exact (MK_COMB (@lem7084023) (@lem7084022 _132484 c)). Qed.
Lemma lem7084025 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term40 _132484 c s) = ((term41 _132484 s c) = (term42 _132484 s c)).
Proof. exact (eq_refl (term40 _132484 c s)). Qed.
Lemma lem7084026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7084027 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term43 _132484 c s) = (term44 _132484 s c).
Proof. exact (MK_COMB (@lem7084026) (@lem7084025 _132484 s c)). Qed.
Lemma lem7084028 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) : (term45 _132484 x s) = (term45 _132484 x s).
Proof. exact (eq_refl (term45 _132484 x s)). Qed.
Lemma lem7084029 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) : (term46 _132484 c x s) = (term47 _132484 c x s).
Proof. exact (MK_COMB (@lem7084027 _132484 s c) (@lem7084028 _132484 x s)). Qed.
Lemma lem7084030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7084031 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) : (term48 _132484 c x s) = (term49 _132484 c x s).
Proof. exact (MK_COMB (@lem7084030) (@lem7084029 _132484 c x s)). Qed.
Lemma lem7084032 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : (term50 _132484 c x s) = ((term51 _132484 x s c) = (term52 _132484 x s c)).
Proof. exact (eq_refl (term50 _132484 c x s)). Qed.
Lemma lem7084033 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : (term53 _132484 c x s) = (term54 _132484 x s c).
Proof. exact (MK_COMB (@lem7084031 _132484 c x s) (@lem7084032 _132484 x s c)). Qed.
Lemma lem7084034 {_132484 : Type'} (x : _132484) (c : real) : (term55 _132484 c x) = (term56 _132484 x c).
Proof. exact (fun_ext (fun s : _132484 -> Prop => @lem7084033 _132484 x s c)). Qed.
Lemma lem7084035 {_132484 : Type'} : (@all (_132484 -> Prop)) = (@all (_132484 -> Prop)).
Proof. exact (eq_refl (@all (_132484 -> Prop))). Qed.
Lemma lem7084036 {_132484 : Type'} (x : _132484) (c : real) : (term57 _132484 c x) = (term58 _132484 x c).
Proof. exact (MK_COMB (@lem7084035 _132484) (@lem7084034 _132484 x c)). Qed.
Lemma lem7084037 {_132484 : Type'} (c : real) : (term59 _132484 c) = (term60 _132484 c).
Proof. exact (fun_ext (fun x : _132484 => @lem7084036 _132484 x c)). Qed.
Lemma lem7084038 {_132484 : Type'} : (@all _132484) = (@all _132484).
Proof. exact (eq_refl (@all _132484)). Qed.
Lemma lem7084039 {_132484 : Type'} (c : real) : (term61 _132484 c) = (term62 _132484 c).
Proof. exact (MK_COMB (@lem7084038 _132484) (@lem7084037 _132484 c)). Qed.
Lemma lem7084040 {_132484 : Type'} (c : real) : (term63 _132484 c) = (term64 _132484 c).
Proof. exact (MK_COMB (@lem7084024 _132484 c) (@lem7084039 _132484 c)). Qed.
Lemma lem7084041 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7084042 {_132484 : Type'} (c : real) : (term65 _132484 c) = (term66 _132484 c).
Proof. exact (MK_COMB (@lem7084041) (@lem7084040 _132484 c)). Qed.
Lemma lem7084043 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term40 _132484 c s) = ((term41 _132484 s c) = (term42 _132484 s c)).
Proof. exact (eq_refl (term40 _132484 c s)). Qed.
Lemma lem7084044 {_132484 : Type'} (s : _132484 -> Prop) : (term67 _132484 s) = (term67 _132484 s).
Proof. exact (eq_refl (term67 _132484 s)). Qed.
Lemma lem7084045 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term68 _132484 c s) = (term69 _132484 s c).
Proof. exact (MK_COMB (@lem7084044 _132484 s) (@lem7084043 _132484 s c)). Qed.
Lemma lem7084046 {_132484 : Type'} (c : real) : (term70 _132484 c) = (term71 _132484 c).
Proof. exact (fun_ext (fun s : _132484 -> Prop => @lem7084045 _132484 s c)). Qed.
Lemma lem7084047 {_132484 : Type'} : (@all (_132484 -> Prop)) = (@all (_132484 -> Prop)).
Proof. exact (eq_refl (@all (_132484 -> Prop))). Qed.
Lemma lem7084048 {_132484 : Type'} (c : real) : (term72 _132484 c) = (term73 _132484 c).
Proof. exact (MK_COMB (@lem7084047 _132484) (@lem7084046 _132484 c)). Qed.
Lemma lem7084049 {_132484 : Type'} (c : real) : (term33 _132484 c) = (term74 _132484 c).
Proof. exact (MK_COMB (@lem7084042 _132484 c) (@lem7084048 _132484 c)). Qed.
Lemma lem7084050 {_132484 : Type'} (c : real) : term74 _132484 c.
Proof. exact (EQ_MP (@lem7084049 _132484 c) (@lem7084021 _132484 c)). Qed.
Lemma lem7084056 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term25.
Proof. exact (EQ_MP (@lem7084000 _131483 f) (@lem7083999 _131483 f)). Qed.
Lemma lem7084057 {_132484 : Type'} (f : _132484 -> real) : (@sum _132484 (@EMPTY _132484) f) = term25.
Proof. exact (@lem7084056 _132484 f). Qed.
Lemma lem7084058 {_132484 : Type'} (c : real) : (term36 _132484 c) = term25.
Proof. exact (@lem7084057 _132484 (term75 _132484 c)). Qed.
Lemma lem7084059 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7084060 {_132484 : Type'} (c : real) : (term76 _132484 c) = term77.
Proof. exact (MK_COMB (@lem7084059) (@lem7084058 _132484 c)). Qed.
Lemma lem7084062 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem7084063 {_132484 : Type'} : (@CARD _132484 (@EMPTY _132484)) = (NUMERAL 0).
Proof. exact (@lem7084062 _132484). Qed.
Lemma lem7084064 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7084065 {_132484 : Type'} : (term78 _132484) = term25.
Proof. exact (MK_COMB (@lem7084064) (@lem7084063 _132484)). Qed.
Lemma lem7084066 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7084067 {_132484 : Type'} : (term79 _132484) = term80.
Proof. exact (MK_COMB (@lem7084066) (@lem7084065 _132484)). Qed.
Lemma lem7084068 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7084069 {_132484 : Type'} (c : real) : (term37 _132484 c) = (term81 c).
Proof. exact (MK_COMB (@lem7084067 _132484) (@lem7084068 c)). Qed.
Lemma lem7084070 {_132484 : Type'} (c : real) : ((term36 _132484 c) = (term37 _132484 c)) = (term25 = (term81 c)).
Proof. exact (MK_COMB (@lem7084060 _132484 c) (@lem7084069 _132484 c)). Qed.
Lemma lem7084073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7084074 {_132484 : Type'} (c : real) : (term39 _132484 c) = (term82 c).
Proof. exact (MK_COMB (@lem7084073) (@lem7084070 _132484 c)). Qed.
Lemma lem7084088 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term83 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7084089 (p : Prop) (q : Prop) (p' : Prop) : term84 p q p'.
Proof. exact (fun q' : Prop => @lem7084088 p q p' q'). Qed.
Lemma lem7084090 (p : Prop) (q : Prop) : term85 p q.
Proof. exact (fun p' : Prop => @lem7084089 p q p'). Qed.
Lemma lem7084091 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : term86 _132484 x s c.
Proof. exact (@lem7084090 (term47 _132484 c x s) ((term51 _132484 x s c) = (term52 _132484 x s c))). Qed.
Lemma lem7084092 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (p' : Prop) : term87 _132484 x s c p'.
Proof. exact (@lem7084091 _132484 x s c p'). Qed.
Lemma lem7084093 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (p' : Prop) : (term87 _132484 x s c p') = (term88 _132484 x s c p').
Proof. exact (eq_refl (term87 _132484 x s c p')). Qed.
Lemma lem7084094 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (p' : Prop) : term88 _132484 x s c p'.
Proof. exact (EQ_MP (@lem7084093 _132484 x s c p') (@lem7084092 _132484 x s c p')). Qed.
Lemma lem7084095 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (p' : Prop) (q' : Prop) : term89 _132484 x s c p' q'.
Proof. exact (@lem7084094 _132484 x s c p' q'). Qed.
Lemma lem7084096 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (p' : Prop) (q' : Prop) : (term89 _132484 x s c p' q') = (term90 _132484 x s c p' q').
Proof. exact (eq_refl (term89 _132484 x s c p' q')). Qed.
Lemma lem7084097 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (p' : Prop) (q' : Prop) : term90 _132484 x s c p' q'.
Proof. exact (EQ_MP (@lem7084096 _132484 x s c p' q') (@lem7084095 _132484 x s c p' q')). Qed.
Lemma lem7084104 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) : (term47 _132484 c x s) = (term47 _132484 c x s).
Proof. exact (eq_refl (term47 _132484 c x s)). Qed.
Lemma lem7084105 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (q' : Prop) : term91 _132484 c x s q'.
Proof. exact (@lem7084097 _132484 x s c (term47 _132484 c x s) q'). Qed.
Lemma lem7084106 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (q' : Prop) : term92 _132484 c x s q'.
Proof. exact (@lem7084105 _132484 c x s q' (@lem7084104 _132484 c x s)). Qed.
Lemma lem7084107 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term47 _132484 c x s.
Proof. exact (h1). Qed.
Lemma lem7084108 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term45 _132484 x s.
Proof. exact (proj2 (@lem7084107 _132484 c x s h1)). Qed.
Lemma lem7084109 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : @FINITE _132484 s.
Proof. exact (proj2 (@lem7084108 _132484 c x s h1)). Qed.
Lemma lem7084110 {_132484 : Type'} (s : _132484 -> Prop) : (@FINITE _132484 s) = ((@FINITE _132484 s) = True).
Proof. exact (@lem7 (@FINITE _132484 s)). Qed.
Lemma lem7084112 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term93 _132484 x s.
Proof. exact (proj1 (@lem7084108 _132484 c x s h1)). Qed.
Lemma lem7084113 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) : term94 _132484 x s.
Proof. exact (@lem82 (@IN _132484 x s)). Qed.
Lemma lem7084119 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term20 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7083992 _131524 x f s h0). Qed.
Lemma lem7084120 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (f : _132484 -> real) : term20 _132484 x s f.
Proof. exact (@lem7084119 _132484 x s f). Qed.
Lemma lem7084121 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : term95 _132484 x s c.
Proof. exact (@lem7084120 _132484 x s (term75 _132484 c)). Qed.
Lemma lem7084123 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (@FINITE _132484 s) = True.
Proof. exact (EQ_MP (@lem7084110 _132484 s) (@lem7084109 _132484 c x s h1)). Qed.
Lemma lem7084124 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : True = (@FINITE _132484 s).
Proof. exact (SYM (@lem7084123 _132484 c x s h1)). Qed.
Lemma lem7084125 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : @FINITE _132484 s.
Proof. exact (EQ_MP (@lem7084124 _132484 c x s h1) (@lem0)). Qed.
Lemma lem7084126 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term51 _132484 x s c) = (term96 _132484 x s c).
Proof. exact (@lem7084121 _132484 x s c (@lem7084125 _132484 c x s h1)). Qed.
Lemma lem7084128 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term97 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7084129 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term98 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7084128 _2963 g t e g' t' e'). Qed.
Lemma lem7084130 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term99 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7084129 _2963 g t e g' t'). Qed.
Lemma lem7084131 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term100 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7084130 _2963 g t e g'). Qed.
Lemma lem7084132 (g : Prop) (t : real) (e : real) : term101 g t e.
Proof. exact (@lem7084131 real g t e). Qed.
Lemma lem7084133 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : term102 _132484 x s c.
Proof. exact (@lem7084132 (@IN _132484 x s) (term41 _132484 s c) (term103 _132484 x s c)). Qed.
Lemma lem7084134 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) : term104 _132484 x s c g'.
Proof. exact (@lem7084133 _132484 x s c g'). Qed.
Lemma lem7084135 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) : (term104 _132484 x s c g') = (term105 _132484 x s c g').
Proof. exact (eq_refl (term104 _132484 x s c g')). Qed.
Lemma lem7084136 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) : term105 _132484 x s c g'.
Proof. exact (EQ_MP (@lem7084135 _132484 x s c g') (@lem7084134 _132484 x s c g')). Qed.
Lemma lem7084137 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) (t' : real) : term106 _132484 x s c g' t'.
Proof. exact (@lem7084136 _132484 x s c g' t'). Qed.
Lemma lem7084138 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) (t' : real) : (term106 _132484 x s c g' t') = (term107 _132484 x s c g' t').
Proof. exact (eq_refl (term106 _132484 x s c g' t')). Qed.
Lemma lem7084139 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) (t' : real) : term107 _132484 x s c g' t'.
Proof. exact (EQ_MP (@lem7084138 _132484 x s c g' t') (@lem7084137 _132484 x s c g' t')). Qed.
Lemma lem7084140 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) (t' : real) (e' : real) : term108 _132484 x s c g' t' e'.
Proof. exact (@lem7084139 _132484 x s c g' t' e'). Qed.
Lemma lem7084141 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) (t' : real) (e' : real) : (term108 _132484 x s c g' t' e') = (term109 _132484 x s c g' t' e').
Proof. exact (eq_refl (term108 _132484 x s c g' t' e')). Qed.
Lemma lem7084142 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (g' : Prop) (t' : real) (e' : real) : term109 _132484 x s c g' t' e'.
Proof. exact (EQ_MP (@lem7084141 _132484 x s c g' t' e') (@lem7084140 _132484 x s c g' t' e')). Qed.
Lemma lem7084144 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (@IN _132484 x s) = False.
Proof. exact (@lem7084113 _132484 x s (@lem7084112 _132484 c x s h1)). Qed.
Lemma lem7084145 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) (t' : real) (e' : real) : term110 _132484 x s c t' e'.
Proof. exact (@lem7084142 _132484 x s c False t' e'). Qed.
Lemma lem7084146 {_132484 : Type'} (t' : real) (e' : real) (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term111 _132484 x s c t' e'.
Proof. exact (@lem7084145 _132484 x s c t' e' (@lem7084144 _132484 c x s h1)). Qed.
Lemma lem7084151 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term41 _132484 s c) = (term42 _132484 s c).
Proof. exact (proj1 (@lem7084107 _132484 c x s h1)). Qed.
Lemma lem7084152 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term41 _132484 s c) = (term42 _132484 s c).
Proof. exact (@lem7084151 _132484 c x s h1). Qed.
Lemma lem7084153 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term112 _132484 s c.
Proof. exact (fun h0 : False => @lem7084152 _132484 c x s h1). Qed.
Lemma lem7084154 {_132484 : Type'} (e' : real) (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term113 _132484 x s c e'.
Proof. exact (@lem7084146 _132484 (term42 _132484 s c) e' c x s h1). Qed.
Lemma lem7084155 {_132484 : Type'} (e' : real) (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term114 _132484 x s c e'.
Proof. exact (@lem7084154 _132484 e' c x s h1 (@lem7084153 _132484 c x s h1)). Qed.
Lemma lem7084162 {A B : Type'} (f : A -> B) (y : A) : (term115 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7084163 {_132484 : Type'} (f : _132484 -> real) (y : _132484) : (term116 _132484 f y) = (f y).
Proof. exact (@lem7084162 _132484 real f y). Qed.
Lemma lem7084164 {_132484 : Type'} (c : real) (x : _132484) : (term117 _132484 c x) = (term118 _132484 c x).
Proof. exact (@lem7084163 _132484 (term75 _132484 c) x). Qed.
Lemma lem7084165 {_132484 : Type'} (n : _132484) (c : real) : (term118 _132484 c n) = c.
Proof. exact (eq_refl (term118 _132484 c n)). Qed.
Lemma lem7084166 {_132484 : Type'} (c : real) : (term119 _132484 c) = (term75 _132484 c).
Proof. exact (fun_ext (fun n : _132484 => @lem7084165 _132484 n c)). Qed.
Lemma lem7084167 {_132484 : Type'} (x : _132484) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7084168 {_132484 : Type'} (c : real) (x : _132484) : (term117 _132484 c x) = (term118 _132484 c x).
Proof. exact (MK_COMB (@lem7084166 _132484 c) (@lem7084167 _132484 x)). Qed.
Lemma lem7084169 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7084170 {_132484 : Type'} (c : real) (x : _132484) : (term120 _132484 c x) = (term121 _132484 c x).
Proof. exact (MK_COMB (@lem7084169) (@lem7084168 _132484 c x)). Qed.
Lemma lem7084171 {_132484 : Type'} (x : _132484) (c : real) : (term118 _132484 c x) = c.
Proof. exact (eq_refl (term118 _132484 c x)). Qed.
Lemma lem7084172 {_132484 : Type'} (x : _132484) (c : real) : ((term117 _132484 c x) = (term118 _132484 c x)) = ((term118 _132484 c x) = c).
Proof. exact (MK_COMB (@lem7084170 _132484 c x) (@lem7084171 _132484 x c)). Qed.
Lemma lem7084173 {_132484 : Type'} (x : _132484) (c : real) : (term118 _132484 c x) = c.
Proof. exact (EQ_MP (@lem7084172 _132484 x c) (@lem7084164 _132484 c x)). Qed.
Lemma lem7084174 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7084175 {_132484 : Type'} (x : _132484) (c : real) : (term122 _132484 c x) = (real_add c).
Proof. exact (MK_COMB (@lem7084174) (@lem7084173 _132484 x c)). Qed.
Lemma lem7084177 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term41 _132484 s c) = (term42 _132484 s c).
Proof. exact (proj1 (@lem7084107 _132484 c x s h1)). Qed.
Lemma lem7084178 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term41 _132484 s c) = (term42 _132484 s c).
Proof. exact (@lem7084177 _132484 c x s h1). Qed.
Lemma lem7084179 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term103 _132484 x s c) = (term123 _132484 s c).
Proof. exact (MK_COMB (@lem7084175 _132484 x c) (@lem7084178 _132484 c x s h1)). Qed.
Lemma lem7084180 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term124 _132484 x s c.
Proof. exact (fun h0 : ~ False => @lem7084179 _132484 c x s h1). Qed.
Lemma lem7084181 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term125 _132484 x s c.
Proof. exact (@lem7084155 _132484 (term123 _132484 s c) c x s h1). Qed.
Lemma lem7084182 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term96 _132484 x s c) = (term126 _132484 s c).
Proof. exact (@lem7084181 _132484 c x s h1 (@lem7084180 _132484 c x s h1)). Qed.
Lemma lem7084184 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7084185 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7084184 real t1 t2). Qed.
Lemma lem7084186 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term126 _132484 s c) = (term123 _132484 s c).
Proof. exact (@lem7084185 (term42 _132484 s c) (term123 _132484 s c)). Qed.
Lemma lem7084187 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term96 _132484 x s c) = (term123 _132484 s c).
Proof. exact (TRANS (@lem7084182 _132484 c x s h1) (@lem7084186 _132484 s c)). Qed.
Lemma lem7084188 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term51 _132484 x s c) = (term123 _132484 s c).
Proof. exact (TRANS (@lem7084126 _132484 c x s h1) (@lem7084187 _132484 c x s h1)). Qed.
Lemma lem7084189 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7084190 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term127 _132484 x s c) = (term128 _132484 s c).
Proof. exact (MK_COMB (@lem7084189) (@lem7084188 _132484 c x s h1)). Qed.
Lemma lem7084192 {A : Type'} (x : A) (s : A -> Prop) : term11 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem7083974 A x s h0). Qed.
Lemma lem7084193 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) : term11 _132484 x s.
Proof. exact (@lem7084192 _132484 x s). Qed.
Lemma lem7084195 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (@FINITE _132484 s) = True.
Proof. exact (EQ_MP (@lem7084110 _132484 s) (@lem7084109 _132484 c x s h1)). Qed.
Lemma lem7084196 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : True = (@FINITE _132484 s).
Proof. exact (SYM (@lem7084195 _132484 c x s h1)). Qed.
Lemma lem7084197 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : @FINITE _132484 s.
Proof. exact (EQ_MP (@lem7084196 _132484 c x s h1) (@lem0)). Qed.
Lemma lem7084198 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term12 _132484 x s) = (term13 _132484 x s).
Proof. exact (@lem7084193 _132484 x s (@lem7084197 _132484 c x s h1)). Qed.
Lemma lem7084200 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term97 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7084201 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term98 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7084200 _2963 g t e g' t' e'). Qed.
Lemma lem7084202 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term99 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7084201 _2963 g t e g' t'). Qed.
Lemma lem7084203 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term100 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7084202 _2963 g t e g'). Qed.
Lemma lem7084204 (g : Prop) (t : nat) (e : nat) : term129 g t e.
Proof. exact (@lem7084203 nat g t e). Qed.
Lemma lem7084205 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) : term130 _132484 x s.
Proof. exact (@lem7084204 (@IN _132484 x s) (@CARD _132484 s) (term131 _132484 s)). Qed.
Lemma lem7084206 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) : term132 _132484 x s g'.
Proof. exact (@lem7084205 _132484 x s g'). Qed.
Lemma lem7084207 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) : (term132 _132484 x s g') = (term133 _132484 x s g').
Proof. exact (eq_refl (term132 _132484 x s g')). Qed.
Lemma lem7084208 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) : term133 _132484 x s g'.
Proof. exact (EQ_MP (@lem7084207 _132484 x s g') (@lem7084206 _132484 x s g')). Qed.
Lemma lem7084209 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) (t' : nat) : term134 _132484 x s g' t'.
Proof. exact (@lem7084208 _132484 x s g' t'). Qed.
Lemma lem7084210 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) (t' : nat) : (term134 _132484 x s g' t') = (term135 _132484 x s g' t').
Proof. exact (eq_refl (term134 _132484 x s g' t')). Qed.
Lemma lem7084211 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) (t' : nat) : term135 _132484 x s g' t'.
Proof. exact (EQ_MP (@lem7084210 _132484 x s g' t') (@lem7084209 _132484 x s g' t')). Qed.
Lemma lem7084212 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term136 _132484 x s g' t' e'.
Proof. exact (@lem7084211 _132484 x s g' t' e'). Qed.
Lemma lem7084213 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term136 _132484 x s g' t' e') = (term137 _132484 x s g' t' e').
Proof. exact (eq_refl (term136 _132484 x s g' t' e')). Qed.
Lemma lem7084214 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term137 _132484 x s g' t' e'.
Proof. exact (EQ_MP (@lem7084213 _132484 x s g' t' e') (@lem7084212 _132484 x s g' t' e')). Qed.
Lemma lem7084216 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (@IN _132484 x s) = False.
Proof. exact (@lem7084113 _132484 x s (@lem7084112 _132484 c x s h1)). Qed.
Lemma lem7084217 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (t' : nat) (e' : nat) : term138 _132484 x s t' e'.
Proof. exact (@lem7084214 _132484 x s False t' e'). Qed.
Lemma lem7084218 {_132484 : Type'} (t' : nat) (e' : nat) (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term139 _132484 x s t' e'.
Proof. exact (@lem7084217 _132484 x s t' e' (@lem7084216 _132484 c x s h1)). Qed.
Lemma lem7084222 {_132484 : Type'} (s : _132484 -> Prop) : (@CARD _132484 s) = (@CARD _132484 s).
Proof. exact (eq_refl (@CARD _132484 s)). Qed.
Lemma lem7084223 {_132484 : Type'} (s : _132484 -> Prop) : term140 _132484 s.
Proof. exact (fun h0 : False => @lem7084222 _132484 s). Qed.
Lemma lem7084224 {_132484 : Type'} (e' : nat) (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term141 _132484 x s e'.
Proof. exact (@lem7084218 _132484 (@CARD _132484 s) e' c x s h1). Qed.
Lemma lem7084225 {_132484 : Type'} (e' : nat) (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term142 _132484 x s e'.
Proof. exact (@lem7084224 _132484 e' c x s h1 (@lem7084223 _132484 s)). Qed.
Lemma lem7084231 {_132484 : Type'} (s : _132484 -> Prop) : (term131 _132484 s) = (term131 _132484 s).
Proof. exact (eq_refl (term131 _132484 s)). Qed.
Lemma lem7084232 {_132484 : Type'} (s : _132484 -> Prop) : term143 _132484 s.
Proof. exact (fun h0 : ~ False => @lem7084231 _132484 s). Qed.
Lemma lem7084233 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : term144 _132484 x s.
Proof. exact (@lem7084225 _132484 (term131 _132484 s) c x s h1). Qed.
Lemma lem7084234 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term13 _132484 x s) = (term145 _132484 s).
Proof. exact (@lem7084233 _132484 c x s h1 (@lem7084232 _132484 s)). Qed.
Lemma lem7084236 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7084237 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7084236 nat t1 t2). Qed.
Lemma lem7084238 {_132484 : Type'} (s : _132484 -> Prop) : (term145 _132484 s) = (term131 _132484 s).
Proof. exact (@lem7084237 (@CARD _132484 s) (term131 _132484 s)). Qed.
Lemma lem7084239 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term13 _132484 x s) = (term131 _132484 s).
Proof. exact (TRANS (@lem7084234 _132484 c x s h1) (@lem7084238 _132484 s)). Qed.
Lemma lem7084240 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term12 _132484 x s) = (term131 _132484 s).
Proof. exact (TRANS (@lem7084198 _132484 c x s h1) (@lem7084239 _132484 c x s h1)). Qed.
Lemma lem7084241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7084242 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term146 _132484 x s) = (term147 _132484 s).
Proof. exact (MK_COMB (@lem7084241) (@lem7084240 _132484 c x s h1)). Qed.
Lemma lem7084244 (n : nat) : (term1 n) = (term0 n).
Proof. exact (EQ_MP (@lem7083964 n) (@lem7083963 n)). Qed.
Lemma lem7084245 {_132484 : Type'} (s : _132484 -> Prop) : (term147 _132484 s) = (term148 _132484 s).
Proof. exact (@lem7084244 (@CARD _132484 s)). Qed.
Lemma lem7084246 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term146 _132484 x s) = (term148 _132484 s).
Proof. exact (TRANS (@lem7084242 _132484 c x s h1) (@lem7084245 _132484 s)). Qed.
Lemma lem7084247 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7084248 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term149 _132484 x s) = (term150 _132484 s).
Proof. exact (MK_COMB (@lem7084247) (@lem7084246 _132484 c x s h1)). Qed.
Lemma lem7084249 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7084250 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : (term52 _132484 x s c) = (term151 _132484 s c).
Proof. exact (MK_COMB (@lem7084248 _132484 c x s h1) (@lem7084249 c)). Qed.
Lemma lem7084251 {_132484 : Type'} (c : real) (x : _132484) (s : _132484 -> Prop) (h1 : term47 _132484 c x s) : ((term51 _132484 x s c) = (term52 _132484 x s c)) = ((term123 _132484 s c) = (term151 _132484 s c)).
Proof. exact (MK_COMB (@lem7084190 _132484 c x s h1) (@lem7084250 _132484 c x s h1)). Qed.
Lemma lem7084254 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : term152 _132484 x s c.
Proof. exact (fun h0 : term47 _132484 c x s => @lem7084251 _132484 c x s h0). Qed.
Lemma lem7084255 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : term153 _132484 x s c.
Proof. exact (@lem7084106 _132484 c x s ((term123 _132484 s c) = (term151 _132484 s c))). Qed.
Lemma lem7084256 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : (term54 _132484 x s c) = (term154 _132484 x s c).
Proof. exact (@lem7084255 _132484 x s c (@lem7084254 _132484 x s c)). Qed.
Lemma lem7084302 {_132484 : Type'} (x : _132484) (c : real) : (term56 _132484 x c) = (term155 _132484 x c).
Proof. exact (fun_ext (fun s : _132484 -> Prop => @lem7084256 _132484 x s c)). Qed.
Lemma lem7084348 {_132484 : Type'} : (@all (_132484 -> Prop)) = (@all (_132484 -> Prop)).
Proof. exact (eq_refl (@all (_132484 -> Prop))). Qed.
Lemma lem7084349 {_132484 : Type'} (x : _132484) (c : real) : (term58 _132484 x c) = (term156 _132484 x c).
Proof. exact (MK_COMB (@lem7084348 _132484) (@lem7084302 _132484 x c)). Qed.
Lemma lem7084399 {_132484 : Type'} (c : real) : (term60 _132484 c) = (term157 _132484 c).
Proof. exact (fun_ext (fun x : _132484 => @lem7084349 _132484 x c)). Qed.
Lemma lem7084449 {_132484 : Type'} : (@all _132484) = (@all _132484).
Proof. exact (eq_refl (@all _132484)). Qed.
Lemma lem7084450 {_132484 : Type'} (c : real) : (term62 _132484 c) = (term158 _132484 c).
Proof. exact (MK_COMB (@lem7084449 _132484) (@lem7084399 _132484 c)). Qed.
Lemma lem7084504 {_132484 : Type'} (c : real) : (term64 _132484 c) = (term159 _132484 c).
Proof. exact (MK_COMB (@lem7084074 _132484 c) (@lem7084450 _132484 c)). Qed.
Lemma lem7084562 {_132484 : Type'} (c : real) : (term159 _132484 c) = (term64 _132484 c).
Proof. exact (SYM (@lem7084504 _132484 c)). Qed.
Lemma lem7084578 (c : real) : (term160 c) = (term161 c).
Proof. exact (@lem1988318 term25 (term81 c)). Qed.
Lemma lem7084585 (c : real) : (term81 c) = term25.
Proof. exact (@lem1982729 c). Qed.
Lemma lem7084588 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem7084589 (c : real) : (term163 c) = term164.
Proof. exact (MK_COMB (@lem7084588) (@lem7084585 c)). Qed.
Lemma lem7084590 : term164 = term165.
Proof. exact (@lem1982792 term25 term25). Qed.
Lemma lem7084592 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7084593 : term25 = term167.
Proof. exact (@lem7084592 (NUMERAL 0)). Qed.
Lemma lem7084595 (x : nat) : (term168 x) = (term169 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7084596 : term170 = term171.
Proof. exact (@lem7084595 term172). Qed.
Lemma lem7084597 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7084598 : term173 = term174.
Proof. exact (MK_COMB (@lem7084597) (@lem7084596)). Qed.
Lemma lem7084599 : term175 = term176.
Proof. exact (MK_COMB (@lem7084598) (@lem7084593)). Qed.
Lemma lem7084600 : term176 = term177.
Proof. exact (@lem1981613 term170 term25 term178 term178). Qed.
Lemma lem7084602 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7084603 : term181 = term182.
Proof. exact (@lem7084602 term172 term172). Qed.
Lemma lem7084604 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7084605 : term184 = term172.
Proof. exact (EQ_MP (@lem7084604) (@lem940073)). Qed.
Lemma lem7084606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7084607 : term182 = term178.
Proof. exact (MK_COMB (@lem7084606) (@lem7084605)). Qed.
Lemma lem7084608 : term181 = term178.
Proof. exact (TRANS (@lem7084603) (@lem7084607)). Qed.
Lemma lem7084610 (x : nat) : (term185 x) = term25.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7084611 : term175 = term25.
Proof. exact (@lem7084610 term172). Qed.
Lemma lem7084612 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7084613 : term186 = term187.
Proof. exact (MK_COMB (@lem7084612) (@lem7084611)). Qed.
Lemma lem7084614 : term177 = term167.
Proof. exact (MK_COMB (@lem7084613) (@lem7084608)). Qed.
Lemma lem7084615 : term176 = term167.
Proof. exact (TRANS (@lem7084600) (@lem7084614)). Qed.
Lemma lem7084616 : term175 = term167.
Proof. exact (TRANS (@lem7084599) (@lem7084615)). Qed.
Lemma lem7084618 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7084619 : term167 = term25.
Proof. exact (@lem7084618 term25). Qed.
Lemma lem7084620 : term175 = term25.
Proof. exact (TRANS (@lem7084616) (@lem7084619)). Qed.
Lemma lem7084621 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem7084622 : term165 = term190.
Proof. exact (MK_COMB (@lem7084621) (@lem7084620)). Qed.
Lemma lem7084623 : term190 = term25.
Proof. exact (@lem1982721 term25). Qed.
Lemma lem7084624 : term165 = term25.
Proof. exact (TRANS (@lem7084622) (@lem7084623)). Qed.
Lemma lem7084625 : term164 = term25.
Proof. exact (TRANS (@lem7084590) (@lem7084624)). Qed.
Lemma lem7084626 (c : real) : (term163 c) = term25.
Proof. exact (TRANS (@lem7084589 c) (@lem7084625)). Qed.
Lemma lem7084627 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7084628 (c : real) : (term191 c) = term192.
Proof. exact (MK_COMB (@lem7084627) (@lem7084626 c)). Qed.
Lemma lem7084629 : term192 = term175.
Proof. exact (@lem1982785 term25). Qed.
Lemma lem7084631 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7084632 : term25 = term167.
Proof. exact (@lem7084631 (NUMERAL 0)). Qed.
Lemma lem7084634 (x : nat) : (term168 x) = (term169 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7084635 : term170 = term171.
Proof. exact (@lem7084634 term172). Qed.
Lemma lem7084636 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7084637 : term173 = term174.
Proof. exact (MK_COMB (@lem7084636) (@lem7084635)). Qed.
Lemma lem7084638 : term175 = term176.
Proof. exact (MK_COMB (@lem7084637) (@lem7084632)). Qed.
Lemma lem7084639 : term176 = term177.
Proof. exact (@lem1981613 term170 term25 term178 term178). Qed.
Lemma lem7084641 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7084642 : term181 = term182.
Proof. exact (@lem7084641 term172 term172). Qed.
Lemma lem7084643 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7084644 : term184 = term172.
Proof. exact (EQ_MP (@lem7084643) (@lem940073)). Qed.
Lemma lem7084645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7084646 : term182 = term178.
Proof. exact (MK_COMB (@lem7084645) (@lem7084644)). Qed.
Lemma lem7084647 : term181 = term178.
Proof. exact (TRANS (@lem7084642) (@lem7084646)). Qed.
Lemma lem7084649 (x : nat) : (term185 x) = term25.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7084650 : term175 = term25.
Proof. exact (@lem7084649 term172). Qed.
Lemma lem7084651 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7084652 : term186 = term187.
Proof. exact (MK_COMB (@lem7084651) (@lem7084650)). Qed.
Lemma lem7084653 : term177 = term167.
Proof. exact (MK_COMB (@lem7084652) (@lem7084647)). Qed.
Lemma lem7084654 : term176 = term167.
Proof. exact (TRANS (@lem7084639) (@lem7084653)). Qed.
Lemma lem7084655 : term175 = term167.
Proof. exact (TRANS (@lem7084638) (@lem7084654)). Qed.
Lemma lem7084657 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7084658 : term167 = term25.
Proof. exact (@lem7084657 term25). Qed.
Lemma lem7084659 : term175 = term25.
Proof. exact (TRANS (@lem7084655) (@lem7084658)). Qed.
Lemma lem7084660 : term192 = term25.
Proof. exact (TRANS (@lem7084629) (@lem7084659)). Qed.
Lemma lem7084661 (c : real) : (term193 c) = (term193 c).
Proof. exact (eq_refl (term193 c)). Qed.
Lemma lem7084662 (c : real) : ((term191 c) = term192) = ((term191 c) = term25).
Proof. exact (MK_COMB (@lem7084661 c) (@lem7084660)). Qed.
Lemma lem7084663 (c : real) : (term191 c) = term25.
Proof. exact (EQ_MP (@lem7084662 c) (@lem7084628 c)). Qed.
Lemma lem7084664 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7084665 (c : real) : (term194 c) = term195.
Proof. exact (MK_COMB (@lem7084664) (@lem7084663 c)). Qed.
Lemma lem7084666 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7084667 (c : real) : (term196 c) = term197.
Proof. exact (MK_COMB (@lem7084665 c) (@lem7084666)). Qed.
Lemma lem7084668 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7084669 (c : real) : (term198 c) = term195.
Proof. exact (MK_COMB (@lem7084668) (@lem7084626 c)). Qed.
Lemma lem7084670 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7084671 (c : real) : (term199 c) = term197.
Proof. exact (MK_COMB (@lem7084669 c) (@lem7084670)). Qed.
Lemma lem7084672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7084673 (c : real) : (term200 c) = term201.
Proof. exact (MK_COMB (@lem7084672) (@lem7084671 c)). Qed.
Lemma lem7084674 (c : real) : (term161 c) = term202.
Proof. exact (MK_COMB (@lem7084673 c) (@lem7084667 c)). Qed.
Lemma lem7084688 (c : real) : (term160 c) = term202.
Proof. exact (TRANS (@lem7084578 c) (@lem7084674 c)). Qed.
Lemma lem7084698 (h1 : term202) : term202.
Proof. exact (h1). Qed.
Lemma lem7084699 (h1 : term197) : term197.
Proof. exact (h1). Qed.
Lemma lem7084701 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7084702 : term197 = term203.
Proof. exact (@lem7084701 term25 term25). Qed.
Lemma lem7084704 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7084705 : term25 = term167.
Proof. exact (@lem7084704 (NUMERAL 0)). Qed.
Lemma lem7084707 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7084708 : term25 = term167.
Proof. exact (@lem7084707 (NUMERAL 0)). Qed.
Lemma lem7084709 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7084710 : term204 = term205.
Proof. exact (MK_COMB (@lem7084709) (@lem7084708)). Qed.
Lemma lem7084711 : term203 = term206.
Proof. exact (MK_COMB (@lem7084710) (@lem7084705)). Qed.
Lemma lem7084712 : term207.
Proof. exact (@lem1980255 term25 term178 term25 term178). Qed.
Lemma lem7084714 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084715 : term209 = term210.
Proof. exact (@lem7084714 (NUMERAL 0) term172). Qed.
Lemma lem7084716 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7084717 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7084718 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7084717 h1) (fun h1 : term210 = True => @lem7084716)). Qed.
Lemma lem7084719 : term210 = True.
Proof. exact (EQ_MP (@lem7084718) (@lem7084716)). Qed.
Lemma lem7084720 : term209 = True.
Proof. exact (TRANS (@lem7084715) (@lem7084719)). Qed.
Lemma lem7084721 : True = term209.
Proof. exact (SYM (@lem7084720)). Qed.
Lemma lem7084722 : term209.
Proof. exact (EQ_MP (@lem7084721) (@lem0)). Qed.
Lemma lem7084723 : term212.
Proof. exact (@lem7084712 (@lem7084722)). Qed.
Lemma lem7084725 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084726 : term209 = term210.
Proof. exact (@lem7084725 (NUMERAL 0) term172). Qed.
Lemma lem7084727 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7084728 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7084729 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7084728 h1) (fun h1 : term210 = True => @lem7084727)). Qed.
Lemma lem7084730 : term210 = True.
Proof. exact (EQ_MP (@lem7084729) (@lem7084727)). Qed.
Lemma lem7084731 : term209 = True.
Proof. exact (TRANS (@lem7084726) (@lem7084730)). Qed.
Lemma lem7084732 : True = term209.
Proof. exact (SYM (@lem7084731)). Qed.
Lemma lem7084733 : term209.
Proof. exact (EQ_MP (@lem7084732) (@lem0)). Qed.
Lemma lem7084734 : term206 = term213.
Proof. exact (@lem7084723 (@lem7084733)). Qed.
Lemma lem7084736 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7084737 : term215 = term25.
Proof. exact (@lem7084736 term172). Qed.
Lemma lem7084739 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7084740 : term215 = term25.
Proof. exact (@lem7084739 term172). Qed.
Lemma lem7084741 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7084742 : term216 = term204.
Proof. exact (MK_COMB (@lem7084741) (@lem7084740)). Qed.
Lemma lem7084743 : term213 = term203.
Proof. exact (MK_COMB (@lem7084742) (@lem7084737)). Qed.
Lemma lem7084745 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084746 : term203 = term217.
Proof. exact (@lem7084745 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7084747 : term217 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7084748 : term203 = False.
Proof. exact (TRANS (@lem7084746) (@lem7084747)). Qed.
Lemma lem7084749 : term213 = False.
Proof. exact (TRANS (@lem7084743) (@lem7084748)). Qed.
Lemma lem7084750 : term206 = False.
Proof. exact (TRANS (@lem7084734) (@lem7084749)). Qed.
Lemma lem7084751 : term203 = False.
Proof. exact (TRANS (@lem7084711) (@lem7084750)). Qed.
Lemma lem7084752 : term197 = False.
Proof. exact (TRANS (@lem7084702) (@lem7084751)). Qed.
Lemma lem7084753 (h1 : term197) : False.
Proof. exact (EQ_MP (@lem7084752) (@lem7084699 h1)). Qed.
Lemma lem7084754 (h1 : term197) : term197.
Proof. exact (h1). Qed.
Lemma lem7084756 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7084757 : term197 = term203.
Proof. exact (@lem7084756 term25 term25). Qed.
Lemma lem7084759 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7084760 : term25 = term167.
Proof. exact (@lem7084759 (NUMERAL 0)). Qed.
Lemma lem7084762 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7084763 : term25 = term167.
Proof. exact (@lem7084762 (NUMERAL 0)). Qed.
Lemma lem7084764 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7084765 : term204 = term205.
Proof. exact (MK_COMB (@lem7084764) (@lem7084763)). Qed.
Lemma lem7084766 : term203 = term206.
Proof. exact (MK_COMB (@lem7084765) (@lem7084760)). Qed.
Lemma lem7084767 : term207.
Proof. exact (@lem1980255 term25 term178 term25 term178). Qed.
Lemma lem7084769 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084770 : term209 = term210.
Proof. exact (@lem7084769 (NUMERAL 0) term172). Qed.
Lemma lem7084771 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7084772 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7084773 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7084772 h1) (fun h1 : term210 = True => @lem7084771)). Qed.
Lemma lem7084774 : term210 = True.
Proof. exact (EQ_MP (@lem7084773) (@lem7084771)). Qed.
Lemma lem7084775 : term209 = True.
Proof. exact (TRANS (@lem7084770) (@lem7084774)). Qed.
Lemma lem7084776 : True = term209.
Proof. exact (SYM (@lem7084775)). Qed.
Lemma lem7084777 : term209.
Proof. exact (EQ_MP (@lem7084776) (@lem0)). Qed.
Lemma lem7084778 : term212.
Proof. exact (@lem7084767 (@lem7084777)). Qed.
Lemma lem7084780 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084781 : term209 = term210.
Proof. exact (@lem7084780 (NUMERAL 0) term172). Qed.
Lemma lem7084782 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7084783 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7084784 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7084783 h1) (fun h1 : term210 = True => @lem7084782)). Qed.
Lemma lem7084785 : term210 = True.
Proof. exact (EQ_MP (@lem7084784) (@lem7084782)). Qed.
Lemma lem7084786 : term209 = True.
Proof. exact (TRANS (@lem7084781) (@lem7084785)). Qed.
Lemma lem7084787 : True = term209.
Proof. exact (SYM (@lem7084786)). Qed.
Lemma lem7084788 : term209.
Proof. exact (EQ_MP (@lem7084787) (@lem0)). Qed.
Lemma lem7084789 : term206 = term213.
Proof. exact (@lem7084778 (@lem7084788)). Qed.
Lemma lem7084791 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7084792 : term215 = term25.
Proof. exact (@lem7084791 term172). Qed.
Lemma lem7084794 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7084795 : term215 = term25.
Proof. exact (@lem7084794 term172). Qed.
Lemma lem7084796 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7084797 : term216 = term204.
Proof. exact (MK_COMB (@lem7084796) (@lem7084795)). Qed.
Lemma lem7084798 : term213 = term203.
Proof. exact (MK_COMB (@lem7084797) (@lem7084792)). Qed.
Lemma lem7084800 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084801 : term203 = term217.
Proof. exact (@lem7084800 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7084802 : term217 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7084803 : term203 = False.
Proof. exact (TRANS (@lem7084801) (@lem7084802)). Qed.
Lemma lem7084804 : term213 = False.
Proof. exact (TRANS (@lem7084798) (@lem7084803)). Qed.
Lemma lem7084805 : term206 = False.
Proof. exact (TRANS (@lem7084789) (@lem7084804)). Qed.
Lemma lem7084806 : term203 = False.
Proof. exact (TRANS (@lem7084766) (@lem7084805)). Qed.
Lemma lem7084807 : term197 = False.
Proof. exact (TRANS (@lem7084757) (@lem7084806)). Qed.
Lemma lem7084808 (h1 : term197) : False.
Proof. exact (EQ_MP (@lem7084807) (@lem7084754 h1)). Qed.
Lemma lem7084809 (h1 : term202) : False.
Proof. exact (or_elim (@lem7084698 h1) (fun h0 : term197 => @lem7084753 h0) (fun h0 : term197 => @lem7084808 h0)). Qed.
Lemma lem7084811 (h1 : term202) : term202.
Proof. exact (h1). Qed.
Lemma lem7084812 (h1 : term202) : term202 = False.
Proof. exact (prop_ext (fun h2 : term202 => @lem7084809 h1) (fun h2 : False => @lem7084811 h1)). Qed.
Lemma lem7084813 (h1 : term202) : False.
Proof. exact (EQ_MP (@lem7084812 h1) (@lem7084811 h1)). Qed.
Lemma lem7084814 (c : real) (h1 : term160 c) : term160 c.
Proof. exact (h1). Qed.
Lemma lem7084815 (c : real) (h1 : term160 c) : term202.
Proof. exact (EQ_MP (@lem7084688 c) (@lem7084814 c h1)). Qed.
Lemma lem7084816 (c : real) (h1 : term160 c) : term202 = False.
Proof. exact (prop_ext (fun h2 : term202 => @lem7084813 h2) (fun h2 : False => @lem7084815 c h1)). Qed.
Lemma lem7084817 (c : real) (h1 : term160 c) : False.
Proof. exact (EQ_MP (@lem7084816 c h1) (@lem7084815 c h1)). Qed.
Lemma lem7084818 (c : real) : term218 c.
Proof. exact (fun h0 : term160 c => @lem7084817 c h0). Qed.
Lemma lem7084819 (c : real) : term219 c.
Proof. exact (@lem1386578 (term25 = (term81 c))). Qed.
Lemma lem7084822 (c : real) : term25 = (term81 c).
Proof. exact (@lem7084819 c (@lem7084818 c)). Qed.
Lemma lem7084833 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term220 _132484 s c) = (term221 _132484 s c).
Proof. exact (@lem1988318 (term123 _132484 s c) (term151 _132484 s c)). Qed.
Lemma lem7084845 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term151 _132484 s c) = (term222 _132484 c s).
Proof. exact (@lem1982725 c (term148 _132484 s)). Qed.
Lemma lem7084846 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term222 _132484 c s) = (term223 _132484 s c).
Proof. exact (@lem1982781 (term224 _132484 s) c term178). Qed.
Lemma lem7084847 (c : real) : (term225 c) = (term226 c).
Proof. exact (@lem1982747 term178 c). Qed.
Lemma lem7084848 (c : real) : (term226 c) = c.
Proof. exact (@lem1982709 c). Qed.
Lemma lem7084849 (c : real) : (term225 c) = c.
Proof. exact (TRANS (@lem7084847 c) (@lem7084848 c)). Qed.
Lemma lem7084852 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term227 _132484 c s) = (term227 _132484 c s).
Proof. exact (eq_refl (term227 _132484 c s)). Qed.
Lemma lem7084853 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term223 _132484 s c) = (term228 _132484 s c).
Proof. exact (MK_COMB (@lem7084852 _132484 c s) (@lem7084849 c)). Qed.
Lemma lem7084854 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term222 _132484 c s) = (term228 _132484 s c).
Proof. exact (TRANS (@lem7084846 _132484 s c) (@lem7084853 _132484 s c)). Qed.
Lemma lem7084856 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term151 _132484 s c) = (term228 _132484 s c).
Proof. exact (TRANS (@lem7084845 _132484 c s) (@lem7084854 _132484 s c)). Qed.
Lemma lem7084863 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term42 _132484 s c) = (term229 _132484 c s).
Proof. exact (@lem1982747 c (term224 _132484 s)). Qed.
Lemma lem7084866 (c : real) : (real_add c) = (real_add c).
Proof. exact (eq_refl (real_add c)). Qed.
Lemma lem7084867 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term123 _132484 s c) = (term230 _132484 c s).
Proof. exact (MK_COMB (@lem7084866 c) (@lem7084863 _132484 c s)). Qed.
Lemma lem7084868 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term230 _132484 c s) = (term228 _132484 s c).
Proof. exact (@lem1982761 (term229 _132484 c s) c). Qed.
Lemma lem7084869 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term123 _132484 s c) = (term228 _132484 s c).
Proof. exact (TRANS (@lem7084867 _132484 c s) (@lem7084868 _132484 s c)). Qed.
Lemma lem7084870 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7084871 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term231 _132484 s c) = (term232 _132484 s c).
Proof. exact (MK_COMB (@lem7084870) (@lem7084869 _132484 s c)). Qed.
Lemma lem7084872 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term233 _132484 s c) = (term234 _132484 s c).
Proof. exact (MK_COMB (@lem7084871 _132484 s c) (@lem7084856 _132484 s c)). Qed.
Lemma lem7084873 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term234 _132484 s c) = (term235 _132484 s c).
Proof. exact (@lem1982792 (term228 _132484 s c) (term228 _132484 s c)). Qed.
Lemma lem7084880 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term236 _132484 s c) = (term237 _132484 s c).
Proof. exact (@lem1982781 (term229 _132484 c s) term170 c). Qed.
Lemma lem7084881 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term238 _132484 s c) = (term238 _132484 s c).
Proof. exact (eq_refl (term238 _132484 s c)). Qed.
Lemma lem7084882 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term235 _132484 s c) = (term239 _132484 s c).
Proof. exact (MK_COMB (@lem7084881 _132484 s c) (@lem7084880 _132484 s c)). Qed.
Lemma lem7084883 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term239 _132484 s c) = (term240 _132484 s c).
Proof. exact (@lem1982753 (term229 _132484 c s) (term241 _132484 c s) c (term242 c)). Qed.
Lemma lem7084884 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term243 _132484 c s) = (term244 _132484 c s).
Proof. exact (@lem1982715 term170 (term229 _132484 c s)). Qed.
Lemma lem7084886 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7084887 : term178 = term245.
Proof. exact (@lem7084886 term172). Qed.
Lemma lem7084889 (x : nat) : (term168 x) = (term169 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7084890 : term170 = term171.
Proof. exact (@lem7084889 term172). Qed.
Lemma lem7084891 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7084892 : term246 = term247.
Proof. exact (MK_COMB (@lem7084891) (@lem7084890)). Qed.
Lemma lem7084893 : term248 = term249.
Proof. exact (MK_COMB (@lem7084892) (@lem7084887)). Qed.
Lemma lem7084894 : term250.
Proof. exact (@lem1981473 term170 term178 term178 term178 term25 term178). Qed.
Lemma lem7084896 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084897 : term209 = term210.
Proof. exact (@lem7084896 (NUMERAL 0) term172). Qed.
Lemma lem7084898 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7084899 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7084900 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7084899 h1) (fun h1 : term210 = True => @lem7084898)). Qed.
Lemma lem7084901 : term210 = True.
Proof. exact (EQ_MP (@lem7084900) (@lem7084898)). Qed.
Lemma lem7084902 : term209 = True.
Proof. exact (TRANS (@lem7084897) (@lem7084901)). Qed.
Lemma lem7084903 : True = term209.
Proof. exact (SYM (@lem7084902)). Qed.
Lemma lem7084904 : term209.
Proof. exact (EQ_MP (@lem7084903) (@lem0)). Qed.
Lemma lem7084905 : term251.
Proof. exact (@lem7084894 (@lem7084904)). Qed.
Lemma lem7084907 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084908 : term209 = term210.
Proof. exact (@lem7084907 (NUMERAL 0) term172). Qed.
Lemma lem7084909 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7084910 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7084911 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7084910 h1) (fun h1 : term210 = True => @lem7084909)). Qed.
Lemma lem7084912 : term210 = True.
Proof. exact (EQ_MP (@lem7084911) (@lem7084909)). Qed.
Lemma lem7084913 : term209 = True.
Proof. exact (TRANS (@lem7084908) (@lem7084912)). Qed.
Lemma lem7084914 : True = term209.
Proof. exact (SYM (@lem7084913)). Qed.
Lemma lem7084915 : term209.
Proof. exact (EQ_MP (@lem7084914) (@lem0)). Qed.
Lemma lem7084916 : term252.
Proof. exact (@lem7084905 (@lem7084915)). Qed.
Lemma lem7084918 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7084919 : term209 = term210.
Proof. exact (@lem7084918 (NUMERAL 0) term172). Qed.
Lemma lem7084920 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7084921 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7084922 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7084921 h1) (fun h1 : term210 = True => @lem7084920)). Qed.
Lemma lem7084923 : term210 = True.
Proof. exact (EQ_MP (@lem7084922) (@lem7084920)). Qed.
Lemma lem7084924 : term209 = True.
Proof. exact (TRANS (@lem7084919) (@lem7084923)). Qed.
Lemma lem7084925 : True = term209.
Proof. exact (SYM (@lem7084924)). Qed.
Lemma lem7084926 : term209.
Proof. exact (EQ_MP (@lem7084925) (@lem0)). Qed.
Lemma lem7084927 : term253.
Proof. exact (@lem7084916 (@lem7084926)). Qed.
Lemma lem7084929 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7084930 : term181 = term182.
Proof. exact (@lem7084929 term172 term172). Qed.
Lemma lem7084931 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7084932 : term184 = term172.
Proof. exact (EQ_MP (@lem7084931) (@lem940073)). Qed.
Lemma lem7084933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7084934 : term182 = term178.
Proof. exact (MK_COMB (@lem7084933) (@lem7084932)). Qed.
Lemma lem7084935 : term181 = term178.
Proof. exact (TRANS (@lem7084930) (@lem7084934)). Qed.
Lemma lem7084937 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7084938 : term256 = term257.
Proof. exact (@lem7084937 term172 term172). Qed.
Lemma lem7084939 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7084940 : term184 = term172.
Proof. exact (EQ_MP (@lem7084939) (@lem940073)). Qed.
Lemma lem7084941 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7084942 : term182 = term178.
Proof. exact (MK_COMB (@lem7084941) (@lem7084940)). Qed.
Lemma lem7084943 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7084944 : term257 = term170.
Proof. exact (MK_COMB (@lem7084943) (@lem7084942)). Qed.
Lemma lem7084945 : term256 = term170.
Proof. exact (TRANS (@lem7084938) (@lem7084944)). Qed.
Lemma lem7084946 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7084947 : term258 = term246.
Proof. exact (MK_COMB (@lem7084946) (@lem7084945)). Qed.
Lemma lem7084948 : term259 = term248.
Proof. exact (MK_COMB (@lem7084947) (@lem7084935)). Qed.
Lemma lem7084950 (m : nat) : (term260 m) = term25.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7084951 : term248 = term25.
Proof. exact (@lem7084950 term172). Qed.
Lemma lem7084952 : term259 = term25.
Proof. exact (TRANS (@lem7084948) (@lem7084951)). Qed.
Lemma lem7084953 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7084954 : term261 = term80.
Proof. exact (MK_COMB (@lem7084953) (@lem7084952)). Qed.
Lemma lem7084955 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7084956 : term262 = term215.
Proof. exact (MK_COMB (@lem7084954) (@lem7084955)). Qed.
Lemma lem7084958 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7084959 : term215 = term25.
Proof. exact (@lem7084958 term172). Qed.
Lemma lem7084960 : term262 = term25.
Proof. exact (TRANS (@lem7084956) (@lem7084959)). Qed.
Lemma lem7084962 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7084963 : term181 = term182.
Proof. exact (@lem7084962 term172 term172). Qed.
Lemma lem7084964 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7084965 : term184 = term172.
Proof. exact (EQ_MP (@lem7084964) (@lem940073)). Qed.
Lemma lem7084966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7084967 : term182 = term178.
Proof. exact (MK_COMB (@lem7084966) (@lem7084965)). Qed.
Lemma lem7084968 : term181 = term178.
Proof. exact (TRANS (@lem7084963) (@lem7084967)). Qed.
Lemma lem7084969 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem7084970 : term263 = term215.
Proof. exact (MK_COMB (@lem7084969) (@lem7084968)). Qed.
Lemma lem7084972 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7084973 : term215 = term25.
Proof. exact (@lem7084972 term172). Qed.
Lemma lem7084974 : term263 = term25.
Proof. exact (TRANS (@lem7084970) (@lem7084973)). Qed.
Lemma lem7084975 : term25 = term263.
Proof. exact (SYM (@lem7084974)). Qed.
Lemma lem7084976 : term262 = term263.
Proof. exact (TRANS (@lem7084960) (@lem7084975)). Qed.
Lemma lem7084977 : term249 = term167.
Proof. exact (@lem7084927 (@lem7084976)). Qed.
Lemma lem7084978 : term248 = term167.
Proof. exact (TRANS (@lem7084893) (@lem7084977)). Qed.
Lemma lem7084980 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7084981 : term167 = term25.
Proof. exact (@lem7084980 term25). Qed.
Lemma lem7084982 : term248 = term25.
Proof. exact (TRANS (@lem7084978) (@lem7084981)). Qed.
Lemma lem7084983 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7084984 : term264 = term80.
Proof. exact (MK_COMB (@lem7084983) (@lem7084982)). Qed.
Lemma lem7084985 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term229 _132484 c s) = (term229 _132484 c s).
Proof. exact (eq_refl (term229 _132484 c s)). Qed.
Lemma lem7084986 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term244 _132484 c s) = (term265 _132484 c s).
Proof. exact (MK_COMB (@lem7084984) (@lem7084985 _132484 c s)). Qed.
Lemma lem7084987 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term243 _132484 c s) = (term265 _132484 c s).
Proof. exact (TRANS (@lem7084884 _132484 c s) (@lem7084986 _132484 c s)). Qed.
Lemma lem7084988 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term265 _132484 c s) = term25.
Proof. exact (@lem1982719 (term229 _132484 c s)). Qed.
Lemma lem7084989 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term243 _132484 c s) = term25.
Proof. exact (TRANS (@lem7084987 _132484 c s) (@lem7084988 _132484 c s)). Qed.
Lemma lem7084990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7084991 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : (term266 _132484 c s) = term189.
Proof. exact (MK_COMB (@lem7084990) (@lem7084989 _132484 c s)). Qed.
Lemma lem7084992 (c : real) : (term267 c) = (term268 c).
Proof. exact (@lem1982715 term170 c). Qed.
Lemma lem7084994 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7084995 : term178 = term245.
Proof. exact (@lem7084994 term172). Qed.
Lemma lem7084997 (x : nat) : (term168 x) = (term169 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7084998 : term170 = term171.
Proof. exact (@lem7084997 term172). Qed.
Lemma lem7084999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7085000 : term246 = term247.
Proof. exact (MK_COMB (@lem7084999) (@lem7084998)). Qed.
Lemma lem7085001 : term248 = term249.
Proof. exact (MK_COMB (@lem7085000) (@lem7084995)). Qed.
Lemma lem7085002 : term250.
Proof. exact (@lem1981473 term170 term178 term178 term178 term25 term178). Qed.
Lemma lem7085004 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085005 : term209 = term210.
Proof. exact (@lem7085004 (NUMERAL 0) term172). Qed.
Lemma lem7085006 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7085007 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7085008 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7085007 h1) (fun h1 : term210 = True => @lem7085006)). Qed.
Lemma lem7085009 : term210 = True.
Proof. exact (EQ_MP (@lem7085008) (@lem7085006)). Qed.
Lemma lem7085010 : term209 = True.
Proof. exact (TRANS (@lem7085005) (@lem7085009)). Qed.
Lemma lem7085011 : True = term209.
Proof. exact (SYM (@lem7085010)). Qed.
Lemma lem7085012 : term209.
Proof. exact (EQ_MP (@lem7085011) (@lem0)). Qed.
Lemma lem7085013 : term251.
Proof. exact (@lem7085002 (@lem7085012)). Qed.
Lemma lem7085015 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085016 : term209 = term210.
Proof. exact (@lem7085015 (NUMERAL 0) term172). Qed.
Lemma lem7085017 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7085018 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7085019 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7085018 h1) (fun h1 : term210 = True => @lem7085017)). Qed.
Lemma lem7085020 : term210 = True.
Proof. exact (EQ_MP (@lem7085019) (@lem7085017)). Qed.
Lemma lem7085021 : term209 = True.
Proof. exact (TRANS (@lem7085016) (@lem7085020)). Qed.
Lemma lem7085022 : True = term209.
Proof. exact (SYM (@lem7085021)). Qed.
Lemma lem7085023 : term209.
Proof. exact (EQ_MP (@lem7085022) (@lem0)). Qed.
Lemma lem7085024 : term252.
Proof. exact (@lem7085013 (@lem7085023)). Qed.
Lemma lem7085026 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085027 : term209 = term210.
Proof. exact (@lem7085026 (NUMERAL 0) term172). Qed.
Lemma lem7085028 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7085029 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7085030 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7085029 h1) (fun h1 : term210 = True => @lem7085028)). Qed.
Lemma lem7085031 : term210 = True.
Proof. exact (EQ_MP (@lem7085030) (@lem7085028)). Qed.
Lemma lem7085032 : term209 = True.
Proof. exact (TRANS (@lem7085027) (@lem7085031)). Qed.
Lemma lem7085033 : True = term209.
Proof. exact (SYM (@lem7085032)). Qed.
Lemma lem7085034 : term209.
Proof. exact (EQ_MP (@lem7085033) (@lem0)). Qed.
Lemma lem7085035 : term253.
Proof. exact (@lem7085024 (@lem7085034)). Qed.
Lemma lem7085037 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7085038 : term181 = term182.
Proof. exact (@lem7085037 term172 term172). Qed.
Lemma lem7085039 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7085040 : term184 = term172.
Proof. exact (EQ_MP (@lem7085039) (@lem940073)). Qed.
Lemma lem7085041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7085042 : term182 = term178.
Proof. exact (MK_COMB (@lem7085041) (@lem7085040)). Qed.
Lemma lem7085043 : term181 = term178.
Proof. exact (TRANS (@lem7085038) (@lem7085042)). Qed.
Lemma lem7085045 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7085046 : term256 = term257.
Proof. exact (@lem7085045 term172 term172). Qed.
Lemma lem7085047 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7085048 : term184 = term172.
Proof. exact (EQ_MP (@lem7085047) (@lem940073)). Qed.
Lemma lem7085049 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7085050 : term182 = term178.
Proof. exact (MK_COMB (@lem7085049) (@lem7085048)). Qed.
Lemma lem7085051 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7085052 : term257 = term170.
Proof. exact (MK_COMB (@lem7085051) (@lem7085050)). Qed.
Lemma lem7085053 : term256 = term170.
Proof. exact (TRANS (@lem7085046) (@lem7085052)). Qed.
Lemma lem7085054 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7085055 : term258 = term246.
Proof. exact (MK_COMB (@lem7085054) (@lem7085053)). Qed.
Lemma lem7085056 : term259 = term248.
Proof. exact (MK_COMB (@lem7085055) (@lem7085043)). Qed.
Lemma lem7085058 (m : nat) : (term260 m) = term25.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7085059 : term248 = term25.
Proof. exact (@lem7085058 term172). Qed.
Lemma lem7085060 : term259 = term25.
Proof. exact (TRANS (@lem7085056) (@lem7085059)). Qed.
Lemma lem7085061 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7085062 : term261 = term80.
Proof. exact (MK_COMB (@lem7085061) (@lem7085060)). Qed.
Lemma lem7085063 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7085064 : term262 = term215.
Proof. exact (MK_COMB (@lem7085062) (@lem7085063)). Qed.
Lemma lem7085066 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7085067 : term215 = term25.
Proof. exact (@lem7085066 term172). Qed.
Lemma lem7085068 : term262 = term25.
Proof. exact (TRANS (@lem7085064) (@lem7085067)). Qed.
Lemma lem7085070 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7085071 : term181 = term182.
Proof. exact (@lem7085070 term172 term172). Qed.
Lemma lem7085072 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7085073 : term184 = term172.
Proof. exact (EQ_MP (@lem7085072) (@lem940073)). Qed.
Lemma lem7085074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7085075 : term182 = term178.
Proof. exact (MK_COMB (@lem7085074) (@lem7085073)). Qed.
Lemma lem7085076 : term181 = term178.
Proof. exact (TRANS (@lem7085071) (@lem7085075)). Qed.
Lemma lem7085077 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem7085078 : term263 = term215.
Proof. exact (MK_COMB (@lem7085077) (@lem7085076)). Qed.
Lemma lem7085080 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7085081 : term215 = term25.
Proof. exact (@lem7085080 term172). Qed.
Lemma lem7085082 : term263 = term25.
Proof. exact (TRANS (@lem7085078) (@lem7085081)). Qed.
Lemma lem7085083 : term25 = term263.
Proof. exact (SYM (@lem7085082)). Qed.
Lemma lem7085084 : term262 = term263.
Proof. exact (TRANS (@lem7085068) (@lem7085083)). Qed.
Lemma lem7085085 : term249 = term167.
Proof. exact (@lem7085035 (@lem7085084)). Qed.
Lemma lem7085086 : term248 = term167.
Proof. exact (TRANS (@lem7085001) (@lem7085085)). Qed.
Lemma lem7085088 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7085089 : term167 = term25.
Proof. exact (@lem7085088 term25). Qed.
Lemma lem7085090 : term248 = term25.
Proof. exact (TRANS (@lem7085086) (@lem7085089)). Qed.
Lemma lem7085091 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7085092 : term264 = term80.
Proof. exact (MK_COMB (@lem7085091) (@lem7085090)). Qed.
Lemma lem7085093 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7085094 (c : real) : (term268 c) = (term81 c).
Proof. exact (MK_COMB (@lem7085092) (@lem7085093 c)). Qed.
Lemma lem7085095 (c : real) : (term267 c) = (term81 c).
Proof. exact (TRANS (@lem7084992 c) (@lem7085094 c)). Qed.
Lemma lem7085096 (c : real) : (term81 c) = term25.
Proof. exact (@lem1982719 c). Qed.
Lemma lem7085097 (c : real) : (term267 c) = term25.
Proof. exact (TRANS (@lem7085095 c) (@lem7085096 c)). Qed.
Lemma lem7085098 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term240 _132484 s c) = term190.
Proof. exact (MK_COMB (@lem7084991 _132484 c s) (@lem7085097 c)). Qed.
Lemma lem7085099 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term239 _132484 s c) = term190.
Proof. exact (TRANS (@lem7084883 _132484 s c) (@lem7085098 _132484 s c)). Qed.
Lemma lem7085100 : term190 = term25.
Proof. exact (@lem1982721 term25). Qed.
Lemma lem7085101 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term239 _132484 s c) = term25.
Proof. exact (TRANS (@lem7085099 _132484 s c) (@lem7085100)). Qed.
Lemma lem7085102 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term235 _132484 s c) = term25.
Proof. exact (TRANS (@lem7084882 _132484 s c) (@lem7085101 _132484 s c)). Qed.
Lemma lem7085103 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term234 _132484 s c) = term25.
Proof. exact (TRANS (@lem7084873 _132484 s c) (@lem7085102 _132484 s c)). Qed.
Lemma lem7085104 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term233 _132484 s c) = term25.
Proof. exact (TRANS (@lem7084872 _132484 s c) (@lem7085103 _132484 s c)). Qed.
Lemma lem7085105 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7085106 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term269 _132484 s c) = term192.
Proof. exact (MK_COMB (@lem7085105) (@lem7085104 _132484 s c)). Qed.
Lemma lem7085107 : term192 = term175.
Proof. exact (@lem1982785 term25). Qed.
Lemma lem7085109 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7085110 : term25 = term167.
Proof. exact (@lem7085109 (NUMERAL 0)). Qed.
Lemma lem7085112 (x : nat) : (term168 x) = (term169 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7085113 : term170 = term171.
Proof. exact (@lem7085112 term172). Qed.
Lemma lem7085114 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7085115 : term173 = term174.
Proof. exact (MK_COMB (@lem7085114) (@lem7085113)). Qed.
Lemma lem7085116 : term175 = term176.
Proof. exact (MK_COMB (@lem7085115) (@lem7085110)). Qed.
Lemma lem7085117 : term176 = term177.
Proof. exact (@lem1981613 term170 term25 term178 term178). Qed.
Lemma lem7085119 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7085120 : term181 = term182.
Proof. exact (@lem7085119 term172 term172). Qed.
Lemma lem7085121 : (term183 = (BIT1 0)) = (term184 = term172).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7085122 : term184 = term172.
Proof. exact (EQ_MP (@lem7085121) (@lem940073)). Qed.
Lemma lem7085123 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7085124 : term182 = term178.
Proof. exact (MK_COMB (@lem7085123) (@lem7085122)). Qed.
Lemma lem7085125 : term181 = term178.
Proof. exact (TRANS (@lem7085120) (@lem7085124)). Qed.
Lemma lem7085127 (x : nat) : (term185 x) = term25.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7085128 : term175 = term25.
Proof. exact (@lem7085127 term172). Qed.
Lemma lem7085129 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7085130 : term186 = term187.
Proof. exact (MK_COMB (@lem7085129) (@lem7085128)). Qed.
Lemma lem7085131 : term177 = term167.
Proof. exact (MK_COMB (@lem7085130) (@lem7085125)). Qed.
Lemma lem7085132 : term176 = term167.
Proof. exact (TRANS (@lem7085117) (@lem7085131)). Qed.
Lemma lem7085133 : term175 = term167.
Proof. exact (TRANS (@lem7085116) (@lem7085132)). Qed.
Lemma lem7085135 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7085136 : term167 = term25.
Proof. exact (@lem7085135 term25). Qed.
Lemma lem7085137 : term175 = term25.
Proof. exact (TRANS (@lem7085133) (@lem7085136)). Qed.
Lemma lem7085138 : term192 = term25.
Proof. exact (TRANS (@lem7085107) (@lem7085137)). Qed.
Lemma lem7085139 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term270 _132484 s c) = (term270 _132484 s c).
Proof. exact (eq_refl (term270 _132484 s c)). Qed.
Lemma lem7085140 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : ((term269 _132484 s c) = term192) = ((term269 _132484 s c) = term25).
Proof. exact (MK_COMB (@lem7085139 _132484 s c) (@lem7085138)). Qed.
Lemma lem7085141 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term269 _132484 s c) = term25.
Proof. exact (EQ_MP (@lem7085140 _132484 s c) (@lem7085106 _132484 s c)). Qed.
Lemma lem7085142 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7085143 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term271 _132484 s c) = term195.
Proof. exact (MK_COMB (@lem7085142) (@lem7085141 _132484 s c)). Qed.
Lemma lem7085144 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7085145 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term272 _132484 s c) = term197.
Proof. exact (MK_COMB (@lem7085143 _132484 s c) (@lem7085144)). Qed.
Lemma lem7085146 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7085147 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term273 _132484 s c) = term195.
Proof. exact (MK_COMB (@lem7085146) (@lem7085104 _132484 s c)). Qed.
Lemma lem7085148 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7085149 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term274 _132484 s c) = term197.
Proof. exact (MK_COMB (@lem7085147 _132484 s c) (@lem7085148)). Qed.
Lemma lem7085150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7085151 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term275 _132484 s c) = term201.
Proof. exact (MK_COMB (@lem7085150) (@lem7085149 _132484 s c)). Qed.
Lemma lem7085152 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term221 _132484 s c) = term202.
Proof. exact (MK_COMB (@lem7085151 _132484 s c) (@lem7085145 _132484 s c)). Qed.
Lemma lem7085166 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term220 _132484 s c) = term202.
Proof. exact (TRANS (@lem7084833 _132484 s c) (@lem7085152 _132484 s c)). Qed.
Lemma lem7085176 (h1 : term202) : term202.
Proof. exact (h1). Qed.
Lemma lem7085177 (h1 : term197) : term197.
Proof. exact (h1). Qed.
Lemma lem7085179 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7085180 : term197 = term203.
Proof. exact (@lem7085179 term25 term25). Qed.
Lemma lem7085182 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7085183 : term25 = term167.
Proof. exact (@lem7085182 (NUMERAL 0)). Qed.
Lemma lem7085185 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7085186 : term25 = term167.
Proof. exact (@lem7085185 (NUMERAL 0)). Qed.
Lemma lem7085187 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7085188 : term204 = term205.
Proof. exact (MK_COMB (@lem7085187) (@lem7085186)). Qed.
Lemma lem7085189 : term203 = term206.
Proof. exact (MK_COMB (@lem7085188) (@lem7085183)). Qed.
Lemma lem7085190 : term207.
Proof. exact (@lem1980255 term25 term178 term25 term178). Qed.
Lemma lem7085192 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085193 : term209 = term210.
Proof. exact (@lem7085192 (NUMERAL 0) term172). Qed.
Lemma lem7085194 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7085195 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7085196 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7085195 h1) (fun h1 : term210 = True => @lem7085194)). Qed.
Lemma lem7085197 : term210 = True.
Proof. exact (EQ_MP (@lem7085196) (@lem7085194)). Qed.
Lemma lem7085198 : term209 = True.
Proof. exact (TRANS (@lem7085193) (@lem7085197)). Qed.
Lemma lem7085199 : True = term209.
Proof. exact (SYM (@lem7085198)). Qed.
Lemma lem7085200 : term209.
Proof. exact (EQ_MP (@lem7085199) (@lem0)). Qed.
Lemma lem7085201 : term212.
Proof. exact (@lem7085190 (@lem7085200)). Qed.
Lemma lem7085203 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085204 : term209 = term210.
Proof. exact (@lem7085203 (NUMERAL 0) term172). Qed.
Lemma lem7085205 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7085206 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7085207 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7085206 h1) (fun h1 : term210 = True => @lem7085205)). Qed.
Lemma lem7085208 : term210 = True.
Proof. exact (EQ_MP (@lem7085207) (@lem7085205)). Qed.
Lemma lem7085209 : term209 = True.
Proof. exact (TRANS (@lem7085204) (@lem7085208)). Qed.
Lemma lem7085210 : True = term209.
Proof. exact (SYM (@lem7085209)). Qed.
Lemma lem7085211 : term209.
Proof. exact (EQ_MP (@lem7085210) (@lem0)). Qed.
Lemma lem7085212 : term206 = term213.
Proof. exact (@lem7085201 (@lem7085211)). Qed.
Lemma lem7085214 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7085215 : term215 = term25.
Proof. exact (@lem7085214 term172). Qed.
Lemma lem7085217 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7085218 : term215 = term25.
Proof. exact (@lem7085217 term172). Qed.
Lemma lem7085219 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7085220 : term216 = term204.
Proof. exact (MK_COMB (@lem7085219) (@lem7085218)). Qed.
Lemma lem7085221 : term213 = term203.
Proof. exact (MK_COMB (@lem7085220) (@lem7085215)). Qed.
Lemma lem7085223 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085224 : term203 = term217.
Proof. exact (@lem7085223 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7085225 : term217 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7085226 : term203 = False.
Proof. exact (TRANS (@lem7085224) (@lem7085225)). Qed.
Lemma lem7085227 : term213 = False.
Proof. exact (TRANS (@lem7085221) (@lem7085226)). Qed.
Lemma lem7085228 : term206 = False.
Proof. exact (TRANS (@lem7085212) (@lem7085227)). Qed.
Lemma lem7085229 : term203 = False.
Proof. exact (TRANS (@lem7085189) (@lem7085228)). Qed.
Lemma lem7085230 : term197 = False.
Proof. exact (TRANS (@lem7085180) (@lem7085229)). Qed.
Lemma lem7085231 (h1 : term197) : False.
Proof. exact (EQ_MP (@lem7085230) (@lem7085177 h1)). Qed.
Lemma lem7085232 (h1 : term197) : term197.
Proof. exact (h1). Qed.
Lemma lem7085234 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7085235 : term197 = term203.
Proof. exact (@lem7085234 term25 term25). Qed.
Lemma lem7085237 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7085238 : term25 = term167.
Proof. exact (@lem7085237 (NUMERAL 0)). Qed.
Lemma lem7085240 (x : nat) : (real_of_num x) = (term166 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7085241 : term25 = term167.
Proof. exact (@lem7085240 (NUMERAL 0)). Qed.
Lemma lem7085242 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7085243 : term204 = term205.
Proof. exact (MK_COMB (@lem7085242) (@lem7085241)). Qed.
Lemma lem7085244 : term203 = term206.
Proof. exact (MK_COMB (@lem7085243) (@lem7085238)). Qed.
Lemma lem7085245 : term207.
Proof. exact (@lem1980255 term25 term178 term25 term178). Qed.
Lemma lem7085247 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085248 : term209 = term210.
Proof. exact (@lem7085247 (NUMERAL 0) term172). Qed.
Lemma lem7085249 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7085250 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7085251 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7085250 h1) (fun h1 : term210 = True => @lem7085249)). Qed.
Lemma lem7085252 : term210 = True.
Proof. exact (EQ_MP (@lem7085251) (@lem7085249)). Qed.
Lemma lem7085253 : term209 = True.
Proof. exact (TRANS (@lem7085248) (@lem7085252)). Qed.
Lemma lem7085254 : True = term209.
Proof. exact (SYM (@lem7085253)). Qed.
Lemma lem7085255 : term209.
Proof. exact (EQ_MP (@lem7085254) (@lem0)). Qed.
Lemma lem7085256 : term212.
Proof. exact (@lem7085245 (@lem7085255)). Qed.
Lemma lem7085258 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085259 : term209 = term210.
Proof. exact (@lem7085258 (NUMERAL 0) term172). Qed.
Lemma lem7085260 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7085261 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7085262 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem7085261 h1) (fun h1 : term210 = True => @lem7085260)). Qed.
Lemma lem7085263 : term210 = True.
Proof. exact (EQ_MP (@lem7085262) (@lem7085260)). Qed.
Lemma lem7085264 : term209 = True.
Proof. exact (TRANS (@lem7085259) (@lem7085263)). Qed.
Lemma lem7085265 : True = term209.
Proof. exact (SYM (@lem7085264)). Qed.
Lemma lem7085266 : term209.
Proof. exact (EQ_MP (@lem7085265) (@lem0)). Qed.
Lemma lem7085267 : term206 = term213.
Proof. exact (@lem7085256 (@lem7085266)). Qed.
Lemma lem7085269 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7085270 : term215 = term25.
Proof. exact (@lem7085269 term172). Qed.
Lemma lem7085272 (x : nat) : (term214 x) = term25.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7085273 : term215 = term25.
Proof. exact (@lem7085272 term172). Qed.
Lemma lem7085274 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7085275 : term216 = term204.
Proof. exact (MK_COMB (@lem7085274) (@lem7085273)). Qed.
Lemma lem7085276 : term213 = term203.
Proof. exact (MK_COMB (@lem7085275) (@lem7085270)). Qed.
Lemma lem7085278 (m : nat) (n : nat) : (term208 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7085279 : term203 = term217.
Proof. exact (@lem7085278 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7085280 : term217 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7085281 : term203 = False.
Proof. exact (TRANS (@lem7085279) (@lem7085280)). Qed.
Lemma lem7085282 : term213 = False.
Proof. exact (TRANS (@lem7085276) (@lem7085281)). Qed.
Lemma lem7085283 : term206 = False.
Proof. exact (TRANS (@lem7085267) (@lem7085282)). Qed.
Lemma lem7085284 : term203 = False.
Proof. exact (TRANS (@lem7085244) (@lem7085283)). Qed.
Lemma lem7085285 : term197 = False.
Proof. exact (TRANS (@lem7085235) (@lem7085284)). Qed.
Lemma lem7085286 (h1 : term197) : False.
Proof. exact (EQ_MP (@lem7085285) (@lem7085232 h1)). Qed.
Lemma lem7085287 (h1 : term202) : False.
Proof. exact (or_elim (@lem7085176 h1) (fun h0 : term197 => @lem7085231 h0) (fun h0 : term197 => @lem7085286 h0)). Qed.
Lemma lem7085289 (h1 : term202) : term202.
Proof. exact (h1). Qed.
Lemma lem7085290 (h1 : term202) : term202 = False.
Proof. exact (prop_ext (fun h2 : term202 => @lem7085287 h1) (fun h2 : False => @lem7085289 h1)). Qed.
Lemma lem7085291 (h1 : term202) : False.
Proof. exact (EQ_MP (@lem7085290 h1) (@lem7085289 h1)). Qed.
Lemma lem7085292 {_132484 : Type'} (s : _132484 -> Prop) (c : real) (h1 : term220 _132484 s c) : term220 _132484 s c.
Proof. exact (h1). Qed.
Lemma lem7085293 {_132484 : Type'} (s : _132484 -> Prop) (c : real) (h1 : term220 _132484 s c) : term202.
Proof. exact (EQ_MP (@lem7085166 _132484 s c) (@lem7085292 _132484 s c h1)). Qed.
Lemma lem7085294 {_132484 : Type'} (s : _132484 -> Prop) (c : real) (h1 : term220 _132484 s c) : term202 = False.
Proof. exact (prop_ext (fun h2 : term202 => @lem7085291 h2) (fun h2 : False => @lem7085293 _132484 s c h1)). Qed.
Lemma lem7085295 {_132484 : Type'} (s : _132484 -> Prop) (c : real) (h1 : term220 _132484 s c) : False.
Proof. exact (EQ_MP (@lem7085294 _132484 s c h1) (@lem7085293 _132484 s c h1)). Qed.
Lemma lem7085296 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term276 _132484 s c.
Proof. exact (fun h0 : term220 _132484 s c => @lem7085295 _132484 s c h0). Qed.
Lemma lem7085297 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term277 _132484 s c.
Proof. exact (@lem1386578 ((term123 _132484 s c) = (term151 _132484 s c))). Qed.
Lemma lem7085300 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term123 _132484 s c) = (term151 _132484 s c).
Proof. exact (@lem7085297 _132484 s c (@lem7085296 _132484 s c)). Qed.
Lemma lem7085305 {_132484 : Type'} (x : _132484) (s : _132484 -> Prop) (c : real) : term154 _132484 x s c.
Proof. exact (fun h0 : term47 _132484 c x s => @lem7085300 _132484 s c). Qed.
Lemma lem7085310 {_132484 : Type'} (x : _132484) (c : real) : term156 _132484 x c.
Proof. exact (fun s : _132484 -> Prop => @lem7085305 _132484 x s c). Qed.
Lemma lem7085315 {_132484 : Type'} (c : real) : term158 _132484 c.
Proof. exact (fun x : _132484 => @lem7085310 _132484 x c). Qed.
Lemma lem7085316 {_132484 : Type'} (c : real) : term159 _132484 c.
Proof. exact (conj (@lem7084822 c) (@lem7085315 _132484 c)). Qed.
Lemma lem7085317 {_132484 : Type'} (c : real) : term64 _132484 c.
Proof. exact (EQ_MP (@lem7084562 _132484 c) (@lem7085316 _132484 c)). Qed.
Lemma lem7085318 {_132484 : Type'} (c : real) : term73 _132484 c.
Proof. exact (@lem7084050 _132484 c (@lem7085317 _132484 c)). Qed.
Lemma lem7085323 {_132484 : Type'} : term278 _132484.
Proof. exact (fun c : real => @lem7085318 _132484 c). Qed.
