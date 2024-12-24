Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_LMUL_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import ITERATE_EXPAND_CASES_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_0_spec.
Require Import NSUM_0_spec.
Require Import NSUM_CLAUSES_spec.
Require Import nsum_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem6931081 (m : nat) : term0 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem6931082 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem6931083 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem6931082 m) (@lem6931081 m)). Qed.
Lemma lem6931084 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem6931083 m n). Qed.
Lemma lem6931085 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem6931086 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem6931085 n m) (@lem6931084 m n)). Qed.
Lemma lem6931087 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem6931086 n m p). Qed.
Lemma lem6931088 (n : nat) (m : nat) (p : nat) : (term4 n m p) = ((term5 m n p) = (term6 n m p)).
Proof. exact (eq_refl (term4 n m p)). Qed.
Lemma lem6931090 : term7.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem6931116 : term8.
Proof. exact (proj1 (@lem6931090)). Qed.
Lemma lem6931117 (m : nat) : term9 m.
Proof. exact (@lem6931116 m). Qed.
Lemma lem6931118 (m : nat) : (term9 m) = ((term10 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem6931124 {_126525 : Type'} : term11 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem6931125 {_126525 : Type'} (x : _126525) : term12 _126525 x.
Proof. exact (@lem6931124 _126525 x). Qed.
Lemma lem6931126 {_126525 : Type'} (x : _126525) : (term12 _126525 x) = (term13 _126525 x).
Proof. exact (eq_refl (term12 _126525 x)). Qed.
Lemma lem6931127 {_126525 : Type'} (x : _126525) : term13 _126525 x.
Proof. exact (EQ_MP (@lem6931126 _126525 x) (@lem6931125 _126525 x)). Qed.
Lemma lem6931128 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term14 _126525 x f.
Proof. exact (@lem6931127 _126525 x f). Qed.
Lemma lem6931129 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term14 _126525 x f) = (term15 _126525 x f).
Proof. exact (eq_refl (term14 _126525 x f)). Qed.
Lemma lem6931130 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term15 _126525 x f.
Proof. exact (EQ_MP (@lem6931129 _126525 x f) (@lem6931128 _126525 x f)). Qed.
Lemma lem6931131 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term16 _126525 x f s.
Proof. exact (@lem6931130 _126525 x f s). Qed.
Lemma lem6931132 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term16 _126525 x f s) = (term17 _126525 x s f).
Proof. exact (eq_refl (term16 _126525 x f s)). Qed.
Lemma lem6931133 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term17 _126525 x s f.
Proof. exact (EQ_MP (@lem6931132 _126525 x s f) (@lem6931131 _126525 x f s)). Qed.
Lemma lem6931134 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem6931135 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term18 _126525 x s f) = (term19 _126525 x s f).
Proof. exact (@lem6931133 _126525 x s f (@lem6931134 _126525 s h1)). Qed.
Lemma lem6931141 {_126486 : Type'} : term20 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem6931142 {_126486 : Type'} (f : _126486 -> nat) : term21 _126486 f.
Proof. exact (@lem6931141 _126486 f). Qed.
Lemma lem6931143 {_126486 : Type'} (f : _126486 -> nat) : (term21 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term21 _126486 f)). Qed.
Lemma lem6931145 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem6931146 {A : Type'} (P : type686 A) (h1 : term22 A) : term23 A P.
Proof. exact (@lem6931145 A h1 P). Qed.
Lemma lem6931147 {A : Type'} (P : type686 A) : (term23 A P) = (term24 A P).
Proof. exact (eq_refl (term23 A P)). Qed.
Lemma lem6931148 {A : Type'} (P : type686 A) (h1 : term22 A) : term24 A P.
Proof. exact (EQ_MP (@lem6931147 A P) (@lem6931146 A P h1)). Qed.
Lemma lem6931149 {A : Type'} (P : type686 A) (h1 : term25 A P) : term25 A P.
Proof. exact (h1). Qed.
Lemma lem6931150 {A : Type'} (P : type686 A) (h1 : term22 A) (h2 : term25 A P) : term26 A P.
Proof. exact (@lem6931148 A P h1 (@lem6931149 A P h2)). Qed.
Lemma lem6931151 {A : Type'} (P : type686 A) (h1 : term25 A P) : term27 A P.
Proof. exact (fun h0 : term22 A => @lem6931150 A P h0 h1). Qed.
Lemma lem6931152 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem6931153 {A : Type'} (P : type686 A) (h1 : term22 A) (h2 : term25 A P) : term26 A P.
Proof. exact (@lem6931151 A P h2 (@lem6931152 A h1)). Qed.
Lemma lem6931154 {A : Type'} (P : type686 A) (h1 : term22 A) : term24 A P.
Proof. exact (fun h0 : term25 A P => @lem6931153 A P h1 h0). Qed.
Lemma lem6931155 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (fun P : type686 A => @lem6931154 A P h1). Qed.
Lemma lem6931156 {A : Type'} : term28 A.
Proof. exact (fun h0 : term22 A => @lem6931155 A h0). Qed.
Lemma lem6931157 {A : Type'} : term22 A.
Proof. exact (@lem6931156 A (@lem3558722 A)). Qed.
Lemma lem6931158 {A : Type'} (P : type686 A) : term23 A P.
Proof. exact (@lem6931157 A P). Qed.
Lemma lem6931159 {A : Type'} (P : type686 A) : (term23 A P) = (term24 A P).
Proof. exact (eq_refl (term23 A P)). Qed.
Lemma lem6931161 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (h1). Qed.
Lemma lem6931162 {_126417 : Type'} (h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (SYM (@lem6931161 _126417 h1)). Qed.
Lemma lem6931163 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (h1). Qed.
Lemma lem6931164 {_126417 : Type'} (h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417)) : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (SYM (@lem6931163 _126417 h1)). Qed.
Lemma lem6931165 {_126417 : Type'} : ((@nsum _126417) = (@iterate nat _126417 Nat.add)) = ((@iterate nat _126417 Nat.add) = (@nsum _126417)).
Proof. exact (prop_ext (fun h1 : (@nsum _126417) = (@iterate nat _126417 Nat.add) => @lem6931162 _126417 h1) (fun h1 : (@iterate nat _126417 Nat.add) = (@nsum _126417) => @lem6931164 _126417 h1)). Qed.
Lemma lem6931167 : term7.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem6931193 : term8.
Proof. exact (proj1 (@lem6931167)). Qed.
Lemma lem6931194 (m : nat) : term9 m.
Proof. exact (@lem6931193 m). Qed.
Lemma lem6931195 (m : nat) : (term9 m) = ((term10 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem6931201 {_120327 _120333 : Type'} (op : type1400 _120327) : term29 _120327 _120333 op.
Proof. exact (@lem5738118 _120327 _120333 op). Qed.
Lemma lem6931202 {_120327 _120333 : Type'} (op : type1400 _120327) : (term29 _120327 _120333 op) = (term30 _120327 _120333 op).
Proof. exact (eq_refl (term29 _120327 _120333 op)). Qed.
Lemma lem6931203 {_120327 _120333 : Type'} (op : type1400 _120327) : term30 _120327 _120333 op.
Proof. exact (EQ_MP (@lem6931202 _120327 _120333 op) (@lem6931201 _120327 _120333 op)). Qed.
Lemma lem6931204 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) : term31 _120327 _120333 op f.
Proof. exact (@lem6931203 _120327 _120333 op f). Qed.
Lemma lem6931205 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : (term31 _120327 _120333 op f) = (term32 _120327 _120333 f op).
Proof. exact (eq_refl (term31 _120327 _120333 op f)). Qed.
Lemma lem6931206 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : term32 _120327 _120333 f op.
Proof. exact (EQ_MP (@lem6931205 _120327 _120333 f op) (@lem6931204 _120327 _120333 op f)). Qed.
Lemma lem6931207 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) (s : _120333 -> Prop) : term33 _120327 _120333 f op s.
Proof. exact (@lem6931206 _120327 _120333 f op s). Qed.
Lemma lem6931208 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (term33 _120327 _120333 f op s) = ((@iterate _120327 _120333 op s f) = (term34 _120327 _120333 s f op)).
Proof. exact (eq_refl (term33 _120327 _120333 f op s)). Qed.
Lemma lem6931210 (c : nat) : term35 c.
Proof. exact (@lem9784 (c = (NUMERAL 0))). Qed.
Lemma lem6931211 (c : nat) : (term35 c) = (term36 c).
Proof. exact (eq_refl (term35 c)). Qed.
Lemma lem6931212 (c : nat) : term36 c.
Proof. exact (EQ_MP (@lem6931211 c) (@lem6931210 c)). Qed.
Lemma lem6931214 (c : nat) (h1 : term37 c) : term37 c.
Proof. exact (h1). Qed.
Lemma lem6931215 {A : Type'} (s : A -> Prop) : term38 A s.
Proof. exact (@lem6931080 A s). Qed.
Lemma lem6931216 {A : Type'} (s : A -> Prop) : (term38 A s) = ((term39 A s) = (NUMERAL 0)).
Proof. exact (eq_refl (term38 A s)). Qed.
Lemma lem6931248 : term40.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem6931249 (n : nat) : term41 n.
Proof. exact (@lem6931248 n). Qed.
Lemma lem6931250 (n : nat) : (term41 n) = ((term42 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem6931255 (c : nat) (h1 : c = (NUMERAL 0)) : c = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6931256 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6931257 (c : nat) (h1 : c = (NUMERAL 0)) : (Nat.mul c) = term43.
Proof. exact (MK_COMB (@lem6931256) (@lem6931255 c h1)). Qed.
Lemma lem6931258 {A : Type'} (f : A -> nat) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem6931259 {A : Type'} (f : A -> nat) (x : A) (c : nat) (h1 : c = (NUMERAL 0)) : (term44 A c f x) = (term45 A f x).
Proof. exact (MK_COMB (@lem6931257 c h1) (@lem6931258 A f x)). Qed.
Lemma lem6931261 (n : nat) : (term42 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6931250 n) (@lem6931249 n)). Qed.
Lemma lem6931262 {A : Type'} (f : A -> nat) (x : A) : (term45 A f x) = (NUMERAL 0).
Proof. exact (@lem6931261 (f x)). Qed.
Lemma lem6931263 {A : Type'} (f : A -> nat) (x : A) (c : nat) (h1 : c = (NUMERAL 0)) : (term44 A c f x) = (NUMERAL 0).
Proof. exact (TRANS (@lem6931259 A f x c h1) (@lem6931262 A f x)). Qed.
Lemma lem6931264 {A : Type'} (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : (term46 A c f) = (term47 A).
Proof. exact (fun_ext (fun x : A => @lem6931263 A f x c h1)). Qed.
Lemma lem6931265 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@nsum A s).
Proof. exact (eq_refl (@nsum A s)). Qed.
Lemma lem6931266 {A : Type'} (f : A -> nat) (s : A -> Prop) (c : nat) (h1 : c = (NUMERAL 0)) : (term48 A s c f) = (term39 A s).
Proof. exact (MK_COMB (@lem6931265 A s) (@lem6931264 A f c h1)). Qed.
Lemma lem6931268 {A : Type'} (s : A -> Prop) : (term39 A s) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6931216 A s) (@lem6931215 A s)). Qed.
Lemma lem6931269 {A : Type'} (s : A -> Prop) : (term39 A s) = (NUMERAL 0).
Proof. exact (@lem6931268 A s). Qed.
Lemma lem6931270 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : (term48 A s c f) = (NUMERAL 0).
Proof. exact (TRANS (@lem6931266 A f s c h1) (@lem6931269 A s)). Qed.
Lemma lem6931271 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931272 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : (term49 A s c f) = term50.
Proof. exact (MK_COMB (@lem6931271) (@lem6931270 A s f c h1)). Qed.
Lemma lem6931274 (c : nat) (h1 : c = (NUMERAL 0)) : c = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6931275 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6931276 (c : nat) (h1 : c = (NUMERAL 0)) : (Nat.mul c) = term43.
Proof. exact (MK_COMB (@lem6931275) (@lem6931274 c h1)). Qed.
Lemma lem6931277 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@nsum A s f).
Proof. exact (eq_refl (@nsum A s f)). Qed.
Lemma lem6931278 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : (term51 A c s f) = (term52 A s f).
Proof. exact (MK_COMB (@lem6931276 c h1) (@lem6931277 A s f)). Qed.
Lemma lem6931280 (n : nat) : (term42 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6931250 n) (@lem6931249 n)). Qed.
Lemma lem6931281 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term52 A s f) = (NUMERAL 0).
Proof. exact (@lem6931280 (@nsum A s f)). Qed.
Lemma lem6931282 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : (term51 A c s f) = (NUMERAL 0).
Proof. exact (TRANS (@lem6931278 A s f c h1) (@lem6931281 A s f)). Qed.
Lemma lem6931283 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : ((term48 A s c f) = (term51 A c s f)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6931272 A s f c h1) (@lem6931282 A s f c h1)). Qed.
Lemma lem6931285 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6931286 (x : nat) : (x = x) = True.
Proof. exact (@lem6931285 nat x). Qed.
Lemma lem6931287 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6931286 (NUMERAL 0)). Qed.
Lemma lem6931288 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : ((term48 A s c f) = (term51 A c s f)) = True.
Proof. exact (TRANS (@lem6931283 A s f c h1) (@lem6931287)). Qed.
Lemma lem6931289 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : True = ((term48 A s c f) = (term51 A c s f)).
Proof. exact (SYM (@lem6931288 A s f c h1)). Qed.
Lemma lem6931290 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : c = (NUMERAL 0)) : (term48 A s c f) = (term51 A c s f).
Proof. exact (EQ_MP (@lem6931289 A s f c h1) (@lem0)). Qed.
Lemma lem6931348 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6931349 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6931348 A). Qed.
Lemma lem6931350 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6931351 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem6931349 A) (@lem6931350 A s)). Qed.
Lemma lem6931352 {A : Type'} (c : nat) (f : A -> nat) : (term46 A c f) = (term46 A c f).
Proof. exact (eq_refl (term46 A c f)). Qed.
Lemma lem6931353 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term48 A s c f) = (term53 A s c f).
Proof. exact (MK_COMB (@lem6931351 A s) (@lem6931352 A c f)). Qed.
Lemma lem6931354 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931355 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term49 A s c f) = (term54 A s c f).
Proof. exact (MK_COMB (@lem6931354) (@lem6931353 A s c f)). Qed.
Lemma lem6931357 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6931358 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6931357 A). Qed.
Lemma lem6931359 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6931360 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem6931358 A) (@lem6931359 A s)). Qed.
Lemma lem6931361 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6931362 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@iterate nat A Nat.add s f).
Proof. exact (MK_COMB (@lem6931360 A s) (@lem6931361 A f)). Qed.
Lemma lem6931363 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem6931364 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term51 A c s f) = (term55 A c s f).
Proof. exact (MK_COMB (@lem6931363 c) (@lem6931362 A s f)). Qed.
Lemma lem6931365 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term48 A s c f) = (term51 A c s f)) = ((term53 A s c f) = (term55 A c s f)).
Proof. exact (MK_COMB (@lem6931355 A s c f) (@lem6931364 A c s f)). Qed.
Lemma lem6931368 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term53 A s c f) = (term55 A c s f)) = ((term48 A s c f) = (term51 A c s f)).
Proof. exact (SYM (@lem6931365 A c s f)). Qed.
Lemma lem6931372 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term34 _120327 _120333 s f op).
Proof. exact (EQ_MP (@lem6931208 _120327 _120333 s f op) (@lem6931207 _120327 _120333 f op s)). Qed.
Lemma lem6931373 {A : Type'} (s : A -> Prop) (f : A -> nat) (op : type1606) : (@iterate nat A op s f) = (term56 A s f op).
Proof. exact (@lem6931372 nat A s f op). Qed.
Lemma lem6931374 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term53 A s c f) = (term57 A s c f).
Proof. exact (@lem6931373 A s (term46 A c f) Nat.add). Qed.
Lemma lem6931375 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931376 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term54 A s c f) = (term58 A s c f).
Proof. exact (MK_COMB (@lem6931375) (@lem6931374 A s c f)). Qed.
Lemma lem6931378 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term34 _120327 _120333 s f op).
Proof. exact (EQ_MP (@lem6931208 _120327 _120333 s f op) (@lem6931207 _120327 _120333 f op s)). Qed.
Lemma lem6931379 {A : Type'} (s : A -> Prop) (f : A -> nat) (op : type1606) : (@iterate nat A op s f) = (term56 A s f op).
Proof. exact (@lem6931378 nat A s f op). Qed.
Lemma lem6931380 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@iterate nat A Nat.add s f) = (term59 A s f).
Proof. exact (@lem6931379 A s f Nat.add). Qed.
Lemma lem6931381 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem6931382 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term55 A c s f) = (term60 A c s f).
Proof. exact (MK_COMB (@lem6931381 c) (@lem6931380 A s f)). Qed.
Lemma lem6931383 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term53 A s c f) = (term55 A c s f)) = ((term57 A s c f) = (term60 A c s f)).
Proof. exact (MK_COMB (@lem6931376 A s c f) (@lem6931382 A c s f)). Qed.
Lemma lem6931384 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term57 A s c f) = (term60 A c s f)) = ((term53 A s c f) = (term55 A c s f)).
Proof. exact (SYM (@lem6931383 A c s f)). Qed.
Lemma lem6931385 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : (term61 A c f s) = (@support A nat Nat.add f s)) : (term61 A c f s) = (@support A nat Nat.add f s).
Proof. exact (h1). Qed.
Lemma lem6931386 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term62 A c s f) = (term62 A c s f).
Proof. exact (eq_refl (term62 A c s f)). Qed.
Lemma lem6931387 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : (term61 A c f s) = (@support A nat Nat.add f s)) : (term63 A c f s) = (term64 A c f s).
Proof. exact (MK_COMB (@lem6931386 A c s f) (@lem6931385 A c f s h1)). Qed.
Lemma lem6931388 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term64 A c f s) = ((term65 A s c f) = (term60 A c s f)).
Proof. exact (eq_refl (term64 A c f s)). Qed.
Lemma lem6931389 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) : (term66 A c f s) = (term66 A c f s).
Proof. exact (eq_refl (term66 A c f s)). Qed.
Lemma lem6931390 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term63 A c f s) = (term64 A c f s)) = ((term63 A c f s) = ((term65 A s c f) = (term60 A c s f))).
Proof. exact (MK_COMB (@lem6931389 A c f s) (@lem6931388 A c s f)). Qed.
Lemma lem6931391 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term63 A c f s) = ((term57 A s c f) = (term60 A c s f)).
Proof. exact (eq_refl (term63 A c f s)). Qed.
Lemma lem6931392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6931393 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term66 A c f s) = (term67 A c s f).
Proof. exact (MK_COMB (@lem6931392) (@lem6931391 A c s f)). Qed.
Lemma lem6931394 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term65 A s c f) = (term60 A c s f)) = ((term65 A s c f) = (term60 A c s f)).
Proof. exact (eq_refl ((term65 A s c f) = (term60 A c s f))). Qed.
Lemma lem6931395 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term63 A c f s) = ((term65 A s c f) = (term60 A c s f))) = (((term57 A s c f) = (term60 A c s f)) = ((term65 A s c f) = (term60 A c s f))).
Proof. exact (MK_COMB (@lem6931393 A c s f) (@lem6931394 A c s f)). Qed.
Lemma lem6931396 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term63 A c f s) = (term64 A c f s)) = (((term57 A s c f) = (term60 A c s f)) = ((term65 A s c f) = (term60 A c s f))).
Proof. exact (TRANS (@lem6931390 A c s f) (@lem6931395 A c s f)). Qed.
Lemma lem6931397 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : (term61 A c f s) = (@support A nat Nat.add f s)) : ((term57 A s c f) = (term60 A c s f)) = ((term65 A s c f) = (term60 A c s f)).
Proof. exact (EQ_MP (@lem6931396 A c s f) (@lem6931387 A c f s h1)). Qed.
Lemma lem6931398 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : (term61 A c f s) = (@support A nat Nat.add f s)) : ((term65 A s c f) = (term60 A c s f)) = ((term57 A s c f) = (term60 A c s f)).
Proof. exact (SYM (@lem6931397 A c f s h1)). Qed.
Lemma lem6931399 (m : nat) : term68 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem6931400 (m : nat) : (term68 m) = (term69 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem6931401 (m : nat) : term69 m.
Proof. exact (EQ_MP (@lem6931400 m) (@lem6931399 m)). Qed.
Lemma lem6931402 (m : nat) (n : nat) : term70 m n.
Proof. exact (@lem6931401 m n). Qed.
Lemma lem6931403 (m : nat) (n : nat) : (term70 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term71 m n)).
Proof. exact (eq_refl (term70 m n)). Qed.
Lemma lem6931405 {A B : Type'} (s : A -> Prop) : term72 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem6931406 {A B : Type'} (s : A -> Prop) : (term72 A B s) = (term73 A B s).
Proof. exact (eq_refl (term72 A B s)). Qed.
Lemma lem6931407 {A B : Type'} (s : A -> Prop) : term73 A B s.
Proof. exact (EQ_MP (@lem6931406 A B s) (@lem6931405 A B s)). Qed.
Lemma lem6931408 {A B : Type'} (s : A -> Prop) (f : A -> B) : term74 A B s f.
Proof. exact (@lem6931407 A B s f). Qed.
Lemma lem6931409 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term74 A B s f) = (term75 A B s f).
Proof. exact (eq_refl (term74 A B s f)). Qed.
Lemma lem6931410 {A B : Type'} (s : A -> Prop) (f : A -> B) : term75 A B s f.
Proof. exact (EQ_MP (@lem6931409 A B s f) (@lem6931408 A B s f)). Qed.
Lemma lem6931411 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term76 A B s f op.
Proof. exact (@lem6931410 A B s f op). Qed.
Lemma lem6931412 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term76 A B s f op) = ((@support A B op f s) = (term77 A B s f op)).
Proof. exact (eq_refl (term76 A B s f op)). Qed.
Lemma lem6931414 (c : nat) : term78 c.
Proof. exact (@lem82 (c = (NUMERAL 0))). Qed.
Lemma lem6931430 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term77 A B s f op).
Proof. exact (EQ_MP (@lem6931412 A B s f op) (@lem6931411 A B s f op)). Qed.
Lemma lem6931431 {A : Type'} (s : A -> Prop) (f : A -> nat) (op : type1606) : (@support A nat op f s) = (term79 A s f op).
Proof. exact (@lem6931430 A nat s f op). Qed.
Lemma lem6931432 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term61 A c f s) = (term80 A s c f).
Proof. exact (@lem6931431 A s (term46 A c f) Nat.add). Qed.
Lemma lem6931442 {A B : Type'} (f : A -> B) (y : A) : (term81 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6931443 {A : Type'} (f : A -> nat) (y : A) : (term82 A f y) = (f y).
Proof. exact (@lem6931442 A nat f y). Qed.
Lemma lem6931444 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term83 A c f x) = (term84 A c f x).
Proof. exact (@lem6931443 A (term46 A c f) x). Qed.
Lemma lem6931445 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term84 A c f x) = (term44 A c f x).
Proof. exact (eq_refl (term84 A c f x)). Qed.
Lemma lem6931446 {A : Type'} (c : nat) (f : A -> nat) : (term85 A c f) = (term46 A c f).
Proof. exact (fun_ext (fun x : A => @lem6931445 A c f x)). Qed.
Lemma lem6931447 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6931448 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term83 A c f x) = (term84 A c f x).
Proof. exact (MK_COMB (@lem6931446 A c f) (@lem6931447 A x)). Qed.
Lemma lem6931449 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931450 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term86 A c f x) = (term87 A c f x).
Proof. exact (MK_COMB (@lem6931449) (@lem6931448 A c f x)). Qed.
Lemma lem6931451 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term84 A c f x) = (term44 A c f x).
Proof. exact (eq_refl (term84 A c f x)). Qed.
Lemma lem6931452 {A : Type'} (c : nat) (f : A -> nat) (x : A) : ((term83 A c f x) = (term84 A c f x)) = ((term84 A c f x) = (term44 A c f x)).
Proof. exact (MK_COMB (@lem6931450 A c f x) (@lem6931451 A c f x)). Qed.
Lemma lem6931453 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term84 A c f x) = (term44 A c f x).
Proof. exact (EQ_MP (@lem6931452 A c f x) (@lem6931444 A c f x)). Qed.
Lemma lem6931454 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931455 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term87 A c f x) = (term88 A c f x).
Proof. exact (MK_COMB (@lem6931454) (@lem6931453 A c f x)). Qed.
Lemma lem6931457 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6931458 {A : Type'} (c : nat) (f : A -> nat) (x : A) : ((term84 A c f x) = (@neutral nat Nat.add)) = ((term44 A c f x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6931455 A c f x) (@lem6931457)). Qed.
Lemma lem6931460 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term71 m n).
Proof. exact (EQ_MP (@lem6931403 m n) (@lem6931402 m n)). Qed.
Lemma lem6931461 {A : Type'} (c : nat) (f : A -> nat) (x : A) : ((term44 A c f x) = (NUMERAL 0)) = (term89 A c f x).
Proof. exact (@lem6931460 c (f x)). Qed.
Lemma lem6931465 (c : nat) (h1 : term37 c) : (c = (NUMERAL 0)) = False.
Proof. exact (@lem6931414 c (@lem6931214 c h1)). Qed.
Lemma lem6931466 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6931467 (c : nat) (h1 : term37 c) : (term90 c) = (or False).
Proof. exact (MK_COMB (@lem6931466) (@lem6931465 c h1)). Qed.
Lemma lem6931470 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem6931471 {A : Type'} (f : A -> nat) (x : A) (c : nat) (h1 : term37 c) : (term89 A c f x) = (term91 A f x).
Proof. exact (MK_COMB (@lem6931467 c h1) (@lem6931470 A f x)). Qed.
Lemma lem6931473 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem6931474 {A : Type'} (f : A -> nat) (x : A) : (term91 A f x) = ((f x) = (NUMERAL 0)).
Proof. exact (@lem6931473 ((f x) = (NUMERAL 0))). Qed.
Lemma lem6931477 {A : Type'} (f : A -> nat) (x : A) (c : nat) (h1 : term37 c) : (term89 A c f x) = ((f x) = (NUMERAL 0)).
Proof. exact (TRANS (@lem6931471 A f x c h1) (@lem6931474 A f x)). Qed.
Lemma lem6931478 {A : Type'} (f : A -> nat) (x : A) (c : nat) (h1 : term37 c) : ((term44 A c f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (TRANS (@lem6931461 A c f x) (@lem6931477 A f x c h1)). Qed.
Lemma lem6931479 {A : Type'} (f : A -> nat) (x : A) (c : nat) (h1 : term37 c) : ((term84 A c f x) = (@neutral nat Nat.add)) = ((f x) = (NUMERAL 0)).
Proof. exact (TRANS (@lem6931458 A c f x) (@lem6931478 A f x c h1)). Qed.
Lemma lem6931480 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6931481 {A : Type'} (f : A -> nat) (x : A) (c : nat) (h1 : term37 c) : (term92 A c f x) = (term93 A f x).
Proof. exact (MK_COMB (@lem6931480) (@lem6931479 A f x c h1)). Qed.
Lemma lem6931484 {A : Type'} (x : A) (s : A -> Prop) : (term94 A x s) = (term94 A x s).
Proof. exact (eq_refl (term94 A x s)). Qed.
Lemma lem6931485 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (c : nat) (h1 : term37 c) : (term95 A s c f x) = (term96 A s f x).
Proof. exact (MK_COMB (@lem6931484 A x s) (@lem6931481 A f x c h1)). Qed.
Lemma lem6931490 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6931491 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) (c : nat) (h1 : term37 c) : (term97 A GEN_PVAR_237 s c f x) = (term98 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem6931490 A GEN_PVAR_237) (@lem6931485 A s f x c h1)). Qed.
Lemma lem6931496 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6931497 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) (c : nat) (h1 : term37 c) : (term99 A GEN_PVAR_237 s c f x) = (term100 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem6931491 A GEN_PVAR_237 s f x c h1) (@lem6931496 A x)). Qed.
Lemma lem6931502 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term101 A GEN_PVAR_237 s c f) = (term102 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem6931497 A GEN_PVAR_237 s f x c h1)). Qed.
Lemma lem6931507 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6931508 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term103 A GEN_PVAR_237 s c f) = (term104 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem6931507 A) (@lem6931502 A GEN_PVAR_237 s f c h1)). Qed.
Lemma lem6931517 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term105 A s c f) = (term106 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6931508 A GEN_PVAR_237 s f c h1)). Qed.
Lemma lem6931526 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6931527 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term80 A s c f) = (term107 A s f).
Proof. exact (MK_COMB (@lem6931526 A) (@lem6931517 A s f c h1)). Qed.
Lemma lem6931536 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term61 A c f s) = (term107 A s f).
Proof. exact (TRANS (@lem6931432 A s c f) (@lem6931527 A s f c h1)). Qed.
Lemma lem6931537 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem6931538 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term108 A c f s) = (term109 A s f).
Proof. exact (MK_COMB (@lem6931537 A) (@lem6931536 A s f c h1)). Qed.
Lemma lem6931548 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term77 A B s f op).
Proof. exact (EQ_MP (@lem6931412 A B s f op) (@lem6931411 A B s f op)). Qed.
Lemma lem6931549 {A : Type'} (s : A -> Prop) (f : A -> nat) (op : type1606) : (@support A nat op f s) = (term79 A s f op).
Proof. exact (@lem6931548 A nat s f op). Qed.
Lemma lem6931550 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@support A nat Nat.add f s) = (term110 A s f).
Proof. exact (@lem6931549 A s f Nat.add). Qed.
Lemma lem6931560 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6931561 {A : Type'} (f : A -> nat) (x : A) : (term111 A f x) = (term111 A f x).
Proof. exact (eq_refl (term111 A f x)). Qed.
Lemma lem6931562 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (@neutral nat Nat.add)) = ((f x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6931561 A f x) (@lem6931560)). Qed.
Lemma lem6931565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6931566 {A : Type'} (f : A -> nat) (x : A) : (term112 A f x) = (term93 A f x).
Proof. exact (MK_COMB (@lem6931565) (@lem6931562 A f x)). Qed.
Lemma lem6931569 {A : Type'} (x : A) (s : A -> Prop) : (term94 A x s) = (term94 A x s).
Proof. exact (eq_refl (term94 A x s)). Qed.
Lemma lem6931570 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term113 A s f x) = (term96 A s f x).
Proof. exact (MK_COMB (@lem6931569 A x s) (@lem6931566 A f x)). Qed.
Lemma lem6931575 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem6931576 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term114 A GEN_PVAR_237 s f x) = (term98 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem6931575 A GEN_PVAR_237) (@lem6931570 A s f x)). Qed.
Lemma lem6931581 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6931582 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term115 A GEN_PVAR_237 s f x) = (term100 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem6931576 A GEN_PVAR_237 s f x) (@lem6931581 A x)). Qed.
Lemma lem6931587 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term116 A GEN_PVAR_237 s f) = (term102 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem6931582 A GEN_PVAR_237 s f x)). Qed.
Lemma lem6931592 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6931593 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term117 A GEN_PVAR_237 s f) = (term104 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem6931592 A) (@lem6931587 A GEN_PVAR_237 s f)). Qed.
Lemma lem6931602 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term118 A s f) = (term106 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem6931593 A GEN_PVAR_237 s f)). Qed.
Lemma lem6931611 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6931612 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term110 A s f) = (term107 A s f).
Proof. exact (MK_COMB (@lem6931611 A) (@lem6931602 A s f)). Qed.
Lemma lem6931621 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@support A nat Nat.add f s) = (term107 A s f).
Proof. exact (TRANS (@lem6931550 A s f) (@lem6931612 A s f)). Qed.
Lemma lem6931622 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : ((term61 A c f s) = (@support A nat Nat.add f s)) = ((term107 A s f) = (term107 A s f)).
Proof. exact (MK_COMB (@lem6931538 A s f c h1) (@lem6931621 A s f)). Qed.
Lemma lem6931624 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6931625 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem6931624 (A -> Prop) x). Qed.
Lemma lem6931626 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((term107 A s f) = (term107 A s f)) = True.
Proof. exact (@lem6931625 A (term107 A s f)). Qed.
Lemma lem6931627 {A : Type'} (f : A -> nat) (s : A -> Prop) (c : nat) (h1 : term37 c) : ((term61 A c f s) = (@support A nat Nat.add f s)) = True.
Proof. exact (TRANS (@lem6931622 A s f c h1) (@lem6931626 A s f)). Qed.
Lemma lem6931628 {A : Type'} (f : A -> nat) (s : A -> Prop) (c : nat) (h1 : term37 c) : True = ((term61 A c f s) = (@support A nat Nat.add f s)).
Proof. exact (SYM (@lem6931627 A f s c h1)). Qed.
Lemma lem6931629 {A : Type'} (f : A -> nat) (s : A -> Prop) (c : nat) (h1 : term37 c) : (term61 A c f s) = (@support A nat Nat.add f s).
Proof. exact (EQ_MP (@lem6931628 A f s c h1) (@lem0)). Qed.
Lemma lem6931630 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term119 _476 _475 _474 _477) = (term120 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem6931631 {A : Type'} (_474 : nat) (_475 : Prop) (c : nat) (s : A -> Prop) (f : A -> nat) (_477 : nat) : (term121 A c s f _475 _474 _477) = (term122 A _474 _475 c s f _477).
Proof. exact (@lem6931630 _474 _475 (term123 A c s f) _477). Qed.
Lemma lem6931632 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term124 A s c f) = (term125 A c s f).
Proof. exact (@lem6931631 A (term126 A s c f) (term127 A f s) c s f (@neutral nat Nat.add)). Qed.
Lemma lem6931633 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term128 A c s f) = ((@neutral nat Nat.add) = (term60 A c s f)).
Proof. exact (eq_refl (term128 A c s f)). Qed.
Lemma lem6931634 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term129 A f s) = (term129 A f s).
Proof. exact (eq_refl (term129 A f s)). Qed.
Lemma lem6931635 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term130 A c s f) = (term131 A c s f).
Proof. exact (MK_COMB (@lem6931634 A f s) (@lem6931633 A c s f)). Qed.
Lemma lem6931636 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term132 A s c f) = ((term126 A s c f) = (term60 A c s f)).
Proof. exact (eq_refl (term132 A s c f)). Qed.
Lemma lem6931637 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term133 A f s) = (term133 A f s).
Proof. exact (eq_refl (term133 A f s)). Qed.
Lemma lem6931638 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term134 A s c f) = (term135 A c s f).
Proof. exact (MK_COMB (@lem6931637 A f s) (@lem6931636 A c s f)). Qed.
Lemma lem6931639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6931640 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term136 A s c f) = (term137 A c s f).
Proof. exact (MK_COMB (@lem6931639) (@lem6931638 A c s f)). Qed.
Lemma lem6931641 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term125 A c s f) = (term138 A c s f).
Proof. exact (MK_COMB (@lem6931640 A c s f) (@lem6931635 A c s f)). Qed.
Lemma lem6931642 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term124 A s c f) = ((term65 A s c f) = (term60 A c s f)).
Proof. exact (eq_refl (term124 A s c f)). Qed.
Lemma lem6931643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6931644 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term139 A s c f) = (term140 A c s f).
Proof. exact (MK_COMB (@lem6931643) (@lem6931642 A c s f)). Qed.
Lemma lem6931645 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term124 A s c f) = (term125 A c s f)) = (((term65 A s c f) = (term60 A c s f)) = (term138 A c s f)).
Proof. exact (MK_COMB (@lem6931644 A c s f) (@lem6931641 A c s f)). Qed.
Lemma lem6931646 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term65 A s c f) = (term60 A c s f)) = (term138 A c s f).
Proof. exact (EQ_MP (@lem6931645 A c s f) (@lem6931632 A c s f)). Qed.
Lemma lem6931647 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term138 A c s f) = ((term65 A s c f) = (term60 A c s f)).
Proof. exact (SYM (@lem6931646 A c s f)). Qed.
Lemma lem6931648 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : term127 A f s.
Proof. exact (h1). Qed.
Lemma lem6931649 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term127 A f s) = ((term127 A f s) = True).
Proof. exact (@lem7 (term127 A f s)). Qed.
Lemma lem6931650 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : (term127 A f s) = True.
Proof. exact (EQ_MP (@lem6931649 A f s) (@lem6931648 A f s h1)). Qed.
Lemma lem6931651 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term141 A c s f) = (term141 A c s f).
Proof. exact (eq_refl (term141 A c s f)). Qed.
Lemma lem6931652 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : (term142 A c f s) = (term143 A c s f).
Proof. exact (MK_COMB (@lem6931651 A c s f) (@lem6931650 A f s h1)). Qed.
Lemma lem6931653 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term143 A c s f) = ((term126 A s c f) = (term144 A c s f)).
Proof. exact (eq_refl (term143 A c s f)). Qed.
Lemma lem6931654 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) : (term145 A c f s) = (term145 A c f s).
Proof. exact (eq_refl (term145 A c f s)). Qed.
Lemma lem6931655 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term142 A c f s) = (term143 A c s f)) = ((term142 A c f s) = ((term126 A s c f) = (term144 A c s f))).
Proof. exact (MK_COMB (@lem6931654 A c f s) (@lem6931653 A c s f)). Qed.
Lemma lem6931656 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term142 A c f s) = ((term126 A s c f) = (term60 A c s f)).
Proof. exact (eq_refl (term142 A c f s)). Qed.
Lemma lem6931657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6931658 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term145 A c f s) = (term146 A c s f).
Proof. exact (MK_COMB (@lem6931657) (@lem6931656 A c s f)). Qed.
Lemma lem6931659 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term126 A s c f) = (term144 A c s f)) = ((term126 A s c f) = (term144 A c s f)).
Proof. exact (eq_refl ((term126 A s c f) = (term144 A c s f))). Qed.
Lemma lem6931660 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term142 A c f s) = ((term126 A s c f) = (term144 A c s f))) = (((term126 A s c f) = (term60 A c s f)) = ((term126 A s c f) = (term144 A c s f))).
Proof. exact (MK_COMB (@lem6931658 A c s f) (@lem6931659 A c s f)). Qed.
Lemma lem6931661 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term142 A c f s) = (term143 A c s f)) = (((term126 A s c f) = (term60 A c s f)) = ((term126 A s c f) = (term144 A c s f))).
Proof. exact (TRANS (@lem6931655 A c s f) (@lem6931660 A c s f)). Qed.
Lemma lem6931662 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : ((term126 A s c f) = (term60 A c s f)) = ((term126 A s c f) = (term144 A c s f)).
Proof. exact (EQ_MP (@lem6931661 A c s f) (@lem6931652 A c f s h1)). Qed.
Lemma lem6931663 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : ((term126 A s c f) = (term144 A c s f)) = ((term126 A s c f) = (term60 A c s f)).
Proof. exact (SYM (@lem6931662 A c f s h1)). Qed.
Lemma lem6931664 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term147 A f s) : term147 A f s.
Proof. exact (h1). Qed.
Lemma lem6931665 {A : Type'} (f : A -> nat) (s : A -> Prop) : term148 A f s.
Proof. exact (@lem82 (term127 A f s)). Qed.
Lemma lem6931666 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term147 A f s) : (term127 A f s) = False.
Proof. exact (@lem6931665 A f s (@lem6931664 A f s h1)). Qed.
Lemma lem6931667 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term149 A c s f) = (term149 A c s f).
Proof. exact (eq_refl (term149 A c s f)). Qed.
Lemma lem6931668 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term147 A f s) : (term150 A c f s) = (term151 A c s f).
Proof. exact (MK_COMB (@lem6931667 A c s f) (@lem6931666 A f s h1)). Qed.
Lemma lem6931669 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term151 A c s f) = ((@neutral nat Nat.add) = (term152 A c s f)).
Proof. exact (eq_refl (term151 A c s f)). Qed.
Lemma lem6931670 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) : (term153 A c f s) = (term153 A c f s).
Proof. exact (eq_refl (term153 A c f s)). Qed.
Lemma lem6931671 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term150 A c f s) = (term151 A c s f)) = ((term150 A c f s) = ((@neutral nat Nat.add) = (term152 A c s f))).
Proof. exact (MK_COMB (@lem6931670 A c f s) (@lem6931669 A c s f)). Qed.
Lemma lem6931672 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term150 A c f s) = ((@neutral nat Nat.add) = (term60 A c s f)).
Proof. exact (eq_refl (term150 A c f s)). Qed.
Lemma lem6931673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6931674 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term153 A c f s) = (term154 A c s f).
Proof. exact (MK_COMB (@lem6931673) (@lem6931672 A c s f)). Qed.
Lemma lem6931675 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((@neutral nat Nat.add) = (term152 A c s f)) = ((@neutral nat Nat.add) = (term152 A c s f)).
Proof. exact (eq_refl ((@neutral nat Nat.add) = (term152 A c s f))). Qed.
Lemma lem6931676 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term150 A c f s) = ((@neutral nat Nat.add) = (term152 A c s f))) = (((@neutral nat Nat.add) = (term60 A c s f)) = ((@neutral nat Nat.add) = (term152 A c s f))).
Proof. exact (MK_COMB (@lem6931674 A c s f) (@lem6931675 A c s f)). Qed.
Lemma lem6931677 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term150 A c f s) = (term151 A c s f)) = (((@neutral nat Nat.add) = (term60 A c s f)) = ((@neutral nat Nat.add) = (term152 A c s f))).
Proof. exact (TRANS (@lem6931671 A c s f) (@lem6931676 A c s f)). Qed.
Lemma lem6931678 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term147 A f s) : ((@neutral nat Nat.add) = (term60 A c s f)) = ((@neutral nat Nat.add) = (term152 A c s f)).
Proof. exact (EQ_MP (@lem6931677 A c s f) (@lem6931668 A c f s h1)). Qed.
Lemma lem6931679 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term147 A f s) : ((@neutral nat Nat.add) = (term152 A c s f)) = ((@neutral nat Nat.add) = (term60 A c s f)).
Proof. exact (SYM (@lem6931678 A c f s h1)). Qed.
Lemma lem6931683 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6931684 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem6931683 nat t2 t1). Qed.
Lemma lem6931685 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term155 A s f) = (term156 A s f).
Proof. exact (@lem6931684 (@neutral nat Nat.add) (term156 A s f)). Qed.
Lemma lem6931686 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem6931687 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term144 A c s f) = (term157 A c s f).
Proof. exact (MK_COMB (@lem6931686 c) (@lem6931685 A s f)). Qed.
Lemma lem6931688 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term158 A s c f) = (term158 A s c f).
Proof. exact (eq_refl (term158 A s c f)). Qed.
Lemma lem6931689 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term126 A s c f) = (term144 A c s f)) = ((term126 A s c f) = (term157 A c s f)).
Proof. exact (MK_COMB (@lem6931688 A s c f) (@lem6931687 A c s f)). Qed.
Lemma lem6931692 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term126 A s c f) = (term157 A c s f)) = ((term126 A s c f) = (term144 A c s f)).
Proof. exact (SYM (@lem6931689 A c s f)). Qed.
Lemma lem6931696 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6931697 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931698 : term159 = term50.
Proof. exact (MK_COMB (@lem6931697) (@lem6931696)). Qed.
Lemma lem6931700 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6931701 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6931700 nat t1 t2). Qed.
Lemma lem6931702 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term160 A s f) = (@neutral nat Nat.add).
Proof. exact (@lem6931701 (term156 A s f) (@neutral nat Nat.add)). Qed.
Lemma lem6931704 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem6931705 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term160 A s f) = (NUMERAL 0).
Proof. exact (TRANS (@lem6931702 A s f) (@lem6931704)). Qed.
Lemma lem6931706 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem6931707 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) : (term152 A c s f) = (term10 c).
Proof. exact (MK_COMB (@lem6931706 c) (@lem6931705 A s f)). Qed.
Lemma lem6931709 (m : nat) : (term10 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6931195 m) (@lem6931194 m)). Qed.
Lemma lem6931710 (c : nat) : (term10 c) = (NUMERAL 0).
Proof. exact (@lem6931709 c). Qed.
Lemma lem6931711 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term152 A c s f) = (NUMERAL 0).
Proof. exact (TRANS (@lem6931707 A s f c) (@lem6931710 c)). Qed.
Lemma lem6931712 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((@neutral nat Nat.add) = (term152 A c s f)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6931698) (@lem6931711 A c s f)). Qed.
Lemma lem6931714 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6931715 (x : nat) : (x = x) = True.
Proof. exact (@lem6931714 nat x). Qed.
Lemma lem6931716 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6931715 (NUMERAL 0)). Qed.
Lemma lem6931717 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((@neutral nat Nat.add) = (term152 A c s f)) = True.
Proof. exact (TRANS (@lem6931712 A c s f) (@lem6931716)). Qed.
Lemma lem6931718 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : True = ((@neutral nat Nat.add) = (term152 A c s f)).
Proof. exact (SYM (@lem6931717 A c s f)). Qed.
Lemma lem6931719 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (@neutral nat Nat.add) = (term152 A c s f).
Proof. exact (EQ_MP (@lem6931718 A c s f) (@lem0)). Qed.
Lemma lem6931729 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (EQ_MP (@lem6931165 _126417) (@lem6920372 _126417)). Qed.
Lemma lem6931730 {A : Type'} : (@iterate nat A Nat.add) = (@nsum A).
Proof. exact (@lem6931729 A). Qed.
Lemma lem6931731 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6931732 {A : Type'} (t : A -> Prop) : (@iterate nat A Nat.add t) = (@nsum A t).
Proof. exact (MK_COMB (@lem6931730 A) (@lem6931731 A t)). Qed.
Lemma lem6931733 {A : Type'} (c : nat) (f : A -> nat) : (term46 A c f) = (term46 A c f).
Proof. exact (eq_refl (term46 A c f)). Qed.
Lemma lem6931734 {A : Type'} (t : A -> Prop) (c : nat) (f : A -> nat) : (term53 A t c f) = (term48 A t c f).
Proof. exact (MK_COMB (@lem6931732 A t) (@lem6931733 A c f)). Qed.
Lemma lem6931735 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931736 {A : Type'} (t : A -> Prop) (c : nat) (f : A -> nat) : (term54 A t c f) = (term49 A t c f).
Proof. exact (MK_COMB (@lem6931735) (@lem6931734 A t c f)). Qed.
Lemma lem6931738 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@nsum _126417).
Proof. exact (EQ_MP (@lem6931165 _126417) (@lem6920372 _126417)). Qed.
Lemma lem6931739 {A : Type'} : (@iterate nat A Nat.add) = (@nsum A).
Proof. exact (@lem6931738 A). Qed.
Lemma lem6931740 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6931741 {A : Type'} (t : A -> Prop) : (@iterate nat A Nat.add t) = (@nsum A t).
Proof. exact (MK_COMB (@lem6931739 A) (@lem6931740 A t)). Qed.
Lemma lem6931742 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6931743 {A : Type'} (t : A -> Prop) (f : A -> nat) : (@iterate nat A Nat.add t f) = (@nsum A t f).
Proof. exact (MK_COMB (@lem6931741 A t) (@lem6931742 A f)). Qed.
Lemma lem6931744 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem6931745 {A : Type'} (c : nat) (t : A -> Prop) (f : A -> nat) : (term55 A c t f) = (term51 A c t f).
Proof. exact (MK_COMB (@lem6931744 c) (@lem6931743 A t f)). Qed.
Lemma lem6931746 {A : Type'} (c : nat) (t : A -> Prop) (f : A -> nat) : ((term53 A t c f) = (term55 A c t f)) = ((term48 A t c f) = (term51 A c t f)).
Proof. exact (MK_COMB (@lem6931736 A t c f) (@lem6931745 A c t f)). Qed.
Lemma lem6931749 {A : Type'} (t : A -> Prop) : (term161 A t) = (term161 A t).
Proof. exact (eq_refl (term161 A t)). Qed.
Lemma lem6931750 {A : Type'} (c : nat) (t : A -> Prop) (f : A -> nat) : (term162 A c t f) = (term163 A c t f).
Proof. exact (MK_COMB (@lem6931749 A t) (@lem6931746 A c t f)). Qed.
Lemma lem6931753 {A : Type'} (c : nat) (f : A -> nat) : (term164 A c f) = (term165 A c f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6931750 A c t f)). Qed.
Lemma lem6931754 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6931755 {A : Type'} (c : nat) (f : A -> nat) : (term166 A c f) = (term167 A c f).
Proof. exact (MK_COMB (@lem6931754 A) (@lem6931753 A c f)). Qed.
Lemma lem6931760 {A : Type'} (c : nat) (f : A -> nat) : (term167 A c f) = (term166 A c f).
Proof. exact (SYM (@lem6931755 A c f)). Qed.
Lemma lem6931762 {A : Type'} (P : type686 A) : term24 A P.
Proof. exact (EQ_MP (@lem6931159 A P) (@lem6931158 A P)). Qed.
Lemma lem6931763 {A : Type'} (P : type686 A) : term24 A P.
Proof. exact (@lem6931762 A P). Qed.
Lemma lem6931764 {A : Type'} (c : nat) (f : A -> nat) : term168 A c f.
Proof. exact (@lem6931763 A (term169 A c f)). Qed.
Lemma lem6931765 {A : Type'} (c : nat) (f : A -> nat) : (term170 A c f) = ((term171 A c f) = (term172 A c f)).
Proof. exact (eq_refl (term170 A c f)). Qed.
Lemma lem6931766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6931767 {A : Type'} (c : nat) (f : A -> nat) : (term173 A c f) = (term174 A c f).
Proof. exact (MK_COMB (@lem6931766) (@lem6931765 A c f)). Qed.
Lemma lem6931768 {A : Type'} (c : nat) (t : A -> Prop) (f : A -> nat) : (term175 A c f t) = ((term48 A t c f) = (term51 A c t f)).
Proof. exact (eq_refl (term175 A c f t)). Qed.
Lemma lem6931769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6931770 {A : Type'} (c : nat) (t : A -> Prop) (f : A -> nat) : (term176 A c f t) = (term177 A c t f).
Proof. exact (MK_COMB (@lem6931769) (@lem6931768 A c t f)). Qed.
Lemma lem6931771 {A : Type'} (x : A) (t : A -> Prop) : (term178 A x t) = (term178 A x t).
Proof. exact (eq_refl (term178 A x t)). Qed.
Lemma lem6931772 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) : (term179 A c f x t) = (term180 A c f x t).
Proof. exact (MK_COMB (@lem6931770 A c t f) (@lem6931771 A x t)). Qed.
Lemma lem6931773 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6931774 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) : (term181 A c f x t) = (term182 A c f x t).
Proof. exact (MK_COMB (@lem6931773) (@lem6931772 A c f x t)). Qed.
Lemma lem6931775 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) : (term183 A c f x t) = ((term184 A x t c f) = (term185 A c x t f)).
Proof. exact (eq_refl (term183 A c f x t)). Qed.
Lemma lem6931776 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) : (term186 A c f x t) = (term187 A c x t f).
Proof. exact (MK_COMB (@lem6931774 A c f x t) (@lem6931775 A c x t f)). Qed.
Lemma lem6931777 {A : Type'} (c : nat) (x : A) (f : A -> nat) : (term188 A c f x) = (term189 A c x f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6931776 A c x t f)). Qed.
Lemma lem6931778 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6931779 {A : Type'} (c : nat) (x : A) (f : A -> nat) : (term190 A c f x) = (term191 A c x f).
Proof. exact (MK_COMB (@lem6931778 A) (@lem6931777 A c x f)). Qed.
Lemma lem6931780 {A : Type'} (c : nat) (f : A -> nat) : (term192 A c f) = (term193 A c f).
Proof. exact (fun_ext (fun x : A => @lem6931779 A c x f)). Qed.
Lemma lem6931781 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6931782 {A : Type'} (c : nat) (f : A -> nat) : (term194 A c f) = (term195 A c f).
Proof. exact (MK_COMB (@lem6931781 A) (@lem6931780 A c f)). Qed.
Lemma lem6931783 {A : Type'} (c : nat) (f : A -> nat) : (term196 A c f) = (term197 A c f).
Proof. exact (MK_COMB (@lem6931767 A c f) (@lem6931782 A c f)). Qed.
Lemma lem6931784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6931785 {A : Type'} (c : nat) (f : A -> nat) : (term198 A c f) = (term199 A c f).
Proof. exact (MK_COMB (@lem6931784) (@lem6931783 A c f)). Qed.
Lemma lem6931786 {A : Type'} (c : nat) (t : A -> Prop) (f : A -> nat) : (term175 A c f t) = ((term48 A t c f) = (term51 A c t f)).
Proof. exact (eq_refl (term175 A c f t)). Qed.
Lemma lem6931787 {A : Type'} (t : A -> Prop) : (term161 A t) = (term161 A t).
Proof. exact (eq_refl (term161 A t)). Qed.
Lemma lem6931788 {A : Type'} (c : nat) (t : A -> Prop) (f : A -> nat) : (term200 A c f t) = (term163 A c t f).
Proof. exact (MK_COMB (@lem6931787 A t) (@lem6931786 A c t f)). Qed.
Lemma lem6931789 {A : Type'} (c : nat) (f : A -> nat) : (term201 A c f) = (term165 A c f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6931788 A c t f)). Qed.
Lemma lem6931790 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6931791 {A : Type'} (c : nat) (f : A -> nat) : (term202 A c f) = (term167 A c f).
Proof. exact (MK_COMB (@lem6931790 A) (@lem6931789 A c f)). Qed.
Lemma lem6931792 {A : Type'} (c : nat) (f : A -> nat) : (term168 A c f) = (term203 A c f).
Proof. exact (MK_COMB (@lem6931785 A c f) (@lem6931791 A c f)). Qed.
Lemma lem6931793 {A : Type'} (c : nat) (f : A -> nat) : term203 A c f.
Proof. exact (EQ_MP (@lem6931792 A c f) (@lem6931764 A c f)). Qed.
Lemma lem6931799 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6931143 _126486 f) (@lem6931142 _126486 f)). Qed.
Lemma lem6931800 {A : Type'} (f : A -> nat) : (@nsum A (@EMPTY A) f) = (NUMERAL 0).
Proof. exact (@lem6931799 A f). Qed.
Lemma lem6931801 {A : Type'} (c : nat) (f : A -> nat) : (term171 A c f) = (NUMERAL 0).
Proof. exact (@lem6931800 A (term46 A c f)). Qed.
Lemma lem6931802 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931803 {A : Type'} (c : nat) (f : A -> nat) : (term204 A c f) = term50.
Proof. exact (MK_COMB (@lem6931802) (@lem6931801 A c f)). Qed.
Lemma lem6931805 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6931143 _126486 f) (@lem6931142 _126486 f)). Qed.
Lemma lem6931806 {A : Type'} (f : A -> nat) : (@nsum A (@EMPTY A) f) = (NUMERAL 0).
Proof. exact (@lem6931805 A f). Qed.
Lemma lem6931807 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem6931808 {A : Type'} (f : A -> nat) (c : nat) : (term172 A c f) = (term10 c).
Proof. exact (MK_COMB (@lem6931807 c) (@lem6931806 A f)). Qed.
Lemma lem6931810 (m : nat) : (term10 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6931118 m) (@lem6931117 m)). Qed.
Lemma lem6931811 (c : nat) : (term10 c) = (NUMERAL 0).
Proof. exact (@lem6931810 c). Qed.
Lemma lem6931812 {A : Type'} (c : nat) (f : A -> nat) : (term172 A c f) = (NUMERAL 0).
Proof. exact (TRANS (@lem6931808 A f c) (@lem6931811 c)). Qed.
Lemma lem6931813 {A : Type'} (c : nat) (f : A -> nat) : ((term171 A c f) = (term172 A c f)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6931803 A c f) (@lem6931812 A c f)). Qed.
Lemma lem6931815 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6931816 (x : nat) : (x = x) = True.
Proof. exact (@lem6931815 nat x). Qed.
Lemma lem6931817 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem6931816 (NUMERAL 0)). Qed.
Lemma lem6931818 {A : Type'} (c : nat) (f : A -> nat) : ((term171 A c f) = (term172 A c f)) = True.
Proof. exact (TRANS (@lem6931813 A c f) (@lem6931817)). Qed.
Lemma lem6931819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6931820 {A : Type'} (c : nat) (f : A -> nat) : (term174 A c f) = (and True).
Proof. exact (MK_COMB (@lem6931819) (@lem6931818 A c f)). Qed.
Lemma lem6931832 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term205 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6931833 (p : Prop) (q : Prop) (p' : Prop) : term206 p q p'.
Proof. exact (fun q' : Prop => @lem6931832 p q p' q'). Qed.
Lemma lem6931834 (p : Prop) (q : Prop) : term207 p q.
Proof. exact (fun p' : Prop => @lem6931833 p q p'). Qed.
Lemma lem6931835 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) : term208 A c x t f.
Proof. exact (@lem6931834 (term180 A c f x t) ((term184 A x t c f) = (term185 A c x t f))). Qed.
Lemma lem6931836 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) (p' : Prop) : term209 A c x t f p'.
Proof. exact (@lem6931835 A c x t f p'). Qed.
Lemma lem6931837 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) (p' : Prop) : (term209 A c x t f p') = (term210 A c x t f p').
Proof. exact (eq_refl (term209 A c x t f p')). Qed.
Lemma lem6931838 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) (p' : Prop) : term210 A c x t f p'.
Proof. exact (EQ_MP (@lem6931837 A c x t f p') (@lem6931836 A c x t f p')). Qed.
Lemma lem6931839 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term211 A c x t f p' q'.
Proof. exact (@lem6931838 A c x t f p' q'). Qed.
Lemma lem6931840 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term211 A c x t f p' q') = (term212 A c x t f p' q').
Proof. exact (eq_refl (term211 A c x t f p' q')). Qed.
Lemma lem6931841 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term212 A c x t f p' q'.
Proof. exact (EQ_MP (@lem6931840 A c x t f p' q') (@lem6931839 A c x t f p' q')). Qed.
Lemma lem6931848 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) : (term180 A c f x t) = (term180 A c f x t).
Proof. exact (eq_refl (term180 A c f x t)). Qed.
Lemma lem6931849 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (q' : Prop) : term213 A c f x t q'.
Proof. exact (@lem6931841 A c x t f (term180 A c f x t) q'). Qed.
Lemma lem6931850 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (q' : Prop) : term214 A c f x t q'.
Proof. exact (@lem6931849 A c f x t q' (@lem6931848 A c f x t)). Qed.
Lemma lem6931851 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term180 A c f x t.
Proof. exact (h1). Qed.
Lemma lem6931852 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term178 A x t.
Proof. exact (proj2 (@lem6931851 A c f x t h1)). Qed.
Lemma lem6931853 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : @FINITE A t.
Proof. exact (proj2 (@lem6931852 A c f x t h1)). Qed.
Lemma lem6931854 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem6931856 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term215 A x t.
Proof. exact (proj1 (@lem6931852 A c f x t h1)). Qed.
Lemma lem6931857 {A : Type'} (x : A) (t : A -> Prop) : term216 A x t.
Proof. exact (@lem82 (@IN A x t)). Qed.
Lemma lem6931863 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term17 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6931135 _126525 x f s h0). Qed.
Lemma lem6931864 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term17 A x s f.
Proof. exact (@lem6931863 A x s f). Qed.
Lemma lem6931865 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) : term217 A x t c f.
Proof. exact (@lem6931864 A x t (term46 A c f)). Qed.
Lemma lem6931867 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem6931854 A t) (@lem6931853 A c f x t h1)). Qed.
Lemma lem6931868 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : True = (@FINITE A t).
Proof. exact (SYM (@lem6931867 A c f x t h1)). Qed.
Lemma lem6931869 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : @FINITE A t.
Proof. exact (EQ_MP (@lem6931868 A c f x t h1) (@lem0)). Qed.
Lemma lem6931870 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term184 A x t c f) = (term218 A x t c f).
Proof. exact (@lem6931865 A x t c f (@lem6931869 A c f x t h1)). Qed.
Lemma lem6931872 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term219 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6931873 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term220 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6931872 _2963 g t e g' t' e'). Qed.
Lemma lem6931874 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term221 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6931873 _2963 g t e g' t'). Qed.
Lemma lem6931875 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term222 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6931874 _2963 g t e g'). Qed.
Lemma lem6931876 (g : Prop) (t : nat) (e : nat) : term223 g t e.
Proof. exact (@lem6931875 nat g t e). Qed.
Lemma lem6931877 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) : term224 A x t c f.
Proof. exact (@lem6931876 (@IN A x t) (term48 A t c f) (term225 A x t c f)). Qed.
Lemma lem6931878 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) : term226 A x t c f g'.
Proof. exact (@lem6931877 A x t c f g'). Qed.
Lemma lem6931879 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) : (term226 A x t c f g') = (term227 A x t c f g').
Proof. exact (eq_refl (term226 A x t c f g')). Qed.
Lemma lem6931880 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) : term227 A x t c f g'.
Proof. exact (EQ_MP (@lem6931879 A x t c f g') (@lem6931878 A x t c f g')). Qed.
Lemma lem6931881 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) (t' : nat) : term228 A x t c f g' t'.
Proof. exact (@lem6931880 A x t c f g' t'). Qed.
Lemma lem6931882 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) (t' : nat) : (term228 A x t c f g' t') = (term229 A x t c f g' t').
Proof. exact (eq_refl (term228 A x t c f g' t')). Qed.
Lemma lem6931883 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) (t' : nat) : term229 A x t c f g' t'.
Proof. exact (EQ_MP (@lem6931882 A x t c f g' t') (@lem6931881 A x t c f g' t')). Qed.
Lemma lem6931884 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term230 A x t c f g' t' e'.
Proof. exact (@lem6931883 A x t c f g' t' e'). Qed.
Lemma lem6931885 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term230 A x t c f g' t' e') = (term231 A x t c f g' t' e').
Proof. exact (eq_refl (term230 A x t c f g' t' e')). Qed.
Lemma lem6931886 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term231 A x t c f g' t' e'.
Proof. exact (EQ_MP (@lem6931885 A x t c f g' t' e') (@lem6931884 A x t c f g' t' e')). Qed.
Lemma lem6931888 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (@IN A x t) = False.
Proof. exact (@lem6931857 A x t (@lem6931856 A c f x t h1)). Qed.
Lemma lem6931889 {A : Type'} (x : A) (t : A -> Prop) (c : nat) (f : A -> nat) (t' : nat) (e' : nat) : term232 A x t c f t' e'.
Proof. exact (@lem6931886 A x t c f False t' e'). Qed.
Lemma lem6931890 {A : Type'} (t' : nat) (e' : nat) (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term233 A x t c f t' e'.
Proof. exact (@lem6931889 A x t c f t' e' (@lem6931888 A c f x t h1)). Qed.
Lemma lem6931895 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term48 A t c f) = (term51 A c t f).
Proof. exact (proj1 (@lem6931851 A c f x t h1)). Qed.
Lemma lem6931896 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term48 A t c f) = (term51 A c t f).
Proof. exact (@lem6931895 A c f x t h1). Qed.
Lemma lem6931897 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term234 A c t f.
Proof. exact (fun h0 : False => @lem6931896 A c f x t h1). Qed.
Lemma lem6931898 {A : Type'} (e' : nat) (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term235 A x c t f e'.
Proof. exact (@lem6931890 A (term51 A c t f) e' c f x t h1). Qed.
Lemma lem6931899 {A : Type'} (e' : nat) (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term236 A x c t f e'.
Proof. exact (@lem6931898 A e' c f x t h1 (@lem6931897 A c f x t h1)). Qed.
Lemma lem6931906 {A B : Type'} (f : A -> B) (y : A) : (term81 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6931907 {A : Type'} (f : A -> nat) (y : A) : (term82 A f y) = (f y).
Proof. exact (@lem6931906 A nat f y). Qed.
Lemma lem6931908 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term83 A c f x) = (term84 A c f x).
Proof. exact (@lem6931907 A (term46 A c f) x). Qed.
Lemma lem6931909 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term84 A c f x) = (term44 A c f x).
Proof. exact (eq_refl (term84 A c f x)). Qed.
Lemma lem6931910 {A : Type'} (c : nat) (f : A -> nat) : (term85 A c f) = (term46 A c f).
Proof. exact (fun_ext (fun x : A => @lem6931909 A c f x)). Qed.
Lemma lem6931911 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6931912 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term83 A c f x) = (term84 A c f x).
Proof. exact (MK_COMB (@lem6931910 A c f) (@lem6931911 A x)). Qed.
Lemma lem6931913 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931914 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term86 A c f x) = (term87 A c f x).
Proof. exact (MK_COMB (@lem6931913) (@lem6931912 A c f x)). Qed.
Lemma lem6931915 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term84 A c f x) = (term44 A c f x).
Proof. exact (eq_refl (term84 A c f x)). Qed.
Lemma lem6931916 {A : Type'} (c : nat) (f : A -> nat) (x : A) : ((term83 A c f x) = (term84 A c f x)) = ((term84 A c f x) = (term44 A c f x)).
Proof. exact (MK_COMB (@lem6931914 A c f x) (@lem6931915 A c f x)). Qed.
Lemma lem6931917 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term84 A c f x) = (term44 A c f x).
Proof. exact (EQ_MP (@lem6931916 A c f x) (@lem6931908 A c f x)). Qed.
Lemma lem6931918 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6931919 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term237 A c f x) = (term238 A c f x).
Proof. exact (MK_COMB (@lem6931918) (@lem6931917 A c f x)). Qed.
Lemma lem6931921 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term48 A t c f) = (term51 A c t f).
Proof. exact (proj1 (@lem6931851 A c f x t h1)). Qed.
Lemma lem6931922 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term48 A t c f) = (term51 A c t f).
Proof. exact (@lem6931921 A c f x t h1). Qed.
Lemma lem6931923 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term225 A x t c f) = (term239 A x c t f).
Proof. exact (MK_COMB (@lem6931919 A c f x) (@lem6931922 A c f x t h1)). Qed.
Lemma lem6931924 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term240 A x c t f.
Proof. exact (fun h0 : ~ False => @lem6931923 A c f x t h1). Qed.
Lemma lem6931925 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term241 A x c t f.
Proof. exact (@lem6931899 A (term239 A x c t f) c f x t h1). Qed.
Lemma lem6931926 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term218 A x t c f) = (term242 A x c t f).
Proof. exact (@lem6931925 A c f x t h1 (@lem6931924 A c f x t h1)). Qed.
Lemma lem6931928 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6931929 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6931928 nat t1 t2). Qed.
Lemma lem6931930 {A : Type'} (x : A) (c : nat) (t : A -> Prop) (f : A -> nat) : (term242 A x c t f) = (term239 A x c t f).
Proof. exact (@lem6931929 (term51 A c t f) (term239 A x c t f)). Qed.
Lemma lem6931931 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term218 A x t c f) = (term239 A x c t f).
Proof. exact (TRANS (@lem6931926 A c f x t h1) (@lem6931930 A x c t f)). Qed.
Lemma lem6931932 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term184 A x t c f) = (term239 A x c t f).
Proof. exact (TRANS (@lem6931870 A c f x t h1) (@lem6931931 A c f x t h1)). Qed.
Lemma lem6931933 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6931934 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term243 A x t c f) = (term244 A x c t f).
Proof. exact (MK_COMB (@lem6931933) (@lem6931932 A c f x t h1)). Qed.
Lemma lem6931936 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term17 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6931135 _126525 x f s h0). Qed.
Lemma lem6931937 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term17 A x s f.
Proof. exact (@lem6931936 A x s f). Qed.
Lemma lem6931938 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) : term17 A x t f.
Proof. exact (@lem6931937 A x t f). Qed.
Lemma lem6931940 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem6931854 A t) (@lem6931853 A c f x t h1)). Qed.
Lemma lem6931941 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : True = (@FINITE A t).
Proof. exact (SYM (@lem6931940 A c f x t h1)). Qed.
Lemma lem6931942 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : @FINITE A t.
Proof. exact (EQ_MP (@lem6931941 A c f x t h1) (@lem0)). Qed.
Lemma lem6931943 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term18 A x t f) = (term19 A x t f).
Proof. exact (@lem6931938 A x t f (@lem6931942 A c f x t h1)). Qed.
Lemma lem6931945 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term219 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6931946 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term220 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6931945 _2963 g t e g' t' e'). Qed.
Lemma lem6931947 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term221 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6931946 _2963 g t e g' t'). Qed.
Lemma lem6931948 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term222 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6931947 _2963 g t e g'). Qed.
Lemma lem6931949 (g : Prop) (t : nat) (e : nat) : term223 g t e.
Proof. exact (@lem6931948 nat g t e). Qed.
Lemma lem6931950 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) : term245 A x t f.
Proof. exact (@lem6931949 (@IN A x t) (@nsum A t f) (term246 A x t f)). Qed.
Lemma lem6931951 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) : term247 A x t f g'.
Proof. exact (@lem6931950 A x t f g'). Qed.
Lemma lem6931952 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) : (term247 A x t f g') = (term248 A x t f g').
Proof. exact (eq_refl (term247 A x t f g')). Qed.
Lemma lem6931953 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) : term248 A x t f g'.
Proof. exact (EQ_MP (@lem6931952 A x t f g') (@lem6931951 A x t f g')). Qed.
Lemma lem6931954 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : term249 A x t f g' t'.
Proof. exact (@lem6931953 A x t f g' t'). Qed.
Lemma lem6931955 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : (term249 A x t f g' t') = (term250 A x t f g' t').
Proof. exact (eq_refl (term249 A x t f g' t')). Qed.
Lemma lem6931956 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) : term250 A x t f g' t'.
Proof. exact (EQ_MP (@lem6931955 A x t f g' t') (@lem6931954 A x t f g' t')). Qed.
Lemma lem6931957 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term251 A x t f g' t' e'.
Proof. exact (@lem6931956 A x t f g' t' e'). Qed.
Lemma lem6931958 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term251 A x t f g' t' e') = (term252 A x t f g' t' e').
Proof. exact (eq_refl (term251 A x t f g' t' e')). Qed.
Lemma lem6931959 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term252 A x t f g' t' e'.
Proof. exact (EQ_MP (@lem6931958 A x t f g' t' e') (@lem6931957 A x t f g' t' e')). Qed.
Lemma lem6931961 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (@IN A x t) = False.
Proof. exact (@lem6931857 A x t (@lem6931856 A c f x t h1)). Qed.
Lemma lem6931962 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) (t' : nat) (e' : nat) : term253 A x t f t' e'.
Proof. exact (@lem6931959 A x t f False t' e'). Qed.
Lemma lem6931963 {A : Type'} (t' : nat) (e' : nat) (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term254 A x t f t' e'.
Proof. exact (@lem6931962 A x t f t' e' (@lem6931961 A c f x t h1)). Qed.
Lemma lem6931967 {A : Type'} (t : A -> Prop) (f : A -> nat) : (@nsum A t f) = (@nsum A t f).
Proof. exact (eq_refl (@nsum A t f)). Qed.
Lemma lem6931968 {A : Type'} (t : A -> Prop) (f : A -> nat) : term255 A t f.
Proof. exact (fun h0 : False => @lem6931967 A t f). Qed.
Lemma lem6931969 {A : Type'} (e' : nat) (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term256 A x t f e'.
Proof. exact (@lem6931963 A (@nsum A t f) e' c f x t h1). Qed.
Lemma lem6931970 {A : Type'} (e' : nat) (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term257 A x t f e'.
Proof. exact (@lem6931969 A e' c f x t h1 (@lem6931968 A t f)). Qed.
Lemma lem6931976 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) : (term246 A x t f) = (term246 A x t f).
Proof. exact (eq_refl (term246 A x t f)). Qed.
Lemma lem6931977 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) : term258 A x t f.
Proof. exact (fun h0 : ~ False => @lem6931976 A x t f). Qed.
Lemma lem6931978 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : term259 A x t f.
Proof. exact (@lem6931970 A (term246 A x t f) c f x t h1). Qed.
Lemma lem6931979 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term19 A x t f) = (term260 A x t f).
Proof. exact (@lem6931978 A c f x t h1 (@lem6931977 A x t f)). Qed.
Lemma lem6931981 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6931982 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6931981 nat t1 t2). Qed.
Lemma lem6931983 {A : Type'} (x : A) (t : A -> Prop) (f : A -> nat) : (term260 A x t f) = (term246 A x t f).
Proof. exact (@lem6931982 (@nsum A t f) (term246 A x t f)). Qed.
Lemma lem6931984 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term19 A x t f) = (term246 A x t f).
Proof. exact (TRANS (@lem6931979 A c f x t h1) (@lem6931983 A x t f)). Qed.
Lemma lem6931985 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term18 A x t f) = (term246 A x t f).
Proof. exact (TRANS (@lem6931943 A c f x t h1) (@lem6931984 A c f x t h1)). Qed.
Lemma lem6931986 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem6931987 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term185 A c x t f) = (term261 A c x t f).
Proof. exact (MK_COMB (@lem6931986 c) (@lem6931985 A c f x t h1)). Qed.
Lemma lem6931989 (n : nat) (m : nat) (p : nat) : (term5 m n p) = (term6 n m p).
Proof. exact (EQ_MP (@lem6931088 n m p) (@lem6931087 n m p)). Qed.
Lemma lem6931990 {A : Type'} (x : A) (c : nat) (t : A -> Prop) (f : A -> nat) : (term261 A c x t f) = (term239 A x c t f).
Proof. exact (@lem6931989 (f x) c (@nsum A t f)). Qed.
Lemma lem6931991 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : (term185 A c x t f) = (term239 A x c t f).
Proof. exact (TRANS (@lem6931987 A c f x t h1) (@lem6931990 A x c t f)). Qed.
Lemma lem6931992 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : ((term184 A x t c f) = (term185 A c x t f)) = ((term239 A x c t f) = (term239 A x c t f)).
Proof. exact (MK_COMB (@lem6931934 A c f x t h1) (@lem6931991 A c f x t h1)). Qed.
Lemma lem6931994 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6931995 (x : nat) : (x = x) = True.
Proof. exact (@lem6931994 nat x). Qed.
Lemma lem6931996 {A : Type'} (x : A) (c : nat) (t : A -> Prop) (f : A -> nat) : ((term239 A x c t f) = (term239 A x c t f)) = True.
Proof. exact (@lem6931995 (term239 A x c t f)). Qed.
Lemma lem6931997 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) (h1 : term180 A c f x t) : ((term184 A x t c f) = (term185 A c x t f)) = True.
Proof. exact (TRANS (@lem6931992 A c f x t h1) (@lem6931996 A x c t f)). Qed.
Lemma lem6931998 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) : term262 A c x t f.
Proof. exact (fun h0 : term180 A c f x t => @lem6931997 A c f x t h0). Qed.
Lemma lem6931999 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) : term263 A c f x t.
Proof. exact (@lem6931850 A c f x t True). Qed.
Lemma lem6932000 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) : (term187 A c x t f) = (term264 A c f x t).
Proof. exact (@lem6931999 A c f x t (@lem6931998 A c x t f)). Qed.
Lemma lem6932002 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6932003 {A : Type'} (c : nat) (f : A -> nat) (x : A) (t : A -> Prop) : (term264 A c f x t) = True.
Proof. exact (@lem6932002 (term180 A c f x t)). Qed.
Lemma lem6932004 {A : Type'} (c : nat) (x : A) (t : A -> Prop) (f : A -> nat) : (term187 A c x t f) = True.
Proof. exact (TRANS (@lem6932000 A c f x t) (@lem6932003 A c f x t)). Qed.
Lemma lem6932005 {A : Type'} (c : nat) (x : A) (f : A -> nat) : (term189 A c x f) = (term265 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6932004 A c x t f)). Qed.
Lemma lem6932006 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6932007 {A : Type'} (c : nat) (x : A) (f : A -> nat) : (term191 A c x f) = (term266 A).
Proof. exact (MK_COMB (@lem6932006 A) (@lem6932005 A c x f)). Qed.
Lemma lem6932009 {A : Type'} (t : Prop) : (term267 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6932010 {A : Type'} (t : Prop) : (term268 A t) = t.
Proof. exact (@lem6932009 (A -> Prop) t). Qed.
Lemma lem6932011 {A : Type'} : (term266 A) = True.
Proof. exact (@lem6932010 A True). Qed.
Lemma lem6932012 {A : Type'} (c : nat) (x : A) (f : A -> nat) : (term191 A c x f) = True.
Proof. exact (TRANS (@lem6932007 A c x f) (@lem6932011 A)). Qed.
Lemma lem6932013 {A : Type'} (c : nat) (f : A -> nat) : (term193 A c f) = (term269 A).
Proof. exact (fun_ext (fun x : A => @lem6932012 A c x f)). Qed.
Lemma lem6932014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6932015 {A : Type'} (c : nat) (f : A -> nat) : (term195 A c f) = (term270 A).
Proof. exact (MK_COMB (@lem6932014 A) (@lem6932013 A c f)). Qed.
Lemma lem6932017 {A : Type'} (t : Prop) : (term267 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6932018 {A : Type'} (t : Prop) : (term267 A t) = t.
Proof. exact (@lem6932017 A t). Qed.
Lemma lem6932019 {A : Type'} : (term270 A) = True.
Proof. exact (@lem6932018 A True). Qed.
Lemma lem6932020 {A : Type'} (c : nat) (f : A -> nat) : (term195 A c f) = True.
Proof. exact (TRANS (@lem6932015 A c f) (@lem6932019 A)). Qed.
Lemma lem6932021 {A : Type'} (c : nat) (f : A -> nat) : (term197 A c f) = (True /\ True).
Proof. exact (MK_COMB (@lem6931820 A c f) (@lem6932020 A c f)). Qed.
Lemma lem6932023 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6932024 : (True /\ True) = True.
Proof. exact (@lem6932023 True). Qed.
Lemma lem6932025 {A : Type'} (c : nat) (f : A -> nat) : (term197 A c f) = True.
Proof. exact (TRANS (@lem6932021 A c f) (@lem6932024)). Qed.
Lemma lem6932026 {A : Type'} (c : nat) (f : A -> nat) : True = (term197 A c f).
Proof. exact (SYM (@lem6932025 A c f)). Qed.
Lemma lem6932027 {A : Type'} (c : nat) (f : A -> nat) : term197 A c f.
Proof. exact (EQ_MP (@lem6932026 A c f) (@lem0)). Qed.
Lemma lem6932028 {A : Type'} (c : nat) (f : A -> nat) : term167 A c f.
Proof. exact (@lem6931793 A c f (@lem6932027 A c f)). Qed.
Lemma lem6932029 {A : Type'} (c : nat) (f : A -> nat) : term166 A c f.
Proof. exact (EQ_MP (@lem6931760 A c f) (@lem6932028 A c f)). Qed.
Lemma lem6932030 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) : term271 A c f s.
Proof. exact (@lem6932029 A c f (@support A nat Nat.add f s)). Qed.
Lemma lem6932031 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term271 A c f s) = (term272 A c s f).
Proof. exact (eq_refl (term271 A c f s)). Qed.
Lemma lem6932032 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : term272 A c s f.
Proof. exact (EQ_MP (@lem6932031 A c s f) (@lem6932030 A c f s)). Qed.
Lemma lem6932033 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : (term126 A s c f) = (term157 A c s f).
Proof. exact (@lem6932032 A c s f (@lem6931648 A f s h1)). Qed.
Lemma lem6932034 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : (term126 A s c f) = (term144 A c s f).
Proof. exact (EQ_MP (@lem6931692 A c s f) (@lem6932033 A c f s h1)). Qed.
Lemma lem6932035 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term147 A f s) : (@neutral nat Nat.add) = (term60 A c s f).
Proof. exact (EQ_MP (@lem6931679 A c f s h1) (@lem6931719 A c s f)). Qed.
Lemma lem6932036 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term147 A f s) : (term147 A f s) = ((@neutral nat Nat.add) = (term60 A c s f)).
Proof. exact (prop_ext (fun h2 : term147 A f s => @lem6932035 A c f s h1) (fun h2 : (@neutral nat Nat.add) = (term60 A c s f) => @lem6931664 A f s h1)). Qed.
Lemma lem6932037 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term147 A f s) : (@neutral nat Nat.add) = (term60 A c s f).
Proof. exact (EQ_MP (@lem6932036 A c f s h1) (@lem6931664 A f s h1)). Qed.
Lemma lem6932038 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : term131 A c s f.
Proof. exact (fun h0 : term147 A f s => @lem6932037 A c f s h0). Qed.
Lemma lem6932039 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : (term126 A s c f) = (term60 A c s f).
Proof. exact (EQ_MP (@lem6931663 A c f s h1) (@lem6932034 A c f s h1)). Qed.
Lemma lem6932040 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : (term127 A f s) = ((term126 A s c f) = (term60 A c s f)).
Proof. exact (prop_ext (fun h2 : term127 A f s => @lem6932039 A c f s h1) (fun h2 : (term126 A s c f) = (term60 A c s f) => @lem6931648 A f s h1)). Qed.
Lemma lem6932041 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : term127 A f s) : (term126 A s c f) = (term60 A c s f).
Proof. exact (EQ_MP (@lem6932040 A c f s h1) (@lem6931648 A f s h1)). Qed.
Lemma lem6932042 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : term135 A c s f.
Proof. exact (fun h0 : term127 A f s => @lem6932041 A c f s h0). Qed.
Lemma lem6932043 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : term138 A c s f.
Proof. exact (conj (@lem6932042 A c s f) (@lem6932038 A c s f)). Qed.
Lemma lem6932044 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term65 A s c f) = (term60 A c s f).
Proof. exact (EQ_MP (@lem6931647 A c s f) (@lem6932043 A c s f)). Qed.
Lemma lem6932045 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) (h1 : (term61 A c f s) = (@support A nat Nat.add f s)) : (term57 A s c f) = (term60 A c s f).
Proof. exact (EQ_MP (@lem6931398 A c f s h1) (@lem6932044 A c s f)). Qed.
Lemma lem6932046 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : ((term61 A c f s) = (@support A nat Nat.add f s)) = ((term57 A s c f) = (term60 A c s f)).
Proof. exact (prop_ext (fun h2 : (term61 A c f s) = (@support A nat Nat.add f s) => @lem6932045 A c f s h2) (fun h2 : (term57 A s c f) = (term60 A c s f) => @lem6931629 A f s c h1)). Qed.
Lemma lem6932047 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term57 A s c f) = (term60 A c s f).
Proof. exact (EQ_MP (@lem6932046 A s f c h1) (@lem6931629 A f s c h1)). Qed.
Lemma lem6932048 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term53 A s c f) = (term55 A c s f).
Proof. exact (EQ_MP (@lem6931384 A c s f) (@lem6932047 A s f c h1)). Qed.
Lemma lem6932050 {A : Type'} (s : A -> Prop) (f : A -> nat) (c : nat) (h1 : term37 c) : (term48 A s c f) = (term51 A c s f).
Proof. exact (EQ_MP (@lem6931368 A c s f) (@lem6932048 A s f c h1)). Qed.
Lemma lem6932051 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term48 A s c f) = (term51 A c s f).
Proof. exact (or_elim (@lem6931212 c) (fun h0 : c = (NUMERAL 0) => @lem6931290 A s f c h0) (fun h0 : term37 c => @lem6932050 A s f c h0)). Qed.
Lemma lem6932056 {A : Type'} (c : nat) (f : A -> nat) : term273 A c f.
Proof. exact (fun s : A -> Prop => @lem6932051 A c s f). Qed.
Lemma lem6932061 {A : Type'} (f : A -> nat) : term274 A f.
Proof. exact (fun c : nat => @lem6932056 A c f). Qed.
Lemma lem6932066 {A : Type'} : term275 A.
Proof. exact (fun f : A -> nat => @lem6932061 A f). Qed.
