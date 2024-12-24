Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_POWERSET_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_INJ_EQ_spec.
Require Import FINITE_POWERSET_spec.
Require Import FINITE_SUBSET_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import IN_SING_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1157_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1834_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem4603118 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4603119 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem4603118 A B h1 f). Qed.
Lemma lem4603120 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem4603121 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem4603120 A B f) (@lem4603119 A B f h1)). Qed.
Lemma lem4603122 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term3 A B f s.
Proof. exact (@lem4603121 A B f h1 s). Qed.
Lemma lem4603123 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem4603124 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (EQ_MP (@lem4603123 A B f s) (@lem4603122 A B f s h1)). Qed.
Lemma lem4603125 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term5 A B s f) : term5 A B s f.
Proof. exact (h1). Qed.
Lemma lem4603126 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term5 A B s f) (h2 : term0 A B) : (term6 A B f s) = (@FINITE A s).
Proof. exact (@lem4603124 A B f s h2 (@lem4603125 A B s f h1)). Qed.
Lemma lem4603127 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term5 A B s f) : term7 A B f s.
Proof. exact (fun h0 : term0 A B => @lem4603126 A B s f h1 h0). Qed.
Lemma lem4603128 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4603129 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term5 A B s f) (h2 : term0 A B) : (term6 A B f s) = (@FINITE A s).
Proof. exact (@lem4603127 A B s f h1 (@lem4603128 A B h2)). Qed.
Lemma lem4603130 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (fun h0 : term5 A B s f => @lem4603129 A B s f h0 h1). Qed.
Lemma lem4603131 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun s : A -> Prop => @lem4603130 A B f s h1). Qed.
Lemma lem4603132 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem4603131 A B f h1). Qed.
Lemma lem4603133 {A B : Type'} : term8 A B.
Proof. exact (fun h0 : term0 A B => @lem4603132 A B h0). Qed.
Lemma lem4603134 {A B : Type'} : term0 A B.
Proof. exact (@lem4603133 A B (@lem3618990 A B)). Qed.
Lemma lem4603135 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem4603134 A B f). Qed.
Lemma lem4603136 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem4603137 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem4603136 A B f) (@lem4603135 A B f)). Qed.
Lemma lem4603138 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem4603137 A B f s). Qed.
Lemma lem4603139 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem4603141 (a : Prop) (b : Prop) (h1 : term9 a b) : term9 a b.
Proof. exact (h1). Qed.
Lemma lem4603142 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem4603143 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term9 a b) : a -> b.
Proof. exact (@lem4603141 a b h2 (@lem4603142 a b h1)). Qed.
Lemma lem4603144 (a : Prop) (b : Prop) (h1 : a = b) : term10 a b.
Proof. exact (fun h0 : term9 a b => @lem4603143 a b h1 h0). Qed.
Lemma lem4603145 (a : Prop) (b : Prop) (h1 : term9 a b) : term9 a b.
Proof. exact (h1). Qed.
Lemma lem4603146 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term9 a b) : a -> b.
Proof. exact (@lem4603144 a b h1 (@lem4603145 a b h2)). Qed.
Lemma lem4603147 (a : Prop) (b : Prop) (h1 : term9 a b) : term9 a b.
Proof. exact (fun h0 : a = b => @lem4603146 a b h0 h1). Qed.
Lemma lem4603148 (a : Prop) (b : Prop) : term11 a b.
Proof. exact (fun h0 : term9 a b => @lem4603147 a b h0). Qed.
Lemma lem4603150 {A : Type'} (x : A) : term12 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4603151 {A : Type'} (x : A) : (term12 A x) = (term13 A x).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem4603152 {A : Type'} (x : A) : term13 A x.
Proof. exact (EQ_MP (@lem4603151 A x) (@lem4603150 A x)). Qed.
Lemma lem4603153 {A : Type'} (x : A) (y : A) : term14 A x y.
Proof. exact (@lem4603152 A x y). Qed.
Lemma lem4603154 {A : Type'} (x : A) (y : A) : (term14 A x y) = ((term15 A x y) = (x = y)).
Proof. exact (eq_refl (term14 A x y)). Qed.
Lemma lem4603180 {_83095 : Type'} : term16 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4603181 {_83095 : Type'} (p : _83095 -> Prop) : term17 _83095 p.
Proof. exact (@lem4603180 _83095 p). Qed.
Lemma lem4603182 {_83095 : Type'} (p : _83095 -> Prop) : (term17 _83095 p) = (term18 _83095 p).
Proof. exact (eq_refl (term17 _83095 p)). Qed.
Lemma lem4603183 {_83095 : Type'} (p : _83095 -> Prop) : term18 _83095 p.
Proof. exact (EQ_MP (@lem4603182 _83095 p) (@lem4603181 _83095 p)). Qed.
Lemma lem4603184 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term19 _83095 p x.
Proof. exact (@lem4603183 _83095 p x). Qed.
Lemma lem4603185 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term19 _83095 p x) = ((term20 _83095 x p) = (p x)).
Proof. exact (eq_refl (term19 _83095 p x)). Qed.
Lemma lem4603194 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term21 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4603195 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term21 _87967 _87968 P f) = (term22 _87967 _87968 P f).
Proof. exact (eq_refl (term21 _87967 _87968 P f)). Qed.
Lemma lem4603196 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term22 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4603195 _87967 _87968 P f) (@lem4603194 _87967 _87968 P f)). Qed.
Lemma lem4603197 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term23 _87967 _87968 P f s.
Proof. exact (@lem4603196 _87967 _87968 P f s). Qed.
Lemma lem4603198 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term23 _87967 _87968 P f s) = ((term24 _87967 _87968 f s P) = (term25 _87967 _87968 s P f)).
Proof. exact (eq_refl (term23 _87967 _87968 P f s)). Qed.
Lemma lem4603200 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4603201 {A : Type'} (s : A -> Prop) : (term26 A s) = (term27 A s).
Proof. exact (eq_refl (term26 A s)). Qed.
Lemma lem4603202 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (EQ_MP (@lem4603201 A s) (@lem4603200 A s)). Qed.
Lemma lem4603203 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term28 A s t.
Proof. exact (@lem4603202 A s t). Qed.
Lemma lem4603204 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = ((@SUBSET A s t) = (term29 A s t)).
Proof. exact (eq_refl (term28 A s t)). Qed.
Lemma lem4603215 (p : Prop) (q : Prop) (r : Prop) : (term30 p q r) = (term31 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4603216 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term32 A t s) = (term33 A t s).
Proof. exact (@lem4603215 (@FINITE A t) (@SUBSET A s t) (@FINITE A s)). Qed.
Lemma lem4603221 {A : Type'} (s : A -> Prop) : (term34 A s) = (term35 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4603216 A t s)). Qed.
Lemma lem4603222 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4603223 {A : Type'} (s : A -> Prop) : (term36 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem4603222 A) (@lem4603221 A s)). Qed.
Lemma lem4603228 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4603223 A s)). Qed.
Lemma lem4603229 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4603230 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (MK_COMB (@lem4603229 A) (@lem4603228 A)). Qed.
Lemma lem4603235 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem4603230 A) (@lem3599924 A)). Qed.
Lemma lem4603236 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem4603237 {A : Type'} (s : A -> Prop) (h1 : term41 A) : term42 A s.
Proof. exact (@lem4603236 A h1 s). Qed.
Lemma lem4603238 {A : Type'} (s : A -> Prop) : (term42 A s) = (term37 A s).
Proof. exact (eq_refl (term42 A s)). Qed.
Lemma lem4603239 {A : Type'} (s : A -> Prop) (h1 : term41 A) : term37 A s.
Proof. exact (EQ_MP (@lem4603238 A s) (@lem4603237 A s h1)). Qed.
Lemma lem4603240 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term41 A) : term43 A s t.
Proof. exact (@lem4603239 A s h1 t). Qed.
Lemma lem4603241 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term43 A s t) = (term33 A t s).
Proof. exact (eq_refl (term43 A s t)). Qed.
Lemma lem4603242 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term41 A) : term33 A t s.
Proof. exact (EQ_MP (@lem4603241 A t s) (@lem4603240 A s t h1)). Qed.
Lemma lem4603243 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem4603244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term41 A) (h2 : @FINITE A t) : term44 A t s.
Proof. exact (@lem4603242 A t s h1 (@lem4603243 A t h2)). Qed.
Lemma lem4603245 {A : Type'} (t : A -> Prop) (h1 : term41 A) (h2 : @FINITE A t) : term45 A t.
Proof. exact (fun s : A -> Prop => @lem4603244 A s t h1 h2). Qed.
Lemma lem4603246 {A : Type'} (t : A -> Prop) (h1 : term41 A) : term46 A t.
Proof. exact (fun h0 : @FINITE A t => @lem4603245 A t h1 h0). Qed.
Lemma lem4603247 {A : Type'} (h1 : term41 A) : term47 A.
Proof. exact (fun t : A -> Prop => @lem4603246 A t h1). Qed.
Lemma lem4603248 {A : Type'} : term48 A.
Proof. exact (fun h0 : term41 A => @lem4603247 A h0). Qed.
Lemma lem4603249 {A : Type'} : term47 A.
Proof. exact (@lem4603248 A (@lem4603235 A)). Qed.
Lemma lem4603250 {A : Type'} (t : A -> Prop) : term49 A t.
Proof. exact (@lem4603249 A t). Qed.
Lemma lem4603251 {A : Type'} (t : A -> Prop) : (term49 A t) = (term46 A t).
Proof. exact (eq_refl (term49 A t)). Qed.
Lemma lem4603253 {A : Type'} (s : A -> Prop) : term50 A s.
Proof. exact (@lem4603107 A s). Qed.
Lemma lem4603254 {A : Type'} (s : A -> Prop) : (term50 A s) = (term51 A s).
Proof. exact (eq_refl (term50 A s)). Qed.
Lemma lem4603255 {A : Type'} (s : A -> Prop) : term51 A s.
Proof. exact (EQ_MP (@lem4603254 A s) (@lem4603253 A s)). Qed.
Lemma lem4603256 {A : Type'} (s : A -> Prop) : (term51 A s) = ((term51 A s) = True).
Proof. exact (@lem7 (term51 A s)). Qed.
Lemma lem4603267 {A : Type'} (s : A -> Prop) : (term51 A s) = True.
Proof. exact (EQ_MP (@lem4603256 A s) (@lem4603255 A s)). Qed.
Lemma lem4603268 {A : Type'} (s : A -> Prop) : (term51 A s) = True.
Proof. exact (@lem4603267 A s). Qed.
Lemma lem4603269 {A : Type'} (s : A -> Prop) : True = (term51 A s).
Proof. exact (SYM (@lem4603268 A s)). Qed.
Lemma lem4603270 {A : Type'} (s : A -> Prop) : term51 A s.
Proof. exact (EQ_MP (@lem4603269 A s) (@lem0)). Qed.
Lemma lem4603271 {A : Type'} (s : A -> Prop) (h1 : term52 A s) : term52 A s.
Proof. exact (h1). Qed.
Lemma lem4603272 {A : Type'} (s : A -> Prop) (h1 : term53 A s) : term53 A s.
Proof. exact (h1). Qed.
Lemma lem4603274 {A : Type'} (t : A -> Prop) : term46 A t.
Proof. exact (EQ_MP (@lem4603251 A t) (@lem4603250 A t)). Qed.
Lemma lem4603275 {A : Type'} (t : type686 A) : term54 A t.
Proof. exact (@lem4603274 (A -> Prop) t). Qed.
Lemma lem4603276 {A : Type'} (s : A -> Prop) : term55 A s.
Proof. exact (@lem4603275 A (term56 A s)). Qed.
Lemma lem4603277 {A : Type'} (s : A -> Prop) (h1 : term52 A s) : term57 A s.
Proof. exact (@lem4603276 A s (@lem4603271 A s h1)). Qed.
Lemma lem4603278 {A : Type'} (s : A -> Prop) (h1 : term57 A s) : term57 A s.
Proof. exact (h1). Qed.
Lemma lem4603279 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term57 A s') : term58 A s' s.
Proof. exact (@lem4603278 A s' h1 s). Qed.
Lemma lem4603280 {A : Type'} (s : A -> Prop) (s' : type686 A) : (term58 A s s') = (term59 A s s').
Proof. exact (eq_refl (term58 A s s')). Qed.
Lemma lem4603281 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term57 A s') : term59 A s' s.
Proof. exact (EQ_MP (@lem4603280 A s' s) (@lem4603279 A s s' h1)). Qed.
Lemma lem4603282 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term60 A s s') : term60 A s s'.
Proof. exact (h1). Qed.
Lemma lem4603283 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term57 A s') (h2 : term60 A s s') : @FINITE (A -> Prop) s.
Proof. exact (@lem4603281 A s s' h1 (@lem4603282 A s s' h2)). Qed.
Lemma lem4603284 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term60 A s s') : term61 A s' s.
Proof. exact (fun h0 : term57 A s' => @lem4603283 A s s' h0 h1). Qed.
Lemma lem4603285 {A : Type'} (s : A -> Prop) (h1 : term57 A s) : term57 A s.
Proof. exact (h1). Qed.
Lemma lem4603286 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term57 A s') (h2 : term60 A s s') : @FINITE (A -> Prop) s.
Proof. exact (@lem4603284 A s s' h2 (@lem4603285 A s' h1)). Qed.
Lemma lem4603287 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term57 A s') : term59 A s' s.
Proof. exact (fun h0 : term60 A s s' => @lem4603286 A s s' h1 h0). Qed.
Lemma lem4603288 {A : Type'} (s : A -> Prop) (h1 : term57 A s) : term57 A s.
Proof. exact (fun s' : type686 A => @lem4603287 A s' s h1). Qed.
Lemma lem4603289 {A : Type'} (s : A -> Prop) : term62 A s.
Proof. exact (fun h0 : term57 A s => @lem4603288 A s h0). Qed.
Lemma lem4603290 {A : Type'} (s : A -> Prop) (h1 : term52 A s) : term57 A s.
Proof. exact (@lem4603289 A s (@lem4603277 A s h1)). Qed.
Lemma lem4603291 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term52 A s') : term58 A s' s.
Proof. exact (@lem4603290 A s' h1 s). Qed.
Lemma lem4603292 {A : Type'} (s : A -> Prop) (s' : type686 A) : (term58 A s s') = (term59 A s s').
Proof. exact (eq_refl (term58 A s s')). Qed.
Lemma lem4603295 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term52 A s') : term59 A s' s.
Proof. exact (EQ_MP (@lem4603292 A s' s) (@lem4603291 A s s' h1)). Qed.
Lemma lem4603296 {A : Type'} (s : type686 A) (s' : A -> Prop) (h1 : term52 A s') : term59 A s' s.
Proof. exact (@lem4603295 A s s' h1). Qed.
Lemma lem4603297 {A : Type'} (s : A -> Prop) (h1 : term52 A s) : term63 A s.
Proof. exact (@lem4603296 A (term64 A s) s h1). Qed.
Lemma lem4603299 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term29 A s t).
Proof. exact (EQ_MP (@lem4603204 A s t) (@lem4603203 A s t)). Qed.
Lemma lem4603300 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term65 A s t).
Proof. exact (@lem4603299 (A -> Prop) s t). Qed.
Lemma lem4603301 {A : Type'} (s : A -> Prop) : (term66 A s) = (term67 A s).
Proof. exact (@lem4603300 A (term64 A s) (term56 A s)). Qed.
Lemma lem4603303 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term24 _87967 _87968 f s P) = (term25 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4603198 _87967 _87968 s P f) (@lem4603197 _87967 _87968 P f s)). Qed.
Lemma lem4603304 {A : Type'} (s : A -> Prop) (P : type686 A) (f : type1402 A) : (term68 A f s P) = (term69 A s P f).
Proof. exact (@lem4603303 (A -> Prop) A s P f). Qed.
Lemma lem4603305 {A : Type'} (s : A -> Prop) : (term70 A s) = (term71 A s).
Proof. exact (@lem4603304 A s (term72 A s) (term73 A)). Qed.
Lemma lem4603306 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term74 A s x) = (term75 A x s).
Proof. exact (eq_refl (term74 A s x)). Qed.
Lemma lem4603307 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term76 A x s) = (term76 A x s).
Proof. exact (eq_refl (term76 A x s)). Qed.
Lemma lem4603308 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term77 A s x) = (term78 A x s).
Proof. exact (MK_COMB (@lem4603307 A x s) (@lem4603306 A x s)). Qed.
Lemma lem4603309 {A : Type'} (s : A -> Prop) : (term79 A s) = (term80 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4603308 A x s)). Qed.
Lemma lem4603310 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4603311 {A : Type'} (s : A -> Prop) : (term70 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem4603310 A) (@lem4603309 A s)). Qed.
Lemma lem4603312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4603313 {A : Type'} (s : A -> Prop) : (term81 A s) = (term82 A s).
Proof. exact (MK_COMB (@lem4603312) (@lem4603311 A s)). Qed.
Lemma lem4603314 {A : Type'} (x : A) (s : A -> Prop) : (term83 A s x) = (term84 A x s).
Proof. exact (eq_refl (term83 A s x)). Qed.
Lemma lem4603315 {A : Type'} (x : A) (s : A -> Prop) : (term85 A x s) = (term85 A x s).
Proof. exact (eq_refl (term85 A x s)). Qed.
Lemma lem4603316 {A : Type'} (x : A) (s : A -> Prop) : (term86 A s x) = (term87 A x s).
Proof. exact (MK_COMB (@lem4603315 A x s) (@lem4603314 A x s)). Qed.
Lemma lem4603317 {A : Type'} (s : A -> Prop) : (term88 A s) = (term89 A s).
Proof. exact (fun_ext (fun x : A => @lem4603316 A x s)). Qed.
Lemma lem4603318 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603319 {A : Type'} (s : A -> Prop) : (term71 A s) = (term90 A s).
Proof. exact (MK_COMB (@lem4603318 A) (@lem4603317 A s)). Qed.
Lemma lem4603320 {A : Type'} (s : A -> Prop) : ((term70 A s) = (term71 A s)) = ((term67 A s) = (term90 A s)).
Proof. exact (MK_COMB (@lem4603313 A s) (@lem4603319 A s)). Qed.
Lemma lem4603321 {A : Type'} (s : A -> Prop) : (term67 A s) = (term90 A s).
Proof. exact (EQ_MP (@lem4603320 A s) (@lem4603305 A s)). Qed.
Lemma lem4603329 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4603330 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem4603329 p q p' q'). Qed.
Lemma lem4603331 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem4603330 p q p'). Qed.
Lemma lem4603332 {A : Type'} (x : A) (s : A -> Prop) : term94 A x s.
Proof. exact (@lem4603331 (@IN A x s) (term84 A x s)). Qed.
Lemma lem4603333 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term95 A x s p'.
Proof. exact (@lem4603332 A x s p'). Qed.
Lemma lem4603334 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : (term95 A x s p') = (term96 A x s p').
Proof. exact (eq_refl (term95 A x s p')). Qed.
Lemma lem4603335 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term96 A x s p'.
Proof. exact (EQ_MP (@lem4603334 A x s p') (@lem4603333 A x s p')). Qed.
Lemma lem4603336 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term97 A x s p' q'.
Proof. exact (@lem4603335 A x s p' q'). Qed.
Lemma lem4603337 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term97 A x s p' q') = (term98 A x s p' q').
Proof. exact (eq_refl (term97 A x s p' q')). Qed.
Lemma lem4603338 {A : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term98 A x s p' q'.
Proof. exact (EQ_MP (@lem4603337 A x s p' q') (@lem4603336 A x s p' q')). Qed.
Lemma lem4603339 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4603340 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term99 A x s q'.
Proof. exact (@lem4603338 A x s (@IN A x s) q'). Qed.
Lemma lem4603341 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term100 A x s q'.
Proof. exact (@lem4603340 A x s q' (@lem4603339 A x s)). Qed.
Lemma lem4603342 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4603343 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4603346 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4603185 _83095 p x) (@lem4603184 _83095 p x)). Qed.
Lemma lem4603347 {A : Type'} (p : type686 A) (x : A -> Prop) : (term101 A x p) = (p x).
Proof. exact (@lem4603346 (A -> Prop) p x). Qed.
Lemma lem4603348 {A : Type'} (s : A -> Prop) (x : A) : (term102 A x s) = (term103 A s x).
Proof. exact (@lem4603347 A (term104 A s) (term105 A x)). Qed.
Lemma lem4603349 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term106 A s t) = (@SUBSET A t s).
Proof. exact (eq_refl (term106 A s t)). Qed.
Lemma lem4603350 {A : Type'} (GEN_PVAR_156 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_156) = (@SETSPEC (A -> Prop) GEN_PVAR_156).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_156)). Qed.
Lemma lem4603351 {A : Type'} (GEN_PVAR_156 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term107 A GEN_PVAR_156 s t) = (term108 A GEN_PVAR_156 t s).
Proof. exact (MK_COMB (@lem4603350 A GEN_PVAR_156) (@lem4603349 A t s)). Qed.
Lemma lem4603352 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4603353 {A : Type'} (GEN_PVAR_156 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term109 A GEN_PVAR_156 s t) = (term110 A GEN_PVAR_156 s t).
Proof. exact (MK_COMB (@lem4603351 A GEN_PVAR_156 t s) (@lem4603352 A t)). Qed.
Lemma lem4603354 {A : Type'} (GEN_PVAR_156 : A -> Prop) (s : A -> Prop) : (term111 A GEN_PVAR_156 s) = (term112 A GEN_PVAR_156 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4603353 A GEN_PVAR_156 s t)). Qed.
Lemma lem4603355 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4603356 {A : Type'} (GEN_PVAR_156 : A -> Prop) (s : A -> Prop) : (term113 A GEN_PVAR_156 s) = (term114 A GEN_PVAR_156 s).
Proof. exact (MK_COMB (@lem4603355 A) (@lem4603354 A GEN_PVAR_156 s)). Qed.
Lemma lem4603357 {A : Type'} (s : A -> Prop) : (term115 A s) = (term116 A s).
Proof. exact (fun_ext (fun GEN_PVAR_156 : A -> Prop => @lem4603356 A GEN_PVAR_156 s)). Qed.
Lemma lem4603358 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4603359 {A : Type'} (s : A -> Prop) : (term117 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem4603358 A) (@lem4603357 A s)). Qed.
Lemma lem4603360 {A : Type'} (x : A) : (term118 A x) = (term118 A x).
Proof. exact (eq_refl (term118 A x)). Qed.
Lemma lem4603361 {A : Type'} (x : A) (s : A -> Prop) : (term102 A x s) = (term84 A x s).
Proof. exact (MK_COMB (@lem4603360 A x) (@lem4603359 A s)). Qed.
Lemma lem4603362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4603363 {A : Type'} (x : A) (s : A -> Prop) : (term119 A x s) = (term120 A x s).
Proof. exact (MK_COMB (@lem4603362) (@lem4603361 A x s)). Qed.
Lemma lem4603364 {A : Type'} (x : A) (s : A -> Prop) : (term103 A s x) = (term121 A x s).
Proof. exact (eq_refl (term103 A s x)). Qed.
Lemma lem4603365 {A : Type'} (x : A) (s : A -> Prop) : ((term102 A x s) = (term103 A s x)) = ((term84 A x s) = (term121 A x s)).
Proof. exact (MK_COMB (@lem4603363 A x s) (@lem4603364 A x s)). Qed.
Lemma lem4603366 {A : Type'} (x : A) (s : A -> Prop) : (term84 A x s) = (term121 A x s).
Proof. exact (EQ_MP (@lem4603365 A x s) (@lem4603348 A s x)). Qed.
Lemma lem4603368 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term29 A s t).
Proof. exact (EQ_MP (@lem4603204 A s t) (@lem4603203 A s t)). Qed.
Lemma lem4603369 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term29 A s t).
Proof. exact (@lem4603368 A s t). Qed.
Lemma lem4603370 {A : Type'} (x : A) (s : A -> Prop) : (term121 A x s) = (term122 A x s).
Proof. exact (@lem4603369 A (term105 A x) s). Qed.
Lemma lem4603378 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term91 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4603379 (p : Prop) (q : Prop) (p' : Prop) : term92 p q p'.
Proof. exact (fun q' : Prop => @lem4603378 p q p' q'). Qed.
Lemma lem4603380 (p : Prop) (q : Prop) : term93 p q.
Proof. exact (fun p' : Prop => @lem4603379 p q p'). Qed.
Lemma lem4603381 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : term123 A x x' s.
Proof. exact (@lem4603380 (term124 A x' x) (@IN A x' s)). Qed.
Lemma lem4603382 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (p' : Prop) : term125 A x x' s p'.
Proof. exact (@lem4603381 A x x' s p'). Qed.
Lemma lem4603383 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (p' : Prop) : (term125 A x x' s p') = (term126 A x x' s p').
Proof. exact (eq_refl (term125 A x x' s p')). Qed.
Lemma lem4603384 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (p' : Prop) : term126 A x x' s p'.
Proof. exact (EQ_MP (@lem4603383 A x x' s p') (@lem4603382 A x x' s p')). Qed.
Lemma lem4603385 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term127 A x x' s p' q'.
Proof. exact (@lem4603384 A x x' s p' q'). Qed.
Lemma lem4603386 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term127 A x x' s p' q') = (term128 A x x' s p' q').
Proof. exact (eq_refl (term127 A x x' s p' q')). Qed.
Lemma lem4603387 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term128 A x x' s p' q'.
Proof. exact (EQ_MP (@lem4603386 A x x' s p' q') (@lem4603385 A x x' s p' q')). Qed.
Lemma lem4603389 {A B : Type'} (f : A -> B) (y : A) : (term129 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4603390 {A : Type'} (f : type1402 A) (y : A) : (term130 A f y) = (f y).
Proof. exact (@lem4603389 A (A -> Prop) f y). Qed.
Lemma lem4603391 {A : Type'} (x : A) : (term131 A x) = (term105 A x).
Proof. exact (@lem4603390 A (term73 A) x). Qed.
Lemma lem4603392 {A : Type'} (x : A) : (term105 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term105 A x)). Qed.
Lemma lem4603393 {A : Type'} : (term132 A) = (term73 A).
Proof. exact (fun_ext (fun x : A => @lem4603392 A x)). Qed.
Lemma lem4603394 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4603395 {A : Type'} (x : A) : (term131 A x) = (term105 A x).
Proof. exact (MK_COMB (@lem4603393 A) (@lem4603394 A x)). Qed.
Lemma lem4603396 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4603397 {A : Type'} (x : A) : (term133 A x) = (term134 A x).
Proof. exact (MK_COMB (@lem4603396 A) (@lem4603395 A x)). Qed.
Lemma lem4603398 {A : Type'} (x : A) : (term105 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term105 A x)). Qed.
Lemma lem4603399 {A : Type'} (x : A) : ((term131 A x) = (term105 A x)) = ((term105 A x) = (@INSERT A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem4603397 A x) (@lem4603398 A x)). Qed.
Lemma lem4603400 {A : Type'} (x : A) : (term105 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (EQ_MP (@lem4603399 A x) (@lem4603391 A x)). Qed.
Lemma lem4603401 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem4603402 {A : Type'} (x' : A) (x : A) : (term124 A x' x) = (term15 A x' x).
Proof. exact (MK_COMB (@lem4603401 A x') (@lem4603400 A x)). Qed.
Lemma lem4603404 {A : Type'} (x : A) (y : A) : (term15 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4603154 A x y) (@lem4603153 A x y)). Qed.
Lemma lem4603405 {A : Type'} (x : A) (y : A) : (term15 A x y) = (x = y).
Proof. exact (@lem4603404 A x y). Qed.
Lemma lem4603406 {A : Type'} (x' : A) (x : A) : (term15 A x' x) = (x' = x).
Proof. exact (@lem4603405 A x' x). Qed.
Lemma lem4603409 {A : Type'} (x' : A) (x : A) : (term124 A x' x) = (x' = x).
Proof. exact (TRANS (@lem4603402 A x' x) (@lem4603406 A x' x)). Qed.
Lemma lem4603410 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (q' : Prop) : term135 A s x' x q'.
Proof. exact (@lem4603387 A x x' s (x' = x) q'). Qed.
Lemma lem4603411 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (q' : Prop) : term136 A s x' x q'.
Proof. exact (@lem4603410 A s x' x q' (@lem4603409 A x' x)). Qed.
Lemma lem4603414 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem4603415 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4603416 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (@IN A x') = (@IN A x).
Proof. exact (MK_COMB (@lem4603415 A) (@lem4603414 A x' x h1)). Qed.
Lemma lem4603417 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4603418 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (@IN A x' s) = (@IN A x s).
Proof. exact (MK_COMB (@lem4603416 A x' x h1) (@lem4603417 A s)). Qed.
Lemma lem4603420 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4603343 A x s) (@lem4603342 A x s h1)). Qed.
Lemma lem4603421 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : x' = x) (h2 : @IN A x s) : (@IN A x' s) = True.
Proof. exact (TRANS (@lem4603418 A s x' x h1) (@lem4603420 A x s h2)). Qed.
Lemma lem4603422 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term137 A x x' s.
Proof. exact (fun h0 : x' = x => @lem4603421 A x' x s h0 h1). Qed.
Lemma lem4603423 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : term138 A s x' x.
Proof. exact (@lem4603411 A s x' x True). Qed.
Lemma lem4603424 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term139 A x x' s) = (term140 A x' x).
Proof. exact (@lem4603423 A s x' x (@lem4603422 A x' x s h1)). Qed.
Lemma lem4603428 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4603429 {A : Type'} (x' : A) (x : A) : (term140 A x' x) = True.
Proof. exact (@lem4603428 (x' = x)). Qed.
Lemma lem4603430 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term139 A x x' s) = True.
Proof. exact (TRANS (@lem4603424 A x' x s h1) (@lem4603429 A x' x)). Qed.
Lemma lem4603431 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term141 A x s) = (term142 A).
Proof. exact (fun_ext (fun x' : A => @lem4603430 A x' x s h1)). Qed.
Lemma lem4603432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603433 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term122 A x s) = (term143 A).
Proof. exact (MK_COMB (@lem4603432 A) (@lem4603431 A x s h1)). Qed.
Lemma lem4603435 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4603436 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (@lem4603435 A t). Qed.
Lemma lem4603437 {A : Type'} : (term143 A) = True.
Proof. exact (@lem4603436 A True). Qed.
Lemma lem4603438 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term122 A x s) = True.
Proof. exact (TRANS (@lem4603433 A x s h1) (@lem4603437 A)). Qed.
Lemma lem4603439 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term121 A x s) = True.
Proof. exact (TRANS (@lem4603370 A x s) (@lem4603438 A x s h1)). Qed.
Lemma lem4603440 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term84 A x s) = True.
Proof. exact (TRANS (@lem4603366 A x s) (@lem4603439 A x s h1)). Qed.
Lemma lem4603441 {A : Type'} (x : A) (s : A -> Prop) : term145 A x s.
Proof. exact (fun h0 : @IN A x s => @lem4603440 A x s h0). Qed.
Lemma lem4603442 {A : Type'} (x : A) (s : A -> Prop) : term146 A x s.
Proof. exact (@lem4603341 A x s True). Qed.
Lemma lem4603443 {A : Type'} (x : A) (s : A -> Prop) : (term87 A x s) = (term147 A x s).
Proof. exact (@lem4603442 A x s (@lem4603441 A x s)). Qed.
Lemma lem4603445 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4603446 {A : Type'} (x : A) (s : A -> Prop) : (term147 A x s) = True.
Proof. exact (@lem4603445 (@IN A x s)). Qed.
Lemma lem4603447 {A : Type'} (x : A) (s : A -> Prop) : (term87 A x s) = True.
Proof. exact (TRANS (@lem4603443 A x s) (@lem4603446 A x s)). Qed.
Lemma lem4603448 {A : Type'} (s : A -> Prop) : (term89 A s) = (term142 A).
Proof. exact (fun_ext (fun x : A => @lem4603447 A x s)). Qed.
Lemma lem4603449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603450 {A : Type'} (s : A -> Prop) : (term90 A s) = (term143 A).
Proof. exact (MK_COMB (@lem4603449 A) (@lem4603448 A s)). Qed.
Lemma lem4603452 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4603453 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (@lem4603452 A t). Qed.
Lemma lem4603454 {A : Type'} : (term143 A) = True.
Proof. exact (@lem4603453 A True). Qed.
Lemma lem4603455 {A : Type'} (s : A -> Prop) : (term90 A s) = True.
Proof. exact (TRANS (@lem4603450 A s) (@lem4603454 A)). Qed.
Lemma lem4603456 {A : Type'} (s : A -> Prop) : (term67 A s) = True.
Proof. exact (TRANS (@lem4603321 A s) (@lem4603455 A s)). Qed.
Lemma lem4603457 {A : Type'} (s : A -> Prop) : (term66 A s) = True.
Proof. exact (TRANS (@lem4603301 A s) (@lem4603456 A s)). Qed.
Lemma lem4603458 {A : Type'} (s : A -> Prop) : True = (term66 A s).
Proof. exact (SYM (@lem4603457 A s)). Qed.
Lemma lem4603459 {A : Type'} (s : A -> Prop) : term66 A s.
Proof. exact (EQ_MP (@lem4603458 A s) (@lem0)). Qed.
Lemma lem4603460 {A : Type'} (s : A -> Prop) (h1 : term52 A s) : term53 A s.
Proof. exact (@lem4603297 A s h1 (@lem4603459 A s)). Qed.
Lemma lem4603462 (a : Prop) (b : Prop) : term9 a b.
Proof. exact (@lem4603148 a b (@lem1157 a b)). Qed.
Lemma lem4603463 {A : Type'} (s : A -> Prop) : term148 A s.
Proof. exact (@lem4603462 (term53 A s) (@FINITE A s)). Qed.
Lemma lem4603465 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem4603139 A B f s) (@lem4603138 A B f s)). Qed.
Lemma lem4603466 {A : Type'} (f : type1402 A) (s : A -> Prop) : term149 A f s.
Proof. exact (@lem4603465 A (A -> Prop) f s). Qed.
Lemma lem4603467 {A : Type'} (s : A -> Prop) : term150 A s.
Proof. exact (@lem4603466 A (term73 A) s). Qed.
Lemma lem4603485 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term151 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4603486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term151 A s t).
Proof. exact (@lem4603485 A s t). Qed.
Lemma lem4603487 {A : Type'} (x : A) (y : A) : ((term105 A x) = (term105 A y)) = (term152 A x y).
Proof. exact (@lem4603486 A (term105 A x) (term105 A y)). Qed.
Lemma lem4603497 {A B : Type'} (f : A -> B) (y : A) : (term129 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4603498 {A : Type'} (f : type1402 A) (y : A) : (term130 A f y) = (f y).
Proof. exact (@lem4603497 A (A -> Prop) f y). Qed.
Lemma lem4603499 {A : Type'} (x : A) : (term131 A x) = (term105 A x).
Proof. exact (@lem4603498 A (term73 A) x). Qed.
Lemma lem4603500 {A : Type'} (x : A) : (term105 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term105 A x)). Qed.
Lemma lem4603501 {A : Type'} : (term132 A) = (term73 A).
Proof. exact (fun_ext (fun x : A => @lem4603500 A x)). Qed.
Lemma lem4603502 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4603503 {A : Type'} (x : A) : (term131 A x) = (term105 A x).
Proof. exact (MK_COMB (@lem4603501 A) (@lem4603502 A x)). Qed.
Lemma lem4603504 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4603505 {A : Type'} (x : A) : (term133 A x) = (term134 A x).
Proof. exact (MK_COMB (@lem4603504 A) (@lem4603503 A x)). Qed.
Lemma lem4603506 {A : Type'} (x : A) : (term105 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term105 A x)). Qed.
Lemma lem4603507 {A : Type'} (x : A) : ((term131 A x) = (term105 A x)) = ((term105 A x) = (@INSERT A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem4603505 A x) (@lem4603506 A x)). Qed.
Lemma lem4603508 {A : Type'} (x : A) : (term105 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (EQ_MP (@lem4603507 A x) (@lem4603499 A x)). Qed.
Lemma lem4603509 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem4603510 {A : Type'} (x' : A) (x : A) : (term124 A x' x) = (term15 A x' x).
Proof. exact (MK_COMB (@lem4603509 A x') (@lem4603508 A x)). Qed.
Lemma lem4603511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4603512 {A : Type'} (x' : A) (x : A) : (term153 A x' x) = (term154 A x' x).
Proof. exact (MK_COMB (@lem4603511) (@lem4603510 A x' x)). Qed.
Lemma lem4603514 {A B : Type'} (f : A -> B) (y : A) : (term129 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4603515 {A : Type'} (f : type1402 A) (y : A) : (term130 A f y) = (f y).
Proof. exact (@lem4603514 A (A -> Prop) f y). Qed.
Lemma lem4603516 {A : Type'} (y : A) : (term131 A y) = (term105 A y).
Proof. exact (@lem4603515 A (term73 A) y). Qed.
Lemma lem4603517 {A : Type'} (x : A) : (term105 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term105 A x)). Qed.
Lemma lem4603518 {A : Type'} : (term132 A) = (term73 A).
Proof. exact (fun_ext (fun x : A => @lem4603517 A x)). Qed.
Lemma lem4603519 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4603520 {A : Type'} (y : A) : (term131 A y) = (term105 A y).
Proof. exact (MK_COMB (@lem4603518 A) (@lem4603519 A y)). Qed.
Lemma lem4603521 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4603522 {A : Type'} (y : A) : (term133 A y) = (term134 A y).
Proof. exact (MK_COMB (@lem4603521 A) (@lem4603520 A y)). Qed.
Lemma lem4603523 {A : Type'} (y : A) : (term105 A y) = (@INSERT A y (@EMPTY A)).
Proof. exact (eq_refl (term105 A y)). Qed.
Lemma lem4603524 {A : Type'} (y : A) : ((term131 A y) = (term105 A y)) = ((term105 A y) = (@INSERT A y (@EMPTY A))).
Proof. exact (MK_COMB (@lem4603522 A y) (@lem4603523 A y)). Qed.
Lemma lem4603525 {A : Type'} (y : A) : (term105 A y) = (@INSERT A y (@EMPTY A)).
Proof. exact (EQ_MP (@lem4603524 A y) (@lem4603516 A y)). Qed.
Lemma lem4603526 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem4603527 {A : Type'} (x' : A) (y : A) : (term124 A x' y) = (term15 A x' y).
Proof. exact (MK_COMB (@lem4603526 A x') (@lem4603525 A y)). Qed.
Lemma lem4603528 {A : Type'} (x : A) (x' : A) (y : A) : ((term124 A x' x) = (term124 A x' y)) = ((term15 A x' x) = (term15 A x' y)).
Proof. exact (MK_COMB (@lem4603512 A x' x) (@lem4603527 A x' y)). Qed.
Lemma lem4603533 {A : Type'} (x : A) (y : A) : (term155 A x y) = (term156 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4603528 A x x' y)). Qed.
Lemma lem4603534 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603535 {A : Type'} (x : A) (y : A) : (term152 A x y) = (term157 A x y).
Proof. exact (MK_COMB (@lem4603534 A) (@lem4603533 A x y)). Qed.
Lemma lem4603540 {A : Type'} (x : A) (y : A) : ((term105 A x) = (term105 A y)) = (term157 A x y).
Proof. exact (TRANS (@lem4603487 A x y) (@lem4603535 A x y)). Qed.
Lemma lem4603541 {A : Type'} (y : A) (s : A -> Prop) : (term158 A y s) = (term158 A y s).
Proof. exact (eq_refl (term158 A y s)). Qed.
Lemma lem4603542 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term159 A s x y) = (term160 A s x y).
Proof. exact (MK_COMB (@lem4603541 A y s) (@lem4603540 A x y)). Qed.
Lemma lem4603545 {A : Type'} (x : A) (s : A -> Prop) : (term158 A x s) = (term158 A x s).
Proof. exact (eq_refl (term158 A x s)). Qed.
Lemma lem4603546 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term161 A s x y) = (term162 A s x y).
Proof. exact (MK_COMB (@lem4603545 A x s) (@lem4603542 A s x y)). Qed.
Lemma lem4603549 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4603550 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term163 A s x y) = (term164 A s x y).
Proof. exact (MK_COMB (@lem4603549) (@lem4603546 A s x y)). Qed.
Lemma lem4603555 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4603556 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term165 A s x y) = (term166 A s x y).
Proof. exact (MK_COMB (@lem4603550 A s x y) (@lem4603555 A x y)). Qed.
Lemma lem4603559 {A : Type'} (s : A -> Prop) (x : A) : (term167 A s x) = (term168 A s x).
Proof. exact (fun_ext (fun y : A => @lem4603556 A s x y)). Qed.
Lemma lem4603560 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603561 {A : Type'} (s : A -> Prop) (x : A) : (term169 A s x) = (term170 A s x).
Proof. exact (MK_COMB (@lem4603560 A) (@lem4603559 A s x)). Qed.
Lemma lem4603566 {A : Type'} (s : A -> Prop) : (term171 A s) = (term172 A s).
Proof. exact (fun_ext (fun x : A => @lem4603561 A s x)). Qed.
Lemma lem4603567 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603568 {A : Type'} (s : A -> Prop) : (term173 A s) = (term174 A s).
Proof. exact (MK_COMB (@lem4603567 A) (@lem4603566 A s)). Qed.
Lemma lem4603573 {A : Type'} (s : A -> Prop) : (term174 A s) = (term173 A s).
Proof. exact (SYM (@lem4603568 A s)). Qed.
Lemma lem4603587 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4603588 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4603587 A P x). Qed.
Lemma lem4603589 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4603588 A s x). Qed.
Lemma lem4603590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4603591 {A : Type'} (s : A -> Prop) (x : A) : (term158 A x s) = (term175 A s x).
Proof. exact (MK_COMB (@lem4603590) (@lem4603589 A s x)). Qed.
Lemma lem4603595 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4603596 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4603595 A P x). Qed.
Lemma lem4603597 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4603596 A s y). Qed.
Lemma lem4603598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4603599 {A : Type'} (s : A -> Prop) (y : A) : (term158 A y s) = (term175 A s y).
Proof. exact (MK_COMB (@lem4603598) (@lem4603597 A s y)). Qed.
Lemma lem4603607 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term176 A x y s) = (term177 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4603608 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term176 A x y s) = (term177 A y x s).
Proof. exact (@lem4603607 A y x s). Qed.
Lemma lem4603609 {A : Type'} (x : A) (x' : A) : (term15 A x' x) = (term178 A x x').
Proof. exact (@lem4603608 A x x' (@EMPTY A)). Qed.
Lemma lem4603615 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4603616 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4603615 A x). Qed.
Lemma lem4603617 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem4603616 A x'). Qed.
Lemma lem4603618 {A : Type'} (x' : A) (x : A) : (term179 A x' x) = (term179 A x' x).
Proof. exact (eq_refl (term179 A x' x)). Qed.
Lemma lem4603619 {A : Type'} (x' : A) (x : A) : (term178 A x x') = (term180 A x' x).
Proof. exact (MK_COMB (@lem4603618 A x' x) (@lem4603617 A x')). Qed.
Lemma lem4603621 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4603622 {A : Type'} (x' : A) (x : A) : (term180 A x' x) = (x' = x).
Proof. exact (@lem4603621 (x' = x)). Qed.
Lemma lem4603625 {A : Type'} (x' : A) (x : A) : (term178 A x x') = (x' = x).
Proof. exact (TRANS (@lem4603619 A x' x) (@lem4603622 A x' x)). Qed.
Lemma lem4603626 {A : Type'} (x' : A) (x : A) : (term15 A x' x) = (x' = x).
Proof. exact (TRANS (@lem4603609 A x x') (@lem4603625 A x' x)). Qed.
Lemma lem4603627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4603628 {A : Type'} (x' : A) (x : A) : (term154 A x' x) = (term181 A x' x).
Proof. exact (MK_COMB (@lem4603627) (@lem4603626 A x' x)). Qed.
Lemma lem4603630 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term176 A x y s) = (term177 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4603631 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term176 A x y s) = (term177 A y x s).
Proof. exact (@lem4603630 A y x s). Qed.
Lemma lem4603632 {A : Type'} (y : A) (x' : A) : (term15 A x' y) = (term178 A y x').
Proof. exact (@lem4603631 A y x' (@EMPTY A)). Qed.
Lemma lem4603638 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4603639 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4603638 A x). Qed.
Lemma lem4603640 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem4603639 A x'). Qed.
Lemma lem4603641 {A : Type'} (x' : A) (y : A) : (term179 A x' y) = (term179 A x' y).
Proof. exact (eq_refl (term179 A x' y)). Qed.
Lemma lem4603642 {A : Type'} (x' : A) (y : A) : (term178 A y x') = (term180 A x' y).
Proof. exact (MK_COMB (@lem4603641 A x' y) (@lem4603640 A x')). Qed.
Lemma lem4603644 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4603645 {A : Type'} (x' : A) (y : A) : (term180 A x' y) = (x' = y).
Proof. exact (@lem4603644 (x' = y)). Qed.
Lemma lem4603648 {A : Type'} (x' : A) (y : A) : (term178 A y x') = (x' = y).
Proof. exact (TRANS (@lem4603642 A x' y) (@lem4603645 A x' y)). Qed.
Lemma lem4603649 {A : Type'} (x' : A) (y : A) : (term15 A x' y) = (x' = y).
Proof. exact (TRANS (@lem4603632 A y x') (@lem4603648 A x' y)). Qed.
Lemma lem4603650 {A : Type'} (x : A) (x' : A) (y : A) : ((term15 A x' x) = (term15 A x' y)) = ((x' = x) = (x' = y)).
Proof. exact (MK_COMB (@lem4603628 A x' x) (@lem4603649 A x' y)). Qed.
Lemma lem4603653 {A : Type'} (x : A) (y : A) : (term156 A x y) = (term182 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4603650 A x x' y)). Qed.
Lemma lem4603654 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603655 {A : Type'} (x : A) (y : A) : (term157 A x y) = (term183 A x y).
Proof. exact (MK_COMB (@lem4603654 A) (@lem4603653 A x y)). Qed.
Lemma lem4603660 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term160 A s x y) = (term184 A s x y).
Proof. exact (MK_COMB (@lem4603599 A s y) (@lem4603655 A x y)). Qed.
Lemma lem4603663 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term162 A s x y) = (term185 A s x y).
Proof. exact (MK_COMB (@lem4603591 A s x) (@lem4603660 A s x y)). Qed.
Lemma lem4603666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4603667 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term164 A s x y) = (term186 A s x y).
Proof. exact (MK_COMB (@lem4603666) (@lem4603663 A s x y)). Qed.
Lemma lem4603670 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4603671 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term166 A s x y) = (term187 A s x y).
Proof. exact (MK_COMB (@lem4603667 A s x y) (@lem4603670 A x y)). Qed.
Lemma lem4603674 {A : Type'} (s : A -> Prop) (x : A) : (term168 A s x) = (term188 A s x).
Proof. exact (fun_ext (fun y : A => @lem4603671 A s x y)). Qed.
Lemma lem4603675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603676 {A : Type'} (s : A -> Prop) (x : A) : (term170 A s x) = (term189 A s x).
Proof. exact (MK_COMB (@lem4603675 A) (@lem4603674 A s x)). Qed.
Lemma lem4603681 {A : Type'} (s : A -> Prop) : (term172 A s) = (term190 A s).
Proof. exact (fun_ext (fun x : A => @lem4603676 A s x)). Qed.
Lemma lem4603682 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603683 {A : Type'} (s : A -> Prop) : (term174 A s) = (term191 A s).
Proof. exact (MK_COMB (@lem4603682 A) (@lem4603681 A s)). Qed.
Lemma lem4603688 {A : Type'} (s : A -> Prop) : (term191 A s) = (term174 A s).
Proof. exact (SYM (@lem4603683 A s)). Qed.
Lemma lem4603690 (p : Prop) : p = (term192 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4603691 {A : Type'} (s : A -> Prop) : (term191 A s) = (term193 A s).
Proof. exact (@lem4603690 (term191 A s)). Qed.
Lemma lem4603692 {A : Type'} (s : A -> Prop) : (term193 A s) = (term191 A s).
Proof. exact (SYM (@lem4603691 A s)). Qed.
Lemma lem4603693 {A : Type'} (s : A -> Prop) (h1 : term194 A s) : term194 A s.
Proof. exact (h1). Qed.
Lemma lem4603696 {A : Type'} (s : A -> Prop) (h1 : term193 A s) : term193 A s.
Proof. exact (h1). Qed.
Lemma lem4603697 {A : Type'} (s : A -> Prop) : term195 A s.
Proof. exact (fun h0 : term193 A s => @lem4603696 A s h0). Qed.
Lemma lem4603698 {A : Type'} (s : A -> Prop) (h1 : term195 A s) : term195 A s.
Proof. exact (h1). Qed.
Lemma lem4603699 {A : Type'} (s : A -> Prop) (h1 : term193 A s) : term193 A s.
Proof. exact (h1). Qed.
Lemma lem4603700 {A : Type'} (s : A -> Prop) (h1 : term193 A s) (h2 : term195 A s) : term193 A s.
Proof. exact (@lem4603698 A s h2 (@lem4603699 A s h1)). Qed.
Lemma lem4603701 {A : Type'} (s : A -> Prop) (h1 : term193 A s) : term196 A s.
Proof. exact (fun h0 : term195 A s => @lem4603700 A s h1 h0). Qed.
Lemma lem4603702 {A : Type'} (s : A -> Prop) (h1 : term195 A s) : term195 A s.
Proof. exact (h1). Qed.
Lemma lem4603703 {A : Type'} (s : A -> Prop) (h1 : term193 A s) (h2 : term195 A s) : term193 A s.
Proof. exact (@lem4603701 A s h1 (@lem4603702 A s h2)). Qed.
Lemma lem4603704 {A : Type'} (s : A -> Prop) (h1 : term195 A s) : term195 A s.
Proof. exact (fun h0 : term193 A s => @lem4603703 A s h0 h1). Qed.
Lemma lem4603705 {A : Type'} (s : A -> Prop) : term197 A s.
Proof. exact (fun h0 : term195 A s => @lem4603704 A s h0). Qed.
Lemma lem4603708 {A : Type'} (s : A -> Prop) : term195 A s.
Proof. exact (@lem4603705 A s (@lem4603697 A s)). Qed.
Lemma lem4603709 {A : Type'} (s : A -> Prop) : term195 A s.
Proof. exact (@lem4603708 A s). Qed.
Lemma lem4603715 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4603716 {A : Type'} (s : A -> Prop) : (term193 A s) = (term198 A s).
Proof. exact (@lem4603715 (term194 A s)). Qed.
Lemma lem4603718 (t : Prop) : (term199 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4603719 {A : Type'} (s : A -> Prop) : (term198 A s) = (term191 A s).
Proof. exact (@lem4603718 (term191 A s)). Qed.
Lemma lem4603724 {A : Type'} (s : A -> Prop) : (term193 A s) = (term191 A s).
Proof. exact (TRANS (@lem4603716 A s) (@lem4603719 A s)). Qed.
Lemma lem4603739 {A : Type'} : (term200 A) = (term201 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4603724 A s)). Qed.
Lemma lem4603740 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4603749 {A : Type'} : (term202 A) = (term203 A).
Proof. exact (MK_COMB (@lem4603740 A) (@lem4603739 A)). Qed.
Lemma lem4603750 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4603755 {A : Type'} (x : A) (x' : A) (y : A) : ((x' = x) = (x' = y)) = ((x' = x) = (x' = y)).
Proof. exact (eq_refl ((x' = x) = (x' = y))). Qed.
Lemma lem4603756 {A : Type'} (x : A) (y : A) : (term182 A x y) = (term182 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4603755 A x x' y)). Qed.
Lemma lem4603757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603758 {A : Type'} (x : A) (y : A) : (term183 A x y) = (term183 A x y).
Proof. exact (MK_COMB (@lem4603757 A) (@lem4603756 A x y)). Qed.
Lemma lem4603761 {A : Type'} (s : A -> Prop) (y : A) : (term175 A s y) = (term175 A s y).
Proof. exact (eq_refl (term175 A s y)). Qed.
Lemma lem4603762 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term184 A s x y) = (term184 A s x y).
Proof. exact (MK_COMB (@lem4603761 A s y) (@lem4603758 A x y)). Qed.
Lemma lem4603765 {A : Type'} (s : A -> Prop) (x : A) : (term175 A s x) = (term175 A s x).
Proof. exact (eq_refl (term175 A s x)). Qed.
Lemma lem4603766 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term185 A s x y) = (term185 A s x y).
Proof. exact (MK_COMB (@lem4603765 A s x) (@lem4603762 A s x y)). Qed.
Lemma lem4603767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4603768 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term186 A s x y) = (term186 A s x y).
Proof. exact (MK_COMB (@lem4603767) (@lem4603766 A s x y)). Qed.
Lemma lem4603769 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term187 A s x y) = (term187 A s x y).
Proof. exact (MK_COMB (@lem4603768 A s x y) (@lem4603750 A x y)). Qed.
Lemma lem4603770 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (term188 A s x).
Proof. exact (fun_ext (fun y : A => @lem4603769 A s x y)). Qed.
Lemma lem4603771 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603772 {A : Type'} (s : A -> Prop) (x : A) : (term189 A s x) = (term189 A s x).
Proof. exact (MK_COMB (@lem4603771 A) (@lem4603770 A s x)). Qed.
Lemma lem4603773 {A : Type'} (s : A -> Prop) : (term190 A s) = (term190 A s).
Proof. exact (fun_ext (fun x : A => @lem4603772 A s x)). Qed.
Lemma lem4603774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603775 {A : Type'} (s : A -> Prop) : (term191 A s) = (term191 A s).
Proof. exact (MK_COMB (@lem4603774 A) (@lem4603773 A s)). Qed.
Lemma lem4603776 {A : Type'} : (term201 A) = (term201 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4603775 A s)). Qed.
Lemma lem4603777 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4603778 {A : Type'} : (term203 A) = (term203 A).
Proof. exact (MK_COMB (@lem4603777 A) (@lem4603776 A)). Qed.
Lemma lem4603811 {A : Type'} : (term202 A) = (term203 A).
Proof. exact (TRANS (@lem4603749 A) (@lem4603778 A)). Qed.
Lemma lem4603812 {A : Type'} : (term203 A) = (term202 A).
Proof. exact (SYM (@lem4603811 A)). Qed.
Lemma lem4603813 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term185 A s x y.
Proof. exact (h1). Qed.
Lemma lem4603815 (p : Prop) : p = (term192 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4603816 {A : Type'} (x : A) (y : A) : (x = y) = (term204 A x y).
Proof. exact (@lem4603815 (x = y)). Qed.
Lemma lem4603817 {A : Type'} (x : A) (y : A) : (term204 A x y) = (x = y).
Proof. exact (SYM (@lem4603816 A x y)). Qed.
Lemma lem4603818 {A : Type'} (x : A) (y : A) (h1 : term205 A x y) : term205 A x y.
Proof. exact (h1). Qed.
Lemma lem4603835 {A : Type'} (x : A) (x' : A) (y : A) : ((x' = x) = (x' = y)) = (term206 A x x' y).
Proof. exact (@lem17784 (x' = x) (x' = y)). Qed.
Lemma lem4603836 {A : Type'} (x : A) (y : A) : (term182 A x y) = (term207 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4603835 A x x' y)). Qed.
Lemma lem4603837 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603838 {A : Type'} (x : A) (y : A) : (term183 A x y) = (term208 A x y).
Proof. exact (MK_COMB (@lem4603837 A) (@lem4603836 A x y)). Qed.
Lemma lem4603840 {A : Type'} (s : A -> Prop) (y : A) : (term175 A s y) = (term175 A s y).
Proof. exact (eq_refl (term175 A s y)). Qed.
Lemma lem4603841 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term184 A s x y) = (term209 A s x y).
Proof. exact (MK_COMB (@lem4603840 A s y) (@lem4603838 A x y)). Qed.
Lemma lem4603843 {A : Type'} (s : A -> Prop) (x : A) : (term175 A s x) = (term175 A s x).
Proof. exact (eq_refl (term175 A s x)). Qed.
Lemma lem4603844 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term185 A s x y) = (term210 A s x y).
Proof. exact (MK_COMB (@lem4603843 A s x) (@lem4603841 A s x y)). Qed.
Lemma lem4603846 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4603847 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem4603846 A P Q). Qed.
Lemma lem4603848 {A : Type'} (x : A) (y : A) : (term213 A x y) = (term214 A x y).
Proof. exact (@lem4603847 A (term215 A x y) (term216 A x y)). Qed.
Lemma lem4603849 {A : Type'} (x : A) (x' : A) (y : A) : (term217 A x y x') = (term218 A x x' y).
Proof. exact (eq_refl (term217 A x y x')). Qed.
Lemma lem4603850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4603851 {A : Type'} (x : A) (x' : A) (y : A) : (term219 A x y x') = (term220 A x x' y).
Proof. exact (MK_COMB (@lem4603850) (@lem4603849 A x x' y)). Qed.
Lemma lem4603852 {A : Type'} (x : A) (x' : A) (y : A) : (term221 A x y x') = (term222 A x x' y).
Proof. exact (eq_refl (term221 A x y x')). Qed.
Lemma lem4603853 {A : Type'} (x : A) (x' : A) (y : A) : (term223 A x y x') = (term206 A x x' y).
Proof. exact (MK_COMB (@lem4603851 A x x' y) (@lem4603852 A x x' y)). Qed.
Lemma lem4603854 {A : Type'} (x : A) (y : A) : (term224 A x y) = (term207 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4603853 A x x' y)). Qed.
Lemma lem4603855 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603856 {A : Type'} (x : A) (y : A) : (term213 A x y) = (term208 A x y).
Proof. exact (MK_COMB (@lem4603855 A) (@lem4603854 A x y)). Qed.
Lemma lem4603857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4603858 {A : Type'} (x : A) (y : A) : (term225 A x y) = (term226 A x y).
Proof. exact (MK_COMB (@lem4603857) (@lem4603856 A x y)). Qed.
Lemma lem4603859 {A : Type'} (x : A) (x' : A) (y : A) : (term217 A x y x') = (term218 A x x' y).
Proof. exact (eq_refl (term217 A x y x')). Qed.
Lemma lem4603860 {A : Type'} (x : A) (y : A) : (term227 A x y) = (term215 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4603859 A x x' y)). Qed.
Lemma lem4603861 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603862 {A : Type'} (x : A) (y : A) : (term228 A x y) = (term229 A x y).
Proof. exact (MK_COMB (@lem4603861 A) (@lem4603860 A x y)). Qed.
Lemma lem4603863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4603864 {A : Type'} (x : A) (y : A) : (term230 A x y) = (term231 A x y).
Proof. exact (MK_COMB (@lem4603863) (@lem4603862 A x y)). Qed.
Lemma lem4603865 {A : Type'} (x : A) (x' : A) (y : A) : (term221 A x y x') = (term222 A x x' y).
Proof. exact (eq_refl (term221 A x y x')). Qed.
Lemma lem4603866 {A : Type'} (x : A) (y : A) : (term232 A x y) = (term216 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4603865 A x x' y)). Qed.
Lemma lem4603867 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603868 {A : Type'} (x : A) (y : A) : (term233 A x y) = (term234 A x y).
Proof. exact (MK_COMB (@lem4603867 A) (@lem4603866 A x y)). Qed.
Lemma lem4603869 {A : Type'} (x : A) (y : A) : (term214 A x y) = (term235 A x y).
Proof. exact (MK_COMB (@lem4603864 A x y) (@lem4603868 A x y)). Qed.
Lemma lem4603870 {A : Type'} (x : A) (y : A) : ((term213 A x y) = (term214 A x y)) = ((term208 A x y) = (term235 A x y)).
Proof. exact (MK_COMB (@lem4603858 A x y) (@lem4603869 A x y)). Qed.
Lemma lem4603871 {A : Type'} (x : A) (y : A) : (term208 A x y) = (term235 A x y).
Proof. exact (EQ_MP (@lem4603870 A x y) (@lem4603848 A x y)). Qed.
Lemma lem4603968 {A : Type'} (s : A -> Prop) (y : A) : (term175 A s y) = (term175 A s y).
Proof. exact (eq_refl (term175 A s y)). Qed.
Lemma lem4603969 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term209 A s x y) = (term236 A s x y).
Proof. exact (MK_COMB (@lem4603968 A s y) (@lem4603871 A x y)). Qed.
Lemma lem4603970 {A : Type'} (s : A -> Prop) (x : A) : (term175 A s x) = (term175 A s x).
Proof. exact (eq_refl (term175 A s x)). Qed.
Lemma lem4603973 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term210 A s x y) = (term237 A s x y).
Proof. exact (MK_COMB (@lem4603970 A s x) (@lem4603969 A s x y)). Qed.
Lemma lem4603974 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term185 A s x y) = (term237 A s x y).
Proof. exact (TRANS (@lem4603844 A s x y) (@lem4603973 A s x y)). Qed.
Lemma lem4603975 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term237 A s x y.
Proof. exact (EQ_MP (@lem4603974 A s x y) (@lem4603813 A s x y h1)). Qed.
Lemma lem4603981 {A : Type'} (x : A) (y : A) (h1 : term205 A x y) : term205 A x y.
Proof. exact (h1). Qed.
Lemma lem4603996 {A : Type'} (x : A) (x' : A) (y : A) : (term222 A x x' y) = (term222 A x x' y).
Proof. exact (eq_refl (term222 A x x' y)). Qed.
Lemma lem4603997 {A : Type'} (x : A) (y : A) : (term216 A x y) = (term216 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4603996 A x x' y)). Qed.
Lemma lem4603998 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4603999 {A : Type'} (x : A) (y : A) : (term234 A x y) = (term234 A x y).
Proof. exact (MK_COMB (@lem4603998 A) (@lem4603997 A x y)). Qed.
Lemma lem4604014 {A : Type'} (x : A) (x' : A) (y : A) : (term218 A x x' y) = (term218 A x x' y).
Proof. exact (eq_refl (term218 A x x' y)). Qed.
Lemma lem4604015 {A : Type'} (x : A) (y : A) : (term215 A x y) = (term215 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4604014 A x x' y)). Qed.
Lemma lem4604016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604017 {A : Type'} (x : A) (y : A) : (term229 A x y) = (term229 A x y).
Proof. exact (MK_COMB (@lem4604016 A) (@lem4604015 A x y)). Qed.
Lemma lem4604018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4604019 {A : Type'} (x : A) (y : A) : (term231 A x y) = (term231 A x y).
Proof. exact (MK_COMB (@lem4604018) (@lem4604017 A x y)). Qed.
Lemma lem4604020 {A : Type'} (x : A) (y : A) : (term235 A x y) = (term235 A x y).
Proof. exact (MK_COMB (@lem4604019 A x y) (@lem4603999 A x y)). Qed.
Lemma lem4604025 {A : Type'} (s : A -> Prop) (y : A) : (term175 A s y) = (term175 A s y).
Proof. exact (eq_refl (term175 A s y)). Qed.
Lemma lem4604026 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term236 A s x y) = (term236 A s x y).
Proof. exact (MK_COMB (@lem4604025 A s y) (@lem4604020 A x y)). Qed.
Lemma lem4604031 {A : Type'} (s : A -> Prop) (x : A) : (term175 A s x) = (term175 A s x).
Proof. exact (eq_refl (term175 A s x)). Qed.
Lemma lem4604032 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term237 A s x y) = (term237 A s x y).
Proof. exact (MK_COMB (@lem4604031 A s x) (@lem4604026 A s x y)). Qed.
Lemma lem4604033 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term237 A s x y.
Proof. exact (EQ_MP (@lem4604032 A s x y) (@lem4603975 A s x y h1)). Qed.
Lemma lem4604041 {A : Type'} (x : A) (y : A) (h1 : term205 A x y) : term205 A x y.
Proof. exact (h1). Qed.
Lemma lem4604042 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term236 A s x y.
Proof. exact (proj2 (@lem4604033 A s x y h1)). Qed.
Lemma lem4604044 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term235 A x y.
Proof. exact (proj2 (@lem4604042 A s x y h1)). Qed.
Lemma lem4604046 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term234 A x y.
Proof. exact (proj2 (@lem4604044 A s x y h1)). Qed.
Lemma lem4604051 {A : Type'} (x : A) (y : A) (h1 : term205 A x y) : term205 A x y.
Proof. exact (h1). Qed.
Lemma lem4604080 {A : Type'} (x : A) (x' : A) (y : A) : (term222 A x x' y) = (term222 A x x' y).
Proof. exact (eq_refl (term222 A x x' y)). Qed.
Lemma lem4604081 {A : Type'} (x : A) (y : A) : (term216 A x y) = (term216 A x y).
Proof. exact (fun_ext (fun x' : A => @lem4604080 A x x' y)). Qed.
Lemma lem4604082 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4604084 {A : Type'} (x : A) (y : A) : (term234 A x y) = (term234 A x y).
Proof. exact (MK_COMB (@lem4604082 A) (@lem4604081 A x y)). Qed.
Lemma lem4604085 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term234 A x y.
Proof. exact (EQ_MP (@lem4604084 A x y) (@lem4604046 A s x y h1)). Qed.
Lemma lem4604089 {A : Type'} (_55356 : A) (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term221 A x y _55356.
Proof. exact (@lem4604085 A s x y h1 _55356). Qed.
Lemma lem4604090 {A : Type'} (x : A) (_55356 : A) (y : A) : (term221 A x y _55356) = (term222 A x _55356 y).
Proof. exact (eq_refl (term221 A x y _55356)). Qed.
Lemma lem4604093 {A : Type'} (x : A) (y : A) (h1 : term205 A x y) : term205 A x y.
Proof. exact (h1). Qed.
Lemma lem4604109 {A : Type'} (_55356 : A) (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term222 A x _55356 y.
Proof. exact (EQ_MP (@lem4604090 A x _55356 y) (@lem4604089 A _55356 s x y h1)). Qed.
Lemma lem4604125 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4604126 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4604125 A x). Qed.
Lemma lem4604127 {A : Type'} (x : A) : term238 A x.
Proof. exact (fun h0 : term239 A x => @lem4604126 A x). Qed.
Lemma lem4604129 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4604130 {A : Type'} (x : A) : (term238 A x) = (x = x).
Proof. exact (@lem4604129 (x = x)). Qed.
Lemma lem4604131 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem4604130 A x) (@lem4604127 A x)). Qed.
Lemma lem4604137 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4604138 {A : Type'} (y : A) (_55356 : A) (x : A) : (term222 A x _55356 y) = (term218 A y _55356 x).
Proof. exact (@lem4604137 (_55356 = y) (term205 A _55356 x)). Qed.
Lemma lem4604148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4604149 {A : Type'} (y : A) (_55356 : A) (x : A) : (term241 A x _55356 y) = (term242 A y _55356 x).
Proof. exact (MK_COMB (@lem4604148) (@lem4604138 A y _55356 x)). Qed.
Lemma lem4604159 {A : Type'} (y : A) (_55356 : A) (x : A) : (term218 A y _55356 x) = (term218 A y _55356 x).
Proof. exact (eq_refl (term218 A y _55356 x)). Qed.
Lemma lem4604160 {A : Type'} (y : A) (_55356 : A) (x : A) : ((term222 A x _55356 y) = (term218 A y _55356 x)) = ((term218 A y _55356 x) = (term218 A y _55356 x)).
Proof. exact (MK_COMB (@lem4604149 A y _55356 x) (@lem4604159 A y _55356 x)). Qed.
Lemma lem4604162 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4604163 (x : Prop) : (x = x) = True.
Proof. exact (@lem4604162 Prop x). Qed.
Lemma lem4604164 {A : Type'} (y : A) (_55356 : A) (x : A) : ((term218 A y _55356 x) = (term218 A y _55356 x)) = True.
Proof. exact (@lem4604163 (term218 A y _55356 x)). Qed.
Lemma lem4604165 {A : Type'} (y : A) (_55356 : A) (x : A) : ((term222 A x _55356 y) = (term218 A y _55356 x)) = True.
Proof. exact (TRANS (@lem4604160 A y _55356 x) (@lem4604164 A y _55356 x)). Qed.
Lemma lem4604166 {A : Type'} (y : A) (_55356 : A) (x : A) : True = ((term222 A x _55356 y) = (term218 A y _55356 x)).
Proof. exact (SYM (@lem4604165 A y _55356 x)). Qed.
Lemma lem4604167 {A : Type'} (y : A) (_55356 : A) (x : A) : (term222 A x _55356 y) = (term218 A y _55356 x).
Proof. exact (EQ_MP (@lem4604166 A y _55356 x) (@lem0)). Qed.
Lemma lem4604168 {A : Type'} (_55356 : A) (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term218 A y _55356 x.
Proof. exact (EQ_MP (@lem4604167 A y _55356 x) (@lem4604109 A _55356 s x y h1)). Qed.
Lemma lem4604170 (b : Prop) (a : Prop) : (a \/ b) = (term243 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4604171 {A : Type'} (x : A) (_55356 : A) (y : A) : (term218 A y _55356 x) = (term244 A x _55356 y).
Proof. exact (@lem4604170 (term205 A _55356 x) (_55356 = y)). Qed.
Lemma lem4604173 (a : Prop) : (term199 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4604174 {A : Type'} (_55356 : A) (x : A) : (term245 A _55356 x) = (_55356 = x).
Proof. exact (@lem4604173 (_55356 = x)). Qed.
Lemma lem4604175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4604176 {A : Type'} (_55356 : A) (x : A) : (term246 A _55356 x) = (term247 A _55356 x).
Proof. exact (MK_COMB (@lem4604175) (@lem4604174 A _55356 x)). Qed.
Lemma lem4604177 {A : Type'} (_55356 : A) (y : A) : (_55356 = y) = (_55356 = y).
Proof. exact (eq_refl (_55356 = y)). Qed.
Lemma lem4604178 {A : Type'} (x : A) (_55356 : A) (y : A) : (term244 A x _55356 y) = (term248 A x _55356 y).
Proof. exact (MK_COMB (@lem4604176 A _55356 x) (@lem4604177 A _55356 y)). Qed.
Lemma lem4604179 {A : Type'} (x : A) (_55356 : A) (y : A) : (term218 A y _55356 x) = (term248 A x _55356 y).
Proof. exact (TRANS (@lem4604171 A x _55356 y) (@lem4604178 A x _55356 y)). Qed.
Lemma lem4604182 {A : Type'} (_55356 : A) (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term248 A x _55356 y.
Proof. exact (EQ_MP (@lem4604179 A x _55356 y) (@lem4604168 A _55356 s x y h1)). Qed.
Lemma lem4604183 {A : Type'} (_55356 : A) (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term248 A x _55356 y.
Proof. exact (@lem4604182 A _55356 s x y h1). Qed.
Lemma lem4604184 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term249 A x y.
Proof. exact (@lem4604183 A x s x y h1). Qed.
Lemma lem4604187 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : x = y.
Proof. exact (@lem4604184 A s x y h1 (@lem4604131 A x)). Qed.
Lemma lem4604188 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term250 A x y.
Proof. exact (fun h0 : term205 A x y => @lem4604187 A s x y h1). Qed.
Lemma lem4604190 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4604191 {A : Type'} (x : A) (y : A) : (term250 A x y) = (x = y).
Proof. exact (@lem4604190 (x = y)). Qed.
Lemma lem4604192 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : x = y.
Proof. exact (EQ_MP (@lem4604191 A x y) (@lem4604188 A s x y h1)). Qed.
Lemma lem4604195 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4604197 {A : Type'} (x : A) (y : A) : (term205 A x y) = (term251 A x y).
Proof. exact (@lem4604195 (x = y)). Qed.
Lemma lem4604200 {A : Type'} (x : A) (y : A) (h1 : term205 A x y) : term251 A x y.
Proof. exact (EQ_MP (@lem4604197 A x y) (@lem4604093 A x y h1)). Qed.
Lemma lem4604203 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : False.
Proof. exact (@lem4604200 A x y h1 (@lem4604192 A s x y h2)). Qed.
Lemma lem4604204 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : term252.
Proof. exact (fun h0 : ~ False => @lem4604203 A s x y h1 h2). Qed.
Lemma lem4604206 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4604207 : term252 = False.
Proof. exact (@lem4604206 False). Qed.
Lemma lem4604208 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : False.
Proof. exact (EQ_MP (@lem4604207) (@lem4604204 A s x y h1 h2)). Qed.
Lemma lem4604209 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : (term205 A x y) = False.
Proof. exact (prop_ext (fun h3 : term205 A x y => @lem4604208 A s x y h1 h2) (fun h3 : False => @lem4604093 A x y h1)). Qed.
Lemma lem4604210 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : False.
Proof. exact (EQ_MP (@lem4604209 A s x y h1 h2) (@lem4604093 A x y h1)). Qed.
Lemma lem4604211 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : (term205 A x y) = False.
Proof. exact (prop_ext (fun h3 : term205 A x y => @lem4604210 A s x y h1 h2) (fun h3 : False => @lem4604051 A x y h1)). Qed.
Lemma lem4604212 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : False.
Proof. exact (EQ_MP (@lem4604211 A s x y h1 h2) (@lem4604051 A x y h1)). Qed.
Lemma lem4604213 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : (term205 A x y) = False.
Proof. exact (prop_ext (fun h3 : term205 A x y => @lem4604212 A s x y h1 h2) (fun h3 : False => @lem4604051 A x y h1)). Qed.
Lemma lem4604214 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : False.
Proof. exact (EQ_MP (@lem4604213 A s x y h1 h2) (@lem4604051 A x y h1)). Qed.
Lemma lem4604215 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : (term205 A x y) = False.
Proof. exact (prop_ext (fun h3 : term205 A x y => @lem4604214 A s x y h1 h2) (fun h3 : False => @lem4604041 A x y h1)). Qed.
Lemma lem4604216 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : False.
Proof. exact (EQ_MP (@lem4604215 A s x y h1 h2) (@lem4604041 A x y h1)). Qed.
Lemma lem4604217 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : (term205 A x y) = False.
Proof. exact (prop_ext (fun h3 : term205 A x y => @lem4604216 A s x y h1 h2) (fun h3 : False => @lem4603981 A x y h1)). Qed.
Lemma lem4604218 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : False.
Proof. exact (EQ_MP (@lem4604217 A s x y h1 h2) (@lem4603981 A x y h1)). Qed.
Lemma lem4604219 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : (term205 A x y) = False.
Proof. exact (prop_ext (fun h3 : term205 A x y => @lem4604218 A s x y h1 h2) (fun h3 : False => @lem4603818 A x y h1)). Qed.
Lemma lem4604220 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term205 A x y) (h2 : term185 A s x y) : False.
Proof. exact (EQ_MP (@lem4604219 A s x y h1 h2) (@lem4603818 A x y h1)). Qed.
Lemma lem4604221 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : term204 A x y.
Proof. exact (fun h0 : term205 A x y => @lem4604220 A s x y h0 h1). Qed.
Lemma lem4604222 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term185 A s x y) : x = y.
Proof. exact (EQ_MP (@lem4603817 A x y) (@lem4604221 A s x y h1)). Qed.
Lemma lem4604223 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term187 A s x y.
Proof. exact (fun h0 : term185 A s x y => @lem4604222 A s x y h0). Qed.
Lemma lem4604228 {A : Type'} (s : A -> Prop) (x : A) : term189 A s x.
Proof. exact (fun y : A => @lem4604223 A s x y). Qed.
Lemma lem4604233 {A : Type'} (s : A -> Prop) : term191 A s.
Proof. exact (fun x : A => @lem4604228 A s x). Qed.
Lemma lem4604238 {A : Type'} : term203 A.
Proof. exact (fun s : A -> Prop => @lem4604233 A s). Qed.
Lemma lem4604239 {A : Type'} : term202 A.
Proof. exact (EQ_MP (@lem4603812 A) (@lem4604238 A)). Qed.
Lemma lem4604240 {A : Type'} (s : A -> Prop) : term253 A s.
Proof. exact (@lem4604239 A s). Qed.
Lemma lem4604241 {A : Type'} (s : A -> Prop) : (term253 A s) = (term193 A s).
Proof. exact (eq_refl (term253 A s)). Qed.
Lemma lem4604242 {A : Type'} (s : A -> Prop) : term193 A s.
Proof. exact (EQ_MP (@lem4604241 A s) (@lem4604240 A s)). Qed.
Lemma lem4604244 {A : Type'} (s : A -> Prop) : term193 A s.
Proof. exact (@lem4603709 A s (@lem4604242 A s)). Qed.
Lemma lem4604245 {A : Type'} (s : A -> Prop) (h1 : term194 A s) : False.
Proof. exact (@lem4604244 A s (@lem4603693 A s h1)). Qed.
Lemma lem4604246 {A : Type'} (s : A -> Prop) (h1 : term194 A s) : (term194 A s) = False.
Proof. exact (prop_ext (fun h2 : term194 A s => @lem4604245 A s h1) (fun h2 : False => @lem4603693 A s h1)). Qed.
Lemma lem4604247 {A : Type'} (s : A -> Prop) (h1 : term194 A s) : False.
Proof. exact (EQ_MP (@lem4604246 A s h1) (@lem4603693 A s h1)). Qed.
Lemma lem4604248 {A : Type'} (s : A -> Prop) : term193 A s.
Proof. exact (fun h0 : term194 A s => @lem4604247 A s h0). Qed.
Lemma lem4604249 {A : Type'} (s : A -> Prop) : term191 A s.
Proof. exact (EQ_MP (@lem4603692 A s) (@lem4604248 A s)). Qed.
Lemma lem4604250 {A : Type'} (s : A -> Prop) : term174 A s.
Proof. exact (EQ_MP (@lem4603688 A s) (@lem4604249 A s)). Qed.
Lemma lem4604251 {A : Type'} (s : A -> Prop) : term173 A s.
Proof. exact (EQ_MP (@lem4603573 A s) (@lem4604250 A s)). Qed.
Lemma lem4604252 {A : Type'} (s : A -> Prop) : (term53 A s) = (@FINITE A s).
Proof. exact (@lem4603467 A s (@lem4604251 A s)). Qed.
Lemma lem4604253 {A : Type'} (s : A -> Prop) : term254 A s.
Proof. exact (@lem4603463 A s (@lem4604252 A s)). Qed.
Lemma lem4604254 {A : Type'} (s : A -> Prop) (h1 : term53 A s) : @FINITE A s.
Proof. exact (@lem4604253 A s (@lem4603272 A s h1)). Qed.
Lemma lem4604255 {A : Type'} (s : A -> Prop) (h1 : term52 A s) : (term53 A s) = (@FINITE A s).
Proof. exact (prop_ext (fun h2 : term53 A s => @lem4604254 A s h2) (fun h2 : @FINITE A s => @lem4603460 A s h1)). Qed.
Lemma lem4604256 {A : Type'} (s : A -> Prop) (h1 : term52 A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4604255 A s h1) (@lem4603460 A s h1)). Qed.
Lemma lem4604258 {A : Type'} (s : A -> Prop) : term255 A s.
Proof. exact (fun h0 : term52 A s => @lem4604256 A s h0). Qed.
Lemma lem4604259 {A : Type'} (s : A -> Prop) : term256 A s.
Proof. exact (conj (@lem4604258 A s) (@lem4603270 A s)). Qed.
Lemma lem4604260 {A : Type'} (s : A -> Prop) : (term256 A s) = ((term52 A s) = (@FINITE A s)).
Proof. exact (@lem32 (term52 A s) (@FINITE A s)). Qed.
Lemma lem4604261 {A : Type'} (s : A -> Prop) : (term52 A s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4604260 A s) (@lem4604259 A s)). Qed.
Lemma lem4604266 {A : Type'} : term257 A.
Proof. exact (fun s : A -> Prop => @lem4604261 A s). Qed.
