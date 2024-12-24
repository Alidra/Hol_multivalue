Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_CLAUSES_term_abbrevs.
Require Import FINITE_SUPPORT_spec.
Require Import ITERATE_CLAUSES_GEN_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5753235 {_119939 _119945 : Type'} (op : type1400 _119945) : term0 _119939 _119945 op.
Proof. exact (@lem5720601 _119939 _119945 op). Qed.
Lemma lem5753236 {_119939 _119945 : Type'} (op : type1400 _119945) : (term0 _119939 _119945 op) = (term1 _119939 _119945 op).
Proof. exact (eq_refl (term0 _119939 _119945 op)). Qed.
Lemma lem5753237 {_119939 _119945 : Type'} (op : type1400 _119945) : term1 _119939 _119945 op.
Proof. exact (EQ_MP (@lem5753236 _119939 _119945 op) (@lem5753235 _119939 _119945 op)). Qed.
Lemma lem5753238 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : term2 _119939 _119945 op f.
Proof. exact (@lem5753237 _119939 _119945 op f). Qed.
Lemma lem5753239 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term2 _119939 _119945 op f) = (term3 _119939 _119945 op f).
Proof. exact (eq_refl (term2 _119939 _119945 op f)). Qed.
Lemma lem5753240 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : term3 _119939 _119945 op f.
Proof. exact (EQ_MP (@lem5753239 _119939 _119945 op f) (@lem5753238 _119939 _119945 op f)). Qed.
Lemma lem5753241 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term4 _119939 _119945 op f s.
Proof. exact (@lem5753240 _119939 _119945 op f s). Qed.
Lemma lem5753242 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term4 _119939 _119945 op f s) = (term5 _119939 _119945 op f s).
Proof. exact (eq_refl (term4 _119939 _119945 op f s)). Qed.
Lemma lem5753243 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term5 _119939 _119945 op f s.
Proof. exact (EQ_MP (@lem5753242 _119939 _119945 op f s) (@lem5753241 _119939 _119945 op f s)). Qed.
Lemma lem5753244 {_119939 : Type'} (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : @FINITE _119939 s.
Proof. exact (h1). Qed.
Lemma lem5753245 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : term6 _119939 _119945 op f s.
Proof. exact (@lem5753243 _119939 _119945 op f s (@lem5753244 _119939 s h1)). Qed.
Lemma lem5753246 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term6 _119939 _119945 op f s) = ((term6 _119939 _119945 op f s) = True).
Proof. exact (@lem7 (term6 _119939 _119945 op f s)). Qed.
Lemma lem5753247 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : (term6 _119939 _119945 op f s) = True.
Proof. exact (EQ_MP (@lem5753246 _119939 _119945 op f s) (@lem5753245 _119939 _119945 op f s h1)). Qed.
Lemma lem5753253 {A B : Type'} (op : type1400 B) : term7 A B op.
Proof. exact (@lem5753234 A B op). Qed.
Lemma lem5753254 {A B : Type'} (op : type1400 B) : (term7 A B op) = (term8 A B op).
Proof. exact (eq_refl (term7 A B op)). Qed.
Lemma lem5753255 {A B : Type'} (op : type1400 B) : term8 A B op.
Proof. exact (EQ_MP (@lem5753254 A B op) (@lem5753253 A B op)). Qed.
Lemma lem5753256 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5753257 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term9 A B op.
Proof. exact (@lem5753255 A B op (@lem5753256 B op h1)). Qed.
Lemma lem5753258 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term10 A B op.
Proof. exact (proj2 (@lem5753257 A B op h1)). Qed.
Lemma lem5753259 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term11 A B op f.
Proof. exact (@lem5753258 A B op h1 f). Qed.
Lemma lem5753260 {A B : Type'} (op : type1400 B) (f : A -> B) : (term11 A B op f) = (term12 A B op f).
Proof. exact (eq_refl (term11 A B op f)). Qed.
Lemma lem5753261 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term12 A B op f.
Proof. exact (EQ_MP (@lem5753260 A B op f) (@lem5753259 A B f op h1)). Qed.
Lemma lem5753262 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : term13 A B op f x.
Proof. exact (@lem5753261 A B f op h1 x). Qed.
Lemma lem5753263 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) : (term13 A B op f x) = (term14 A B x op f).
Proof. exact (eq_refl (term13 A B op f x)). Qed.
Lemma lem5753264 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term14 A B x op f.
Proof. exact (EQ_MP (@lem5753263 A B x op f) (@lem5753262 A B f x op h1)). Qed.
Lemma lem5753265 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term15 A B x op f s.
Proof. exact (@lem5753264 A B x f op h1 s). Qed.
Lemma lem5753266 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term15 A B x op f s) = (term16 A B x op s f).
Proof. exact (eq_refl (term15 A B x op f s)). Qed.
Lemma lem5753267 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term16 A B x op s f.
Proof. exact (EQ_MP (@lem5753266 A B x op s f) (@lem5753265 A B x f s op h1)). Qed.
Lemma lem5753268 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term6 A B op f s) : term6 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5753269 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term6 A B op f s) (h2 : @monoidal B op) : (term17 A B op x s f) = (term18 A B x op s f).
Proof. exact (@lem5753267 A B x s f op h2 (@lem5753268 A B op f s h1)). Qed.
Lemma lem5753270 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term6 A B op f s) : term19 A B x op s f.
Proof. exact (fun h0 : @monoidal B op => @lem5753269 A B x f s op h1 h0). Qed.
Lemma lem5753271 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term20 A B x op s f.
Proof. exact (fun h0 : term6 A B op f s => @lem5753270 A B x op f s h0). Qed.
Lemma lem5753273 (p : Prop) (q : Prop) (r : Prop) : (term21 p q r) = (term22 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5753278 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term20 A B x op s f) = (term23 A B x op s f).
Proof. exact (@lem5753273 (term6 A B op f s) (@monoidal B op) ((term17 A B op x s f) = (term18 A B x op s f))). Qed.
Lemma lem5753280 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term24 A B op.
Proof. exact (proj1 (@lem5753257 A B op h1)). Qed.
Lemma lem5753281 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term25 A B op f.
Proof. exact (@lem5753280 A B op h1 f). Qed.
Lemma lem5753282 {A B : Type'} (f : A -> B) (op : type1400 B) : (term25 A B op f) = ((@iterate B A op (@EMPTY A) f) = (@neutral B op)).
Proof. exact (eq_refl (term25 A B op f)). Qed.
Lemma lem5753283 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (@iterate B A op (@EMPTY A) f) = (@neutral B op).
Proof. exact (EQ_MP (@lem5753282 A B f op) (@lem5753281 A B f op h1)). Qed.
Lemma lem5753296 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term26 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5753297 (p : Prop) (q : Prop) (p' : Prop) : term27 p q p'.
Proof. exact (fun q' : Prop => @lem5753296 p q p' q'). Qed.
Lemma lem5753298 (p : Prop) (q : Prop) : term28 p q.
Proof. exact (fun p' : Prop => @lem5753297 p q p'). Qed.
Lemma lem5753299 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term29 _120477 _120519 _120521 op.
Proof. exact (@lem5753298 (@monoidal _120519 op) (term30 _120477 _120519 _120521 op)). Qed.
Lemma lem5753300 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (p' : Prop) : term31 _120477 _120519 _120521 op p'.
Proof. exact (@lem5753299 _120477 _120519 _120521 op p'). Qed.
Lemma lem5753301 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (p' : Prop) : (term31 _120477 _120519 _120521 op p') = (term32 _120477 _120519 _120521 op p').
Proof. exact (eq_refl (term31 _120477 _120519 _120521 op p')). Qed.
Lemma lem5753302 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (p' : Prop) : term32 _120477 _120519 _120521 op p'.
Proof. exact (EQ_MP (@lem5753301 _120477 _120519 _120521 op p') (@lem5753300 _120477 _120519 _120521 op p')). Qed.
Lemma lem5753303 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (p' : Prop) (q' : Prop) : term33 _120477 _120519 _120521 op p' q'.
Proof. exact (@lem5753302 _120477 _120519 _120521 op p' q'). Qed.
Lemma lem5753304 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (p' : Prop) (q' : Prop) : (term33 _120477 _120519 _120521 op p' q') = (term34 _120477 _120519 _120521 op p' q').
Proof. exact (eq_refl (term33 _120477 _120519 _120521 op p' q')). Qed.
Lemma lem5753305 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (p' : Prop) (q' : Prop) : term34 _120477 _120519 _120521 op p' q'.
Proof. exact (EQ_MP (@lem5753304 _120477 _120519 _120521 op p' q') (@lem5753303 _120477 _120519 _120521 op p' q')). Qed.
Lemma lem5753306 {_120519 : Type'} (op : type1400 _120519) : (@monoidal _120519 op) = (@monoidal _120519 op).
Proof. exact (eq_refl (@monoidal _120519 op)). Qed.
Lemma lem5753307 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (q' : Prop) : term35 _120477 _120519 _120521 op q'.
Proof. exact (@lem5753305 _120477 _120519 _120521 op (@monoidal _120519 op) q'). Qed.
Lemma lem5753308 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (q' : Prop) : term36 _120477 _120519 _120521 op q'.
Proof. exact (@lem5753307 _120477 _120519 _120521 op q' (@lem5753306 _120519 op)). Qed.
Lemma lem5753309 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5753310 {_120519 : Type'} (op : type1400 _120519) : (@monoidal _120519 op) = ((@monoidal _120519 op) = True).
Proof. exact (@lem7 (@monoidal _120519 op)). Qed.
Lemma lem5753321 {A B : Type'} (f : A -> B) (op : type1400 B) : term37 A B f op.
Proof. exact (fun h0 : @monoidal B op => @lem5753283 A B f op h0). Qed.
Lemma lem5753322 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term37 _120477 _120519 f op.
Proof. exact (@lem5753321 _120477 _120519 f op). Qed.
Lemma lem5753324 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@monoidal _120519 op) = True.
Proof. exact (EQ_MP (@lem5753310 _120519 op) (@lem5753309 _120519 op h1)). Qed.
Lemma lem5753325 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : True = (@monoidal _120519 op).
Proof. exact (SYM (@lem5753324 _120519 op h1)). Qed.
Lemma lem5753326 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (EQ_MP (@lem5753325 _120519 op h1) (@lem0)). Qed.
Lemma lem5753327 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (@lem5753322 _120477 _120519 f op (@lem5753326 _120519 op h1)). Qed.
Lemma lem5753328 {_120519 : Type'} : (@eq _120519) = (@eq _120519).
Proof. exact (eq_refl (@eq _120519)). Qed.
Lemma lem5753329 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term38 _120477 _120519 op f) = (term39 _120519 op).
Proof. exact (MK_COMB (@lem5753328 _120519) (@lem5753327 _120477 _120519 f op h1)). Qed.
Lemma lem5753330 {_120519 : Type'} (op : type1400 _120519) : (@neutral _120519 op) = (@neutral _120519 op).
Proof. exact (eq_refl (@neutral _120519 op)). Qed.
Lemma lem5753331 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)) = ((@neutral _120519 op) = (@neutral _120519 op)).
Proof. exact (MK_COMB (@lem5753329 _120477 _120519 f op h1) (@lem5753330 _120519 op)). Qed.
Lemma lem5753333 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5753334 {_120519 : Type'} (x : _120519) : (x = x) = True.
Proof. exact (@lem5753333 _120519 x). Qed.
Lemma lem5753335 {_120519 : Type'} (op : type1400 _120519) : ((@neutral _120519 op) = (@neutral _120519 op)) = True.
Proof. exact (@lem5753334 _120519 (@neutral _120519 op)). Qed.
Lemma lem5753336 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)) = True.
Proof. exact (TRANS (@lem5753331 _120477 _120519 f op h1) (@lem5753335 _120519 op)). Qed.
Lemma lem5753337 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term40 _120477 _120519 op) = (term41 _120477 _120519).
Proof. exact (fun_ext (fun f : _120477 -> _120519 => @lem5753336 _120477 _120519 f op h1)). Qed.
Lemma lem5753338 {_120477 _120519 : Type'} : (@all (_120477 -> _120519)) = (@all (_120477 -> _120519)).
Proof. exact (eq_refl (@all (_120477 -> _120519))). Qed.
Lemma lem5753339 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term24 _120477 _120519 op) = (term42 _120477 _120519).
Proof. exact (MK_COMB (@lem5753338 _120477 _120519) (@lem5753337 _120477 _120519 op h1)). Qed.
Lemma lem5753341 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5753342 {_120477 _120519 : Type'} (t : Prop) : (term44 _120477 _120519 t) = t.
Proof. exact (@lem5753341 (_120477 -> _120519) t). Qed.
Lemma lem5753343 {_120477 _120519 : Type'} : (term42 _120477 _120519) = True.
Proof. exact (@lem5753342 _120477 _120519 True). Qed.
Lemma lem5753344 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term24 _120477 _120519 op) = True.
Proof. exact (TRANS (@lem5753339 _120477 _120519 op h1) (@lem5753343 _120477 _120519)). Qed.
Lemma lem5753345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753346 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term45 _120477 _120519 op) = (and True).
Proof. exact (MK_COMB (@lem5753345) (@lem5753344 _120477 _120519 op h1)). Qed.
Lemma lem5753362 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term26 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5753363 (p : Prop) (q : Prop) (p' : Prop) : term27 p q p'.
Proof. exact (fun q' : Prop => @lem5753362 p q p' q'). Qed.
Lemma lem5753364 (p : Prop) (q : Prop) : term28 p q.
Proof. exact (fun p' : Prop => @lem5753363 p q p'). Qed.
Lemma lem5753365 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term46 _120519 _120521 x op s f.
Proof. exact (@lem5753364 (@FINITE _120521 s) ((term47 _120519 _120521 op x s f) = (term48 _120519 _120521 x op s f))). Qed.
Lemma lem5753366 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) (p' : Prop) : term49 _120519 _120521 x op s f p'.
Proof. exact (@lem5753365 _120519 _120521 x op s f p'). Qed.
Lemma lem5753367 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) (p' : Prop) : (term49 _120519 _120521 x op s f p') = (term50 _120519 _120521 x op s f p').
Proof. exact (eq_refl (term49 _120519 _120521 x op s f p')). Qed.
Lemma lem5753368 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) (p' : Prop) : term50 _120519 _120521 x op s f p'.
Proof. exact (EQ_MP (@lem5753367 _120519 _120521 x op s f p') (@lem5753366 _120519 _120521 x op s f p')). Qed.
Lemma lem5753369 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) (p' : Prop) (q' : Prop) : term51 _120519 _120521 x op s f p' q'.
Proof. exact (@lem5753368 _120519 _120521 x op s f p' q'). Qed.
Lemma lem5753370 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) (p' : Prop) (q' : Prop) : (term51 _120519 _120521 x op s f p' q') = (term52 _120519 _120521 x op s f p' q').
Proof. exact (eq_refl (term51 _120519 _120521 x op s f p' q')). Qed.
Lemma lem5753371 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) (p' : Prop) (q' : Prop) : term52 _120519 _120521 x op s f p' q'.
Proof. exact (EQ_MP (@lem5753370 _120519 _120521 x op s f p' q') (@lem5753369 _120519 _120521 x op s f p' q')). Qed.
Lemma lem5753372 {_120521 : Type'} (s : _120521 -> Prop) : (@FINITE _120521 s) = (@FINITE _120521 s).
Proof. exact (eq_refl (@FINITE _120521 s)). Qed.
Lemma lem5753373 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (q' : Prop) : term53 _120519 _120521 x op f s q'.
Proof. exact (@lem5753371 _120519 _120521 x op s f (@FINITE _120521 s) q'). Qed.
Lemma lem5753374 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (q' : Prop) : term54 _120519 _120521 x op f s q'.
Proof. exact (@lem5753373 _120519 _120521 x op f s q' (@lem5753372 _120521 s)). Qed.
Lemma lem5753375 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5753376 {_120521 : Type'} (s : _120521 -> Prop) : (@FINITE _120521 s) = ((@FINITE _120521 s) = True).
Proof. exact (@lem7 (@FINITE _120521 s)). Qed.
Lemma lem5753381 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term23 A B x op s f.
Proof. exact (EQ_MP (@lem5753278 A B x op s f) (@lem5753271 A B x op s f)). Qed.
Lemma lem5753382 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term55 _120519 _120521 x op s f.
Proof. exact (@lem5753381 _120521 _120519 x op s f). Qed.
Lemma lem5753386 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term56 _119939 _119945 op f s.
Proof. exact (fun h0 : @FINITE _119939 s => @lem5753247 _119939 _119945 op f s h0). Qed.
Lemma lem5753387 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) : term57 _120519 _120521 op f s.
Proof. exact (@lem5753386 _120521 _120519 op f s). Qed.
Lemma lem5753389 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : (@FINITE _120521 s) = True.
Proof. exact (EQ_MP (@lem5753376 _120521 s) (@lem5753375 _120521 s h1)). Qed.
Lemma lem5753390 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : True = (@FINITE _120521 s).
Proof. exact (SYM (@lem5753389 _120521 s h1)). Qed.
Lemma lem5753391 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (EQ_MP (@lem5753390 _120521 s h1) (@lem0)). Qed.
Lemma lem5753392 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : (term58 _120519 _120521 op f s) = True.
Proof. exact (@lem5753387 _120519 _120521 op f s (@lem5753391 _120521 s h1)). Qed.
Lemma lem5753393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5753394 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : (term59 _120519 _120521 op f s) = (and True).
Proof. exact (MK_COMB (@lem5753393) (@lem5753392 _120519 _120521 op f s h1)). Qed.
Lemma lem5753396 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@monoidal _120519 op) = True.
Proof. exact (EQ_MP (@lem5753310 _120519 op) (@lem5753309 _120519 op h1)). Qed.
Lemma lem5753397 {_120519 _120521 : Type'} (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term60 _120519 _120521 f s op) = (True /\ True).
Proof. exact (MK_COMB (@lem5753394 _120519 _120521 op f s h1) (@lem5753396 _120519 op h2)). Qed.
Lemma lem5753399 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5753400 : (True /\ True) = True.
Proof. exact (@lem5753399 True). Qed.
Lemma lem5753401 {_120519 _120521 : Type'} (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term60 _120519 _120521 f s op) = True.
Proof. exact (TRANS (@lem5753397 _120519 _120521 f s op h1 h2) (@lem5753400)). Qed.
Lemma lem5753402 {_120519 _120521 : Type'} (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : True = (term60 _120519 _120521 f s op).
Proof. exact (SYM (@lem5753401 _120519 _120521 f s op h1 h2)). Qed.
Lemma lem5753403 {_120519 _120521 : Type'} (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : term60 _120519 _120521 f s op.
Proof. exact (EQ_MP (@lem5753402 _120519 _120521 f s op h1 h2) (@lem0)). Qed.
Lemma lem5753404 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term47 _120519 _120521 op x s f) = (term48 _120519 _120521 x op s f).
Proof. exact (@lem5753382 _120519 _120521 x op s f (@lem5753403 _120519 _120521 f s op h1 h2)). Qed.
Lemma lem5753438 {_120519 : Type'} : (@eq _120519) = (@eq _120519).
Proof. exact (eq_refl (@eq _120519)). Qed.
Lemma lem5753439 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term61 _120519 _120521 op x s f) = (term62 _120519 _120521 x op s f).
Proof. exact (MK_COMB (@lem5753438 _120519) (@lem5753404 _120519 _120521 x f s op h1 h2)). Qed.
Lemma lem5753506 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term48 _120519 _120521 x op s f) = (term48 _120519 _120521 x op s f).
Proof. exact (eq_refl (term48 _120519 _120521 x op s f)). Qed.
Lemma lem5753507 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : ((term47 _120519 _120521 op x s f) = (term48 _120519 _120521 x op s f)) = ((term48 _120519 _120521 x op s f) = (term48 _120519 _120521 x op s f)).
Proof. exact (MK_COMB (@lem5753439 _120519 _120521 x f s op h1 h2) (@lem5753506 _120519 _120521 x op s f)). Qed.
Lemma lem5753509 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5753510 {_120519 : Type'} (x : _120519) : (x = x) = True.
Proof. exact (@lem5753509 _120519 x). Qed.
Lemma lem5753511 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : ((term48 _120519 _120521 x op s f) = (term48 _120519 _120521 x op s f)) = True.
Proof. exact (@lem5753510 _120519 (term48 _120519 _120521 x op s f)). Qed.
Lemma lem5753512 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : ((term47 _120519 _120521 op x s f) = (term48 _120519 _120521 x op s f)) = True.
Proof. exact (TRANS (@lem5753507 _120519 _120521 x f s op h1 h2) (@lem5753511 _120519 _120521 x op s f)). Qed.
Lemma lem5753513 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term63 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5753512 _120519 _120521 x f s op h0 h1). Qed.
Lemma lem5753514 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) : term64 _120519 _120521 x op f s.
Proof. exact (@lem5753374 _120519 _120521 x op f s True). Qed.
Lemma lem5753515 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term65 _120519 _120521 x op s f) = (term66 _120521 s).
Proof. exact (@lem5753514 _120519 _120521 x op f s (@lem5753513 _120519 _120521 x s f op h1)). Qed.
Lemma lem5753517 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5753518 {_120521 : Type'} (s : _120521 -> Prop) : (term66 _120521 s) = True.
Proof. exact (@lem5753517 (@FINITE _120521 s)). Qed.
Lemma lem5753519 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term65 _120519 _120521 x op s f) = True.
Proof. exact (TRANS (@lem5753515 _120519 _120521 x f s op h1) (@lem5753518 _120521 s)). Qed.
Lemma lem5753520 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term67 _120519 _120521 x op f) = (term68 _120521).
Proof. exact (fun_ext (fun s : _120521 -> Prop => @lem5753519 _120519 _120521 x s f op h1)). Qed.
Lemma lem5753521 {_120521 : Type'} : (@all (_120521 -> Prop)) = (@all (_120521 -> Prop)).
Proof. exact (eq_refl (@all (_120521 -> Prop))). Qed.
Lemma lem5753522 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term69 _120519 _120521 x op f) = (term70 _120521).
Proof. exact (MK_COMB (@lem5753521 _120521) (@lem5753520 _120519 _120521 x f op h1)). Qed.
Lemma lem5753524 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5753525 {_120521 : Type'} (t : Prop) : (term71 _120521 t) = t.
Proof. exact (@lem5753524 (_120521 -> Prop) t). Qed.
Lemma lem5753526 {_120521 : Type'} : (term70 _120521) = True.
Proof. exact (@lem5753525 _120521 True). Qed.
Lemma lem5753527 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term69 _120519 _120521 x op f) = True.
Proof. exact (TRANS (@lem5753522 _120519 _120521 x f op h1) (@lem5753526 _120521)). Qed.
Lemma lem5753528 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term72 _120519 _120521 op f) = (term73 _120521).
Proof. exact (fun_ext (fun x : _120521 => @lem5753527 _120519 _120521 x f op h1)). Qed.
Lemma lem5753529 {_120521 : Type'} : (@all _120521) = (@all _120521).
Proof. exact (eq_refl (@all _120521)). Qed.
Lemma lem5753530 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term74 _120519 _120521 op f) = (term75 _120521).
Proof. exact (MK_COMB (@lem5753529 _120521) (@lem5753528 _120519 _120521 f op h1)). Qed.
Lemma lem5753532 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5753533 {_120521 : Type'} (t : Prop) : (term43 _120521 t) = t.
Proof. exact (@lem5753532 _120521 t). Qed.
Lemma lem5753534 {_120521 : Type'} : (term75 _120521) = True.
Proof. exact (@lem5753533 _120521 True). Qed.
Lemma lem5753535 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term74 _120519 _120521 op f) = True.
Proof. exact (TRANS (@lem5753530 _120519 _120521 f op h1) (@lem5753534 _120521)). Qed.
Lemma lem5753536 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term76 _120519 _120521 op) = (term77 _120519 _120521).
Proof. exact (fun_ext (fun f : _120521 -> _120519 => @lem5753535 _120519 _120521 f op h1)). Qed.
Lemma lem5753537 {_120519 _120521 : Type'} : (@all (_120521 -> _120519)) = (@all (_120521 -> _120519)).
Proof. exact (eq_refl (@all (_120521 -> _120519))). Qed.
Lemma lem5753538 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term78 _120519 _120521 op) = (term79 _120519 _120521).
Proof. exact (MK_COMB (@lem5753537 _120519 _120521) (@lem5753536 _120519 _120521 op h1)). Qed.
Lemma lem5753540 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5753541 {_120519 _120521 : Type'} (t : Prop) : (term80 _120519 _120521 t) = t.
Proof. exact (@lem5753540 (_120521 -> _120519) t). Qed.
Lemma lem5753542 {_120519 _120521 : Type'} : (term79 _120519 _120521) = True.
Proof. exact (@lem5753541 _120519 _120521 True). Qed.
Lemma lem5753543 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term78 _120519 _120521 op) = True.
Proof. exact (TRANS (@lem5753538 _120519 _120521 op h1) (@lem5753542 _120519 _120521)). Qed.
Lemma lem5753544 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term30 _120477 _120519 _120521 op) = (True /\ True).
Proof. exact (MK_COMB (@lem5753346 _120477 _120519 op h1) (@lem5753543 _120519 _120521 op h1)). Qed.
Lemma lem5753546 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5753547 : (True /\ True) = True.
Proof. exact (@lem5753546 True). Qed.
Lemma lem5753548 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : (term30 _120477 _120519 _120521 op) = True.
Proof. exact (TRANS (@lem5753544 _120477 _120519 _120521 op h1) (@lem5753547)). Qed.
Lemma lem5753549 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term81 _120477 _120519 _120521 op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5753548 _120477 _120519 _120521 op h0). Qed.
Lemma lem5753550 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term82 _120477 _120519 _120521 op.
Proof. exact (@lem5753308 _120477 _120519 _120521 op True). Qed.
Lemma lem5753551 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term83 _120477 _120519 _120521 op) = (term84 _120519 op).
Proof. exact (@lem5753550 _120477 _120519 _120521 op (@lem5753549 _120477 _120519 _120521 op)). Qed.
Lemma lem5753553 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5753554 {_120519 : Type'} (op : type1400 _120519) : (term84 _120519 op) = True.
Proof. exact (@lem5753553 (@monoidal _120519 op)). Qed.
Lemma lem5753555 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term83 _120477 _120519 _120521 op) = True.
Proof. exact (TRANS (@lem5753551 _120477 _120519 _120521 op) (@lem5753554 _120519 op)). Qed.
Lemma lem5753556 {_120477 _120519 _120521 : Type'} : (term85 _120477 _120519 _120521) = (term86 _120519).
Proof. exact (fun_ext (fun op : type1400 _120519 => @lem5753555 _120477 _120519 _120521 op)). Qed.
Lemma lem5753557 {_120519 : Type'} : (@all (_120519 -> _120519 -> _120519)) = (@all (_120519 -> _120519 -> _120519)).
Proof. exact (eq_refl (@all (_120519 -> _120519 -> _120519))). Qed.
Lemma lem5753558 {_120477 _120519 _120521 : Type'} : (term87 _120477 _120519 _120521) = (term88 _120519).
Proof. exact (MK_COMB (@lem5753557 _120519) (@lem5753556 _120477 _120519 _120521)). Qed.
Lemma lem5753560 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5753561 {_120519 : Type'} (t : Prop) : (term89 _120519 t) = t.
Proof. exact (@lem5753560 (type1400 _120519) t). Qed.
Lemma lem5753562 {_120519 : Type'} : (term88 _120519) = True.
Proof. exact (@lem5753561 _120519 True). Qed.
Lemma lem5753563 {_120477 _120519 _120521 : Type'} : (term87 _120477 _120519 _120521) = True.
Proof. exact (TRANS (@lem5753558 _120477 _120519 _120521) (@lem5753562 _120519)). Qed.
Lemma lem5753564 {_120477 _120519 _120521 : Type'} : True = (term87 _120477 _120519 _120521).
Proof. exact (SYM (@lem5753563 _120477 _120519 _120521)). Qed.
Lemma lem5753565 {_120477 _120519 _120521 : Type'} : term87 _120477 _120519 _120521.
Proof. exact (EQ_MP (@lem5753564 _120477 _120519 _120521) (@lem0)). Qed.
