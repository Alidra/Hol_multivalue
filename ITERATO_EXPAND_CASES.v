Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATO_EXPAND_CASES_term_abbrevs.
Require Import ITERATO_SUPPORT_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm6401305_spec.
Require Import thm82_spec.
Lemma lem6449239 {A K : Type'} (dom : A -> Prop) : term0 A K dom.
Proof. exact (@lem6401305 A K dom). Qed.
Lemma lem6449240 {A K : Type'} (dom : A -> Prop) : (term0 A K dom) = (term1 A K dom).
Proof. exact (eq_refl (term0 A K dom)). Qed.
Lemma lem6449241 {A K : Type'} (dom : A -> Prop) : term1 A K dom.
Proof. exact (EQ_MP (@lem6449240 A K dom) (@lem6449239 A K dom)). Qed.
Lemma lem6449242 {A K : Type'} (dom : A -> Prop) (neut : A) : term2 A K dom neut.
Proof. exact (@lem6449241 A K dom neut). Qed.
Lemma lem6449243 {A K : Type'} (dom : A -> Prop) (neut : A) : (term2 A K dom neut) = (term3 A K dom neut).
Proof. exact (eq_refl (term2 A K dom neut)). Qed.
Lemma lem6449244 {A K : Type'} (dom : A -> Prop) (neut : A) : term3 A K dom neut.
Proof. exact (EQ_MP (@lem6449243 A K dom neut) (@lem6449242 A K dom neut)). Qed.
Lemma lem6449245 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term4 A K dom neut op.
Proof. exact (@lem6449244 A K dom neut op). Qed.
Lemma lem6449246 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term4 A K dom neut op) = (term5 A K op dom neut).
Proof. exact (eq_refl (term4 A K dom neut op)). Qed.
Lemma lem6449247 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : term5 A K op dom neut.
Proof. exact (EQ_MP (@lem6449246 A K op dom neut) (@lem6449245 A K dom neut op)). Qed.
Lemma lem6449248 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) (ltle : type1402 K) : term6 A K op dom neut ltle.
Proof. exact (@lem6449247 A K op dom neut ltle). Qed.
Lemma lem6449249 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term6 A K op dom neut ltle) = (term7 A K op ltle dom neut).
Proof. exact (eq_refl (term6 A K op dom neut ltle)). Qed.
Lemma lem6449250 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : term7 A K op ltle dom neut.
Proof. exact (EQ_MP (@lem6449249 A K op ltle dom neut) (@lem6449248 A K op dom neut ltle)). Qed.
Lemma lem6449251 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (k : K -> Prop) : term8 A K op ltle dom neut k.
Proof. exact (@lem6449250 A K op ltle dom neut k). Qed.
Lemma lem6449252 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term8 A K op ltle dom neut k) = (term9 A K op ltle k dom neut).
Proof. exact (eq_refl (term8 A K op ltle dom neut k)). Qed.
Lemma lem6449253 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : term9 A K op ltle k dom neut.
Proof. exact (EQ_MP (@lem6449252 A K op ltle k dom neut) (@lem6449251 A K op ltle dom neut k)). Qed.
Lemma lem6449254 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : term10 A K op ltle k dom neut f.
Proof. exact (@lem6449253 A K op ltle k dom neut f). Qed.
Lemma lem6449255 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term10 A K op ltle k dom neut f) = ((@iterato A K dom neut op ltle k f) = (term11 A K op ltle k f dom neut)).
Proof. exact (eq_refl (term10 A K op ltle k dom neut f)). Qed.
Lemma lem6449257 {A K : Type'} (dom : A -> Prop) : term12 A K dom.
Proof. exact (@lem6449238 A K dom). Qed.
Lemma lem6449258 {A K : Type'} (dom : A -> Prop) : (term12 A K dom) = (term13 A K dom).
Proof. exact (eq_refl (term12 A K dom)). Qed.
Lemma lem6449259 {A K : Type'} (dom : A -> Prop) : term13 A K dom.
Proof. exact (EQ_MP (@lem6449258 A K dom) (@lem6449257 A K dom)). Qed.
Lemma lem6449260 {A K : Type'} (dom : A -> Prop) (neut : A) : term14 A K dom neut.
Proof. exact (@lem6449259 A K dom neut). Qed.
Lemma lem6449261 {A K : Type'} (dom : A -> Prop) (neut : A) : (term14 A K dom neut) = (term15 A K dom neut).
Proof. exact (eq_refl (term14 A K dom neut)). Qed.
Lemma lem6449262 {A K : Type'} (dom : A -> Prop) (neut : A) : term15 A K dom neut.
Proof. exact (EQ_MP (@lem6449261 A K dom neut) (@lem6449260 A K dom neut)). Qed.
Lemma lem6449263 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term16 A K dom neut op.
Proof. exact (@lem6449262 A K dom neut op). Qed.
Lemma lem6449264 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term16 A K dom neut op) = (term17 A K dom neut op).
Proof. exact (eq_refl (term16 A K dom neut op)). Qed.
Lemma lem6449265 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term17 A K dom neut op.
Proof. exact (EQ_MP (@lem6449264 A K dom neut op) (@lem6449263 A K dom neut op)). Qed.
Lemma lem6449266 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term18 A K dom neut op ltle.
Proof. exact (@lem6449265 A K dom neut op ltle). Qed.
Lemma lem6449267 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term18 A K dom neut op ltle) = (term19 A K dom neut op ltle).
Proof. exact (eq_refl (term18 A K dom neut op ltle)). Qed.
Lemma lem6449268 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term19 A K dom neut op ltle.
Proof. exact (EQ_MP (@lem6449267 A K dom neut op ltle) (@lem6449266 A K dom neut op ltle)). Qed.
Lemma lem6449269 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : term20 A K dom neut op ltle k.
Proof. exact (@lem6449268 A K dom neut op ltle k). Qed.
Lemma lem6449270 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : (term20 A K dom neut op ltle k) = (term21 A K dom neut op ltle k).
Proof. exact (eq_refl (term20 A K dom neut op ltle k)). Qed.
Lemma lem6449271 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : term21 A K dom neut op ltle k.
Proof. exact (EQ_MP (@lem6449270 A K dom neut op ltle k) (@lem6449269 A K dom neut op ltle k)). Qed.
Lemma lem6449272 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term22 A K dom neut op ltle k f.
Proof. exact (@lem6449271 A K dom neut op ltle k f). Qed.
Lemma lem6449273 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term22 A K dom neut op ltle k f) = ((term23 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f)).
Proof. exact (eq_refl (term22 A K dom neut op ltle k f)). Qed.
Lemma lem6449275 {A : Type'} (_474 : A) (_475 : Prop) (_476 : A -> Prop) (_477 : A) : (term24 A _476 _475 _474 _477) = (term25 A _474 _475 _476 _477).
Proof. exact (@lem13473 A _474 _475 _476 _477). Qed.
Lemma lem6449276 {A K : Type'} (_474 : A) (_475 : Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (_477 : A) : (term26 A K dom neut op ltle k f _475 _474 _477) = (term27 A K _474 _475 dom neut op ltle k f _477).
Proof. exact (@lem6449275 A _474 _475 (term28 A K dom neut op ltle k f) _477). Qed.
Lemma lem6449277 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : (term29 A K op ltle k dom f neut) = (term30 A K dom op ltle k f neut).
Proof. exact (@lem6449276 A K (term23 A K op ltle k dom neut f) (term31 A K k f dom neut) dom neut op ltle k f neut). Qed.
Lemma lem6449278 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : (term32 A K dom op ltle k f neut) = ((@iterato A K dom neut op ltle k f) = neut).
Proof. exact (eq_refl (term32 A K dom op ltle k f neut)). Qed.
Lemma lem6449279 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term33 A K k f dom neut) = (term33 A K k f dom neut).
Proof. exact (eq_refl (term33 A K k f dom neut)). Qed.
Lemma lem6449280 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : (term34 A K dom op ltle k f neut) = (term35 A K dom op ltle k f neut).
Proof. exact (MK_COMB (@lem6449279 A K k f dom neut) (@lem6449278 A K dom op ltle k f neut)). Qed.
Lemma lem6449281 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term36 A K op ltle k dom neut f) = ((@iterato A K dom neut op ltle k f) = (term23 A K op ltle k dom neut f)).
Proof. exact (eq_refl (term36 A K op ltle k dom neut f)). Qed.
Lemma lem6449282 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term37 A K k f dom neut) = (term37 A K k f dom neut).
Proof. exact (eq_refl (term37 A K k f dom neut)). Qed.
Lemma lem6449283 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term38 A K op ltle k dom neut f) = (term39 A K op ltle k dom neut f).
Proof. exact (MK_COMB (@lem6449282 A K k f dom neut) (@lem6449281 A K op ltle k dom neut f)). Qed.
Lemma lem6449284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6449285 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term40 A K op ltle k dom neut f) = (term41 A K op ltle k dom neut f).
Proof. exact (MK_COMB (@lem6449284) (@lem6449283 A K op ltle k dom neut f)). Qed.
Lemma lem6449286 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : (term30 A K dom op ltle k f neut) = (term42 A K dom op ltle k f neut).
Proof. exact (MK_COMB (@lem6449285 A K op ltle k dom neut f) (@lem6449280 A K dom op ltle k f neut)). Qed.
Lemma lem6449287 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term29 A K op ltle k dom f neut) = ((@iterato A K dom neut op ltle k f) = (term43 A K op ltle k dom f neut)).
Proof. exact (eq_refl (term29 A K op ltle k dom f neut)). Qed.
Lemma lem6449288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6449289 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term44 A K op ltle k dom f neut) = (term45 A K op ltle k dom f neut).
Proof. exact (MK_COMB (@lem6449288) (@lem6449287 A K op ltle k dom f neut)). Qed.
Lemma lem6449290 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : ((term29 A K op ltle k dom f neut) = (term30 A K dom op ltle k f neut)) = (((@iterato A K dom neut op ltle k f) = (term43 A K op ltle k dom f neut)) = (term42 A K dom op ltle k f neut)).
Proof. exact (MK_COMB (@lem6449289 A K op ltle k dom f neut) (@lem6449286 A K dom op ltle k f neut)). Qed.
Lemma lem6449291 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : ((@iterato A K dom neut op ltle k f) = (term43 A K op ltle k dom f neut)) = (term42 A K dom op ltle k f neut).
Proof. exact (EQ_MP (@lem6449290 A K dom op ltle k f neut) (@lem6449277 A K dom op ltle k f neut)). Qed.
Lemma lem6449292 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term42 A K dom op ltle k f neut) = ((@iterato A K dom neut op ltle k f) = (term43 A K op ltle k dom f neut)).
Proof. exact (SYM (@lem6449291 A K dom op ltle k f neut)). Qed.
Lemma lem6449310 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : term46 A K k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6449330 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term23 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f).
Proof. exact (EQ_MP (@lem6449273 A K dom neut op ltle k f) (@lem6449272 A K dom neut op ltle k f)). Qed.
Lemma lem6449331 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term23 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f).
Proof. exact (@lem6449330 A K dom neut op ltle k f). Qed.
Lemma lem6449332 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term47 A K dom neut op ltle k f) = (term47 A K dom neut op ltle k f).
Proof. exact (eq_refl (term47 A K dom neut op ltle k f)). Qed.
Lemma lem6449333 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : ((@iterato A K dom neut op ltle k f) = (term23 A K op ltle k dom neut f)) = ((@iterato A K dom neut op ltle k f) = (@iterato A K dom neut op ltle k f)).
Proof. exact (MK_COMB (@lem6449332 A K dom neut op ltle k f) (@lem6449331 A K dom neut op ltle k f)). Qed.
Lemma lem6449335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6449336 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6449335 A x). Qed.
Lemma lem6449337 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : ((@iterato A K dom neut op ltle k f) = (@iterato A K dom neut op ltle k f)) = True.
Proof. exact (@lem6449336 A (@iterato A K dom neut op ltle k f)). Qed.
Lemma lem6449338 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : ((@iterato A K dom neut op ltle k f) = (term23 A K op ltle k dom neut f)) = True.
Proof. exact (TRANS (@lem6449333 A K dom neut op ltle k f) (@lem6449337 A K dom neut op ltle k f)). Qed.
Lemma lem6449339 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : True = ((@iterato A K dom neut op ltle k f) = (term23 A K op ltle k dom neut f)).
Proof. exact (SYM (@lem6449338 A K op ltle k dom neut f)). Qed.
Lemma lem6449342 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (@iterato A K dom neut op ltle k f) = (term11 A K op ltle k f dom neut).
Proof. exact (EQ_MP (@lem6449255 A K op ltle k f dom neut) (@lem6449254 A K op ltle k dom neut f)). Qed.
Lemma lem6449343 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (@iterato A K dom neut op ltle k f) = (term11 A K op ltle k f dom neut).
Proof. exact (@lem6449342 A K op ltle k f dom neut). Qed.
Lemma lem6449344 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6449345 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term47 A K dom neut op ltle k f) = (term48 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6449344 A) (@lem6449343 A K op ltle k f dom neut)). Qed.
Lemma lem6449346 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6449347 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((@iterato A K dom neut op ltle k f) = neut) = ((term11 A K op ltle k f dom neut) = neut).
Proof. exact (MK_COMB (@lem6449345 A K op ltle k f dom neut) (@lem6449346 A neut)). Qed.
Lemma lem6449348 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : ((term11 A K op ltle k f dom neut) = neut) = ((@iterato A K dom neut op ltle k f) = neut).
Proof. exact (SYM (@lem6449347 A K op ltle k f dom neut)). Qed.
Lemma lem6449349 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : term49 A K k f dom neut.
Proof. exact (@lem82 (term31 A K k f dom neut)). Qed.
Lemma lem6449356 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term31 A K k f dom neut) = False.
Proof. exact (@lem6449349 A K k f dom neut (@lem6449310 A K k f dom neut h1)). Qed.
Lemma lem6449357 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term31 A K k f dom neut) = False.
Proof. exact (@lem6449356 A K k f dom neut h1). Qed.
Lemma lem6449358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6449359 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term50 A K k f dom neut) = (and False).
Proof. exact (MK_COMB (@lem6449358) (@lem6449357 A K k f dom neut h1)). Qed.
Lemma lem6449368 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term51 A K k f dom neut) = (term51 A K k f dom neut).
Proof. exact (eq_refl (term51 A K k f dom neut)). Qed.
Lemma lem6449369 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term52 A K k f dom neut) = (term53 A K k f dom neut).
Proof. exact (MK_COMB (@lem6449359 A K k f dom neut h1) (@lem6449368 A K k f dom neut)). Qed.
Lemma lem6449371 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6449372 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term53 A K k f dom neut) = False.
Proof. exact (@lem6449371 (term51 A K k f dom neut)). Qed.
Lemma lem6449373 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term52 A K k f dom neut) = False.
Proof. exact (TRANS (@lem6449369 A K k f dom neut h1) (@lem6449372 A K k f dom neut)). Qed.
Lemma lem6449374 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem6449375 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term54 A K k f dom neut) = (@COND A False).
Proof. exact (MK_COMB (@lem6449374 A) (@lem6449373 A K k f dom neut h1)). Qed.
Lemma lem6449420 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term55 A K op ltle k f dom neut) = (term55 A K op ltle k f dom neut).
Proof. exact (eq_refl (term55 A K op ltle k f dom neut)). Qed.
Lemma lem6449421 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term56 A K op ltle k f dom neut) = (term57 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6449375 A K k f dom neut h1) (@lem6449420 A K op ltle k f dom neut)). Qed.
Lemma lem6449422 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6449423 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term11 A K op ltle k f dom neut) = (term58 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6449421 A K op ltle k f dom neut h1) (@lem6449422 A neut)). Qed.
Lemma lem6449425 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6449426 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem6449425 A t1 t2). Qed.
Lemma lem6449427 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term58 A K op ltle k f dom neut) = neut.
Proof. exact (@lem6449426 A (term55 A K op ltle k f dom neut) neut). Qed.
Lemma lem6449428 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term11 A K op ltle k f dom neut) = neut.
Proof. exact (TRANS (@lem6449423 A K op ltle k f dom neut h1) (@lem6449427 A K op ltle k f dom neut)). Qed.
Lemma lem6449429 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6449430 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term48 A K op ltle k f dom neut) = (@eq A neut).
Proof. exact (MK_COMB (@lem6449429 A) (@lem6449428 A K op ltle k f dom neut h1)). Qed.
Lemma lem6449431 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6449432 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : ((term11 A K op ltle k f dom neut) = neut) = (neut = neut).
Proof. exact (MK_COMB (@lem6449430 A K op ltle k f dom neut h1) (@lem6449431 A neut)). Qed.
Lemma lem6449434 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6449435 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6449434 A x). Qed.
Lemma lem6449436 {A : Type'} (neut : A) : (neut = neut) = True.
Proof. exact (@lem6449435 A neut). Qed.
Lemma lem6449437 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : ((term11 A K op ltle k f dom neut) = neut) = True.
Proof. exact (TRANS (@lem6449432 A K op ltle k f dom neut h1) (@lem6449436 A neut)). Qed.
Lemma lem6449438 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : True = ((term11 A K op ltle k f dom neut) = neut).
Proof. exact (SYM (@lem6449437 A K op ltle k f dom neut h1)). Qed.
Lemma lem6449439 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term11 A K op ltle k f dom neut) = neut.
Proof. exact (EQ_MP (@lem6449438 A K op ltle k f dom neut h1) (@lem0)). Qed.
Lemma lem6449441 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (@iterato A K dom neut op ltle k f) = neut.
Proof. exact (EQ_MP (@lem6449348 A K dom op ltle k f neut) (@lem6449439 A K op ltle k f dom neut h1)). Qed.
Lemma lem6449442 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (term46 A K k f dom neut) = ((@iterato A K dom neut op ltle k f) = neut).
Proof. exact (prop_ext (fun h2 : term46 A K k f dom neut => @lem6449441 A K op ltle k f dom neut h1) (fun h2 : (@iterato A K dom neut op ltle k f) = neut => @lem6449310 A K k f dom neut h1)). Qed.
Lemma lem6449443 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term46 A K k f dom neut) : (@iterato A K dom neut op ltle k f) = neut.
Proof. exact (EQ_MP (@lem6449442 A K op ltle k f dom neut h1) (@lem6449310 A K k f dom neut h1)). Qed.
Lemma lem6449444 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : term35 A K dom op ltle k f neut.
Proof. exact (fun h0 : term46 A K k f dom neut => @lem6449443 A K op ltle k f dom neut h0). Qed.
Lemma lem6449445 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (@iterato A K dom neut op ltle k f) = (term23 A K op ltle k dom neut f).
Proof. exact (EQ_MP (@lem6449339 A K op ltle k dom neut f) (@lem0)). Qed.
Lemma lem6449446 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : term39 A K op ltle k dom neut f.
Proof. exact (fun h0 : term31 A K k f dom neut => @lem6449445 A K op ltle k dom neut f). Qed.
Lemma lem6449447 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (neut : A) : term42 A K dom op ltle k f neut.
Proof. exact (conj (@lem6449446 A K op ltle k dom neut f) (@lem6449444 A K dom op ltle k f neut)). Qed.
Lemma lem6449448 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle k f) = (term43 A K op ltle k dom f neut).
Proof. exact (EQ_MP (@lem6449292 A K op ltle k dom f neut) (@lem6449447 A K dom op ltle k f neut)). Qed.
Lemma lem6449453 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : term59 A K op ltle k dom neut.
Proof. exact (fun f : K -> A => @lem6449448 A K op ltle k dom f neut). Qed.
Lemma lem6449458 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : term60 A K op ltle dom neut.
Proof. exact (fun k : K -> Prop => @lem6449453 A K op ltle k dom neut). Qed.
Lemma lem6449463 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : term61 A K op dom neut.
Proof. exact (fun ltle : type1402 K => @lem6449458 A K op ltle dom neut). Qed.
Lemma lem6449468 {A K : Type'} (dom : A -> Prop) (neut : A) : term62 A K dom neut.
Proof. exact (fun op : type1400 A => @lem6449463 A K op dom neut). Qed.
Lemma lem6449473 {A K : Type'} (dom : A -> Prop) : term63 A K dom.
Proof. exact (fun neut : A => @lem6449468 A K dom neut). Qed.
Lemma lem6449478 {A K : Type'} : term64 A K.
Proof. exact (fun dom : A -> Prop => @lem6449473 A K dom). Qed.
