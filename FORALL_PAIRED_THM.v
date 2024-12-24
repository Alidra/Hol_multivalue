Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_PAIRED_THM_term_abbrevs.
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
Lemma lem55244 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term0 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem55245 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term0 _5106 _5107 P) = ((term1 _5106 _5107 P) = (term2 _5106 _5107 P)).
Proof. exact (eq_refl (term0 _5106 _5107 P)). Qed.
Lemma lem55247 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem55248 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem55249 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem55248 A B f) (@lem55247 A B f)). Qed.
Lemma lem55250 {A B : Type'} (f : A -> B) (g : A -> B) : term5 A B f g.
Proof. exact (@lem55249 A B f g). Qed.
Lemma lem55251 {A B : Type'} (f : A -> B) (g : A -> B) : (term5 A B f g) = ((f = g) = (term6 A B f g)).
Proof. exact (eq_refl (term5 A B f g)). Qed.
Lemma lem55254 {A : Type'} : (@all A) = (term7 A).
Proof. exact (@all_def A). Qed.
Lemma lem55255 {_5733 _5734 : Type'} : (@all (prod _5734 _5733)) = (term8 _5733 _5734).
Proof. exact (@lem55254 (prod _5734 _5733)). Qed.
Lemma lem55256 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term9 _5733 _5734 P) = (term9 _5733 _5734 P).
Proof. exact (eq_refl (term9 _5733 _5734 P)). Qed.
Lemma lem55257 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term10 _5733 _5734 P) = (term11 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55255 _5733 _5734) (@lem55256 _5733 _5734 P)). Qed.
Lemma lem55258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55259 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term12 _5733 _5734 P) = (term13 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55258) (@lem55257 _5733 _5734 P)). Qed.
Lemma lem55260 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term14 _5733 _5734 P) = (term14 _5733 _5734 P).
Proof. exact (eq_refl (term14 _5733 _5734 P)). Qed.
Lemma lem55261 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term10 _5733 _5734 P) = (term14 _5733 _5734 P)) = ((term11 _5733 _5734 P) = (term14 _5733 _5734 P)).
Proof. exact (MK_COMB (@lem55259 _5733 _5734 P) (@lem55260 _5733 _5734 P)). Qed.
Lemma lem55262 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term11 _5733 _5734 P) = (term14 _5733 _5734 P)) = ((term10 _5733 _5734 P) = (term14 _5733 _5734 P)).
Proof. exact (SYM (@lem55261 _5733 _5734 P)). Qed.
Lemma lem55268 {A B : Type'} (f : A -> B) (y : A) : (term15 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55269 {_5733 _5734 : Type'} (f : type330 _5733 _5734) (y : type1223 _5733 _5734) : (term16 _5733 _5734 f y) = (f y).
Proof. exact (@lem55268 (type1223 _5733 _5734) Prop f y). Qed.
Lemma lem55270 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term17 _5733 _5734 P) = (term11 _5733 _5734 P).
Proof. exact (@lem55269 _5733 _5734 (term8 _5733 _5734) (term9 _5733 _5734 P)). Qed.
Lemma lem55271 {_5733 _5734 : Type'} (P : type1223 _5733 _5734) : (term18 _5733 _5734 P) = (P = (term19 _5733 _5734)).
Proof. exact (eq_refl (term18 _5733 _5734 P)). Qed.
Lemma lem55272 {_5733 _5734 : Type'} : (term20 _5733 _5734) = (term8 _5733 _5734).
Proof. exact (fun_ext (fun P : type1223 _5733 _5734 => @lem55271 _5733 _5734 P)). Qed.
Lemma lem55273 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term9 _5733 _5734 P) = (term9 _5733 _5734 P).
Proof. exact (eq_refl (term9 _5733 _5734 P)). Qed.
Lemma lem55274 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term17 _5733 _5734 P) = (term11 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55272 _5733 _5734) (@lem55273 _5733 _5734 P)). Qed.
Lemma lem55275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55276 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term21 _5733 _5734 P) = (term13 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55275) (@lem55274 _5733 _5734 P)). Qed.
Lemma lem55277 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term11 _5733 _5734 P) = ((term9 _5733 _5734 P) = (term19 _5733 _5734)).
Proof. exact (eq_refl (term11 _5733 _5734 P)). Qed.
Lemma lem55278 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term17 _5733 _5734 P) = (term11 _5733 _5734 P)) = ((term11 _5733 _5734 P) = ((term9 _5733 _5734 P) = (term19 _5733 _5734))).
Proof. exact (MK_COMB (@lem55276 _5733 _5734 P) (@lem55277 _5733 _5734 P)). Qed.
Lemma lem55279 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term11 _5733 _5734 P) = ((term9 _5733 _5734 P) = (term19 _5733 _5734)).
Proof. exact (EQ_MP (@lem55278 _5733 _5734 P) (@lem55270 _5733 _5734 P)). Qed.
Lemma lem55283 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term6 A B f g).
Proof. exact (EQ_MP (@lem55251 A B f g) (@lem55250 A B f g)). Qed.
Lemma lem55284 {_5733 _5734 : Type'} (f : type1223 _5733 _5734) (g : type1223 _5733 _5734) : (f = g) = (term22 _5733 _5734 f g).
Proof. exact (@lem55283 (prod _5734 _5733) Prop f g). Qed.
Lemma lem55285 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term9 _5733 _5734 P) = (term19 _5733 _5734)) = (term23 _5733 _5734 P).
Proof. exact (@lem55284 _5733 _5734 (term9 _5733 _5734 P) (term19 _5733 _5734)). Qed.
Lemma lem55291 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term2 _5106 _5107 P).
Proof. exact (EQ_MP (@lem55245 _5106 _5107 P) (@lem55244 _5106 _5107 P)). Qed.
Lemma lem55292 {_5733 _5734 : Type'} (P : type1223 _5733 _5734) : (term1 _5733 _5734 P) = (term2 _5733 _5734 P).
Proof. exact (@lem55291 _5733 _5734 P). Qed.
Lemma lem55293 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term24 _5733 _5734 P) = (term25 _5733 _5734 P).
Proof. exact (@lem55292 _5733 _5734 (term26 _5733 _5734 P)). Qed.
Lemma lem55294 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : prod _5734 _5733) : (term27 _5733 _5734 P x) = ((term28 _5733 _5734 P x) = (term29 _5733 _5734 x)).
Proof. exact (eq_refl (term27 _5733 _5734 P x)). Qed.
Lemma lem55295 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term30 _5733 _5734 P) = (term26 _5733 _5734 P).
Proof. exact (fun_ext (fun x : prod _5734 _5733 => @lem55294 _5733 _5734 P x)). Qed.
Lemma lem55296 {_5733 _5734 : Type'} : (@all (prod _5734 _5733)) = (@all (prod _5734 _5733)).
Proof. exact (eq_refl (@all (prod _5734 _5733))). Qed.
Lemma lem55297 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term24 _5733 _5734 P) = (term23 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55296 _5733 _5734) (@lem55295 _5733 _5734 P)). Qed.
Lemma lem55298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55299 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term31 _5733 _5734 P) = (term32 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55298) (@lem55297 _5733 _5734 P)). Qed.
Lemma lem55300 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) (p2 : _5733) : (term33 _5733 _5734 P p1 p2) = ((term34 _5733 _5734 P p1 p2) = (term35 _5733 _5734 p1 p2)).
Proof. exact (eq_refl (term33 _5733 _5734 P p1 p2)). Qed.
Lemma lem55301 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) : (term36 _5733 _5734 P p1) = (term37 _5733 _5734 P p1).
Proof. exact (fun_ext (fun p2 : _5733 => @lem55300 _5733 _5734 P p1 p2)). Qed.
Lemma lem55302 {_5733 : Type'} : (@all _5733) = (@all _5733).
Proof. exact (eq_refl (@all _5733)). Qed.
Lemma lem55303 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) : (term38 _5733 _5734 P p1) = (term39 _5733 _5734 P p1).
Proof. exact (MK_COMB (@lem55302 _5733) (@lem55301 _5733 _5734 P p1)). Qed.
Lemma lem55304 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term40 _5733 _5734 P) = (term41 _5733 _5734 P).
Proof. exact (fun_ext (fun p1 : _5734 => @lem55303 _5733 _5734 P p1)). Qed.
Lemma lem55305 {_5734 : Type'} : (@all _5734) = (@all _5734).
Proof. exact (eq_refl (@all _5734)). Qed.
Lemma lem55306 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term25 _5733 _5734 P) = (term42 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55305 _5734) (@lem55304 _5733 _5734 P)). Qed.
Lemma lem55307 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term24 _5733 _5734 P) = (term25 _5733 _5734 P)) = ((term23 _5733 _5734 P) = (term42 _5733 _5734 P)).
Proof. exact (MK_COMB (@lem55299 _5733 _5734 P) (@lem55306 _5733 _5734 P)). Qed.
Lemma lem55308 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term23 _5733 _5734 P) = (term42 _5733 _5734 P).
Proof. exact (EQ_MP (@lem55307 _5733 _5734 P) (@lem55293 _5733 _5734 P)). Qed.
Lemma lem55315 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term9 _5733 _5734 P) = (term19 _5733 _5734)) = (term42 _5733 _5734 P).
Proof. exact (TRANS (@lem55285 _5733 _5734 P) (@lem55308 _5733 _5734 P)). Qed.
Lemma lem55316 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term11 _5733 _5734 P) = (term42 _5733 _5734 P).
Proof. exact (TRANS (@lem55279 _5733 _5734 P) (@lem55315 _5733 _5734 P)). Qed.
Lemma lem55327 {_5733 _5734 : Type'} (a0 : _5734) (a1 : _5733) : a0 = (term43 _5733 _5734 a0 a1).
Proof. exact (@lem51128 _5734 _5733 a0 a1). Qed.
Lemma lem55328 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : x = (term43 _5733 _5734 x y).
Proof. exact (@lem55327 _5733 _5734 x y). Qed.
Lemma lem55329 {_5733 _5734 : Type'} (a0 : _5734) (a1 : _5733) : a1 = (term44 _5733 _5734 a0 a1).
Proof. exact (@lem51159 _5734 _5733 a0 a1). Qed.
Lemma lem55330 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : y = (term44 _5733 _5734 x y).
Proof. exact (@lem55329 _5733 _5734 x y). Qed.
Lemma lem55331 {_5734 : Type'} (x : _5734) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem55332 {_5734 : Type'} : (term45 _5734) = (term45 _5734).
Proof. exact (eq_refl (term45 _5734)). Qed.
Lemma lem55333 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : (term46 _5734 x) = (term47 _5733 _5734 x y).
Proof. exact (MK_COMB (@lem55332 _5734) (@lem55328 _5733 _5734 x y)). Qed.
Lemma lem55334 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : (term47 _5733 _5734 x y) = (term43 _5733 _5734 x y).
Proof. exact (eq_refl (term47 _5733 _5734 x y)). Qed.
Lemma lem55335 {_5734 : Type'} (x : _5734) : (term48 _5734 x) = (term48 _5734 x).
Proof. exact (eq_refl (term48 _5734 x)). Qed.
Lemma lem55336 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : ((term46 _5734 x) = (term47 _5733 _5734 x y)) = ((term46 _5734 x) = (term43 _5733 _5734 x y)).
Proof. exact (MK_COMB (@lem55335 _5734 x) (@lem55334 _5733 _5734 x y)). Qed.
Lemma lem55337 {_5734 : Type'} (x : _5734) : (term46 _5734 x) = x.
Proof. exact (eq_refl (term46 _5734 x)). Qed.
Lemma lem55338 {_5734 : Type'} : (@eq _5734) = (@eq _5734).
Proof. exact (eq_refl (@eq _5734)). Qed.
Lemma lem55339 {_5734 : Type'} (x : _5734) : (term48 _5734 x) = (@eq _5734 x).
Proof. exact (MK_COMB (@lem55338 _5734) (@lem55337 _5734 x)). Qed.
Lemma lem55340 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : (term43 _5733 _5734 x y) = (term43 _5733 _5734 x y).
Proof. exact (eq_refl (term43 _5733 _5734 x y)). Qed.
Lemma lem55341 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : ((term46 _5734 x) = (term43 _5733 _5734 x y)) = (x = (term43 _5733 _5734 x y)).
Proof. exact (MK_COMB (@lem55339 _5734 x) (@lem55340 _5733 _5734 x y)). Qed.
Lemma lem55342 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : ((term46 _5734 x) = (term47 _5733 _5734 x y)) = (x = (term43 _5733 _5734 x y)).
Proof. exact (TRANS (@lem55336 _5733 _5734 x y) (@lem55341 _5733 _5734 x y)). Qed.
Lemma lem55343 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : x = (term43 _5733 _5734 x y).
Proof. exact (EQ_MP (@lem55342 _5733 _5734 x y) (@lem55333 _5733 _5734 x y)). Qed.
Lemma lem55344 {_5734 : Type'} (x : _5734) : (@eq _5734 x) = (@eq _5734 x).
Proof. exact (eq_refl (@eq _5734 x)). Qed.
Lemma lem55345 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : (x = x) = (x = (term43 _5733 _5734 x y)).
Proof. exact (MK_COMB (@lem55344 _5734 x) (@lem55343 _5733 _5734 x y)). Qed.
Lemma lem55346 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : x = (term43 _5733 _5734 x y).
Proof. exact (EQ_MP (@lem55345 _5733 _5734 x y) (@lem55331 _5734 x)). Qed.
Lemma lem55347 {_5733 : Type'} (y : _5733) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem55348 {_5733 : Type'} : (term45 _5733) = (term45 _5733).
Proof. exact (eq_refl (term45 _5733)). Qed.
Lemma lem55349 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : (term46 _5733 y) = (term49 _5733 _5734 x y).
Proof. exact (MK_COMB (@lem55348 _5733) (@lem55330 _5733 _5734 x y)). Qed.
Lemma lem55350 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : (term49 _5733 _5734 x y) = (term44 _5733 _5734 x y).
Proof. exact (eq_refl (term49 _5733 _5734 x y)). Qed.
Lemma lem55351 {_5733 : Type'} (y : _5733) : (term48 _5733 y) = (term48 _5733 y).
Proof. exact (eq_refl (term48 _5733 y)). Qed.
Lemma lem55352 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : ((term46 _5733 y) = (term49 _5733 _5734 x y)) = ((term46 _5733 y) = (term44 _5733 _5734 x y)).
Proof. exact (MK_COMB (@lem55351 _5733 y) (@lem55350 _5733 _5734 x y)). Qed.
Lemma lem55353 {_5733 : Type'} (y : _5733) : (term46 _5733 y) = y.
Proof. exact (eq_refl (term46 _5733 y)). Qed.
Lemma lem55354 {_5733 : Type'} : (@eq _5733) = (@eq _5733).
Proof. exact (eq_refl (@eq _5733)). Qed.
Lemma lem55355 {_5733 : Type'} (y : _5733) : (term48 _5733 y) = (@eq _5733 y).
Proof. exact (MK_COMB (@lem55354 _5733) (@lem55353 _5733 y)). Qed.
Lemma lem55356 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : (term44 _5733 _5734 x y) = (term44 _5733 _5734 x y).
Proof. exact (eq_refl (term44 _5733 _5734 x y)). Qed.
Lemma lem55357 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : ((term46 _5733 y) = (term44 _5733 _5734 x y)) = (y = (term44 _5733 _5734 x y)).
Proof. exact (MK_COMB (@lem55355 _5733 y) (@lem55356 _5733 _5734 x y)). Qed.
Lemma lem55358 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : ((term46 _5733 y) = (term49 _5733 _5734 x y)) = (y = (term44 _5733 _5734 x y)).
Proof. exact (TRANS (@lem55352 _5733 _5734 x y) (@lem55357 _5733 _5734 x y)). Qed.
Lemma lem55359 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : y = (term44 _5733 _5734 x y).
Proof. exact (EQ_MP (@lem55358 _5733 _5734 x y) (@lem55349 _5733 _5734 x y)). Qed.
Lemma lem55360 {_5733 : Type'} (y : _5733) : (@eq _5733 y) = (@eq _5733 y).
Proof. exact (eq_refl (@eq _5733 y)). Qed.
Lemma lem55361 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : (y = y) = (y = (term44 _5733 _5734 x y)).
Proof. exact (MK_COMB (@lem55360 _5733 y) (@lem55359 _5733 _5734 x y)). Qed.
Lemma lem55362 {_5733 _5734 : Type'} (x : _5734) (y : _5733) : y = (term44 _5733 _5734 x y).
Proof. exact (EQ_MP (@lem55361 _5733 _5734 x y) (@lem55347 _5733 y)). Qed.
Lemma lem55363 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term50 _5733 _5734 P) = (term50 _5733 _5734 P).
Proof. exact (eq_refl (term50 _5733 _5734 P)). Qed.
Lemma lem55364 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term51 _5733 _5734 P x) = (term52 _5733 _5734 P x y).
Proof. exact (MK_COMB (@lem55363 _5733 _5734 P) (@lem55346 _5733 _5734 x y)). Qed.
Lemma lem55365 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term52 _5733 _5734 P x y) = (term53 _5733 _5734 P x y).
Proof. exact (eq_refl (term52 _5733 _5734 P x y)). Qed.
Lemma lem55366 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) : (term54 _5733 _5734 P x) = (term54 _5733 _5734 P x).
Proof. exact (eq_refl (term54 _5733 _5734 P x)). Qed.
Lemma lem55367 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : ((term51 _5733 _5734 P x) = (term52 _5733 _5734 P x y)) = ((term51 _5733 _5734 P x) = (term53 _5733 _5734 P x y)).
Proof. exact (MK_COMB (@lem55366 _5733 _5734 P x) (@lem55365 _5733 _5734 P x y)). Qed.
Lemma lem55368 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) : (term51 _5733 _5734 P x) = (term55 _5733 _5734 P x).
Proof. exact (eq_refl (term51 _5733 _5734 P x)). Qed.
Lemma lem55369 {_5733 : Type'} : (@eq (_5733 -> Prop)) = (@eq (_5733 -> Prop)).
Proof. exact (eq_refl (@eq (_5733 -> Prop))). Qed.
Lemma lem55370 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) : (term54 _5733 _5734 P x) = (term56 _5733 _5734 P x).
Proof. exact (MK_COMB (@lem55369 _5733) (@lem55368 _5733 _5734 P x)). Qed.
Lemma lem55371 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term53 _5733 _5734 P x y) = (term53 _5733 _5734 P x y).
Proof. exact (eq_refl (term53 _5733 _5734 P x y)). Qed.
Lemma lem55372 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : ((term51 _5733 _5734 P x) = (term53 _5733 _5734 P x y)) = ((term55 _5733 _5734 P x) = (term53 _5733 _5734 P x y)).
Proof. exact (MK_COMB (@lem55370 _5733 _5734 P x) (@lem55371 _5733 _5734 P x y)). Qed.
Lemma lem55373 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : ((term51 _5733 _5734 P x) = (term52 _5733 _5734 P x y)) = ((term55 _5733 _5734 P x) = (term53 _5733 _5734 P x y)).
Proof. exact (TRANS (@lem55367 _5733 _5734 P x y) (@lem55372 _5733 _5734 P x y)). Qed.
Lemma lem55374 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term55 _5733 _5734 P x) = (term53 _5733 _5734 P x y).
Proof. exact (EQ_MP (@lem55373 _5733 _5734 P x y) (@lem55364 _5733 _5734 P x y)). Qed.
Lemma lem55375 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term57 _5733 _5734 P x y) = (term58 _5733 _5734 P x y).
Proof. exact (MK_COMB (@lem55374 _5733 _5734 P x y) (@lem55362 _5733 _5734 x y)). Qed.
Lemma lem55376 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term58 _5733 _5734 P x y) = (term59 _5733 _5734 P x y).
Proof. exact (eq_refl (term58 _5733 _5734 P x y)). Qed.
Lemma lem55377 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term60 _5733 _5734 P x y) = (term60 _5733 _5734 P x y).
Proof. exact (eq_refl (term60 _5733 _5734 P x y)). Qed.
Lemma lem55378 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : ((term57 _5733 _5734 P x y) = (term58 _5733 _5734 P x y)) = ((term57 _5733 _5734 P x y) = (term59 _5733 _5734 P x y)).
Proof. exact (MK_COMB (@lem55377 _5733 _5734 P x y) (@lem55376 _5733 _5734 P x y)). Qed.
Lemma lem55379 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term57 _5733 _5734 P x y) = (P x y).
Proof. exact (eq_refl (term57 _5733 _5734 P x y)). Qed.
Lemma lem55380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55381 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term60 _5733 _5734 P x y) = (term61 _5733 _5734 P x y).
Proof. exact (MK_COMB (@lem55380) (@lem55379 _5733 _5734 P x y)). Qed.
Lemma lem55382 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term59 _5733 _5734 P x y) = (term59 _5733 _5734 P x y).
Proof. exact (eq_refl (term59 _5733 _5734 P x y)). Qed.
Lemma lem55383 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : ((term57 _5733 _5734 P x y) = (term59 _5733 _5734 P x y)) = ((P x y) = (term59 _5733 _5734 P x y)).
Proof. exact (MK_COMB (@lem55381 _5733 _5734 P x y) (@lem55382 _5733 _5734 P x y)). Qed.
Lemma lem55384 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : ((term57 _5733 _5734 P x y) = (term58 _5733 _5734 P x y)) = ((P x y) = (term59 _5733 _5734 P x y)).
Proof. exact (TRANS (@lem55378 _5733 _5734 P x y) (@lem55383 _5733 _5734 P x y)). Qed.
Lemma lem55385 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (P x y) = (term59 _5733 _5734 P x y).
Proof. exact (EQ_MP (@lem55384 _5733 _5734 P x y) (@lem55375 _5733 _5734 P x y)). Qed.
Lemma lem55386 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term59 _5733 _5734 P x y) = (P x y).
Proof. exact (SYM (@lem55385 _5733 _5734 P x y)). Qed.
Lemma lem55387 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term62 _5733 _5734 P x y) = (term59 _5733 _5734 P x y).
Proof. exact (eq_refl (term62 _5733 _5734 P x y)). Qed.
Lemma lem55388 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term62 _5733 _5734 P x y) = (P x y).
Proof. exact (TRANS (@lem55387 _5733 _5734 P x y) (@lem55386 _5733 _5734 P x y)). Qed.
Lemma lem55389 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) : term63 _5733 _5734 P x.
Proof. exact (fun y : _5733 => @lem55388 _5733 _5734 P x y). Qed.
Lemma lem55390 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : term64 _5733 _5734 P.
Proof. exact (fun x : _5734 => @lem55389 _5733 _5734 P x). Qed.
Lemma lem55391 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : term65 _5733 _5734 P.
Proof. exact (ex_intro (term66 _5733 _5734 P) (term67 _5733 _5734 P) (@lem55390 _5733 _5734 P)). Qed.
Lemma lem55393 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem55394 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem55393 Prop a b). Qed.
Lemma lem55395 {_5733 _5734 : Type'} (_1528 : type1223 _5733 _5734) (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : ((term68 _5733 _5734 _1528 x y) = (P x y)) = (term69 _5733 _5734 _1528 P x y).
Proof. exact (@lem55394 (term68 _5733 _5734 _1528 x y) (P x y)). Qed.
Lemma lem55396 {_5733 _5734 : Type'} (_1528 : type1223 _5733 _5734) (P : type1470 _5733 _5734) (x : _5734) : (term70 _5733 _5734 _1528 P x) = (term71 _5733 _5734 _1528 P x).
Proof. exact (fun_ext (fun y : _5733 => @lem55395 _5733 _5734 _1528 P x y)). Qed.
Lemma lem55397 {_5733 : Type'} : (@all _5733) = (@all _5733).
Proof. exact (eq_refl (@all _5733)). Qed.
Lemma lem55398 {_5733 _5734 : Type'} (_1528 : type1223 _5733 _5734) (P : type1470 _5733 _5734) (x : _5734) : (term72 _5733 _5734 _1528 P x) = (term73 _5733 _5734 _1528 P x).
Proof. exact (MK_COMB (@lem55397 _5733) (@lem55396 _5733 _5734 _1528 P x)). Qed.
Lemma lem55399 {_5733 _5734 : Type'} (_1528 : type1223 _5733 _5734) (P : type1470 _5733 _5734) : (term74 _5733 _5734 _1528 P) = (term75 _5733 _5734 _1528 P).
Proof. exact (fun_ext (fun x : _5734 => @lem55398 _5733 _5734 _1528 P x)). Qed.
Lemma lem55400 {_5734 : Type'} : (@all _5734) = (@all _5734).
Proof. exact (eq_refl (@all _5734)). Qed.
Lemma lem55401 {_5733 _5734 : Type'} (_1528 : type1223 _5733 _5734) (P : type1470 _5733 _5734) : (term76 _5733 _5734 _1528 P) = (term77 _5733 _5734 _1528 P).
Proof. exact (MK_COMB (@lem55400 _5734) (@lem55399 _5733 _5734 _1528 P)). Qed.
Lemma lem55402 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term66 _5733 _5734 P) = (term78 _5733 _5734 P).
Proof. exact (fun_ext (fun _1528 : type1223 _5733 _5734 => @lem55401 _5733 _5734 _1528 P)). Qed.
Lemma lem55403 {_5733 _5734 : Type'} : (@ex ((prod _5734 _5733) -> Prop)) = (@ex ((prod _5734 _5733) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5734 _5733) -> Prop))). Qed.
Lemma lem55404 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term65 _5733 _5734 P) = (term79 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55403 _5733 _5734) (@lem55402 _5733 _5734 P)). Qed.
Lemma lem55405 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : term79 _5733 _5734 P.
Proof. exact (EQ_MP (@lem55404 _5733 _5734 P) (@lem55391 _5733 _5734 P)). Qed.
Lemma lem55407 {_5076 : Type'} (P : _5076 -> Prop) : term80 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem55408 {_5733 _5734 : Type'} (P : type330 _5733 _5734) : term81 _5733 _5734 P.
Proof. exact (@lem55407 (type1223 _5733 _5734) P). Qed.
Lemma lem55409 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : term82 _5733 _5734 P.
Proof. exact (@lem55408 _5733 _5734 (term78 _5733 _5734 P)). Qed.
Lemma lem55410 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : term83 _5733 _5734 P.
Proof. exact (@lem55409 _5733 _5734 P (@lem55405 _5733 _5734 P)). Qed.
Lemma lem55411 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term83 _5733 _5734 P) = (term84 _5733 _5734 P).
Proof. exact (eq_refl (term83 _5733 _5734 P)). Qed.
Lemma lem55412 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : term84 _5733 _5734 P.
Proof. exact (EQ_MP (@lem55411 _5733 _5734 P) (@lem55410 _5733 _5734 P)). Qed.
Lemma lem55413 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) : term85 _5733 _5734 P x.
Proof. exact (@lem55412 _5733 _5734 P x). Qed.
Lemma lem55414 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) : (term85 _5733 _5734 P x) = (term86 _5733 _5734 P x).
Proof. exact (eq_refl (term85 _5733 _5734 P x)). Qed.
Lemma lem55415 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) : term86 _5733 _5734 P x.
Proof. exact (EQ_MP (@lem55414 _5733 _5734 P x) (@lem55413 _5733 _5734 P x)). Qed.
Lemma lem55416 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : term87 _5733 _5734 P x y.
Proof. exact (@lem55415 _5733 _5734 P x y). Qed.
Lemma lem55417 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term87 _5733 _5734 P x y) = (term88 _5733 _5734 P x y).
Proof. exact (eq_refl (term87 _5733 _5734 P x y)). Qed.
Lemma lem55418 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : term88 _5733 _5734 P x y.
Proof. exact (EQ_MP (@lem55417 _5733 _5734 P x y) (@lem55416 _5733 _5734 P x y)). Qed.
Lemma lem55420 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem55421 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem55420 Prop a b). Qed.
Lemma lem55422 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term88 _5733 _5734 P x y) = ((term34 _5733 _5734 P x y) = (P x y)).
Proof. exact (@lem55421 (term34 _5733 _5734 P x y) (P x y)). Qed.
Lemma lem55423 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term34 _5733 _5734 P x y) = (P x y).
Proof. exact (EQ_MP (@lem55422 _5733 _5734 P x y) (@lem55418 _5733 _5734 P x y)). Qed.
Lemma lem55424 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (x : _5734) (y : _5733) : (term34 _5733 _5734 P x y) = (P x y).
Proof. exact (@lem55423 _5733 _5734 P x y). Qed.
Lemma lem55425 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) (p2 : _5733) : (term34 _5733 _5734 P p1 p2) = (P p1 p2).
Proof. exact (@lem55424 _5733 _5734 P p1 p2). Qed.
Lemma lem55426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55427 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) (p2 : _5733) : (term89 _5733 _5734 P p1 p2) = (term61 _5733 _5734 P p1 p2).
Proof. exact (MK_COMB (@lem55426) (@lem55425 _5733 _5734 P p1 p2)). Qed.
Lemma lem55429 {A B : Type'} (f : A -> B) (y : A) : (term15 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55430 {_5733 _5734 : Type'} (f : type1223 _5733 _5734) (y : prod _5734 _5733) : (term90 _5733 _5734 f y) = (f y).
Proof. exact (@lem55429 (prod _5734 _5733) Prop f y). Qed.
Lemma lem55431 {_5733 _5734 : Type'} (p1 : _5734) (p2 : _5733) : (term91 _5733 _5734 p1 p2) = (term35 _5733 _5734 p1 p2).
Proof. exact (@lem55430 _5733 _5734 (term19 _5733 _5734) (@pair _5734 _5733 p1 p2)). Qed.
Lemma lem55432 {_5733 _5734 : Type'} (x : prod _5734 _5733) : (term29 _5733 _5734 x) = True.
Proof. exact (eq_refl (term29 _5733 _5734 x)). Qed.
Lemma lem55433 {_5733 _5734 : Type'} : (term92 _5733 _5734) = (term19 _5733 _5734).
Proof. exact (fun_ext (fun x : prod _5734 _5733 => @lem55432 _5733 _5734 x)). Qed.
Lemma lem55434 {_5733 _5734 : Type'} (p1 : _5734) (p2 : _5733) : (@pair _5734 _5733 p1 p2) = (@pair _5734 _5733 p1 p2).
Proof. exact (eq_refl (@pair _5734 _5733 p1 p2)). Qed.
Lemma lem55435 {_5733 _5734 : Type'} (p1 : _5734) (p2 : _5733) : (term91 _5733 _5734 p1 p2) = (term35 _5733 _5734 p1 p2).
Proof. exact (MK_COMB (@lem55433 _5733 _5734) (@lem55434 _5733 _5734 p1 p2)). Qed.
Lemma lem55436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55437 {_5733 _5734 : Type'} (p1 : _5734) (p2 : _5733) : (term93 _5733 _5734 p1 p2) = (term94 _5733 _5734 p1 p2).
Proof. exact (MK_COMB (@lem55436) (@lem55435 _5733 _5734 p1 p2)). Qed.
Lemma lem55438 {_5733 _5734 : Type'} (p1 : _5734) (p2 : _5733) : (term35 _5733 _5734 p1 p2) = True.
Proof. exact (eq_refl (term35 _5733 _5734 p1 p2)). Qed.
Lemma lem55439 {_5733 _5734 : Type'} (p1 : _5734) (p2 : _5733) : ((term91 _5733 _5734 p1 p2) = (term35 _5733 _5734 p1 p2)) = ((term35 _5733 _5734 p1 p2) = True).
Proof. exact (MK_COMB (@lem55437 _5733 _5734 p1 p2) (@lem55438 _5733 _5734 p1 p2)). Qed.
Lemma lem55440 {_5733 _5734 : Type'} (p1 : _5734) (p2 : _5733) : (term35 _5733 _5734 p1 p2) = True.
Proof. exact (EQ_MP (@lem55439 _5733 _5734 p1 p2) (@lem55431 _5733 _5734 p1 p2)). Qed.
Lemma lem55441 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) (p2 : _5733) : ((term34 _5733 _5734 P p1 p2) = (term35 _5733 _5734 p1 p2)) = ((P p1 p2) = True).
Proof. exact (MK_COMB (@lem55427 _5733 _5734 P p1 p2) (@lem55440 _5733 _5734 p1 p2)). Qed.
Lemma lem55443 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem55444 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) (p2 : _5733) : ((P p1 p2) = True) = (P p1 p2).
Proof. exact (@lem55443 (P p1 p2)). Qed.
Lemma lem55445 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) (p2 : _5733) : ((term34 _5733 _5734 P p1 p2) = (term35 _5733 _5734 p1 p2)) = (P p1 p2).
Proof. exact (TRANS (@lem55441 _5733 _5734 P p1 p2) (@lem55444 _5733 _5734 P p1 p2)). Qed.
Lemma lem55446 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) : (term37 _5733 _5734 P p1) = (term55 _5733 _5734 P p1).
Proof. exact (fun_ext (fun p2 : _5733 => @lem55445 _5733 _5734 P p1 p2)). Qed.
Lemma lem55447 {_5733 : Type'} : (@all _5733) = (@all _5733).
Proof. exact (eq_refl (@all _5733)). Qed.
Lemma lem55448 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) (p1 : _5734) : (term39 _5733 _5734 P p1) = (term95 _5733 _5734 P p1).
Proof. exact (MK_COMB (@lem55447 _5733) (@lem55446 _5733 _5734 P p1)). Qed.
Lemma lem55455 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term41 _5733 _5734 P) = (term96 _5733 _5734 P).
Proof. exact (fun_ext (fun p1 : _5734 => @lem55448 _5733 _5734 P p1)). Qed.
Lemma lem55456 {_5734 : Type'} : (@all _5734) = (@all _5734).
Proof. exact (eq_refl (@all _5734)). Qed.
Lemma lem55457 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term42 _5733 _5734 P) = (term14 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55456 _5734) (@lem55455 _5733 _5734 P)). Qed.
Lemma lem55464 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term11 _5733 _5734 P) = (term14 _5733 _5734 P).
Proof. exact (TRANS (@lem55316 _5733 _5734 P) (@lem55457 _5733 _5734 P)). Qed.
Lemma lem55465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55466 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term13 _5733 _5734 P) = (term97 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55465) (@lem55464 _5733 _5734 P)). Qed.
Lemma lem55479 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term14 _5733 _5734 P) = (term14 _5733 _5734 P).
Proof. exact (eq_refl (term14 _5733 _5734 P)). Qed.
Lemma lem55480 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term11 _5733 _5734 P) = (term14 _5733 _5734 P)) = ((term14 _5733 _5734 P) = (term14 _5733 _5734 P)).
Proof. exact (MK_COMB (@lem55466 _5733 _5734 P) (@lem55479 _5733 _5734 P)). Qed.
Lemma lem55482 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem55483 (x : Prop) : (x = x) = True.
Proof. exact (@lem55482 Prop x). Qed.
Lemma lem55484 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True.
Proof. exact (@lem55483 (term14 _5733 _5734 P)). Qed.
Lemma lem55487 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term98 _5733 _5734 P) = (term98 _5733 _5734 P).
Proof. exact (eq_refl (term98 _5733 _5734 P)). Qed.
Lemma lem55488 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term98 _5733 _5734 P) = (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True).
Proof. exact (eq_refl (term98 _5733 _5734 P)). Qed.
Lemma lem55489 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term99 _5733 _5734 P) = (term99 _5733 _5734 P).
Proof. exact (eq_refl (term99 _5733 _5734 P)). Qed.
Lemma lem55490 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term98 _5733 _5734 P) = (term98 _5733 _5734 P)) = ((term98 _5733 _5734 P) = (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True)).
Proof. exact (MK_COMB (@lem55489 _5733 _5734 P) (@lem55488 _5733 _5734 P)). Qed.
Lemma lem55491 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term98 _5733 _5734 P) = (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True).
Proof. exact (eq_refl (term98 _5733 _5734 P)). Qed.
Lemma lem55492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55493 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term99 _5733 _5734 P) = (term100 _5733 _5734 P).
Proof. exact (MK_COMB (@lem55492) (@lem55491 _5733 _5734 P)). Qed.
Lemma lem55494 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True) = (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True).
Proof. exact (eq_refl (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True)). Qed.
Lemma lem55495 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term98 _5733 _5734 P) = (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True)) = ((((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True) = (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True)).
Proof. exact (MK_COMB (@lem55493 _5733 _5734 P) (@lem55494 _5733 _5734 P)). Qed.
Lemma lem55496 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term98 _5733 _5734 P) = (term98 _5733 _5734 P)) = ((((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True) = (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True)).
Proof. exact (TRANS (@lem55490 _5733 _5734 P) (@lem55495 _5733 _5734 P)). Qed.
Lemma lem55497 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True) = (((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True).
Proof. exact (EQ_MP (@lem55496 _5733 _5734 P) (@lem55487 _5733 _5734 P)). Qed.
Lemma lem55498 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term14 _5733 _5734 P) = (term14 _5733 _5734 P)) = True.
Proof. exact (EQ_MP (@lem55497 _5733 _5734 P) (@lem55484 _5733 _5734 P)). Qed.
Lemma lem55499 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : ((term11 _5733 _5734 P) = (term14 _5733 _5734 P)) = True.
Proof. exact (TRANS (@lem55480 _5733 _5734 P) (@lem55498 _5733 _5734 P)). Qed.
Lemma lem55500 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : True = ((term11 _5733 _5734 P) = (term14 _5733 _5734 P)).
Proof. exact (SYM (@lem55499 _5733 _5734 P)). Qed.
Lemma lem55501 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term11 _5733 _5734 P) = (term14 _5733 _5734 P).
Proof. exact (EQ_MP (@lem55500 _5733 _5734 P) (@lem0)). Qed.
Lemma lem55502 {_5733 _5734 : Type'} (P : type1470 _5733 _5734) : (term10 _5733 _5734 P) = (term14 _5733 _5734 P).
Proof. exact (EQ_MP (@lem55262 _5733 _5734 P) (@lem55501 _5733 _5734 P)). Qed.
Lemma lem55507 {_5733 _5734 : Type'} : term101 _5733 _5734.
Proof. exact (fun P : type1470 _5733 _5734 => @lem55502 _5733 _5734 P). Qed.
