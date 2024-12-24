Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJ_INVERSE2_term_abbrevs.
Require Import SELECT_UNIQUE_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem1046248 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem1046249 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term1 A P.
Proof. exact (@lem1046248 A h1 P). Qed.
Lemma lem1046250 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem1046251 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem1046250 A P) (@lem1046249 A P h1)). Qed.
Lemma lem1046252 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term3 A P x.
Proof. exact (@lem1046251 A P h1 x). Qed.
Lemma lem1046253 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem1046254 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (EQ_MP (@lem1046253 A P x) (@lem1046252 A P x h1)). Qed.
Lemma lem1046255 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term5 A P x.
Proof. exact (h1). Qed.
Lemma lem1046256 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem1046254 A P x h2 (@lem1046255 A P x h1)). Qed.
Lemma lem1046257 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term6 A P x.
Proof. exact (fun h0 : term0 A => @lem1046256 A P x h1 h0). Qed.
Lemma lem1046258 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem1046259 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem1046257 A P x h1 (@lem1046258 A h2)). Qed.
Lemma lem1046260 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (fun h0 : term5 A P x => @lem1046259 A P x h0 h1). Qed.
Lemma lem1046261 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (fun x : A => @lem1046260 A P x h1). Qed.
Lemma lem1046262 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : A -> Prop => @lem1046261 A P h1). Qed.
Lemma lem1046263 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem1046262 A h0). Qed.
Lemma lem1046264 {A : Type'} : term0 A.
Proof. exact (@lem1046263 A (@lem9522 A)). Qed.
Lemma lem1046265 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem1046264 A P). Qed.
Lemma lem1046266 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem1046267 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem1046266 A P) (@lem1046265 A P)). Qed.
Lemma lem1046268 {A : Type'} (P : A -> Prop) (x : A) : term3 A P x.
Proof. exact (@lem1046267 A P x). Qed.
Lemma lem1046269 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem1046271 {A B C : Type'} (P : type1412 A B C) (h1 : term8 A B C P) : term8 A B C P.
Proof. exact (h1). Qed.
Lemma lem1046278 {A B C : Type'} (x1 : A) (P : type1412 A B C) (h1 : term8 A B C P) : term9 A B C P x1.
Proof. exact (@lem1046271 A B C P h1 x1). Qed.
Lemma lem1046279 {A B C : Type'} (P : type1412 A B C) (x1 : A) : (term9 A B C P x1) = (term10 A B C P x1).
Proof. exact (eq_refl (term9 A B C P x1)). Qed.
Lemma lem1046280 {A B C : Type'} (x1 : A) (P : type1412 A B C) (h1 : term8 A B C P) : term10 A B C P x1.
Proof. exact (EQ_MP (@lem1046279 A B C P x1) (@lem1046278 A B C x1 P h1)). Qed.
Lemma lem1046281 {A B C : Type'} (x1 : A) (y1 : B) (P : type1412 A B C) (h1 : term8 A B C P) : term11 A B C P x1 y1.
Proof. exact (@lem1046280 A B C x1 P h1 y1). Qed.
Lemma lem1046282 {A B C : Type'} (P : type1412 A B C) (x1 : A) (y1 : B) : (term11 A B C P x1 y1) = (term12 A B C P x1 y1).
Proof. exact (eq_refl (term11 A B C P x1 y1)). Qed.
Lemma lem1046283 {A B C : Type'} (x1 : A) (y1 : B) (P : type1412 A B C) (h1 : term8 A B C P) : term12 A B C P x1 y1.
Proof. exact (EQ_MP (@lem1046282 A B C P x1 y1) (@lem1046281 A B C x1 y1 P h1)). Qed.
Lemma lem1046284 {A B C : Type'} (x1 : A) (y1 : B) (x2 : A) (P : type1412 A B C) (h1 : term8 A B C P) : term13 A B C P x1 y1 x2.
Proof. exact (@lem1046283 A B C x1 y1 P h1 x2). Qed.
Lemma lem1046285 {A B C : Type'} (P : type1412 A B C) (x1 : A) (x2 : A) (y1 : B) : (term13 A B C P x1 y1 x2) = (term14 A B C P x1 x2 y1).
Proof. exact (eq_refl (term13 A B C P x1 y1 x2)). Qed.
Lemma lem1046286 {A B C : Type'} (x1 : A) (x2 : A) (y1 : B) (P : type1412 A B C) (h1 : term8 A B C P) : term14 A B C P x1 x2 y1.
Proof. exact (EQ_MP (@lem1046285 A B C P x1 x2 y1) (@lem1046284 A B C x1 y1 x2 P h1)). Qed.
Lemma lem1046287 {A B C : Type'} (x1 : A) (x2 : A) (y1 : B) (y2 : B) (P : type1412 A B C) (h1 : term8 A B C P) : term15 A B C P x1 x2 y1 y2.
Proof. exact (@lem1046286 A B C x1 x2 y1 P h1 y2). Qed.
Lemma lem1046288 {A B C : Type'} (P : type1412 A B C) (x1 : A) (x2 : A) (y1 : B) (y2 : B) : (term15 A B C P x1 x2 y1 y2) = (((P x1 y1) = (P x2 y2)) = (term16 A B x1 x2 y1 y2)).
Proof. exact (eq_refl (term15 A B C P x1 x2 y1 y2)). Qed.
Lemma lem1046295 {A B : Type'} (f : A -> B) (y : A) : (term17 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1046296 {A C : Type'} (f : C -> A) (y : C) : (term18 A C f y) = (f y).
Proof. exact (@lem1046295 C A f y). Qed.
Lemma lem1046297 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term19 A B C P x y) = (term20 A B C P x y).
Proof. exact (@lem1046296 A C (term21 A B C P) (P x y)). Qed.
Lemma lem1046298 {A B C : Type'} (P : type1412 A B C) (z : C) : (term22 A B C P z) = (term23 A B C P z).
Proof. exact (eq_refl (term22 A B C P z)). Qed.
Lemma lem1046299 {A B C : Type'} (P : type1412 A B C) : (term24 A B C P) = (term21 A B C P).
Proof. exact (fun_ext (fun z : C => @lem1046298 A B C P z)). Qed.
Lemma lem1046300 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1046301 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term19 A B C P x y) = (term20 A B C P x y).
Proof. exact (MK_COMB (@lem1046299 A B C P) (@lem1046300 A B C P x y)). Qed.
Lemma lem1046302 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1046303 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term25 A B C P x y) = (term26 A B C P x y).
Proof. exact (MK_COMB (@lem1046302 A) (@lem1046301 A B C P x y)). Qed.
Lemma lem1046304 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term20 A B C P x y) = (term27 A B C P x y).
Proof. exact (eq_refl (term20 A B C P x y)). Qed.
Lemma lem1046305 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : ((term19 A B C P x y) = (term20 A B C P x y)) = ((term20 A B C P x y) = (term27 A B C P x y)).
Proof. exact (MK_COMB (@lem1046303 A B C P x y) (@lem1046304 A B C P x y)). Qed.
Lemma lem1046306 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term20 A B C P x y) = (term27 A B C P x y).
Proof. exact (EQ_MP (@lem1046305 A B C P x y) (@lem1046297 A B C P x y)). Qed.
Lemma lem1046312 {A B C : Type'} (x1 : A) (x2 : A) (y1 : B) (y2 : B) (P : type1412 A B C) (h1 : term8 A B C P) : ((P x1 y1) = (P x2 y2)) = (term16 A B x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1046288 A B C P x1 x2 y1 y2) (@lem1046287 A B C x1 x2 y1 y2 P h1)). Qed.
Lemma lem1046313 {A B C : Type'} (x1 : A) (x2 : A) (y1 : B) (y2 : B) (P : type1412 A B C) (h1 : term8 A B C P) : ((P x1 y1) = (P x2 y2)) = (term16 A B x1 x2 y1 y2).
Proof. exact (@lem1046312 A B C x1 x2 y1 y2 P h1). Qed.
Lemma lem1046314 {A B C : Type'} (x' : A) (x : A) (y' : B) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : ((P x' y') = (P x y)) = (term16 A B x' x y' y).
Proof. exact (@lem1046313 A B C x' x y' y P h1). Qed.
Lemma lem1046321 {A B C : Type'} (x' : A) (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term28 A B C x' P x y) = (term29 A B x' x y).
Proof. exact (fun_ext (fun y' : B => @lem1046314 A B C x' x y' y P h1)). Qed.
Lemma lem1046322 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1046323 {A B C : Type'} (x' : A) (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term30 A B C x' P x y) = (term31 A B x' x y).
Proof. exact (MK_COMB (@lem1046322 B) (@lem1046321 A B C x' x y P h1)). Qed.
Lemma lem1046328 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term32 A B C P x y) = (term33 A B x y).
Proof. exact (fun_ext (fun x' : A => @lem1046323 A B C x' x y P h1)). Qed.
Lemma lem1046329 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem1046330 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term27 A B C P x y) = (term34 A B x y).
Proof. exact (MK_COMB (@lem1046329 A) (@lem1046328 A B C x y P h1)). Qed.
Lemma lem1046331 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term20 A B C P x y) = (term34 A B x y).
Proof. exact (TRANS (@lem1046306 A B C P x y) (@lem1046330 A B C x y P h1)). Qed.
Lemma lem1046332 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1046333 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term26 A B C P x y) = (term35 A B x y).
Proof. exact (MK_COMB (@lem1046332 A) (@lem1046331 A B C x y P h1)). Qed.
Lemma lem1046334 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1046335 {A B C : Type'} (y : B) (x : A) (P : type1412 A B C) (h1 : term8 A B C P) : ((term20 A B C P x y) = x) = ((term34 A B x y) = x).
Proof. exact (MK_COMB (@lem1046333 A B C x y P h1) (@lem1046334 A x)). Qed.
Lemma lem1046338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1046339 {A B C : Type'} (y : B) (x : A) (P : type1412 A B C) (h1 : term8 A B C P) : (term36 A B C P y x) = (term37 A B y x).
Proof. exact (MK_COMB (@lem1046338) (@lem1046335 A B C y x P h1)). Qed.
Lemma lem1046343 {A B : Type'} (f : A -> B) (y : A) : (term17 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1046344 {B C : Type'} (f : C -> B) (y : C) : (term18 B C f y) = (f y).
Proof. exact (@lem1046343 C B f y). Qed.
Lemma lem1046345 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term38 A B C P x y) = (term39 A B C P x y).
Proof. exact (@lem1046344 B C (term40 A B C P) (P x y)). Qed.
Lemma lem1046346 {A B C : Type'} (P : type1412 A B C) (z : C) : (term41 A B C P z) = (term42 A B C P z).
Proof. exact (eq_refl (term41 A B C P z)). Qed.
Lemma lem1046347 {A B C : Type'} (P : type1412 A B C) : (term43 A B C P) = (term40 A B C P).
Proof. exact (fun_ext (fun z : C => @lem1046346 A B C P z)). Qed.
Lemma lem1046348 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1046349 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term38 A B C P x y) = (term39 A B C P x y).
Proof. exact (MK_COMB (@lem1046347 A B C P) (@lem1046348 A B C P x y)). Qed.
Lemma lem1046350 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1046351 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term44 A B C P x y) = (term45 A B C P x y).
Proof. exact (MK_COMB (@lem1046350 B) (@lem1046349 A B C P x y)). Qed.
Lemma lem1046352 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term39 A B C P x y) = (term46 A B C P x y).
Proof. exact (eq_refl (term39 A B C P x y)). Qed.
Lemma lem1046353 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : ((term38 A B C P x y) = (term39 A B C P x y)) = ((term39 A B C P x y) = (term46 A B C P x y)).
Proof. exact (MK_COMB (@lem1046351 A B C P x y) (@lem1046352 A B C P x y)). Qed.
Lemma lem1046354 {A B C : Type'} (P : type1412 A B C) (x : A) (y : B) : (term39 A B C P x y) = (term46 A B C P x y).
Proof. exact (EQ_MP (@lem1046353 A B C P x y) (@lem1046345 A B C P x y)). Qed.
Lemma lem1046360 {A B C : Type'} (x1 : A) (x2 : A) (y1 : B) (y2 : B) (P : type1412 A B C) (h1 : term8 A B C P) : ((P x1 y1) = (P x2 y2)) = (term16 A B x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1046288 A B C P x1 x2 y1 y2) (@lem1046287 A B C x1 x2 y1 y2 P h1)). Qed.
Lemma lem1046361 {A B C : Type'} (x1 : A) (x2 : A) (y1 : B) (y2 : B) (P : type1412 A B C) (h1 : term8 A B C P) : ((P x1 y1) = (P x2 y2)) = (term16 A B x1 x2 y1 y2).
Proof. exact (@lem1046360 A B C x1 x2 y1 y2 P h1). Qed.
Lemma lem1046362 {A B C : Type'} (x' : A) (x : A) (y' : B) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : ((P x' y') = (P x y)) = (term16 A B x' x y' y).
Proof. exact (@lem1046361 A B C x' x y' y P h1). Qed.
Lemma lem1046369 {A B C : Type'} (x : A) (y' : B) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term47 A B C y' P x y) = (term48 A B x y' y).
Proof. exact (fun_ext (fun x' : A => @lem1046362 A B C x' x y' y P h1)). Qed.
Lemma lem1046370 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1046371 {A B C : Type'} (x : A) (y' : B) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term49 A B C y' P x y) = (term50 A B x y' y).
Proof. exact (MK_COMB (@lem1046370 A) (@lem1046369 A B C x y' y P h1)). Qed.
Lemma lem1046376 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term51 A B C P x y) = (term52 A B x y).
Proof. exact (fun_ext (fun y' : B => @lem1046371 A B C x y' y P h1)). Qed.
Lemma lem1046377 {B : Type'} : (@ε B) = (@ε B).
Proof. exact (eq_refl (@ε B)). Qed.
Lemma lem1046378 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term46 A B C P x y) = (term53 A B x y).
Proof. exact (MK_COMB (@lem1046377 B) (@lem1046376 A B C x y P h1)). Qed.
Lemma lem1046379 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term39 A B C P x y) = (term53 A B x y).
Proof. exact (TRANS (@lem1046354 A B C P x y) (@lem1046378 A B C x y P h1)). Qed.
Lemma lem1046380 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1046381 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term45 A B C P x y) = (term54 A B x y).
Proof. exact (MK_COMB (@lem1046380 B) (@lem1046379 A B C x y P h1)). Qed.
Lemma lem1046382 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1046383 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : ((term39 A B C P x y) = y) = ((term53 A B x y) = y).
Proof. exact (MK_COMB (@lem1046381 A B C x y P h1) (@lem1046382 B y)). Qed.
Lemma lem1046386 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term55 A B C P x y) = (term56 A B x y).
Proof. exact (MK_COMB (@lem1046339 A B C y x P h1) (@lem1046383 A B C x y P h1)). Qed.
Lemma lem1046389 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : (term56 A B x y) = (term55 A B C P x y).
Proof. exact (SYM (@lem1046386 A B C x y P h1)). Qed.
Lemma lem1046391 {A : Type'} (P : A -> Prop) (x : A) : term4 A P x.
Proof. exact (EQ_MP (@lem1046269 A P x) (@lem1046268 A P x)). Qed.
Lemma lem1046392 {A : Type'} (P : A -> Prop) (x : A) : term4 A P x.
Proof. exact (@lem1046391 A P x). Qed.
Lemma lem1046393 {A B : Type'} (y : B) (x : A) : term57 A B y x.
Proof. exact (@lem1046392 A (term33 A B x y) x). Qed.
Lemma lem1046395 {A : Type'} (P : A -> Prop) (x : A) : term4 A P x.
Proof. exact (EQ_MP (@lem1046269 A P x) (@lem1046268 A P x)). Qed.
Lemma lem1046396 {B : Type'} (P : B -> Prop) (x : B) : term4 B P x.
Proof. exact (@lem1046395 B P x). Qed.
Lemma lem1046397 {A B : Type'} (x : A) (y : B) : term58 A B x y.
Proof. exact (@lem1046396 B (term52 A B x y) y). Qed.
Lemma lem1046398 {A B : Type'} (y' : A) (x : A) (y : B) : (term59 A B x y y') = (term31 A B y' x y).
Proof. exact (eq_refl (term59 A B x y y')). Qed.
Lemma lem1046399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1046400 {A B : Type'} (y' : A) (x : A) (y : B) : (term60 A B x y y') = (term61 A B y' x y).
Proof. exact (MK_COMB (@lem1046399) (@lem1046398 A B y' x y)). Qed.
Lemma lem1046401 {A : Type'} (y' : A) (x : A) : (y' = x) = (y' = x).
Proof. exact (eq_refl (y' = x)). Qed.
Lemma lem1046402 {A B : Type'} (y : B) (y' : A) (x : A) : ((term59 A B x y y') = (y' = x)) = ((term31 A B y' x y) = (y' = x)).
Proof. exact (MK_COMB (@lem1046400 A B y' x y) (@lem1046401 A y' x)). Qed.
Lemma lem1046403 {A B : Type'} (y : B) (y' : A) (x : A) : ((term31 A B y' x y) = (y' = x)) = ((term59 A B x y y') = (y' = x)).
Proof. exact (SYM (@lem1046402 A B y y' x)). Qed.
Lemma lem1046404 {A B : Type'} (x : A) (y' : B) (y : B) : (term62 A B x y y') = (term50 A B x y' y).
Proof. exact (eq_refl (term62 A B x y y')). Qed.
Lemma lem1046405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1046406 {A B : Type'} (x : A) (y' : B) (y : B) : (term63 A B x y y') = (term64 A B x y' y).
Proof. exact (MK_COMB (@lem1046405) (@lem1046404 A B x y' y)). Qed.
Lemma lem1046407 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem1046408 {A B : Type'} (x : A) (y' : B) (y : B) : ((term62 A B x y y') = (y' = y)) = ((term50 A B x y' y) = (y' = y)).
Proof. exact (MK_COMB (@lem1046406 A B x y' y) (@lem1046407 B y' y)). Qed.
Lemma lem1046409 {A B : Type'} (x : A) (y' : B) (y : B) : ((term50 A B x y' y) = (y' = y)) = ((term62 A B x y y') = (y' = y)).
Proof. exact (SYM (@lem1046408 A B x y' y)). Qed.
Lemma lem1046410 {A B : Type'} (y' : A) (x : A) (y : B) (h1 : term31 A B y' x y) : term31 A B y' x y.
Proof. exact (h1). Qed.
Lemma lem1046411 {A B : Type'} (y' : A) (x : A) (y'' : B) (y : B) (h1 : term16 A B y' x y'' y) : term16 A B y' x y'' y.
Proof. exact (h1). Qed.
Lemma lem1046413 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem1046415 {A B : Type'} (y' : A) (x : A) (y'' : B) (y : B) (h1 : term16 A B y' x y'' y) : y' = x.
Proof. exact (proj1 (@lem1046411 A B y' x y'' y h1)). Qed.
Lemma lem1046416 {A B : Type'} (y' : A) (x : A) (y'' : B) (y : B) (h1 : term16 A B y' x y'' y) : (y' = x) = (y' = x).
Proof. exact (prop_ext (fun h2 : y' = x => @lem1046413 A y' x h2) (fun h2 : y' = x => @lem1046415 A B y' x y'' y h1)). Qed.
Lemma lem1046417 {A B : Type'} (y' : A) (x : A) (y'' : B) (y : B) (h1 : term16 A B y' x y'' y) : y' = x.
Proof. exact (EQ_MP (@lem1046416 A B y' x y'' y h1) (@lem1046415 A B y' x y'' y h1)). Qed.
Lemma lem1046418 {A B : Type'} (y' : A) (x : A) (y : B) (h1 : term31 A B y' x y) : y' = x.
Proof. exact (ex_elim (@lem1046410 A B y' x y h1) (fun y'' : B => fun h0 : term29 A B y' x y y'' => @lem1046417 A B y' x y'' y h0)). Qed.
Lemma lem1046419 {A B : Type'} (y : B) (y' : A) (x : A) : term65 A B y y' x.
Proof. exact (fun h0 : term31 A B y' x y => @lem1046418 A B y' x y h0). Qed.
Lemma lem1046420 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem1046421 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : term50 A B x y' y) : term50 A B x y' y.
Proof. exact (h1). Qed.
Lemma lem1046422 {A B : Type'} (x' : A) (x : A) (y' : B) (y : B) (h1 : term16 A B x' x y' y) : term16 A B x' x y' y.
Proof. exact (h1). Qed.
Lemma lem1046423 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : y' = y.
Proof. exact (h1). Qed.
Lemma lem1046425 {A B : Type'} (x' : A) (x : A) (y' : B) (y : B) (h1 : term16 A B x' x y' y) : y' = y.
Proof. exact (proj2 (@lem1046422 A B x' x y' y h1)). Qed.
Lemma lem1046427 {A B : Type'} (x' : A) (x : A) (y' : B) (y : B) (h1 : term16 A B x' x y' y) : (y' = y) = (y' = y).
Proof. exact (prop_ext (fun h2 : y' = y => @lem1046423 B y' y h2) (fun h2 : y' = y => @lem1046425 A B x' x y' y h1)). Qed.
Lemma lem1046428 {A B : Type'} (x' : A) (x : A) (y' : B) (y : B) (h1 : term16 A B x' x y' y) : y' = y.
Proof. exact (EQ_MP (@lem1046427 A B x' x y' y h1) (@lem1046425 A B x' x y' y h1)). Qed.
Lemma lem1046429 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : term50 A B x y' y) : y' = y.
Proof. exact (ex_elim (@lem1046421 A B x y' y h1) (fun x' : A => fun h0 : term48 A B x y' y x' => @lem1046428 A B x' x y' y h0)). Qed.
Lemma lem1046430 {A B : Type'} (x : A) (y' : B) (y : B) : term66 A B x y' y.
Proof. exact (fun h0 : term50 A B x y' y => @lem1046429 A B x y' y h0). Qed.
Lemma lem1046431 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : y' = y.
Proof. exact (h1). Qed.
Lemma lem1046453 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem1046454 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1046455 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : (@eq A y') = (@eq A x).
Proof. exact (MK_COMB (@lem1046454 A) (@lem1046453 A y' x h1)). Qed.
Lemma lem1046456 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1046457 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : (y' = x) = (x = x).
Proof. exact (MK_COMB (@lem1046455 A y' x h1) (@lem1046456 A x)). Qed.
Lemma lem1046459 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1046460 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1046459 A x). Qed.
Lemma lem1046461 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : (y' = x) = True.
Proof. exact (TRANS (@lem1046457 A y' x h1) (@lem1046460 A x)). Qed.
Lemma lem1046462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1046463 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : (term67 A y' x) = (and True).
Proof. exact (MK_COMB (@lem1046462) (@lem1046461 A y' x h1)). Qed.
Lemma lem1046468 {B : Type'} (y' : B) (y : B) : (y' = y) = (y' = y).
Proof. exact (eq_refl (y' = y)). Qed.
Lemma lem1046469 {A B : Type'} (y' : B) (y : B) (y'' : A) (x : A) (h1 : y'' = x) : (term16 A B y'' x y' y) = (term68 B y' y).
Proof. exact (MK_COMB (@lem1046463 A y'' x h1) (@lem1046468 B y' y)). Qed.
Lemma lem1046471 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1046472 {B : Type'} (y' : B) (y : B) : (term68 B y' y) = (y' = y).
Proof. exact (@lem1046471 (y' = y)). Qed.
Lemma lem1046477 {A B : Type'} (y' : B) (y : B) (y'' : A) (x : A) (h1 : y'' = x) : (term16 A B y'' x y' y) = (y' = y).
Proof. exact (TRANS (@lem1046469 A B y' y y'' x h1) (@lem1046472 B y' y)). Qed.
Lemma lem1046478 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : (term29 A B y' x y) = (term69 B y).
Proof. exact (fun_ext (fun y'' : B => @lem1046477 A B y'' y y' x h1)). Qed.
Lemma lem1046479 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1046480 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : (term31 A B y' x y) = (term70 B y).
Proof. exact (MK_COMB (@lem1046479 B) (@lem1046478 A B y y' x h1)). Qed.
Lemma lem1046485 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : (term70 B y) = (term31 A B y' x y).
Proof. exact (SYM (@lem1046480 A B y y' x h1)). Qed.
Lemma lem1046509 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : y' = y.
Proof. exact (h1). Qed.
Lemma lem1046510 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1046511 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : (@eq B y') = (@eq B y).
Proof. exact (MK_COMB (@lem1046510 B) (@lem1046509 B y' y h1)). Qed.
Lemma lem1046512 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1046513 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : (y' = y) = (y = y).
Proof. exact (MK_COMB (@lem1046511 B y' y h1) (@lem1046512 B y)). Qed.
Lemma lem1046515 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1046516 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem1046515 B x). Qed.
Lemma lem1046517 {B : Type'} (y : B) : (y = y) = True.
Proof. exact (@lem1046516 B y). Qed.
Lemma lem1046518 {B : Type'} (y' : B) (y : B) (h1 : y' = y) : (y' = y) = True.
Proof. exact (TRANS (@lem1046513 B y' y h1) (@lem1046517 B y)). Qed.
Lemma lem1046519 {A : Type'} (x' : A) (x : A) : (term67 A x' x) = (term67 A x' x).
Proof. exact (eq_refl (term67 A x' x)). Qed.
Lemma lem1046520 {A B : Type'} (x' : A) (x : A) (y' : B) (y : B) (h1 : y' = y) : (term16 A B x' x y' y) = (term71 A x' x).
Proof. exact (MK_COMB (@lem1046519 A x' x) (@lem1046518 B y' y h1)). Qed.
Lemma lem1046522 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1046523 {A : Type'} (x' : A) (x : A) : (term71 A x' x) = (x' = x).
Proof. exact (@lem1046522 (x' = x)). Qed.
Lemma lem1046526 {A B : Type'} (x' : A) (x : A) (y' : B) (y : B) (h1 : y' = y) : (term16 A B x' x y' y) = (x' = x).
Proof. exact (TRANS (@lem1046520 A B x' x y' y h1) (@lem1046523 A x' x)). Qed.
Lemma lem1046527 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : (term48 A B x y' y) = (term69 A x).
Proof. exact (fun_ext (fun x' : A => @lem1046526 A B x' x y' y h1)). Qed.
Lemma lem1046528 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1046529 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : (term50 A B x y' y) = (term70 A x).
Proof. exact (MK_COMB (@lem1046528 A) (@lem1046527 A B x y' y h1)). Qed.
Lemma lem1046534 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : (term70 A x) = (term50 A B x y' y).
Proof. exact (SYM (@lem1046529 A B x y' y h1)). Qed.
Lemma lem1046535 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1046536 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1046537 {A : Type'} (x : A) : term70 A x.
Proof. exact (ex_intro (term69 A x) x (@lem1046536 A x)). Qed.
Lemma lem1046538 {B : Type'} (y : B) : term70 B y.
Proof. exact (ex_intro (term69 B y) y (@lem1046535 B y)). Qed.
Lemma lem1046539 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : term50 A B x y' y.
Proof. exact (EQ_MP (@lem1046534 A B x y' y h1) (@lem1046537 A x)). Qed.
Lemma lem1046540 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : term31 A B y' x y.
Proof. exact (EQ_MP (@lem1046485 A B y y' x h1) (@lem1046538 B y)). Qed.
Lemma lem1046541 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : (y' = y) = (term50 A B x y' y).
Proof. exact (prop_ext (fun h2 : y' = y => @lem1046539 A B x y' y h1) (fun h2 : term50 A B x y' y => @lem1046431 B y' y h1)). Qed.
Lemma lem1046542 {A B : Type'} (x : A) (y' : B) (y : B) (h1 : y' = y) : term50 A B x y' y.
Proof. exact (EQ_MP (@lem1046541 A B x y' y h1) (@lem1046431 B y' y h1)). Qed.
Lemma lem1046543 {A B : Type'} (x : A) (y' : B) (y : B) : term72 A B x y' y.
Proof. exact (fun h0 : y' = y => @lem1046542 A B x y' y h0). Qed.
Lemma lem1046544 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : (y' = x) = (term31 A B y' x y).
Proof. exact (prop_ext (fun h2 : y' = x => @lem1046540 A B y y' x h1) (fun h2 : term31 A B y' x y => @lem1046420 A y' x h1)). Qed.
Lemma lem1046545 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : term31 A B y' x y.
Proof. exact (EQ_MP (@lem1046544 A B y y' x h1) (@lem1046420 A y' x h1)). Qed.
Lemma lem1046546 {A B : Type'} (y' : A) (x : A) (y : B) : term73 A B y' x y.
Proof. exact (fun h0 : y' = x => @lem1046545 A B y y' x h0). Qed.
Lemma lem1046547 {A B : Type'} (x : A) (y' : B) (y : B) : term74 A B x y' y.
Proof. exact (conj (@lem1046430 A B x y' y) (@lem1046543 A B x y' y)). Qed.
Lemma lem1046548 {A B : Type'} (x : A) (y' : B) (y : B) : (term74 A B x y' y) = ((term50 A B x y' y) = (y' = y)).
Proof. exact (@lem32 (term50 A B x y' y) (y' = y)). Qed.
Lemma lem1046549 {A B : Type'} (x : A) (y' : B) (y : B) : (term50 A B x y' y) = (y' = y).
Proof. exact (EQ_MP (@lem1046548 A B x y' y) (@lem1046547 A B x y' y)). Qed.
Lemma lem1046550 {A B : Type'} (y' : A) (x : A) (y : B) : term75 A B y' x y.
Proof. exact (conj (@lem1046419 A B y y' x) (@lem1046546 A B y' x y)). Qed.
Lemma lem1046551 {A B : Type'} (y : B) (y' : A) (x : A) : (term75 A B y' x y) = ((term31 A B y' x y) = (y' = x)).
Proof. exact (@lem32 (term31 A B y' x y) (y' = x)). Qed.
Lemma lem1046552 {A B : Type'} (y : B) (y' : A) (x : A) : (term31 A B y' x y) = (y' = x).
Proof. exact (EQ_MP (@lem1046551 A B y y' x) (@lem1046550 A B y' x y)). Qed.
Lemma lem1046553 {A B : Type'} (x : A) (y' : B) (y : B) : (term62 A B x y y') = (y' = y).
Proof. exact (EQ_MP (@lem1046409 A B x y' y) (@lem1046549 A B x y' y)). Qed.
Lemma lem1046554 {A B : Type'} (y : B) (y' : A) (x : A) : (term59 A B x y y') = (y' = x).
Proof. exact (EQ_MP (@lem1046403 A B y y' x) (@lem1046552 A B y y' x)). Qed.
Lemma lem1046559 {A B : Type'} (x : A) (y : B) : term76 A B x y.
Proof. exact (fun y' : B => @lem1046553 A B x y' y). Qed.
Lemma lem1046564 {A B : Type'} (y : B) (x : A) : term77 A B y x.
Proof. exact (fun y' : A => @lem1046554 A B y y' x). Qed.
Lemma lem1046565 {A B : Type'} (x : A) (y : B) : (term53 A B x y) = y.
Proof. exact (@lem1046397 A B x y (@lem1046559 A B x y)). Qed.
Lemma lem1046566 {A B : Type'} (y : B) (x : A) : (term34 A B x y) = x.
Proof. exact (@lem1046393 A B y x (@lem1046564 A B y x)). Qed.
Lemma lem1046567 {A B : Type'} (x : A) (y : B) : term56 A B x y.
Proof. exact (conj (@lem1046566 A B y x) (@lem1046565 A B x y)). Qed.
Lemma lem1046568 {A B C : Type'} (x : A) (y : B) (P : type1412 A B C) (h1 : term8 A B C P) : term55 A B C P x y.
Proof. exact (EQ_MP (@lem1046389 A B C x y P h1) (@lem1046567 A B x y)). Qed.
Lemma lem1046573 {A B C : Type'} (x : A) (P : type1412 A B C) (h1 : term8 A B C P) : term78 A B C P x.
Proof. exact (fun y : B => @lem1046568 A B C x y P h1). Qed.
Lemma lem1046578 {A B C : Type'} (P : type1412 A B C) (h1 : term8 A B C P) : term79 A B C P.
Proof. exact (fun x : A => @lem1046573 A B C x P h1). Qed.
Lemma lem1046579 {A B C : Type'} (P : type1412 A B C) (h1 : term8 A B C P) : term80 A B C P.
Proof. exact (ex_intro (term81 A B C P) (term40 A B C P) (@lem1046578 A B C P h1)). Qed.
Lemma lem1046580 {A B C : Type'} (P : type1412 A B C) (h1 : term8 A B C P) : term82 A B C P.
Proof. exact (ex_intro (term83 A B C P) (term21 A B C P) (@lem1046579 A B C P h1)). Qed.
Lemma lem1046581 {A B C : Type'} (P : type1412 A B C) : term84 A B C P.
Proof. exact (fun h0 : term8 A B C P => @lem1046580 A B C P h0). Qed.
Lemma lem1046586 {A B C : Type'} : term85 A B C.
Proof. exact (fun P : type1412 A B C => @lem1046581 A B C P). Qed.
