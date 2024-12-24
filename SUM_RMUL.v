Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_RMUL_term_abbrevs.
Require Import SUM_LMUL_spec.
Require Import thm0_spec.
Require Import thm1338712_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem7070265 {A : Type'} (f : A -> real) : term0 A f.
Proof. exact (@lem7070264 A f). Qed.
Lemma lem7070266 {A : Type'} (f : A -> real) : (term0 A f) = (term1 A f).
Proof. exact (eq_refl (term0 A f)). Qed.
Lemma lem7070267 {A : Type'} (f : A -> real) : term1 A f.
Proof. exact (EQ_MP (@lem7070266 A f) (@lem7070265 A f)). Qed.
Lemma lem7070268 {A : Type'} (f : A -> real) (c : real) : term2 A f c.
Proof. exact (@lem7070267 A f c). Qed.
Lemma lem7070269 {A : Type'} (c : real) (f : A -> real) : (term2 A f c) = (term3 A c f).
Proof. exact (eq_refl (term2 A f c)). Qed.
Lemma lem7070270 {A : Type'} (c : real) (f : A -> real) : term3 A c f.
Proof. exact (EQ_MP (@lem7070269 A c f) (@lem7070268 A f c)). Qed.
Lemma lem7070271 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) : term4 A c f s.
Proof. exact (@lem7070270 A c f s). Qed.
Lemma lem7070272 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term4 A c f s) = ((term5 A s c f) = (term6 A c s f)).
Proof. exact (eq_refl (term4 A c f s)). Qed.
Lemma lem7070274 (x : real) : term7 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem7070275 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7070276 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem7070275 x) (@lem7070274 x)). Qed.
Lemma lem7070277 (x : real) (y : real) : term9 x y.
Proof. exact (@lem7070276 x y). Qed.
Lemma lem7070278 (y : real) (x : real) : (term9 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem7070295 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem7070278 y x) (@lem7070277 x y)). Qed.
Lemma lem7070296 {A : Type'} (c : real) (f : A -> real) (x : A) : (term10 A f x c) = (term11 A c f x).
Proof. exact (@lem7070295 c (f x)). Qed.
Lemma lem7070297 {A : Type'} (c : real) (f : A -> real) : (term12 A f c) = (term13 A c f).
Proof. exact (fun_ext (fun x : A => @lem7070296 A c f x)). Qed.
Lemma lem7070298 {A : Type'} (s : A -> Prop) : (@sum A s) = (@sum A s).
Proof. exact (eq_refl (@sum A s)). Qed.
Lemma lem7070299 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term14 A s f c) = (term5 A s c f).
Proof. exact (MK_COMB (@lem7070298 A s) (@lem7070297 A c f)). Qed.
Lemma lem7070300 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070301 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term15 A s f c) = (term16 A s c f).
Proof. exact (MK_COMB (@lem7070300) (@lem7070299 A s c f)). Qed.
Lemma lem7070303 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem7070278 y x) (@lem7070277 x y)). Qed.
Lemma lem7070304 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term17 A s f c) = (term6 A c s f).
Proof. exact (@lem7070303 c (@sum A s f)). Qed.
Lemma lem7070305 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term14 A s f c) = (term17 A s f c)) = ((term5 A s c f) = (term6 A c s f)).
Proof. exact (MK_COMB (@lem7070301 A s c f) (@lem7070304 A c s f)). Qed.
Lemma lem7070306 {A : Type'} (c : real) (f : A -> real) : (term18 A f c) = (term19 A c f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7070305 A c s f)). Qed.
Lemma lem7070307 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7070308 {A : Type'} (c : real) (f : A -> real) : (term20 A f c) = (term3 A c f).
Proof. exact (MK_COMB (@lem7070307 A) (@lem7070306 A c f)). Qed.
Lemma lem7070309 {A : Type'} (f : A -> real) : (term21 A f) = (term22 A f).
Proof. exact (fun_ext (fun c : real => @lem7070308 A c f)). Qed.
Lemma lem7070310 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7070311 {A : Type'} (f : A -> real) : (term23 A f) = (term1 A f).
Proof. exact (MK_COMB (@lem7070310) (@lem7070309 A f)). Qed.
Lemma lem7070312 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7070311 A f)). Qed.
Lemma lem7070313 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7070314 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem7070313 A) (@lem7070312 A)). Qed.
Lemma lem7070315 {A : Type'} : (term27 A) = (term26 A).
Proof. exact (SYM (@lem7070314 A)). Qed.
Lemma lem7070331 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term5 A s c f) = (term6 A c s f).
Proof. exact (EQ_MP (@lem7070272 A c s f) (@lem7070271 A c f s)). Qed.
Lemma lem7070332 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term5 A s c f) = (term6 A c s f).
Proof. exact (@lem7070331 A c s f). Qed.
Lemma lem7070333 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070334 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term16 A s c f) = (term28 A c s f).
Proof. exact (MK_COMB (@lem7070333) (@lem7070332 A c s f)). Qed.
Lemma lem7070335 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term6 A c s f) = (term6 A c s f).
Proof. exact (eq_refl (term6 A c s f)). Qed.
Lemma lem7070336 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term5 A s c f) = (term6 A c s f)) = ((term6 A c s f) = (term6 A c s f)).
Proof. exact (MK_COMB (@lem7070334 A c s f) (@lem7070335 A c s f)). Qed.
Lemma lem7070338 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7070339 (x : real) : (x = x) = True.
Proof. exact (@lem7070338 real x). Qed.
Lemma lem7070340 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term6 A c s f) = (term6 A c s f)) = True.
Proof. exact (@lem7070339 (term6 A c s f)). Qed.
Lemma lem7070341 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term5 A s c f) = (term6 A c s f)) = True.
Proof. exact (TRANS (@lem7070336 A c s f) (@lem7070340 A c s f)). Qed.
Lemma lem7070342 {A : Type'} (c : real) (f : A -> real) : (term19 A c f) = (term29 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7070341 A c s f)). Qed.
Lemma lem7070343 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7070344 {A : Type'} (c : real) (f : A -> real) : (term3 A c f) = (term30 A).
Proof. exact (MK_COMB (@lem7070343 A) (@lem7070342 A c f)). Qed.
Lemma lem7070346 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070347 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem7070346 (A -> Prop) t). Qed.
Lemma lem7070348 {A : Type'} : (term30 A) = True.
Proof. exact (@lem7070347 A True). Qed.
Lemma lem7070349 {A : Type'} (c : real) (f : A -> real) : (term3 A c f) = True.
Proof. exact (TRANS (@lem7070344 A c f) (@lem7070348 A)). Qed.
Lemma lem7070350 {A : Type'} (f : A -> real) : (term22 A f) = term33.
Proof. exact (fun_ext (fun c : real => @lem7070349 A c f)). Qed.
Lemma lem7070351 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7070352 {A : Type'} (f : A -> real) : (term1 A f) = term34.
Proof. exact (MK_COMB (@lem7070351) (@lem7070350 A f)). Qed.
Lemma lem7070354 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070355 (t : Prop) : (term35 t) = t.
Proof. exact (@lem7070354 real t). Qed.
Lemma lem7070356 : term34 = True.
Proof. exact (@lem7070355 True). Qed.
Lemma lem7070357 {A : Type'} (f : A -> real) : (term1 A f) = True.
Proof. exact (TRANS (@lem7070352 A f) (@lem7070356)). Qed.
Lemma lem7070358 {A : Type'} : (term25 A) = (term36 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7070357 A f)). Qed.
Lemma lem7070359 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7070360 {A : Type'} : (term27 A) = (term37 A).
Proof. exact (MK_COMB (@lem7070359 A) (@lem7070358 A)). Qed.
Lemma lem7070362 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070363 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (@lem7070362 (A -> real) t). Qed.
Lemma lem7070364 {A : Type'} : (term37 A) = True.
Proof. exact (@lem7070363 A True). Qed.
Lemma lem7070365 {A : Type'} : (term27 A) = True.
Proof. exact (TRANS (@lem7070360 A) (@lem7070364 A)). Qed.
Lemma lem7070366 {A : Type'} : True = (term27 A).
Proof. exact (SYM (@lem7070365 A)). Qed.
Lemma lem7070367 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem7070366 A) (@lem0)). Qed.
Lemma lem7070368 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem7070315 A) (@lem7070367 A)). Qed.
