Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_PRODUCT_term_abbrevs.
Require Import FINITE_PRODUCT_DEPENDENT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4323220 {A B C : Type'} (f : type1412 A B C) : term0 A B C f.
Proof. exact (@lem4323219 A B C f). Qed.
Lemma lem4323221 {A B C : Type'} (f : type1412 A B C) : (term0 A B C f) = (term1 A B C f).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem4323222 {A B C : Type'} (f : type1412 A B C) : term1 A B C f.
Proof. exact (EQ_MP (@lem4323221 A B C f) (@lem4323220 A B C f)). Qed.
Lemma lem4323223 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) : term2 A B C f s.
Proof. exact (@lem4323222 A B C f s). Qed.
Lemma lem4323224 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) : (term2 A B C f s) = (term3 A B C s f).
Proof. exact (eq_refl (term2 A B C f s)). Qed.
Lemma lem4323225 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) : term3 A B C s f.
Proof. exact (EQ_MP (@lem4323224 A B C s f) (@lem4323223 A B C f s)). Qed.
Lemma lem4323226 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) (t : type1413 A B) : term4 A B C s f t.
Proof. exact (@lem4323225 A B C s f t). Qed.
Lemma lem4323227 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term4 A B C s f t) = (term5 A B C s t f).
Proof. exact (eq_refl (term4 A B C s f t)). Qed.
Lemma lem4323228 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term5 A B C s t f.
Proof. exact (EQ_MP (@lem4323227 A B C s t f) (@lem4323226 A B C s f t)). Qed.
Lemma lem4323229 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term6 A B s t) : term6 A B s t.
Proof. exact (h1). Qed.
Lemma lem4323230 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term6 A B s t) : term7 A B C s t f.
Proof. exact (@lem4323228 A B C s t f (@lem4323229 A B s t h1)). Qed.
Lemma lem4323231 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term7 A B C s t f) = ((term7 A B C s t f) = True).
Proof. exact (@lem7 (term7 A B C s t f)). Qed.
Lemma lem4323232 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term6 A B s t) : (term7 A B C s t f) = True.
Proof. exact (EQ_MP (@lem4323231 A B C s t f) (@lem4323230 A B C f s t h1)). Qed.
Lemma lem4323249 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4323250 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem4323249 p q p' q'). Qed.
Lemma lem4323251 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem4323250 p q p'). Qed.
Lemma lem4323252 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term11 A B s t.
Proof. exact (@lem4323251 (term12 A B s t) (term13 A B s t)). Qed.
Lemma lem4323253 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : term14 A B s t p'.
Proof. exact (@lem4323252 A B s t p'). Qed.
Lemma lem4323254 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : (term14 A B s t p') = (term15 A B s t p').
Proof. exact (eq_refl (term14 A B s t p')). Qed.
Lemma lem4323255 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : term15 A B s t p'.
Proof. exact (EQ_MP (@lem4323254 A B s t p') (@lem4323253 A B s t p')). Qed.
Lemma lem4323256 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : term16 A B s t p' q'.
Proof. exact (@lem4323255 A B s t p' q'). Qed.
Lemma lem4323257 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : (term16 A B s t p' q') = (term17 A B s t p' q').
Proof. exact (eq_refl (term16 A B s t p' q')). Qed.
Lemma lem4323258 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : term17 A B s t p' q'.
Proof. exact (EQ_MP (@lem4323257 A B s t p' q') (@lem4323256 A B s t p' q')). Qed.
Lemma lem4323261 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term12 A B s t) = (term12 A B s t).
Proof. exact (eq_refl (term12 A B s t)). Qed.
Lemma lem4323262 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term18 A B s t q'.
Proof. exact (@lem4323258 A B s t (term12 A B s t) q'). Qed.
Lemma lem4323263 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term19 A B s t q'.
Proof. exact (@lem4323262 A B s t q' (@lem4323261 A B s t)). Qed.
Lemma lem4323264 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : term12 A B s t.
Proof. exact (h1). Qed.
Lemma lem4323265 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : @FINITE B t.
Proof. exact (proj2 (@lem4323264 A B s t h1)). Qed.
Lemma lem4323266 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem4323268 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : @FINITE A s.
Proof. exact (proj1 (@lem4323264 A B s t h1)). Qed.
Lemma lem4323269 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4323272 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term20 A B C s t f.
Proof. exact (fun h0 : term6 A B s t => @lem4323232 A B C f s t h0). Qed.
Lemma lem4323273 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1409 A B) : term21 A B s t f.
Proof. exact (@lem4323272 A B (prod A B) s t f). Qed.
Lemma lem4323274 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term22 A B s t.
Proof. exact (@lem4323273 A B s (term23 A B t) (@pair A B)). Qed.
Lemma lem4323275 {A B : Type'} (x : A) (t : B -> Prop) : (term24 A B t x) = t.
Proof. exact (eq_refl (term24 A B t x)). Qed.
Lemma lem4323276 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem4323277 {A B : Type'} (x : A) (t : B -> Prop) : (term25 A B t x) = (@FINITE B t).
Proof. exact (MK_COMB (@lem4323276 B) (@lem4323275 A B x t)). Qed.
Lemma lem4323278 {A : Type'} (x : A) (s : A -> Prop) : (term26 A x s) = (term26 A x s).
Proof. exact (eq_refl (term26 A x s)). Qed.
Lemma lem4323279 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term27 A B s t x) = (term28 A B x s t).
Proof. exact (MK_COMB (@lem4323278 A x s) (@lem4323277 A B x t)). Qed.
Lemma lem4323280 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term29 A B s t) = (term30 A B s t).
Proof. exact (fun_ext (fun x : A => @lem4323279 A B x s t)). Qed.
Lemma lem4323281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4323282 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term31 A B s t) = (term32 A B s t).
Proof. exact (MK_COMB (@lem4323281 A) (@lem4323280 A B s t)). Qed.
Lemma lem4323283 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem4323284 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term34 A B s t) = (term35 A B s t).
Proof. exact (MK_COMB (@lem4323283 A s) (@lem4323282 A B s t)). Qed.
Lemma lem4323285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4323286 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term36 A B s t) = (term37 A B s t).
Proof. exact (MK_COMB (@lem4323285) (@lem4323284 A B s t)). Qed.
Lemma lem4323287 {A B : Type'} (x : A) (t : B -> Prop) : (term24 A B t x) = t.
Proof. exact (eq_refl (term24 A B t x)). Qed.
Lemma lem4323288 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem4323289 {A B : Type'} (x : A) (y : B) (t : B -> Prop) : (term38 A B y t x) = (@IN B y t).
Proof. exact (MK_COMB (@lem4323288 B y) (@lem4323287 A B x t)). Qed.
Lemma lem4323290 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term39 A x s).
Proof. exact (eq_refl (term39 A x s)). Qed.
Lemma lem4323291 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term40 A B s y t x) = (term41 A B x s y t).
Proof. exact (MK_COMB (@lem4323290 A x s) (@lem4323289 A B x y t)). Qed.
Lemma lem4323292 {A B : Type'} (GEN_PVAR_127 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_127) = (@SETSPEC (prod A B) GEN_PVAR_127).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_127)). Qed.
Lemma lem4323293 {A B : Type'} (GEN_PVAR_127 : prod A B) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term42 A B GEN_PVAR_127 s y t x) = (term43 A B GEN_PVAR_127 x s y t).
Proof. exact (MK_COMB (@lem4323292 A B GEN_PVAR_127) (@lem4323291 A B x s y t)). Qed.
Lemma lem4323294 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4323295 {A B : Type'} (GEN_PVAR_127 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) (y : B) : (term44 A B GEN_PVAR_127 s t x y) = (term45 A B GEN_PVAR_127 s t x y).
Proof. exact (MK_COMB (@lem4323293 A B GEN_PVAR_127 x s y t) (@lem4323294 A B x y)). Qed.
Lemma lem4323296 {A B : Type'} (GEN_PVAR_127 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) : (term46 A B GEN_PVAR_127 s t x) = (term47 A B GEN_PVAR_127 s t x).
Proof. exact (fun_ext (fun y : B => @lem4323295 A B GEN_PVAR_127 s t x y)). Qed.
Lemma lem4323297 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4323298 {A B : Type'} (GEN_PVAR_127 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) : (term48 A B GEN_PVAR_127 s t x) = (term49 A B GEN_PVAR_127 s t x).
Proof. exact (MK_COMB (@lem4323297 B) (@lem4323296 A B GEN_PVAR_127 s t x)). Qed.
Lemma lem4323299 {A B : Type'} (GEN_PVAR_127 : prod A B) (s : A -> Prop) (t : B -> Prop) : (term50 A B GEN_PVAR_127 s t) = (term51 A B GEN_PVAR_127 s t).
Proof. exact (fun_ext (fun x : A => @lem4323298 A B GEN_PVAR_127 s t x)). Qed.
Lemma lem4323300 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4323301 {A B : Type'} (GEN_PVAR_127 : prod A B) (s : A -> Prop) (t : B -> Prop) : (term52 A B GEN_PVAR_127 s t) = (term53 A B GEN_PVAR_127 s t).
Proof. exact (MK_COMB (@lem4323300 A) (@lem4323299 A B GEN_PVAR_127 s t)). Qed.
Lemma lem4323302 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term54 A B s t) = (term55 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_127 : prod A B => @lem4323301 A B GEN_PVAR_127 s t)). Qed.
Lemma lem4323303 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4323304 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term56 A B s t) = (term57 A B s t).
Proof. exact (MK_COMB (@lem4323303 A B) (@lem4323302 A B s t)). Qed.
Lemma lem4323305 {A B : Type'} : (@FINITE (prod A B)) = (@FINITE (prod A B)).
Proof. exact (eq_refl (@FINITE (prod A B))). Qed.
Lemma lem4323306 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term58 A B s t) = (term13 A B s t).
Proof. exact (MK_COMB (@lem4323305 A B) (@lem4323304 A B s t)). Qed.
Lemma lem4323307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4323308 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term59 A B s t) = (term60 A B s t).
Proof. exact (MK_COMB (@lem4323307) (@lem4323306 A B s t)). Qed.
Lemma lem4323309 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem4323310 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term58 A B s t) = True) = ((term13 A B s t) = True).
Proof. exact (MK_COMB (@lem4323308 A B s t) (@lem4323309)). Qed.
Lemma lem4323311 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term22 A B s t) = (term61 A B s t).
Proof. exact (MK_COMB (@lem4323286 A B s t) (@lem4323310 A B s t)). Qed.
Lemma lem4323312 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term61 A B s t.
Proof. exact (EQ_MP (@lem4323311 A B s t) (@lem4323274 A B s t)). Qed.
Lemma lem4323316 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4323269 A s) (@lem4323268 A B s t h1)). Qed.
Lemma lem4323317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4323318 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term33 A s) = (and True).
Proof. exact (MK_COMB (@lem4323317) (@lem4323316 A B s t h1)). Qed.
Lemma lem4323326 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4323327 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem4323326 p q p' q'). Qed.
Lemma lem4323328 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem4323327 p q p'). Qed.
Lemma lem4323329 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : term62 A B x s t.
Proof. exact (@lem4323328 (@IN A x s) (@FINITE B t)). Qed.
Lemma lem4323330 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (p' : Prop) : term63 A B x s t p'.
Proof. exact (@lem4323329 A B x s t p'). Qed.
Lemma lem4323331 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (p' : Prop) : (term63 A B x s t p') = (term64 A B x s t p').
Proof. exact (eq_refl (term63 A B x s t p')). Qed.
Lemma lem4323332 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (p' : Prop) : term64 A B x s t p'.
Proof. exact (EQ_MP (@lem4323331 A B x s t p') (@lem4323330 A B x s t p')). Qed.
Lemma lem4323333 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : term65 A B x s t p' q'.
Proof. exact (@lem4323332 A B x s t p' q'). Qed.
Lemma lem4323334 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : (term65 A B x s t p' q') = (term66 A B x s t p' q').
Proof. exact (eq_refl (term65 A B x s t p' q')). Qed.
Lemma lem4323335 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : term66 A B x s t p' q'.
Proof. exact (EQ_MP (@lem4323334 A B x s t p' q') (@lem4323333 A B x s t p' q')). Qed.
Lemma lem4323336 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4323337 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (q' : Prop) : term67 A B t x s q'.
Proof. exact (@lem4323335 A B x s t (@IN A x s) q'). Qed.
Lemma lem4323338 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (q' : Prop) : term68 A B t x s q'.
Proof. exact (@lem4323337 A B t x s q' (@lem4323336 A x s)). Qed.
Lemma lem4323343 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem4323266 B t) (@lem4323265 A B s t h1)). Qed.
Lemma lem4323344 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : term69 A B x s t.
Proof. exact (fun h0 : @IN A x s => @lem4323343 A B s t h1). Qed.
Lemma lem4323345 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : term70 A B t x s.
Proof. exact (@lem4323338 A B t x s True). Qed.
Lemma lem4323346 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term28 A B x s t) = (term71 A x s).
Proof. exact (@lem4323345 A B t x s (@lem4323344 A B x s t h1)). Qed.
Lemma lem4323348 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4323349 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = True.
Proof. exact (@lem4323348 (@IN A x s)). Qed.
Lemma lem4323350 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term28 A B x s t) = True.
Proof. exact (TRANS (@lem4323346 A B x s t h1) (@lem4323349 A x s)). Qed.
Lemma lem4323351 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term30 A B s t) = (term72 A).
Proof. exact (fun_ext (fun x : A => @lem4323350 A B x s t h1)). Qed.
Lemma lem4323352 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4323353 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term32 A B s t) = (term73 A).
Proof. exact (MK_COMB (@lem4323352 A) (@lem4323351 A B s t h1)). Qed.
Lemma lem4323355 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4323356 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (@lem4323355 A t). Qed.
Lemma lem4323357 {A : Type'} : (term73 A) = True.
Proof. exact (@lem4323356 A True). Qed.
Lemma lem4323358 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term32 A B s t) = True.
Proof. exact (TRANS (@lem4323353 A B s t h1) (@lem4323357 A)). Qed.
Lemma lem4323359 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term35 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4323318 A B s t h1) (@lem4323358 A B s t h1)). Qed.
Lemma lem4323361 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4323362 : (True /\ True) = True.
Proof. exact (@lem4323361 True). Qed.
Lemma lem4323363 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term35 A B s t) = True.
Proof. exact (TRANS (@lem4323359 A B s t h1) (@lem4323362)). Qed.
Lemma lem4323364 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : True = (term35 A B s t).
Proof. exact (SYM (@lem4323363 A B s t h1)). Qed.
Lemma lem4323365 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : term35 A B s t.
Proof. exact (EQ_MP (@lem4323364 A B s t h1) (@lem0)). Qed.
Lemma lem4323366 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term12 A B s t) : (term13 A B s t) = True.
Proof. exact (@lem4323312 A B s t (@lem4323365 A B s t h1)). Qed.
Lemma lem4323367 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term75 A B s t.
Proof. exact (fun h0 : term12 A B s t => @lem4323366 A B s t h0). Qed.
Lemma lem4323368 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term76 A B s t.
Proof. exact (@lem4323263 A B s t True). Qed.
Lemma lem4323369 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term77 A B s t) = (term78 A B s t).
Proof. exact (@lem4323368 A B s t (@lem4323367 A B s t)). Qed.
Lemma lem4323371 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4323372 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term78 A B s t) = True.
Proof. exact (@lem4323371 (term12 A B s t)). Qed.
Lemma lem4323373 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term77 A B s t) = True.
Proof. exact (TRANS (@lem4323369 A B s t) (@lem4323372 A B s t)). Qed.
Lemma lem4323374 {A B : Type'} (s : A -> Prop) : (term79 A B s) = (term80 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4323373 A B s t)). Qed.
Lemma lem4323375 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4323376 {A B : Type'} (s : A -> Prop) : (term81 A B s) = (term82 B).
Proof. exact (MK_COMB (@lem4323375 B) (@lem4323374 A B s)). Qed.
Lemma lem4323378 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4323379 {B : Type'} (t : Prop) : (term83 B t) = t.
Proof. exact (@lem4323378 (B -> Prop) t). Qed.
Lemma lem4323380 {B : Type'} : (term82 B) = True.
Proof. exact (@lem4323379 B True). Qed.
Lemma lem4323381 {A B : Type'} (s : A -> Prop) : (term81 A B s) = True.
Proof. exact (TRANS (@lem4323376 A B s) (@lem4323380 B)). Qed.
Lemma lem4323382 {A B : Type'} : (term84 A B) = (term80 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4323381 A B s)). Qed.
Lemma lem4323383 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4323384 {A B : Type'} : (term85 A B) = (term82 A).
Proof. exact (MK_COMB (@lem4323383 A) (@lem4323382 A B)). Qed.
Lemma lem4323386 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4323387 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (@lem4323386 (A -> Prop) t). Qed.
Lemma lem4323388 {A : Type'} : (term82 A) = True.
Proof. exact (@lem4323387 A True). Qed.
Lemma lem4323389 {A B : Type'} : (term85 A B) = True.
Proof. exact (TRANS (@lem4323384 A B) (@lem4323388 A)). Qed.
Lemma lem4323390 {A B : Type'} : True = (term85 A B).
Proof. exact (SYM (@lem4323389 A B)). Qed.
Lemma lem4323391 {A B : Type'} : term85 A B.
Proof. exact (EQ_MP (@lem4323390 A B) (@lem0)). Qed.
