Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_EQ_MEMBERS_term_abbrevs.
Require Import EXTENSIONAL_EQ_spec.
Require Import IN_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Lemma lem4409264 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4409265 {A B : Type'} (s : A -> Prop) (h1 : term0 A B) : term1 A B s.
Proof. exact (@lem4409264 A B h1 s). Qed.
Lemma lem4409266 {A B : Type'} (s : A -> Prop) : (term1 A B s) = (term2 A B s).
Proof. exact (eq_refl (term1 A B s)). Qed.
Lemma lem4409267 {A B : Type'} (s : A -> Prop) (h1 : term0 A B) : term2 A B s.
Proof. exact (EQ_MP (@lem4409266 A B s) (@lem4409265 A B s h1)). Qed.
Lemma lem4409268 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term0 A B) : term3 A B s f.
Proof. exact (@lem4409267 A B s h1 f). Qed.
Lemma lem4409269 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term3 A B s f) = (term4 A B s f).
Proof. exact (eq_refl (term3 A B s f)). Qed.
Lemma lem4409270 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term0 A B) : term4 A B s f.
Proof. exact (EQ_MP (@lem4409269 A B s f) (@lem4409268 A B s f h1)). Qed.
Lemma lem4409271 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term0 A B) : term5 A B s f g.
Proof. exact (@lem4409270 A B s f h1 g). Qed.
Lemma lem4409272 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term5 A B s f g) = (term6 A B s f g).
Proof. exact (eq_refl (term5 A B s f g)). Qed.
Lemma lem4409273 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term0 A B) : term6 A B s f g.
Proof. exact (EQ_MP (@lem4409272 A B s f g) (@lem4409271 A B s f g h1)). Qed.
Lemma lem4409274 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term7 A B s f g) : term7 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4409275 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term0 A B) (h2 : term7 A B s f g) : f = g.
Proof. exact (@lem4409273 A B s f g h1 (@lem4409274 A B s f g h2)). Qed.
Lemma lem4409276 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term7 A B s f g) : term8 A B f g.
Proof. exact (fun h0 : term0 A B => @lem4409275 A B s f g h0 h1). Qed.
Lemma lem4409277 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term9 A B f g) : term9 A B f g.
Proof. exact (h1). Qed.
Lemma lem4409278 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term9 A B f g) : term8 A B f g.
Proof. exact (ex_elim (@lem4409277 A B f g h1) (fun s : A -> Prop => fun h0 : term10 A B f g s => @lem4409276 A B s f g h0)). Qed.
Lemma lem4409279 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4409280 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term0 A B) (h2 : term9 A B f g) : f = g.
Proof. exact (@lem4409278 A B f g h2 (@lem4409279 A B h1)). Qed.
Lemma lem4409281 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : term0 A B) : term11 A B f g.
Proof. exact (fun h0 : term9 A B f g => @lem4409280 A B f g h1 h0). Qed.
Lemma lem4409282 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term12 A B f.
Proof. exact (fun g : A -> B => @lem4409281 A B f g h1). Qed.
Lemma lem4409283 {A B : Type'} (h1 : term0 A B) : term13 A B.
Proof. exact (fun f : A -> B => @lem4409282 A B f h1). Qed.
Lemma lem4409284 {A B : Type'} : term14 A B.
Proof. exact (fun h0 : term0 A B => @lem4409283 A B h0). Qed.
Lemma lem4409285 {A B : Type'} : term13 A B.
Proof. exact (@lem4409284 A B (@lem4385509 A B)). Qed.
Lemma lem4409286 {A B : Type'} (f : A -> B) : term15 A B f.
Proof. exact (@lem4409285 A B f). Qed.
Lemma lem4409287 {A B : Type'} (f : A -> B) : (term15 A B f) = (term12 A B f).
Proof. exact (eq_refl (term15 A B f)). Qed.
Lemma lem4409288 {A B : Type'} (f : A -> B) : term12 A B f.
Proof. exact (EQ_MP (@lem4409287 A B f) (@lem4409286 A B f)). Qed.
Lemma lem4409289 {A B : Type'} (f : A -> B) (g : A -> B) : term16 A B f g.
Proof. exact (@lem4409288 A B f g). Qed.
Lemma lem4409290 {A B : Type'} (f : A -> B) (g : A -> B) : (term16 A B f g) = (term11 A B f g).
Proof. exact (eq_refl (term16 A B f g)). Qed.
Lemma lem4409316 {_83095 : Type'} : term17 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4409317 {_83095 : Type'} (p : _83095 -> Prop) : term18 _83095 p.
Proof. exact (@lem4409316 _83095 p). Qed.
Lemma lem4409318 {_83095 : Type'} (p : _83095 -> Prop) : (term18 _83095 p) = (term19 _83095 p).
Proof. exact (eq_refl (term18 _83095 p)). Qed.
Lemma lem4409319 {_83095 : Type'} (p : _83095 -> Prop) : term19 _83095 p.
Proof. exact (EQ_MP (@lem4409318 _83095 p) (@lem4409317 _83095 p)). Qed.
Lemma lem4409320 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term20 _83095 p x.
Proof. exact (@lem4409319 _83095 p x). Qed.
Lemma lem4409321 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 p x) = ((term21 _83095 x p) = (p x)).
Proof. exact (eq_refl (term20 _83095 p x)). Qed.
Lemma lem4409330 {A K : Type'} (k : K -> Prop) : term22 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4409331 {A K : Type'} (k : K -> Prop) : (term22 A K k) = (term23 A K k).
Proof. exact (eq_refl (term22 A K k)). Qed.
Lemma lem4409332 {A K : Type'} (k : K -> Prop) : term23 A K k.
Proof. exact (EQ_MP (@lem4409331 A K k) (@lem4409330 A K k)). Qed.
Lemma lem4409333 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term24 A K k s.
Proof. exact (@lem4409332 A K k s). Qed.
Lemma lem4409334 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term24 A K k s) = ((@cartesian_product A K k s) = (term25 A K k s)).
Proof. exact (eq_refl (term24 A K k s)). Qed.
Lemma lem4409357 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term25 A K k s).
Proof. exact (EQ_MP (@lem4409334 A K k s) (@lem4409333 A K k s)). Qed.
Lemma lem4409358 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term25 A K k s).
Proof. exact (@lem4409357 A K k s). Qed.
Lemma lem4409371 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4409372 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term26 A K x k s) = (term27 A K x k s).
Proof. exact (MK_COMB (@lem4409371 A K x) (@lem4409358 A K k s)). Qed.
Lemma lem4409374 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4409321 _83095 p x) (@lem4409320 _83095 p x)). Qed.
Lemma lem4409375 {A K : Type'} (p : type805 A K) (x : K -> A) : (term28 A K x p) = (p x).
Proof. exact (@lem4409374 (K -> A) p x). Qed.
Lemma lem4409376 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term29 A K x k s) = (term30 A K k s x).
Proof. exact (@lem4409375 A K (term31 A K k s) x). Qed.
Lemma lem4409377 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term30 A K k s f) = (term32 A K k f s).
Proof. exact (eq_refl (term30 A K k s f)). Qed.
Lemma lem4409378 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4409379 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term33 A K GEN_PVAR_140 k s f) = (term34 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4409378 A K GEN_PVAR_140) (@lem4409377 A K k f s)). Qed.
Lemma lem4409380 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4409381 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term35 A K GEN_PVAR_140 k s f) = (term36 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4409379 A K GEN_PVAR_140 k f s) (@lem4409380 A K f)). Qed.
Lemma lem4409382 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term37 A K GEN_PVAR_140 k s) = (term38 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4409381 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4409383 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4409384 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term39 A K GEN_PVAR_140 k s) = (term40 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4409383 A K) (@lem4409382 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4409385 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term41 A K k s) = (term42 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4409384 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4409386 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4409387 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term43 A K k s) = (term25 A K k s).
Proof. exact (MK_COMB (@lem4409386 A K) (@lem4409385 A K k s)). Qed.
Lemma lem4409388 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4409389 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term29 A K x k s) = (term27 A K x k s).
Proof. exact (MK_COMB (@lem4409388 A K x) (@lem4409387 A K k s)). Qed.
Lemma lem4409390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4409391 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term44 A K x k s) = (term45 A K x k s).
Proof. exact (MK_COMB (@lem4409390) (@lem4409389 A K x k s)). Qed.
Lemma lem4409392 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term30 A K k s x) = (term32 A K k x s).
Proof. exact (eq_refl (term30 A K k s x)). Qed.
Lemma lem4409393 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term29 A K x k s) = (term30 A K k s x)) = ((term27 A K x k s) = (term32 A K k x s)).
Proof. exact (MK_COMB (@lem4409391 A K x k s) (@lem4409392 A K k x s)). Qed.
Lemma lem4409394 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term27 A K x k s) = (term32 A K k x s).
Proof. exact (EQ_MP (@lem4409393 A K k x s) (@lem4409376 A K k s x)). Qed.
Lemma lem4409403 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term26 A K x k s) = (term32 A K k x s).
Proof. exact (TRANS (@lem4409372 A K x k s) (@lem4409394 A K k x s)). Qed.
Lemma lem4409404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4409405 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term46 A K x k s) = (term47 A K k x s).
Proof. exact (MK_COMB (@lem4409404) (@lem4409403 A K k x s)). Qed.
Lemma lem4409409 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term25 A K k s).
Proof. exact (EQ_MP (@lem4409334 A K k s) (@lem4409333 A K k s)). Qed.
Lemma lem4409410 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term25 A K k s).
Proof. exact (@lem4409409 A K k s). Qed.
Lemma lem4409423 {A K : Type'} (y : K -> A) : (@IN (K -> A) y) = (@IN (K -> A) y).
Proof. exact (eq_refl (@IN (K -> A) y)). Qed.
Lemma lem4409424 {A K : Type'} (y : K -> A) (k : K -> Prop) (s : type1470 A K) : (term26 A K y k s) = (term27 A K y k s).
Proof. exact (MK_COMB (@lem4409423 A K y) (@lem4409410 A K k s)). Qed.
Lemma lem4409426 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4409321 _83095 p x) (@lem4409320 _83095 p x)). Qed.
Lemma lem4409427 {A K : Type'} (p : type805 A K) (x : K -> A) : (term28 A K x p) = (p x).
Proof. exact (@lem4409426 (K -> A) p x). Qed.
Lemma lem4409428 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (y : K -> A) : (term29 A K y k s) = (term30 A K k s y).
Proof. exact (@lem4409427 A K (term31 A K k s) y). Qed.
Lemma lem4409429 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term30 A K k s f) = (term32 A K k f s).
Proof. exact (eq_refl (term30 A K k s f)). Qed.
Lemma lem4409430 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4409431 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term33 A K GEN_PVAR_140 k s f) = (term34 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4409430 A K GEN_PVAR_140) (@lem4409429 A K k f s)). Qed.
Lemma lem4409432 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4409433 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term35 A K GEN_PVAR_140 k s f) = (term36 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4409431 A K GEN_PVAR_140 k f s) (@lem4409432 A K f)). Qed.
Lemma lem4409434 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term37 A K GEN_PVAR_140 k s) = (term38 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4409433 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4409435 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4409436 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term39 A K GEN_PVAR_140 k s) = (term40 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4409435 A K) (@lem4409434 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4409437 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term41 A K k s) = (term42 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4409436 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4409438 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4409439 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term43 A K k s) = (term25 A K k s).
Proof. exact (MK_COMB (@lem4409438 A K) (@lem4409437 A K k s)). Qed.
Lemma lem4409440 {A K : Type'} (y : K -> A) : (@IN (K -> A) y) = (@IN (K -> A) y).
Proof. exact (eq_refl (@IN (K -> A) y)). Qed.
Lemma lem4409441 {A K : Type'} (y : K -> A) (k : K -> Prop) (s : type1470 A K) : (term29 A K y k s) = (term27 A K y k s).
Proof. exact (MK_COMB (@lem4409440 A K y) (@lem4409439 A K k s)). Qed.
Lemma lem4409442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4409443 {A K : Type'} (y : K -> A) (k : K -> Prop) (s : type1470 A K) : (term44 A K y k s) = (term45 A K y k s).
Proof. exact (MK_COMB (@lem4409442) (@lem4409441 A K y k s)). Qed.
Lemma lem4409444 {A K : Type'} (k : K -> Prop) (y : K -> A) (s : type1470 A K) : (term30 A K k s y) = (term32 A K k y s).
Proof. exact (eq_refl (term30 A K k s y)). Qed.
Lemma lem4409445 {A K : Type'} (k : K -> Prop) (y : K -> A) (s : type1470 A K) : ((term29 A K y k s) = (term30 A K k s y)) = ((term27 A K y k s) = (term32 A K k y s)).
Proof. exact (MK_COMB (@lem4409443 A K y k s) (@lem4409444 A K k y s)). Qed.
Lemma lem4409446 {A K : Type'} (k : K -> Prop) (y : K -> A) (s : type1470 A K) : (term27 A K y k s) = (term32 A K k y s).
Proof. exact (EQ_MP (@lem4409445 A K k y s) (@lem4409428 A K k s y)). Qed.
Lemma lem4409455 {A K : Type'} (k : K -> Prop) (y : K -> A) (s : type1470 A K) : (term26 A K y k s) = (term32 A K k y s).
Proof. exact (TRANS (@lem4409424 A K y k s) (@lem4409446 A K k y s)). Qed.
Lemma lem4409456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4409457 {A K : Type'} (k : K -> Prop) (y : K -> A) (s : type1470 A K) : (term46 A K y k s) = (term47 A K k y s).
Proof. exact (MK_COMB (@lem4409456) (@lem4409455 A K k y s)). Qed.
Lemma lem4409466 {A K : Type'} (k : K -> Prop) (x : K -> A) (y : K -> A) : (term48 A K k x y) = (term48 A K k x y).
Proof. exact (eq_refl (term48 A K k x y)). Qed.
Lemma lem4409467 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) : (term49 A K s k x y) = (term50 A K s k x y).
Proof. exact (MK_COMB (@lem4409457 A K k y s) (@lem4409466 A K k x y)). Qed.
Lemma lem4409470 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) : (term51 A K s k x y) = (term52 A K s k x y).
Proof. exact (MK_COMB (@lem4409405 A K k x s) (@lem4409467 A K s k x y)). Qed.
Lemma lem4409473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4409474 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) : (term53 A K s k x y) = (term54 A K s k x y).
Proof. exact (MK_COMB (@lem4409473) (@lem4409470 A K s k x y)). Qed.
Lemma lem4409477 {A K : Type'} (x : K -> A) (y : K -> A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4409478 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) : (term55 A K s k x y) = (term56 A K s k x y).
Proof. exact (MK_COMB (@lem4409474 A K s k x y) (@lem4409477 A K x y)). Qed.
Lemma lem4409481 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term57 A K s k x) = (term58 A K s k x).
Proof. exact (fun_ext (fun y : K -> A => @lem4409478 A K s k x y)). Qed.
Lemma lem4409482 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4409483 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term59 A K s k x) = (term60 A K s k x).
Proof. exact (MK_COMB (@lem4409482 A K) (@lem4409481 A K s k x)). Qed.
Lemma lem4409488 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term61 A K s k) = (term62 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4409483 A K s k x)). Qed.
Lemma lem4409489 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4409490 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term63 A K s k) = (term64 A K s k).
Proof. exact (MK_COMB (@lem4409489 A K) (@lem4409488 A K s k)). Qed.
Lemma lem4409495 {A K : Type'} (k : K -> Prop) : (term65 A K k) = (term66 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4409490 A K s k)). Qed.
Lemma lem4409496 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4409497 {A K : Type'} (k : K -> Prop) : (term67 A K k) = (term68 A K k).
Proof. exact (MK_COMB (@lem4409496 A K) (@lem4409495 A K k)). Qed.
Lemma lem4409502 {A K : Type'} : (term69 A K) = (term70 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4409497 A K k)). Qed.
Lemma lem4409503 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4409504 {A K : Type'} : (term71 A K) = (term72 A K).
Proof. exact (MK_COMB (@lem4409503 K) (@lem4409502 A K)). Qed.
Lemma lem4409509 {A K : Type'} : (term72 A K) = (term71 A K).
Proof. exact (SYM (@lem4409504 A K)). Qed.
Lemma lem4409510 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term52 A K s k x y) : term52 A K s k x y.
Proof. exact (h1). Qed.
Lemma lem4409511 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term50 A K s k x y) : term50 A K s k x y.
Proof. exact (h1). Qed.
Lemma lem4409512 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term32 A K k x s) : term32 A K k x s.
Proof. exact (h1). Qed.
Lemma lem4409514 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : @EXTENSIONAL K A k x) : @EXTENSIONAL K A k x.
Proof. exact (h1). Qed.
Lemma lem4409515 {A K : Type'} (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term48 A K k x y) : term48 A K k x y.
Proof. exact (h1). Qed.
Lemma lem4409516 {A K : Type'} (k : K -> Prop) (y : K -> A) (s : type1470 A K) (h1 : term32 A K k y s) : term32 A K k y s.
Proof. exact (h1). Qed.
Lemma lem4409518 {A K : Type'} (k : K -> Prop) (y : K -> A) (h1 : @EXTENSIONAL K A k y) : @EXTENSIONAL K A k y.
Proof. exact (h1). Qed.
Lemma lem4409520 {A B : Type'} (f : A -> B) (g : A -> B) : term11 A B f g.
Proof. exact (EQ_MP (@lem4409290 A B f g) (@lem4409289 A B f g)). Qed.
Lemma lem4409521 {A K : Type'} (f : K -> A) (g : K -> A) : term73 A K f g.
Proof. exact (@lem4409520 K A f g). Qed.
Lemma lem4409522 {A K : Type'} (x : K -> A) (y : K -> A) : term73 A K x y.
Proof. exact (@lem4409521 A K x y). Qed.
Lemma lem4409523 {A : Type'} (P : A -> Prop) : term74 A P.
Proof. exact (@lem3181151 A P). Qed.
Lemma lem4409524 {A : Type'} (P : A -> Prop) : (term74 A P) = (term75 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4409525 {A : Type'} (P : A -> Prop) : term75 A P.
Proof. exact (EQ_MP (@lem4409524 A P) (@lem4409523 A P)). Qed.
Lemma lem4409526 {A : Type'} (P : A -> Prop) (x : A) : term76 A P x.
Proof. exact (@lem4409525 A P x). Qed.
Lemma lem4409527 {A : Type'} (P : A -> Prop) (x : A) : (term76 A P x) = ((@IN A x P) = (P x)).
Proof. exact (eq_refl (term76 A P x)). Qed.
Lemma lem4409529 {A K : Type'} (k : K -> Prop) (x : K -> A) : (@EXTENSIONAL K A k x) = ((@EXTENSIONAL K A k x) = True).
Proof. exact (@lem7 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4409536 {A K : Type'} (k : K -> Prop) (y : K -> A) : (@EXTENSIONAL K A k y) = ((@EXTENSIONAL K A k y) = True).
Proof. exact (@lem7 (@EXTENSIONAL K A k y)). Qed.
Lemma lem4409543 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term48 A K k x y) : term77 A K k x y i.
Proof. exact (@lem4409515 A K k x y h1 i). Qed.
Lemma lem4409544 {A K : Type'} (k : K -> Prop) (x : K -> A) (y : K -> A) (i : K) : (term77 A K k x y i) = (term78 A K k x y i).
Proof. exact (eq_refl (term77 A K k x y i)). Qed.
Lemma lem4409545 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term48 A K k x y) : term78 A K k x y i.
Proof. exact (EQ_MP (@lem4409544 A K k x y i) (@lem4409543 A K i k x y h1)). Qed.
Lemma lem4409546 {A K : Type'} (k : K -> Prop) (x : K -> A) (y : K -> A) (i : K) : (term78 A K k x y i) = ((term78 A K k x y i) = True).
Proof. exact (@lem7 (term78 A K k x y i)). Qed.
Lemma lem4409551 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem4409527 A P x) (@lem4409526 A P x)). Qed.
Lemma lem4409552 {A K : Type'} (P : type805 A K) (x : K -> A) : (@IN (K -> A) x P) = (P x).
Proof. exact (@lem4409551 (K -> A) P x). Qed.
Lemma lem4409553 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term79 A K x k) = (@EXTENSIONAL K A k x).
Proof. exact (@lem4409552 A K (@EXTENSIONAL K A k) x). Qed.
Lemma lem4409555 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : @EXTENSIONAL K A k x) : (@EXTENSIONAL K A k x) = True.
Proof. exact (EQ_MP (@lem4409529 A K k x) (@lem4409514 A K k x h1)). Qed.
Lemma lem4409556 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : @EXTENSIONAL K A k x) : (term79 A K x k) = True.
Proof. exact (TRANS (@lem4409553 A K k x) (@lem4409555 A K k x h1)). Qed.
Lemma lem4409557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4409558 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : @EXTENSIONAL K A k x) : (term80 A K x k) = (and True).
Proof. exact (MK_COMB (@lem4409557) (@lem4409556 A K k x h1)). Qed.
Lemma lem4409562 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem4409527 A P x) (@lem4409526 A P x)). Qed.
Lemma lem4409563 {A K : Type'} (P : type805 A K) (x : K -> A) : (@IN (K -> A) x P) = (P x).
Proof. exact (@lem4409562 (K -> A) P x). Qed.
Lemma lem4409564 {A K : Type'} (k : K -> Prop) (y : K -> A) : (term79 A K y k) = (@EXTENSIONAL K A k y).
Proof. exact (@lem4409563 A K (@EXTENSIONAL K A k) y). Qed.
Lemma lem4409566 {A K : Type'} (k : K -> Prop) (y : K -> A) (h1 : @EXTENSIONAL K A k y) : (@EXTENSIONAL K A k y) = True.
Proof. exact (EQ_MP (@lem4409536 A K k y) (@lem4409518 A K k y h1)). Qed.
Lemma lem4409567 {A K : Type'} (k : K -> Prop) (y : K -> A) (h1 : @EXTENSIONAL K A k y) : (term79 A K y k) = True.
Proof. exact (TRANS (@lem4409564 A K k y) (@lem4409566 A K k y h1)). Qed.
Lemma lem4409568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4409569 {A K : Type'} (k : K -> Prop) (y : K -> A) (h1 : @EXTENSIONAL K A k y) : (term80 A K y k) = (and True).
Proof. exact (MK_COMB (@lem4409568) (@lem4409567 A K k y h1)). Qed.
Lemma lem4409575 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term48 A K k x y) : (term78 A K k x y i) = True.
Proof. exact (EQ_MP (@lem4409546 A K k x y i) (@lem4409545 A K i k x y h1)). Qed.
Lemma lem4409576 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term48 A K k x y) : (term78 A K k x y i) = True.
Proof. exact (@lem4409575 A K i k x y h1). Qed.
Lemma lem4409577 {A K : Type'} (x : K) (k : K -> Prop) (x' : K -> A) (y : K -> A) (h1 : term48 A K k x' y) : (term78 A K k x' y x) = True.
Proof. exact (@lem4409576 A K x k x' y h1). Qed.
Lemma lem4409578 {A K : Type'} (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term48 A K k x y) : (term81 A K k x y) = (term82 K).
Proof. exact (fun_ext (fun x' : K => @lem4409577 A K x' k x y h1)). Qed.
Lemma lem4409579 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4409580 {A K : Type'} (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term48 A K k x y) : (term48 A K k x y) = (term83 K).
Proof. exact (MK_COMB (@lem4409579 K) (@lem4409578 A K k x y h1)). Qed.
Lemma lem4409582 {A : Type'} (t : Prop) : (term84 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4409583 {K : Type'} (t : Prop) : (term84 K t) = t.
Proof. exact (@lem4409582 K t). Qed.
Lemma lem4409584 {K : Type'} : (term83 K) = True.
Proof. exact (@lem4409583 K True). Qed.
Lemma lem4409585 {A K : Type'} (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term48 A K k x y) : (term48 A K k x y) = True.
Proof. exact (TRANS (@lem4409580 A K k x y h1) (@lem4409584 K)). Qed.
Lemma lem4409586 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k y) : (term85 A K k x y) = (True /\ True).
Proof. exact (MK_COMB (@lem4409569 A K k y h2) (@lem4409585 A K k x y h1)). Qed.
Lemma lem4409588 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4409589 : (True /\ True) = True.
Proof. exact (@lem4409588 True). Qed.
Lemma lem4409590 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k y) : (term85 A K k x y) = True.
Proof. exact (TRANS (@lem4409586 A K x k y h1 h2) (@lem4409589)). Qed.
Lemma lem4409591 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : (term86 A K k x y) = (True /\ True).
Proof. exact (MK_COMB (@lem4409558 A K k x h2) (@lem4409590 A K x k y h1 h3)). Qed.
Lemma lem4409593 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4409594 : (True /\ True) = True.
Proof. exact (@lem4409593 True). Qed.
Lemma lem4409595 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : (term86 A K k x y) = True.
Proof. exact (TRANS (@lem4409591 A K x k y h1 h2 h3) (@lem4409594)). Qed.
Lemma lem4409596 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : True = (term86 A K k x y).
Proof. exact (SYM (@lem4409595 A K x k y h1 h2 h3)). Qed.
Lemma lem4409597 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : term86 A K k x y.
Proof. exact (EQ_MP (@lem4409596 A K x k y h1 h2 h3) (@lem0)). Qed.
Lemma lem4409598 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : term87 A K x y.
Proof. exact (ex_intro (term88 A K x y) k (@lem4409597 A K x k y h1 h2 h3)). Qed.
Lemma lem4409599 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : x = y.
Proof. exact (@lem4409522 A K x y (@lem4409598 A K x k y h1 h2 h3)). Qed.
Lemma lem4409600 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term52 A K s k x y) : term50 A K s k x y.
Proof. exact (proj2 (@lem4409510 A K s k x y h1)). Qed.
Lemma lem4409601 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term52 A K s k x y) : term32 A K k x s.
Proof. exact (proj1 (@lem4409510 A K s k x y h1)). Qed.
Lemma lem4409602 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term50 A K s k x y) : term48 A K k x y.
Proof. exact (proj2 (@lem4409511 A K s k x y h1)). Qed.
Lemma lem4409603 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term50 A K s k x y) : term32 A K k y s.
Proof. exact (proj1 (@lem4409511 A K s k x y h1)). Qed.
Lemma lem4409604 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : (term48 A K k x y) = (x = y).
Proof. exact (prop_ext (fun h4 : term48 A K k x y => @lem4409599 A K x k y h1 h2 h3) (fun h4 : x = y => @lem4409515 A K k x y h1)). Qed.
Lemma lem4409605 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : x = y.
Proof. exact (EQ_MP (@lem4409604 A K x k y h1 h2 h3) (@lem4409515 A K k x y h1)). Qed.
Lemma lem4409607 {A K : Type'} (k : K -> Prop) (y : K -> A) (s : type1470 A K) (h1 : term32 A K k y s) : @EXTENSIONAL K A k y.
Proof. exact (proj1 (@lem4409516 A K k y s h1)). Qed.
Lemma lem4409608 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : (@EXTENSIONAL K A k y) = (x = y).
Proof. exact (prop_ext (fun h4 : @EXTENSIONAL K A k y => @lem4409605 A K x k y h1 h2 h3) (fun h4 : x = y => @lem4409518 A K k y h3)). Qed.
Lemma lem4409609 {A K : Type'} (x : K -> A) (k : K -> Prop) (y : K -> A) (h1 : term48 A K k x y) (h2 : @EXTENSIONAL K A k x) (h3 : @EXTENSIONAL K A k y) : x = y.
Proof. exact (EQ_MP (@lem4409608 A K x k y h1 h2 h3) (@lem4409518 A K k y h3)). Qed.
Lemma lem4409610 {A K : Type'} (y : K -> A) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term48 A K k x y) (h2 : term32 A K k y s) (h3 : @EXTENSIONAL K A k x) : (@EXTENSIONAL K A k y) = (x = y).
Proof. exact (prop_ext (fun h4 : @EXTENSIONAL K A k y => @lem4409609 A K x k y h1 h3 h4) (fun h4 : x = y => @lem4409607 A K k y s h2)). Qed.
Lemma lem4409611 {A K : Type'} (y : K -> A) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term48 A K k x y) (h2 : term32 A K k y s) (h3 : @EXTENSIONAL K A k x) : x = y.
Proof. exact (EQ_MP (@lem4409610 A K y s k x h1 h2 h3) (@lem4409607 A K k y s h2)). Qed.
Lemma lem4409612 {A K : Type'} (y : K -> A) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term50 A K s k x y) (h2 : term32 A K k y s) (h3 : @EXTENSIONAL K A k x) : (term48 A K k x y) = (x = y).
Proof. exact (prop_ext (fun h4 : term48 A K k x y => @lem4409611 A K y s k x h4 h2 h3) (fun h4 : x = y => @lem4409602 A K s k x y h1)). Qed.
Lemma lem4409613 {A K : Type'} (y : K -> A) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term50 A K s k x y) (h2 : term32 A K k y s) (h3 : @EXTENSIONAL K A k x) : x = y.
Proof. exact (EQ_MP (@lem4409612 A K y s k x h1 h2 h3) (@lem4409602 A K s k x y h1)). Qed.
Lemma lem4409614 {A K : Type'} (s : type1470 A K) (y : K -> A) (k : K -> Prop) (x : K -> A) (h1 : term50 A K s k x y) (h2 : @EXTENSIONAL K A k x) : (term32 A K k y s) = (x = y).
Proof. exact (prop_ext (fun h3 : term32 A K k y s => @lem4409613 A K y s k x h1 h3 h2) (fun h3 : x = y => @lem4409603 A K s k x y h1)). Qed.
Lemma lem4409615 {A K : Type'} (s : type1470 A K) (y : K -> A) (k : K -> Prop) (x : K -> A) (h1 : term50 A K s k x y) (h2 : @EXTENSIONAL K A k x) : x = y.
Proof. exact (EQ_MP (@lem4409614 A K s y k x h1 h2) (@lem4409603 A K s k x y h1)). Qed.
Lemma lem4409617 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term32 A K k x s) : @EXTENSIONAL K A k x.
Proof. exact (proj1 (@lem4409512 A K k x s h1)). Qed.
Lemma lem4409618 {A K : Type'} (s : type1470 A K) (y : K -> A) (k : K -> Prop) (x : K -> A) (h1 : term50 A K s k x y) (h2 : @EXTENSIONAL K A k x) : (@EXTENSIONAL K A k x) = (x = y).
Proof. exact (prop_ext (fun h3 : @EXTENSIONAL K A k x => @lem4409615 A K s y k x h1 h2) (fun h3 : x = y => @lem4409514 A K k x h2)). Qed.
Lemma lem4409619 {A K : Type'} (s : type1470 A K) (y : K -> A) (k : K -> Prop) (x : K -> A) (h1 : term50 A K s k x y) (h2 : @EXTENSIONAL K A k x) : x = y.
Proof. exact (EQ_MP (@lem4409618 A K s y k x h1 h2) (@lem4409514 A K k x h2)). Qed.
Lemma lem4409620 {A K : Type'} (y : K -> A) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term50 A K s k x y) (h2 : term32 A K k x s) : (@EXTENSIONAL K A k x) = (x = y).
Proof. exact (prop_ext (fun h3 : @EXTENSIONAL K A k x => @lem4409619 A K s y k x h1 h3) (fun h3 : x = y => @lem4409617 A K k x s h2)). Qed.
Lemma lem4409621 {A K : Type'} (y : K -> A) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term50 A K s k x y) (h2 : term32 A K k x s) : x = y.
Proof. exact (EQ_MP (@lem4409620 A K y k x s h1 h2) (@lem4409617 A K k x s h2)). Qed.
Lemma lem4409622 {A K : Type'} (y : K -> A) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term52 A K s k x y) (h2 : term32 A K k x s) : (term50 A K s k x y) = (x = y).
Proof. exact (prop_ext (fun h3 : term50 A K s k x y => @lem4409621 A K y k x s h3 h2) (fun h3 : x = y => @lem4409600 A K s k x y h1)). Qed.
Lemma lem4409623 {A K : Type'} (y : K -> A) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term52 A K s k x y) (h2 : term32 A K k x s) : x = y.
Proof. exact (EQ_MP (@lem4409622 A K y k x s h1 h2) (@lem4409600 A K s k x y h1)). Qed.
Lemma lem4409624 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term52 A K s k x y) : (term32 A K k x s) = (x = y).
Proof. exact (prop_ext (fun h2 : term32 A K k x s => @lem4409623 A K y k x s h1 h2) (fun h2 : x = y => @lem4409601 A K s k x y h1)). Qed.
Lemma lem4409625 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) (h1 : term52 A K s k x y) : x = y.
Proof. exact (EQ_MP (@lem4409624 A K s k x y h1) (@lem4409601 A K s k x y h1)). Qed.
Lemma lem4409626 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (y : K -> A) : term56 A K s k x y.
Proof. exact (fun h0 : term52 A K s k x y => @lem4409625 A K s k x y h0). Qed.
Lemma lem4409631 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : term60 A K s k x.
Proof. exact (fun y : K -> A => @lem4409626 A K s k x y). Qed.
Lemma lem4409636 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : term64 A K s k.
Proof. exact (fun x : K -> A => @lem4409631 A K s k x). Qed.
Lemma lem4409641 {A K : Type'} (k : K -> Prop) : term68 A K k.
Proof. exact (fun s : type1470 A K => @lem4409636 A K s k). Qed.
Lemma lem4409646 {A K : Type'} : term72 A K.
Proof. exact (fun k : K -> Prop => @lem4409641 A K k). Qed.
Lemma lem4409647 {A K : Type'} : term71 A K.
Proof. exact (EQ_MP (@lem4409509 A K) (@lem4409646 A K)). Qed.
