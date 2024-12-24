Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_IMAGE_LE_term_abbrevs.
Require Import FINITE_IMAGE_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import SUM_LE_INCLUDED_spec.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem7196260 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7196261 {A B : Type'} (f : A -> real) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem7196260 A B h1 f). Qed.
Lemma lem7196262 {A B : Type'} (f : A -> real) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem7196263 {A B : Type'} (f : A -> real) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem7196262 A B f) (@lem7196261 A B f h1)). Qed.
Lemma lem7196264 {A B : Type'} (f : A -> real) (g : B -> real) (h1 : term0 A B) : term3 A B f g.
Proof. exact (@lem7196263 A B f h1 g). Qed.
Lemma lem7196265 {A B : Type'} (f : A -> real) (g : B -> real) : (term3 A B f g) = (term4 A B f g).
Proof. exact (eq_refl (term3 A B f g)). Qed.
Lemma lem7196266 {A B : Type'} (f : A -> real) (g : B -> real) (h1 : term0 A B) : term4 A B f g.
Proof. exact (EQ_MP (@lem7196265 A B f g) (@lem7196264 A B f g h1)). Qed.
Lemma lem7196267 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (h1 : term0 A B) : term5 A B f g s.
Proof. exact (@lem7196266 A B f g h1 s). Qed.
Lemma lem7196268 {A B : Type'} (s : A -> Prop) (f : A -> real) (g : B -> real) : (term5 A B f g s) = (term6 A B s f g).
Proof. exact (eq_refl (term5 A B f g s)). Qed.
Lemma lem7196269 {A B : Type'} (s : A -> Prop) (f : A -> real) (g : B -> real) (h1 : term0 A B) : term6 A B s f g.
Proof. exact (EQ_MP (@lem7196268 A B s f g) (@lem7196267 A B f g s h1)). Qed.
Lemma lem7196270 {A B : Type'} (s : A -> Prop) (f : A -> real) (g : B -> real) (t : B -> Prop) (h1 : term0 A B) : term7 A B s f g t.
Proof. exact (@lem7196269 A B s f g h1 t). Qed.
Lemma lem7196271 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term7 A B s f g t) = (term8 A B s f t g).
Proof. exact (eq_refl (term7 A B s f g t)). Qed.
Lemma lem7196272 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) (h1 : term0 A B) : term8 A B s f t g.
Proof. exact (EQ_MP (@lem7196271 A B s f t g) (@lem7196270 A B s f g t h1)). Qed.
Lemma lem7196273 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) (i : B -> A) (h1 : term0 A B) : term9 A B s f t g i.
Proof. exact (@lem7196272 A B s f t g h1 i). Qed.
Lemma lem7196274 {A B : Type'} (i : B -> A) (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term9 A B s f t g i) = (term10 A B i s f t g).
Proof. exact (eq_refl (term9 A B s f t g i)). Qed.
Lemma lem7196275 {A B : Type'} (i : B -> A) (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) (h1 : term0 A B) : term10 A B i s f t g.
Proof. exact (EQ_MP (@lem7196274 A B i s f t g) (@lem7196273 A B s f t g i h1)). Qed.
Lemma lem7196276 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term11 A B s t i f g) : term11 A B s t i f g.
Proof. exact (h1). Qed.
Lemma lem7196277 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term0 A B) (h2 : term11 A B s t i f g) : term12 A B s f t g.
Proof. exact (@lem7196275 A B i s f t g h1 (@lem7196276 A B s t i f g h2)). Qed.
Lemma lem7196278 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term11 A B s t i f g) : term13 A B s f t g.
Proof. exact (fun h0 : term0 A B => @lem7196277 A B s t i f g h0 h1). Qed.
Lemma lem7196279 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> real) (g : B -> real) (h1 : term14 A B s t f g) : term14 A B s t f g.
Proof. exact (h1). Qed.
Lemma lem7196280 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> real) (g : B -> real) (h1 : term14 A B s t f g) : term13 A B s f t g.
Proof. exact (ex_elim (@lem7196279 A B s t f g h1) (fun i : B -> A => fun h0 : term15 A B s t f g i => @lem7196278 A B s t i f g h0)). Qed.
Lemma lem7196281 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7196282 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> real) (g : B -> real) (h1 : term0 A B) (h2 : term14 A B s t f g) : term12 A B s f t g.
Proof. exact (@lem7196280 A B s t f g h2 (@lem7196281 A B h1)). Qed.
Lemma lem7196283 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) (h1 : term0 A B) : term16 A B s f t g.
Proof. exact (fun h0 : term14 A B s t f g => @lem7196282 A B s t f g h1 h0). Qed.
Lemma lem7196284 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (h1 : term0 A B) : term17 A B s f t.
Proof. exact (fun g : B -> real => @lem7196283 A B s f t g h1). Qed.
Lemma lem7196285 {A B : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A B) : term18 A B s f.
Proof. exact (fun t : B -> Prop => @lem7196284 A B s f t h1). Qed.
Lemma lem7196286 {A B : Type'} (s : A -> Prop) (h1 : term0 A B) : term19 A B s.
Proof. exact (fun f : A -> real => @lem7196285 A B s f h1). Qed.
Lemma lem7196287 {A B : Type'} (h1 : term0 A B) : term20 A B.
Proof. exact (fun s : A -> Prop => @lem7196286 A B s h1). Qed.
Lemma lem7196288 {A B : Type'} : term21 A B.
Proof. exact (fun h0 : term0 A B => @lem7196287 A B h0). Qed.
Lemma lem7196289 {A B : Type'} : term20 A B.
Proof. exact (@lem7196288 A B (@lem7196249 A B)). Qed.
Lemma lem7196290 {A B : Type'} (s : A -> Prop) : term22 A B s.
Proof. exact (@lem7196289 A B s). Qed.
Lemma lem7196291 {A B : Type'} (s : A -> Prop) : (term22 A B s) = (term19 A B s).
Proof. exact (eq_refl (term22 A B s)). Qed.
Lemma lem7196292 {A B : Type'} (s : A -> Prop) : term19 A B s.
Proof. exact (EQ_MP (@lem7196291 A B s) (@lem7196290 A B s)). Qed.
Lemma lem7196293 {A B : Type'} (s : A -> Prop) (f : A -> real) : term23 A B s f.
Proof. exact (@lem7196292 A B s f). Qed.
Lemma lem7196294 {A B : Type'} (s : A -> Prop) (f : A -> real) : (term23 A B s f) = (term18 A B s f).
Proof. exact (eq_refl (term23 A B s f)). Qed.
Lemma lem7196295 {A B : Type'} (s : A -> Prop) (f : A -> real) : term18 A B s f.
Proof. exact (EQ_MP (@lem7196294 A B s f) (@lem7196293 A B s f)). Qed.
Lemma lem7196296 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) : term24 A B s f t.
Proof. exact (@lem7196295 A B s f t). Qed.
Lemma lem7196297 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) : (term24 A B s f t) = (term17 A B s f t).
Proof. exact (eq_refl (term24 A B s f t)). Qed.
Lemma lem7196298 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) : term17 A B s f t.
Proof. exact (EQ_MP (@lem7196297 A B s f t) (@lem7196296 A B s f t)). Qed.
Lemma lem7196299 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : term25 A B s f t g.
Proof. exact (@lem7196298 A B s f t g). Qed.
Lemma lem7196300 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term25 A B s f t g) = (term16 A B s f t g).
Proof. exact (eq_refl (term25 A B s f t g)). Qed.
Lemma lem7196302 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term26 A B s g f) : term26 A B s g f.
Proof. exact (h1). Qed.
Lemma lem7196303 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : term27 A B s g f.
Proof. exact (h1). Qed.
Lemma lem7196304 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7196306 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : term16 A B s f t g.
Proof. exact (EQ_MP (@lem7196300 A B s f t g) (@lem7196299 A B s f t g)). Qed.
Lemma lem7196307 {A B : Type'} (s : B -> Prop) (f : B -> real) (t : A -> Prop) (g : A -> real) : term28 A B s f t g.
Proof. exact (@lem7196306 B A s f t g). Qed.
Lemma lem7196308 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term29 A B s g f.
Proof. exact (@lem7196307 A B (@IMAGE A B f s) g s (@o A B real g f)). Qed.
Lemma lem7196309 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term30 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem7196310 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term30 _87967 _87968 P f) = (term31 _87967 _87968 P f).
Proof. exact (eq_refl (term30 _87967 _87968 P f)). Qed.
Lemma lem7196311 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term31 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem7196310 _87967 _87968 P f) (@lem7196309 _87967 _87968 P f)). Qed.
Lemma lem7196312 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term32 _87967 _87968 P f s.
Proof. exact (@lem7196311 _87967 _87968 P f s). Qed.
Lemma lem7196313 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term32 _87967 _87968 P f s) = ((term33 _87967 _87968 f s P) = (term34 _87967 _87968 s P f)).
Proof. exact (eq_refl (term32 _87967 _87968 P f s)). Qed.
Lemma lem7196315 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem7196316 {A B : Type'} (f : A -> B) : (term35 A B f) = (term36 A B f).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem7196317 {A B : Type'} (f : A -> B) : term36 A B f.
Proof. exact (EQ_MP (@lem7196316 A B f) (@lem7196315 A B f)). Qed.
Lemma lem7196318 {A B : Type'} (f : A -> B) (s : A -> Prop) : term37 A B f s.
Proof. exact (@lem7196317 A B f s). Qed.
Lemma lem7196319 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term37 A B f s) = (term38 A B f s).
Proof. exact (eq_refl (term37 A B f s)). Qed.
Lemma lem7196320 {A B : Type'} (f : A -> B) (s : A -> Prop) : term38 A B f s.
Proof. exact (EQ_MP (@lem7196319 A B f s) (@lem7196318 A B f s)). Qed.
Lemma lem7196321 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7196322 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term39 A B f s.
Proof. exact (@lem7196320 A B f s (@lem7196321 A s h1)). Qed.
Lemma lem7196323 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term39 A B f s) = ((term39 A B f s) = True).
Proof. exact (@lem7 (term39 A B f s)). Qed.
Lemma lem7196324 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term39 A B f s) = True.
Proof. exact (EQ_MP (@lem7196323 A B f s) (@lem7196322 A B f s h1)). Qed.
Lemma lem7196330 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7196351 {A B : Type'} (f : A -> B) (s : A -> Prop) : term40 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem7196324 A B f s h0). Qed.
Lemma lem7196352 {A B : Type'} (f : A -> B) (s : A -> Prop) : term40 A B f s.
Proof. exact (@lem7196351 A B f s). Qed.
Lemma lem7196354 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7196330 A s) (@lem7196304 A s h1)). Qed.
Lemma lem7196355 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7196354 A s h1)). Qed.
Lemma lem7196356 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7196355 A s h1) (@lem0)). Qed.
Lemma lem7196357 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term39 A B f s) = True.
Proof. exact (@lem7196352 A B f s (@lem7196356 A s h1)). Qed.
Lemma lem7196358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7196359 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term41 A B f s) = (and True).
Proof. exact (MK_COMB (@lem7196358) (@lem7196357 A B f s h1)). Qed.
Lemma lem7196363 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7196330 A s) (@lem7196304 A s h1)). Qed.
Lemma lem7196364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7196365 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term42 A s) = (and True).
Proof. exact (MK_COMB (@lem7196364) (@lem7196363 A s h1)). Qed.
Lemma lem7196396 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term33 _87967 _87968 f s P) = (term34 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem7196313 _87967 _87968 s P f) (@lem7196312 _87967 _87968 P f s)). Qed.
Lemma lem7196397 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term43 A B f s P) = (term44 A B s P f).
Proof. exact (@lem7196396 B A s P f). Qed.
Lemma lem7196398 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term45 A B s i g f) = (term46 A B s i g f).
Proof. exact (@lem7196397 A B s (term47 A B s i g f) f). Qed.
Lemma lem7196399 {A B : Type'} (s : A -> Prop) (i : A -> B) (x : B) (g : B -> real) (f : A -> B) : (term48 A B s i g f x) = (term49 A B s i x g f).
Proof. exact (eq_refl (term48 A B s i g f x)). Qed.
Lemma lem7196400 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term50 A B x f s) = (term50 A B x f s).
Proof. exact (eq_refl (term50 A B x f s)). Qed.
Lemma lem7196401 {A B : Type'} (s : A -> Prop) (i : A -> B) (x : B) (g : B -> real) (f : A -> B) : (term51 A B s i g f x) = (term52 A B s i x g f).
Proof. exact (MK_COMB (@lem7196400 A B x f s) (@lem7196399 A B s i x g f)). Qed.
Lemma lem7196402 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term53 A B s i g f) = (term54 A B s i g f).
Proof. exact (fun_ext (fun x : B => @lem7196401 A B s i x g f)). Qed.
Lemma lem7196403 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7196404 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term45 A B s i g f) = (term55 A B s i g f).
Proof. exact (MK_COMB (@lem7196403 B) (@lem7196402 A B s i g f)). Qed.
Lemma lem7196405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7196406 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term56 A B s i g f) = (term57 A B s i g f).
Proof. exact (MK_COMB (@lem7196405) (@lem7196404 A B s i g f)). Qed.
Lemma lem7196407 {A B : Type'} (s : A -> Prop) (i : A -> B) (x : A) (g : B -> real) (f : A -> B) : (term58 A B s i g f x) = (term59 A B s i x g f).
Proof. exact (eq_refl (term58 A B s i g f x)). Qed.
Lemma lem7196408 {A : Type'} (x : A) (s : A -> Prop) : (term60 A x s) = (term60 A x s).
Proof. exact (eq_refl (term60 A x s)). Qed.
Lemma lem7196409 {A B : Type'} (s : A -> Prop) (i : A -> B) (x : A) (g : B -> real) (f : A -> B) : (term61 A B s i g f x) = (term62 A B s i x g f).
Proof. exact (MK_COMB (@lem7196408 A x s) (@lem7196407 A B s i x g f)). Qed.
Lemma lem7196410 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term63 A B s i g f) = (term64 A B s i g f).
Proof. exact (fun_ext (fun x : A => @lem7196409 A B s i x g f)). Qed.
Lemma lem7196411 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7196412 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term46 A B s i g f) = (term65 A B s i g f).
Proof. exact (MK_COMB (@lem7196411 A) (@lem7196410 A B s i g f)). Qed.
Lemma lem7196413 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : ((term45 A B s i g f) = (term46 A B s i g f)) = ((term55 A B s i g f) = (term65 A B s i g f)).
Proof. exact (MK_COMB (@lem7196406 A B s i g f) (@lem7196412 A B s i g f)). Qed.
Lemma lem7196414 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term55 A B s i g f) = (term65 A B s i g f).
Proof. exact (EQ_MP (@lem7196413 A B s i g f) (@lem7196398 A B s i g f)). Qed.
Lemma lem7196462 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term66 A B s g f) = (term66 A B s g f).
Proof. exact (eq_refl (term66 A B s g f)). Qed.
Lemma lem7196463 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term67 A B s i g f) = (term68 A B s i g f).
Proof. exact (MK_COMB (@lem7196462 A B s g f) (@lem7196414 A B s i g f)). Qed.
Lemma lem7196540 {A B : Type'} (i : A -> B) (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term69 A B s i g f) = (term70 A B s i g f).
Proof. exact (MK_COMB (@lem7196365 A s h1) (@lem7196463 A B s i g f)). Qed.
Lemma lem7196542 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7196543 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term70 A B s i g f) = (term68 A B s i g f).
Proof. exact (@lem7196542 (term68 A B s i g f)). Qed.
Lemma lem7196620 {A B : Type'} (i : A -> B) (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term69 A B s i g f) = (term68 A B s i g f).
Proof. exact (TRANS (@lem7196540 A B i g f s h1) (@lem7196543 A B s i g f)). Qed.
Lemma lem7196621 {A B : Type'} (i : A -> B) (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term71 A B s i g f) = (term70 A B s i g f).
Proof. exact (MK_COMB (@lem7196359 A B f s h1) (@lem7196620 A B i g f s h1)). Qed.
Lemma lem7196623 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7196624 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term70 A B s i g f) = (term68 A B s i g f).
Proof. exact (@lem7196623 (term68 A B s i g f)). Qed.
Lemma lem7196701 {A B : Type'} (i : A -> B) (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term71 A B s i g f) = (term68 A B s i g f).
Proof. exact (TRANS (@lem7196621 A B i g f s h1) (@lem7196624 A B s i g f)). Qed.
Lemma lem7196702 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term72 A B s g f) = (term73 A B s g f).
Proof. exact (fun_ext (fun i : A -> B => @lem7196701 A B i g f s h1)). Qed.
Lemma lem7196779 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7196780 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term74 A B s g f) = (term75 A B s g f).
Proof. exact (MK_COMB (@lem7196779 A B) (@lem7196702 A B g f s h1)). Qed.
Lemma lem7196861 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term75 A B s g f) = (term74 A B s g f).
Proof. exact (SYM (@lem7196780 A B g f s h1)). Qed.
Lemma lem7196862 {A B C : Type'} (f : B -> C) : term76 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem7196863 {A B C : Type'} (f : B -> C) : (term76 A B C f) = (term77 A B C f).
Proof. exact (eq_refl (term76 A B C f)). Qed.
Lemma lem7196864 {A B C : Type'} (f : B -> C) : term77 A B C f.
Proof. exact (EQ_MP (@lem7196863 A B C f) (@lem7196862 A B C f)). Qed.
Lemma lem7196865 {A B C : Type'} (f : B -> C) (g : A -> B) : term78 A B C f g.
Proof. exact (@lem7196864 A B C f g). Qed.
Lemma lem7196866 {A B C : Type'} (f : B -> C) (g : A -> B) : (term78 A B C f g) = (term79 A B C f g).
Proof. exact (eq_refl (term78 A B C f g)). Qed.
Lemma lem7196867 {A B C : Type'} (f : B -> C) (g : A -> B) : term79 A B C f g.
Proof. exact (EQ_MP (@lem7196866 A B C f g) (@lem7196865 A B C f g)). Qed.
Lemma lem7196868 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term80 A B C f g x.
Proof. exact (@lem7196867 A B C f g x). Qed.
Lemma lem7196869 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term80 A B C f g x) = ((@o A B C f g x) = (term81 A B C f g x)).
Proof. exact (eq_refl (term80 A B C f g x)). Qed.
Lemma lem7196873 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : term82 A B s g f x.
Proof. exact (@lem7196303 A B s g f h1 x). Qed.
Lemma lem7196874 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (x : A) : (term82 A B s g f x) = (term83 A B s g f x).
Proof. exact (eq_refl (term82 A B s g f x)). Qed.
Lemma lem7196875 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : term83 A B s g f x.
Proof. exact (EQ_MP (@lem7196874 A B s g f x) (@lem7196873 A B x s g f h1)). Qed.
Lemma lem7196876 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (x : A) : (term83 A B s g f x) = ((term83 A B s g f x) = True).
Proof. exact (@lem7 (term83 A B s g f x)). Qed.
Lemma lem7196891 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term81 A B C f g x).
Proof. exact (EQ_MP (@lem7196869 A B C f g x) (@lem7196868 A B C f g x)). Qed.
Lemma lem7196892 {A B : Type'} (f : B -> real) (g : A -> B) (x : A) : (@o A B real f g x) = (term84 A B f g x).
Proof. exact (@lem7196891 A B real f g x). Qed.
Lemma lem7196893 {A B : Type'} (g : B -> real) (f : A -> B) (y : A) : (@o A B real g f y) = (term84 A B g f y).
Proof. exact (@lem7196892 A B g f y). Qed.
Lemma lem7196894 : term85 = term85.
Proof. exact (eq_refl term85). Qed.
Lemma lem7196895 {A B : Type'} (g : B -> real) (f : A -> B) (y : A) : (term86 A B g f y) = (term87 A B g f y).
Proof. exact (MK_COMB (@lem7196894) (@lem7196893 A B g f y)). Qed.
Lemma lem7196896 {A : Type'} (y : A) (s : A -> Prop) : (term60 A y s) = (term60 A y s).
Proof. exact (eq_refl (term60 A y s)). Qed.
Lemma lem7196897 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (y : A) : (term88 A B s g f y) = (term83 A B s g f y).
Proof. exact (MK_COMB (@lem7196896 A y s) (@lem7196895 A B g f y)). Qed.
Lemma lem7196899 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term83 A B s g f x) = True.
Proof. exact (EQ_MP (@lem7196876 A B s g f x) (@lem7196875 A B x s g f h1)). Qed.
Lemma lem7196900 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term83 A B s g f x) = True.
Proof. exact (@lem7196899 A B x s g f h1). Qed.
Lemma lem7196901 {A B : Type'} (y : A) (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term83 A B s g f y) = True.
Proof. exact (@lem7196900 A B y s g f h1). Qed.
Lemma lem7196902 {A B : Type'} (y : A) (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term88 A B s g f y) = True.
Proof. exact (TRANS (@lem7196897 A B s g f y) (@lem7196901 A B y s g f h1)). Qed.
Lemma lem7196903 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term89 A B s g f) = (term90 A).
Proof. exact (fun_ext (fun y : A => @lem7196902 A B y s g f h1)). Qed.
Lemma lem7196904 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7196905 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term91 A B s g f) = (term92 A).
Proof. exact (MK_COMB (@lem7196904 A) (@lem7196903 A B s g f h1)). Qed.
Lemma lem7196907 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7196908 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem7196907 A t). Qed.
Lemma lem7196909 {A : Type'} : (term92 A) = True.
Proof. exact (@lem7196908 A True). Qed.
Lemma lem7196910 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term91 A B s g f) = True.
Proof. exact (TRANS (@lem7196905 A B s g f h1) (@lem7196909 A)). Qed.
Lemma lem7196911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7196912 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term66 A B s g f) = (and True).
Proof. exact (MK_COMB (@lem7196911) (@lem7196910 A B s g f h1)). Qed.
Lemma lem7196930 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term81 A B C f g x).
Proof. exact (EQ_MP (@lem7196869 A B C f g x) (@lem7196868 A B C f g x)). Qed.
Lemma lem7196931 {A B : Type'} (f : B -> real) (g : A -> B) (x : A) : (@o A B real f g x) = (term84 A B f g x).
Proof. exact (@lem7196930 A B real f g x). Qed.
Lemma lem7196932 {A B : Type'} (g : B -> real) (f : A -> B) (y : A) : (@o A B real g f y) = (term84 A B g f y).
Proof. exact (@lem7196931 A B g f y). Qed.
Lemma lem7196933 {A B : Type'} (g : B -> real) (f : A -> B) (x : A) : (term94 A B g f x) = (term94 A B g f x).
Proof. exact (eq_refl (term94 A B g f x)). Qed.
Lemma lem7196934 {A B : Type'} (x : A) (g : B -> real) (f : A -> B) (y : A) : (term95 A B x g f y) = (term96 A B x g f y).
Proof. exact (MK_COMB (@lem7196933 A B g f x) (@lem7196932 A B g f y)). Qed.
Lemma lem7196935 {A B : Type'} (i : A -> B) (y : A) (f : A -> B) (x : A) : (term97 A B i y f x) = (term97 A B i y f x).
Proof. exact (eq_refl (term97 A B i y f x)). Qed.
Lemma lem7196936 {A B : Type'} (i : A -> B) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term98 A B i x g f y) = (term99 A B i x g f y).
Proof. exact (MK_COMB (@lem7196935 A B i y f x) (@lem7196934 A B x g f y)). Qed.
Lemma lem7196939 {A : Type'} (y : A) (s : A -> Prop) : (term100 A y s) = (term100 A y s).
Proof. exact (eq_refl (term100 A y s)). Qed.
Lemma lem7196940 {A B : Type'} (s : A -> Prop) (i : A -> B) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term101 A B s i x g f y) = (term102 A B s i x g f y).
Proof. exact (MK_COMB (@lem7196939 A y s) (@lem7196936 A B i x g f y)). Qed.
Lemma lem7196943 {A B : Type'} (s : A -> Prop) (i : A -> B) (x : A) (g : B -> real) (f : A -> B) : (term103 A B s i x g f) = (term104 A B s i x g f).
Proof. exact (fun_ext (fun y : A => @lem7196940 A B s i x g f y)). Qed.
Lemma lem7196944 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7196945 {A B : Type'} (s : A -> Prop) (i : A -> B) (x : A) (g : B -> real) (f : A -> B) : (term59 A B s i x g f) = (term105 A B s i x g f).
Proof. exact (MK_COMB (@lem7196944 A) (@lem7196943 A B s i x g f)). Qed.
Lemma lem7196950 {A : Type'} (x : A) (s : A -> Prop) : (term60 A x s) = (term60 A x s).
Proof. exact (eq_refl (term60 A x s)). Qed.
Lemma lem7196951 {A B : Type'} (s : A -> Prop) (i : A -> B) (x : A) (g : B -> real) (f : A -> B) : (term62 A B s i x g f) = (term106 A B s i x g f).
Proof. exact (MK_COMB (@lem7196950 A x s) (@lem7196945 A B s i x g f)). Qed.
Lemma lem7196954 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term64 A B s i g f) = (term107 A B s i g f).
Proof. exact (fun_ext (fun x : A => @lem7196951 A B s i x g f)). Qed.
Lemma lem7196955 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7196956 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term65 A B s i g f) = (term108 A B s i g f).
Proof. exact (MK_COMB (@lem7196955 A) (@lem7196954 A B s i g f)). Qed.
Lemma lem7196961 {A B : Type'} (i : A -> B) (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term68 A B s i g f) = (term109 A B s i g f).
Proof. exact (MK_COMB (@lem7196912 A B s g f h1) (@lem7196956 A B s i g f)). Qed.
Lemma lem7196963 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7196964 {A B : Type'} (s : A -> Prop) (i : A -> B) (g : B -> real) (f : A -> B) : (term109 A B s i g f) = (term108 A B s i g f).
Proof. exact (@lem7196963 (term108 A B s i g f)). Qed.
Lemma lem7196981 {A B : Type'} (i : A -> B) (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term68 A B s i g f) = (term108 A B s i g f).
Proof. exact (TRANS (@lem7196961 A B i s g f h1) (@lem7196964 A B s i g f)). Qed.
Lemma lem7196982 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term73 A B s g f) = (term110 A B s g f).
Proof. exact (fun_ext (fun i : A -> B => @lem7196981 A B i s g f h1)). Qed.
Lemma lem7196983 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7196984 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term75 A B s g f) = (term111 A B s g f).
Proof. exact (MK_COMB (@lem7196983 A B) (@lem7196982 A B s g f h1)). Qed.
Lemma lem7196989 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : (term111 A B s g f) = (term75 A B s g f).
Proof. exact (SYM (@lem7196984 A B s g f h1)). Qed.
Lemma lem7196991 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7196992 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term113 A B s g f) = (term114 A B s g f).
Proof. exact (@lem7196991 (term113 A B s g f)). Qed.
Lemma lem7196993 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term114 A B s g f) = (term113 A B s g f).
Proof. exact (SYM (@lem7196992 A B s g f)). Qed.
Lemma lem7196994 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : term115 A B s g f.
Proof. exact (h1). Qed.
Lemma lem7196997 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term116 A B s g f) : term116 A B s g f.
Proof. exact (h1). Qed.
Lemma lem7196998 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term117 A B s g f.
Proof. exact (fun h0 : term116 A B s g f => @lem7196997 A B s g f h0). Qed.
Lemma lem7196999 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term117 A B s g f) : term117 A B s g f.
Proof. exact (h1). Qed.
Lemma lem7197000 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term116 A B s g f) : term116 A B s g f.
Proof. exact (h1). Qed.
Lemma lem7197001 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term116 A B s g f) (h2 : term117 A B s g f) : term116 A B s g f.
Proof. exact (@lem7196999 A B s g f h2 (@lem7197000 A B s g f h1)). Qed.
Lemma lem7197002 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term116 A B s g f) : term118 A B s g f.
Proof. exact (fun h0 : term117 A B s g f => @lem7197001 A B s g f h1 h0). Qed.
Lemma lem7197003 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term117 A B s g f) : term117 A B s g f.
Proof. exact (h1). Qed.
Lemma lem7197004 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term116 A B s g f) (h2 : term117 A B s g f) : term116 A B s g f.
Proof. exact (@lem7197002 A B s g f h1 (@lem7197003 A B s g f h2)). Qed.
Lemma lem7197005 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term117 A B s g f) : term117 A B s g f.
Proof. exact (fun h0 : term116 A B s g f => @lem7197004 A B s g f h0 h1). Qed.
Lemma lem7197006 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term119 A B s g f.
Proof. exact (fun h0 : term117 A B s g f => @lem7197005 A B s g f h0). Qed.
Lemma lem7197009 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term117 A B s g f.
Proof. exact (@lem7197006 A B s g f (@lem7196998 A B s g f)). Qed.
Lemma lem7197010 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term117 A B s g f.
Proof. exact (@lem7197009 A B s g f). Qed.
Lemma lem7197084 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7197085 : term120 = term121.
Proof. exact (@lem7197084 term122). Qed.
Lemma lem7197090 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term123 A B s g f) = (term123 A B s g f).
Proof. exact (eq_refl (term123 A B s g f)). Qed.
Lemma lem7197091 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term116 A B s g f) = (term124 A B s g f).
Proof. exact (MK_COMB (@lem7197090 A B s g f) (@lem7197085)). Qed.
Lemma lem7197094 {A B : Type'} (g : B -> real) (f : A -> B) : (term125 A B g f) = (term126 A B g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7197091 A B s g f)). Qed.
Lemma lem7197095 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7197096 {A B : Type'} (g : B -> real) (f : A -> B) : (term127 A B g f) = (term128 A B g f).
Proof. exact (MK_COMB (@lem7197095 A) (@lem7197094 A B g f)). Qed.
Lemma lem7197101 {A B : Type'} (f : A -> B) : (term129 A B f) = (term130 A B f).
Proof. exact (fun_ext (fun g : B -> real => @lem7197096 A B g f)). Qed.
Lemma lem7197102 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7197103 {A B : Type'} (f : A -> B) : (term131 A B f) = (term132 A B f).
Proof. exact (MK_COMB (@lem7197102 B) (@lem7197101 A B f)). Qed.
Lemma lem7197108 {A B : Type'} : (term133 A B) = (term134 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem7197103 A B f)). Qed.
Lemma lem7197109 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7197118 {A B : Type'} : (term135 A B) = (term136 A B).
Proof. exact (MK_COMB (@lem7197109 A B) (@lem7197108 A B)). Qed.
Lemma lem7197119 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem7197120 : term137 = term137.
Proof. exact (fun_ext (fun x : real => @lem7197119 x)). Qed.
Lemma lem7197121 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7197122 : term122 = term122.
Proof. exact (MK_COMB (@lem7197121) (@lem7197120)). Qed.
Lemma lem7197123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7197124 : term121 = term121.
Proof. exact (MK_COMB (@lem7197123) (@lem7197122)). Qed.
Lemma lem7197133 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term138 A B s x g f y) = (term138 A B s x g f y).
Proof. exact (eq_refl (term138 A B s x g f y)). Qed.
Lemma lem7197134 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term139 A B s x g f) = (term139 A B s x g f).
Proof. exact (fun_ext (fun y : A => @lem7197133 A B s x g f y)). Qed.
Lemma lem7197135 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7197136 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term140 A B s x g f) = (term140 A B s x g f).
Proof. exact (MK_COMB (@lem7197135 A) (@lem7197134 A B s x g f)). Qed.
Lemma lem7197139 {A : Type'} (x : A) (s : A -> Prop) : (term60 A x s) = (term60 A x s).
Proof. exact (eq_refl (term60 A x s)). Qed.
Lemma lem7197140 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term141 A B s x g f) = (term141 A B s x g f).
Proof. exact (MK_COMB (@lem7197139 A x s) (@lem7197136 A B s x g f)). Qed.
Lemma lem7197141 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term142 A B s g f) = (term142 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem7197140 A B s x g f)). Qed.
Lemma lem7197142 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7197143 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term113 A B s g f) = (term113 A B s g f).
Proof. exact (MK_COMB (@lem7197142 A) (@lem7197141 A B s g f)). Qed.
Lemma lem7197144 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7197145 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term115 A B s g f) = (term115 A B s g f).
Proof. exact (MK_COMB (@lem7197144) (@lem7197143 A B s g f)). Qed.
Lemma lem7197146 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7197147 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term123 A B s g f) = (term123 A B s g f).
Proof. exact (MK_COMB (@lem7197146) (@lem7197145 A B s g f)). Qed.
Lemma lem7197148 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term124 A B s g f) = (term124 A B s g f).
Proof. exact (MK_COMB (@lem7197147 A B s g f) (@lem7197124)). Qed.
Lemma lem7197149 {A B : Type'} (g : B -> real) (f : A -> B) : (term126 A B g f) = (term126 A B g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7197148 A B s g f)). Qed.
Lemma lem7197150 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7197151 {A B : Type'} (g : B -> real) (f : A -> B) : (term128 A B g f) = (term128 A B g f).
Proof. exact (MK_COMB (@lem7197150 A) (@lem7197149 A B g f)). Qed.
Lemma lem7197152 {A B : Type'} (f : A -> B) : (term130 A B f) = (term130 A B f).
Proof. exact (fun_ext (fun g : B -> real => @lem7197151 A B g f)). Qed.
Lemma lem7197153 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7197154 {A B : Type'} (f : A -> B) : (term132 A B f) = (term132 A B f).
Proof. exact (MK_COMB (@lem7197153 B) (@lem7197152 A B f)). Qed.
Lemma lem7197155 {A B : Type'} : (term134 A B) = (term134 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem7197154 A B f)). Qed.
Lemma lem7197156 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7197157 {A B : Type'} : (term136 A B) = (term136 A B).
Proof. exact (MK_COMB (@lem7197156 A B) (@lem7197155 A B)). Qed.
Lemma lem7197204 {A B : Type'} : (term135 A B) = (term136 A B).
Proof. exact (TRANS (@lem7197118 A B) (@lem7197157 A B)). Qed.
Lemma lem7197205 {A B : Type'} : (term136 A B) = (term135 A B).
Proof. exact (SYM (@lem7197204 A B)). Qed.
Lemma lem7197206 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : term115 A B s g f.
Proof. exact (h1). Qed.
Lemma lem7197207 (h1 : term122) : term122.
Proof. exact (h1). Qed.
Lemma lem7197216 {A B : Type'} (x : A) (g : B -> real) (f : A -> B) (y : A) : (term143 A B x g f y) = (term144 A B x g f y).
Proof. exact (@lem17045 ((f y) = (f x)) (term96 A B x g f y)). Qed.
Lemma lem7197218 {A : Type'} (y : A) (s : A -> Prop) : (term145 A y s) = (term145 A y s).
Proof. exact (eq_refl (term145 A y s)). Qed.
Lemma lem7197219 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term146 A B s x g f y) = (term147 A B s x g f y).
Proof. exact (MK_COMB (@lem7197218 A y s) (@lem7197216 A B x g f y)). Qed.
Lemma lem7197220 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term148 A B s x g f y) = (term146 A B s x g f y).
Proof. exact (@lem17045 (@IN A y s) (term149 A B x g f y)). Qed.
Lemma lem7197221 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term148 A B s x g f y) = (term147 A B s x g f y).
Proof. exact (TRANS (@lem7197220 A B s x g f y) (@lem7197219 A B s x g f y)). Qed.
Lemma lem7197222 {A : Type'} (P : A -> Prop) : (term150 A P) = (term151 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7197223 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term152 A B s x g f) = (term153 A B s x g f).
Proof. exact (@lem7197222 A (term139 A B s x g f)). Qed.
Lemma lem7197224 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term154 A B s x g f y) = (term138 A B s x g f y).
Proof. exact (eq_refl (term154 A B s x g f y)). Qed.
Lemma lem7197225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7197226 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term155 A B s x g f y) = (term148 A B s x g f y).
Proof. exact (MK_COMB (@lem7197225) (@lem7197224 A B s x g f y)). Qed.
Lemma lem7197227 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term155 A B s x g f y) = (term147 A B s x g f y).
Proof. exact (TRANS (@lem7197226 A B s x g f y) (@lem7197221 A B s x g f y)). Qed.
Lemma lem7197228 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term156 A B s x g f) = (term157 A B s x g f).
Proof. exact (fun_ext (fun y : A => @lem7197227 A B s x g f y)). Qed.
Lemma lem7197229 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7197230 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term153 A B s x g f) = (term158 A B s x g f).
Proof. exact (MK_COMB (@lem7197229 A) (@lem7197228 A B s x g f)). Qed.
Lemma lem7197231 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term152 A B s x g f) = (term158 A B s x g f).
Proof. exact (TRANS (@lem7197223 A B s x g f) (@lem7197230 A B s x g f)). Qed.
Lemma lem7197233 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (term100 A x s).
Proof. exact (eq_refl (term100 A x s)). Qed.
Lemma lem7197234 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term159 A B s x g f) = (term160 A B s x g f).
Proof. exact (MK_COMB (@lem7197233 A x s) (@lem7197231 A B s x g f)). Qed.
Lemma lem7197235 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term161 A B s x g f) = (term159 A B s x g f).
Proof. exact (@lem17362 (@IN A x s) (term140 A B s x g f)). Qed.
Lemma lem7197236 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term161 A B s x g f) = (term160 A B s x g f).
Proof. exact (TRANS (@lem7197235 A B s x g f) (@lem7197234 A B s x g f)). Qed.
Lemma lem7197237 {A : Type'} (P : A -> Prop) : (term162 A P) = (term163 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7197238 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term115 A B s g f) = (term164 A B s g f).
Proof. exact (@lem7197237 A (term142 A B s g f)). Qed.
Lemma lem7197239 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term165 A B s g f x) = (term141 A B s x g f).
Proof. exact (eq_refl (term165 A B s g f x)). Qed.
Lemma lem7197240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7197241 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term166 A B s g f x) = (term161 A B s x g f).
Proof. exact (MK_COMB (@lem7197240) (@lem7197239 A B s x g f)). Qed.
Lemma lem7197242 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term166 A B s g f x) = (term160 A B s x g f).
Proof. exact (TRANS (@lem7197241 A B s x g f) (@lem7197236 A B s x g f)). Qed.
Lemma lem7197243 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term167 A B s g f) = (term168 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem7197242 A B s x g f)). Qed.
Lemma lem7197244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7197245 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term164 A B s g f) = (term169 A B s g f).
Proof. exact (MK_COMB (@lem7197244 A) (@lem7197243 A B s g f)). Qed.
Lemma lem7197346 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term115 A B s g f) = (term169 A B s g f).
Proof. exact (TRANS (@lem7197238 A B s g f) (@lem7197245 A B s g f)). Qed.
Lemma lem7197347 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : term169 A B s g f.
Proof. exact (EQ_MP (@lem7197346 A B s g f) (@lem7197206 A B s g f h1)). Qed.
Lemma lem7197348 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem7197349 : term137 = term137.
Proof. exact (fun_ext (fun x : real => @lem7197348 x)). Qed.
Lemma lem7197350 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7197359 : term122 = term122.
Proof. exact (MK_COMB (@lem7197350) (@lem7197349)). Qed.
Lemma lem7197360 (h1 : term122) : term122.
Proof. exact (EQ_MP (@lem7197359) (@lem7197207 h1)). Qed.
Lemma lem7197361 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term160 A B s x g f.
Proof. exact (h1). Qed.
Lemma lem7197366 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem7197367 : term137 = term137.
Proof. exact (fun_ext (fun x : real => @lem7197366 x)). Qed.
Lemma lem7197368 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7197369 : term122 = term122.
Proof. exact (MK_COMB (@lem7197368) (@lem7197367)). Qed.
Lemma lem7197370 (h1 : term122) : term122.
Proof. exact (EQ_MP (@lem7197369) (@lem7197360 h1)). Qed.
Lemma lem7197409 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term147 A B s x g f y) = (term147 A B s x g f y).
Proof. exact (eq_refl (term147 A B s x g f y)). Qed.
Lemma lem7197410 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term157 A B s x g f) = (term157 A B s x g f).
Proof. exact (fun_ext (fun y : A => @lem7197409 A B s x g f y)). Qed.
Lemma lem7197411 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7197412 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term158 A B s x g f) = (term158 A B s x g f).
Proof. exact (MK_COMB (@lem7197411 A) (@lem7197410 A B s x g f)). Qed.
Lemma lem7197419 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (term100 A x s).
Proof. exact (eq_refl (term100 A x s)). Qed.
Lemma lem7197420 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term160 A B s x g f) = (term160 A B s x g f).
Proof. exact (MK_COMB (@lem7197419 A x s) (@lem7197412 A B s x g f)). Qed.
Lemma lem7197421 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term160 A B s x g f.
Proof. exact (EQ_MP (@lem7197420 A B s x g f) (@lem7197361 A B s x g f h1)). Qed.
Lemma lem7197422 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term158 A B s x g f.
Proof. exact (proj2 (@lem7197421 A B s x g f h1)). Qed.
Lemma lem7197425 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem7197426 : term137 = term137.
Proof. exact (fun_ext (fun x : real => @lem7197425 x)). Qed.
Lemma lem7197427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7197429 : term122 = term122.
Proof. exact (MK_COMB (@lem7197427) (@lem7197426)). Qed.
Lemma lem7197430 (h1 : term122) : term122.
Proof. exact (EQ_MP (@lem7197429) (@lem7197370 h1)). Qed.
Lemma lem7197448 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (y : A) : (term147 A B s x g f y) = (term147 A B s x g f y).
Proof. exact (eq_refl (term147 A B s x g f y)). Qed.
Lemma lem7197449 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term157 A B s x g f) = (term157 A B s x g f).
Proof. exact (fun_ext (fun y : A => @lem7197448 A B s x g f y)). Qed.
Lemma lem7197450 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7197452 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) : (term158 A B s x g f) = (term158 A B s x g f).
Proof. exact (MK_COMB (@lem7197450 A) (@lem7197449 A B s x g f)). Qed.
Lemma lem7197453 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term158 A B s x g f.
Proof. exact (EQ_MP (@lem7197452 A B s x g f) (@lem7197422 A B s x g f h1)). Qed.
Lemma lem7197454 (_96469 : real) (h1 : term122) : term170 _96469.
Proof. exact (@lem7197430 h1 _96469). Qed.
Lemma lem7197455 (_96469 : real) : (term170 _96469) = (real_le _96469 _96469).
Proof. exact (eq_refl (term170 _96469)). Qed.
Lemma lem7197457 {A B : Type'} (_96470 : A) (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term171 A B s x g f _96470.
Proof. exact (@lem7197453 A B s x g f h1 _96470). Qed.
Lemma lem7197458 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (_96470 : A) : (term171 A B s x g f _96470) = (term147 A B s x g f _96470).
Proof. exact (eq_refl (term171 A B s x g f _96470)). Qed.
Lemma lem7197473 {A B : Type'} (_96470 : A) (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term147 A B s x g f _96470.
Proof. exact (EQ_MP (@lem7197458 A B s x g f _96470) (@lem7197457 A B _96470 s x g f h1)). Qed.
Lemma lem7197537 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : @IN A x s.
Proof. exact (proj1 (@lem7197421 A B s x g f h1)). Qed.
Lemma lem7197538 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term172 A x s.
Proof. exact (fun h0 : term173 A x s => @lem7197537 A B s x g f h1). Qed.
Lemma lem7197540 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7197541 {A : Type'} (x : A) (s : A -> Prop) : (term172 A x s) = (@IN A x s).
Proof. exact (@lem7197540 (@IN A x s)). Qed.
Lemma lem7197542 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : @IN A x s.
Proof. exact (EQ_MP (@lem7197541 A x s) (@lem7197538 A B s x g f h1)). Qed.
Lemma lem7197544 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem7197545 {B : Type'} (x : B) : x = x.
Proof. exact (@lem7197544 B x). Qed.
Lemma lem7197546 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem7197545 B (f x)). Qed.
Lemma lem7197547 {A B : Type'} (f : A -> B) (x : A) : term175 A B f x.
Proof. exact (fun h0 : term176 A B f x => @lem7197546 A B f x). Qed.
Lemma lem7197549 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7197550 {A B : Type'} (f : A -> B) (x : A) : (term175 A B f x) = ((f x) = (f x)).
Proof. exact (@lem7197549 ((f x) = (f x))). Qed.
Lemma lem7197551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem7197550 A B f x) (@lem7197547 A B f x)). Qed.
Lemma lem7197553 (_96469 : real) (h1 : term122) : real_le _96469 _96469.
Proof. exact (EQ_MP (@lem7197455 _96469) (@lem7197454 _96469 h1)). Qed.
Lemma lem7197554 {A B : Type'} (g : B -> real) (f : A -> B) (x : A) (h1 : term122) : term177 A B g f x.
Proof. exact (@lem7197553 (term84 A B g f x) h1). Qed.
Lemma lem7197555 {A B : Type'} (g : B -> real) (f : A -> B) (x : A) (h1 : term122) : term178 A B g f x.
Proof. exact (fun h0 : term179 A B g f x => @lem7197554 A B g f x h1). Qed.
Lemma lem7197557 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7197558 {A B : Type'} (g : B -> real) (f : A -> B) (x : A) : (term178 A B g f x) = (term177 A B g f x).
Proof. exact (@lem7197557 (term177 A B g f x)). Qed.
Lemma lem7197559 {A B : Type'} (g : B -> real) (f : A -> B) (x : A) (h1 : term122) : term177 A B g f x.
Proof. exact (EQ_MP (@lem7197558 A B g f x) (@lem7197555 A B g f x h1)). Qed.
Lemma lem7197561 (a : Prop) (b : Prop) : (term180 a b) = (term181 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7197562 {A B : Type'} (x : A) (g : B -> real) (f : A -> B) (_96470 : A) : (term144 A B x g f _96470) = (term143 A B x g f _96470).
Proof. exact (@lem7197561 ((f _96470) = (f x)) (term96 A B x g f _96470)). Qed.
Lemma lem7197563 {A : Type'} (_96470 : A) (s : A -> Prop) : (term145 A _96470 s) = (term145 A _96470 s).
Proof. exact (eq_refl (term145 A _96470 s)). Qed.
Lemma lem7197564 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (_96470 : A) : (term147 A B s x g f _96470) = (term146 A B s x g f _96470).
Proof. exact (MK_COMB (@lem7197563 A _96470 s) (@lem7197562 A B x g f _96470)). Qed.
Lemma lem7197566 (a : Prop) (b : Prop) : (term180 a b) = (term181 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7197567 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (_96470 : A) : (term146 A B s x g f _96470) = (term148 A B s x g f _96470).
Proof. exact (@lem7197566 (@IN A _96470 s) (term149 A B x g f _96470)). Qed.
Lemma lem7197568 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (_96470 : A) : (term147 A B s x g f _96470) = (term148 A B s x g f _96470).
Proof. exact (TRANS (@lem7197564 A B s x g f _96470) (@lem7197567 A B s x g f _96470)). Qed.
Lemma lem7197570 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7197571 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (_96470 : A) : (term148 A B s x g f _96470) = (term182 A B s x g f _96470).
Proof. exact (@lem7197570 (term138 A B s x g f _96470)). Qed.
Lemma lem7197572 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (_96470 : A) : (term147 A B s x g f _96470) = (term182 A B s x g f _96470).
Proof. exact (TRANS (@lem7197568 A B s x g f _96470) (@lem7197571 A B s x g f _96470)). Qed.
Lemma lem7197574 {A B : Type'} (g : B -> real) (f : A -> B) (x : A) (h1 : term122) : term183 A B g f x.
Proof. exact (conj (@lem7197551 A B f x) (@lem7197559 A B g f x h1)). Qed.
Lemma lem7197575 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : term184 A B s g f x.
Proof. exact (conj (@lem7197542 A B s x g f h2) (@lem7197574 A B g f x h1)). Qed.
Lemma lem7197577 {A B : Type'} (_96470 : A) (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term182 A B s x g f _96470.
Proof. exact (EQ_MP (@lem7197572 A B s x g f _96470) (@lem7197473 A B _96470 s x g f h1)). Qed.
Lemma lem7197578 {A B : Type'} (_96470 : A) (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term182 A B s x g f _96470.
Proof. exact (@lem7197577 A B _96470 s x g f h1). Qed.
Lemma lem7197579 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term160 A B s x g f) : term185 A B s g f x.
Proof. exact (@lem7197578 A B x s x g f h1). Qed.
Lemma lem7197582 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : False.
Proof. exact (@lem7197579 A B s x g f h2 (@lem7197575 A B s x g f h1 h2)). Qed.
Lemma lem7197583 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : term186.
Proof. exact (fun h0 : ~ False => @lem7197582 A B s x g f h1 h2). Qed.
Lemma lem7197585 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7197586 : term186 = False.
Proof. exact (@lem7197585 False). Qed.
Lemma lem7197587 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : False.
Proof. exact (EQ_MP (@lem7197586) (@lem7197583 A B s x g f h1 h2)). Qed.
Lemma lem7197588 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : term122 = False.
Proof. exact (prop_ext (fun h3 : term122 => @lem7197587 A B s x g f h1 h2) (fun h3 : False => @lem7197430 h1)). Qed.
Lemma lem7197589 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : False.
Proof. exact (EQ_MP (@lem7197588 A B s x g f h1 h2) (@lem7197430 h1)). Qed.
Lemma lem7197590 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : (term160 A B s x g f) = False.
Proof. exact (prop_ext (fun h3 : term160 A B s x g f => @lem7197589 A B s x g f h1 h2) (fun h3 : False => @lem7197421 A B s x g f h2)). Qed.
Lemma lem7197591 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : False.
Proof. exact (EQ_MP (@lem7197590 A B s x g f h1 h2) (@lem7197421 A B s x g f h2)). Qed.
Lemma lem7197592 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : term122 = False.
Proof. exact (prop_ext (fun h3 : term122 => @lem7197591 A B s x g f h1 h2) (fun h3 : False => @lem7197370 h1)). Qed.
Lemma lem7197593 {A B : Type'} (s : A -> Prop) (x : A) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term160 A B s x g f) : False.
Proof. exact (EQ_MP (@lem7197592 A B s x g f h1 h2) (@lem7197370 h1)). Qed.
Lemma lem7197594 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term115 A B s g f) : False.
Proof. exact (ex_elim (@lem7197347 A B s g f h2) (fun x : A => fun h0 : term168 A B s g f x => @lem7197593 A B s x g f h1 h0)). Qed.
Lemma lem7197595 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term115 A B s g f) : term122 = False.
Proof. exact (prop_ext (fun h3 : term122 => @lem7197594 A B s g f h1 h2) (fun h3 : False => @lem7197360 h1)). Qed.
Lemma lem7197596 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term122) (h2 : term115 A B s g f) : False.
Proof. exact (EQ_MP (@lem7197595 A B s g f h1 h2) (@lem7197360 h1)). Qed.
Lemma lem7197597 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : term120.
Proof. exact (fun h0 : term122 => @lem7197596 A B s g f h0 h1). Qed.
Lemma lem7197598 : term120 = term121.
Proof. exact (@lem69 term122). Qed.
Lemma lem7197599 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : term121.
Proof. exact (EQ_MP (@lem7197598) (@lem7197597 A B s g f h1)). Qed.
Lemma lem7197600 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term124 A B s g f.
Proof. exact (fun h0 : term115 A B s g f => @lem7197599 A B s g f h0). Qed.
Lemma lem7197605 {A B : Type'} (g : B -> real) (f : A -> B) : term128 A B g f.
Proof. exact (fun s : A -> Prop => @lem7197600 A B s g f). Qed.
Lemma lem7197610 {A B : Type'} (f : A -> B) : term132 A B f.
Proof. exact (fun g : B -> real => @lem7197605 A B g f). Qed.
Lemma lem7197615 {A B : Type'} : term136 A B.
Proof. exact (fun f : A -> B => @lem7197610 A B f). Qed.
Lemma lem7197616 {A B : Type'} : term135 A B.
Proof. exact (EQ_MP (@lem7197205 A B) (@lem7197615 A B)). Qed.
Lemma lem7197617 {A B : Type'} (f : A -> B) : term187 A B f.
Proof. exact (@lem7197616 A B f). Qed.
Lemma lem7197618 {A B : Type'} (f : A -> B) : (term187 A B f) = (term131 A B f).
Proof. exact (eq_refl (term187 A B f)). Qed.
Lemma lem7197619 {A B : Type'} (f : A -> B) : term131 A B f.
Proof. exact (EQ_MP (@lem7197618 A B f) (@lem7197617 A B f)). Qed.
Lemma lem7197620 {A B : Type'} (f : A -> B) (g : B -> real) : term188 A B f g.
Proof. exact (@lem7197619 A B f g). Qed.
Lemma lem7197621 {A B : Type'} (g : B -> real) (f : A -> B) : (term188 A B f g) = (term127 A B g f).
Proof. exact (eq_refl (term188 A B f g)). Qed.
Lemma lem7197622 {A B : Type'} (g : B -> real) (f : A -> B) : term127 A B g f.
Proof. exact (EQ_MP (@lem7197621 A B g f) (@lem7197620 A B f g)). Qed.
Lemma lem7197623 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) : term189 A B g f s.
Proof. exact (@lem7197622 A B g f s). Qed.
Lemma lem7197624 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : (term189 A B g f s) = (term116 A B s g f).
Proof. exact (eq_refl (term189 A B g f s)). Qed.
Lemma lem7197625 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term116 A B s g f.
Proof. exact (EQ_MP (@lem7197624 A B s g f) (@lem7197623 A B g f s)). Qed.
Lemma lem7197627 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term116 A B s g f.
Proof. exact (@lem7197010 A B s g f (@lem7197625 A B s g f)). Qed.
Lemma lem7197628 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : term120.
Proof. exact (@lem7197627 A B s g f (@lem7196994 A B s g f h1)). Qed.
Lemma lem7197629 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : False.
Proof. exact (@lem7197628 A B s g f h1 (@lem1339240)). Qed.
Lemma lem7197630 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : (term115 A B s g f) = False.
Proof. exact (prop_ext (fun h2 : term115 A B s g f => @lem7197629 A B s g f h1) (fun h2 : False => @lem7196994 A B s g f h1)). Qed.
Lemma lem7197631 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term115 A B s g f) : False.
Proof. exact (EQ_MP (@lem7197630 A B s g f h1) (@lem7196994 A B s g f h1)). Qed.
Lemma lem7197632 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term114 A B s g f.
Proof. exact (fun h0 : term115 A B s g f => @lem7197631 A B s g f h0). Qed.
Lemma lem7197633 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term113 A B s g f.
Proof. exact (EQ_MP (@lem7196993 A B s g f) (@lem7197632 A B s g f)). Qed.
Lemma lem7197634 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term111 A B s g f.
Proof. exact (ex_intro (term110 A B s g f) f (@lem7197633 A B s g f)). Qed.
Lemma lem7197635 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term27 A B s g f) : term75 A B s g f.
Proof. exact (EQ_MP (@lem7196989 A B s g f h1) (@lem7197634 A B s g f)). Qed.
Lemma lem7197636 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : term27 A B s g f) (h2 : @FINITE A s) : term74 A B s g f.
Proof. exact (EQ_MP (@lem7196861 A B g f s h2) (@lem7197635 A B s g f h1)). Qed.
Lemma lem7197637 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : term27 A B s g f) (h2 : @FINITE A s) : term190 A B s g f.
Proof. exact (@lem7196308 A B s g f (@lem7197636 A B g f s h1 h2)). Qed.
Lemma lem7197638 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term26 A B s g f) : term27 A B s g f.
Proof. exact (proj2 (@lem7196302 A B s g f h1)). Qed.
Lemma lem7197639 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term26 A B s g f) : @FINITE A s.
Proof. exact (proj1 (@lem7196302 A B s g f h1)). Qed.
Lemma lem7197640 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : term27 A B s g f) (h2 : @FINITE A s) : (term27 A B s g f) = (term190 A B s g f).
Proof. exact (prop_ext (fun h3 : term27 A B s g f => @lem7197637 A B g f s h1 h2) (fun h3 : term190 A B s g f => @lem7196303 A B s g f h1)). Qed.
Lemma lem7197641 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : term27 A B s g f) (h2 : @FINITE A s) : term190 A B s g f.
Proof. exact (EQ_MP (@lem7197640 A B g f s h1 h2) (@lem7196303 A B s g f h1)). Qed.
Lemma lem7197642 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : term27 A B s g f) (h2 : @FINITE A s) : (@FINITE A s) = (term190 A B s g f).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7197641 A B g f s h1 h2) (fun h3 : term190 A B s g f => @lem7196304 A s h2)). Qed.
Lemma lem7197643 {A B : Type'} (g : B -> real) (f : A -> B) (s : A -> Prop) (h1 : term27 A B s g f) (h2 : @FINITE A s) : term190 A B s g f.
Proof. exact (EQ_MP (@lem7197642 A B g f s h1 h2) (@lem7196304 A s h2)). Qed.
Lemma lem7197644 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : @FINITE A s) (h2 : term26 A B s g f) : (term27 A B s g f) = (term190 A B s g f).
Proof. exact (prop_ext (fun h3 : term27 A B s g f => @lem7197643 A B g f s h3 h1) (fun h3 : term190 A B s g f => @lem7197638 A B s g f h2)). Qed.
Lemma lem7197645 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : @FINITE A s) (h2 : term26 A B s g f) : term190 A B s g f.
Proof. exact (EQ_MP (@lem7197644 A B s g f h1 h2) (@lem7197638 A B s g f h2)). Qed.
Lemma lem7197646 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term26 A B s g f) : (@FINITE A s) = (term190 A B s g f).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7197645 A B s g f h2 h1) (fun h2 : term190 A B s g f => @lem7197639 A B s g f h1)). Qed.
Lemma lem7197647 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) (h1 : term26 A B s g f) : term190 A B s g f.
Proof. exact (EQ_MP (@lem7197646 A B s g f h1) (@lem7197639 A B s g f h1)). Qed.
Lemma lem7197648 {A B : Type'} (s : A -> Prop) (g : B -> real) (f : A -> B) : term191 A B s g f.
Proof. exact (fun h0 : term26 A B s g f => @lem7197647 A B s g f h0). Qed.
Lemma lem7197653 {A B : Type'} (g : B -> real) (f : A -> B) : term192 A B g f.
Proof. exact (fun s : A -> Prop => @lem7197648 A B s g f). Qed.
Lemma lem7197658 {A B : Type'} (f : A -> B) : term193 A B f.
Proof. exact (fun g : B -> real => @lem7197653 A B g f). Qed.
Lemma lem7197663 {A B : Type'} : term194 A B.
Proof. exact (fun f : A -> B => @lem7197658 A B f). Qed.
