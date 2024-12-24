Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_COMPOSE_LEFT_term_abbrevs.
Require Import FORALL_IN_IMAGE_spec.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import SUBSET_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4393246 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term0 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4393247 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term0 _87967 _87968 P f) = (term1 _87967 _87968 P f).
Proof. exact (eq_refl (term0 _87967 _87968 P f)). Qed.
Lemma lem4393248 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term1 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4393247 _87967 _87968 P f) (@lem4393246 _87967 _87968 P f)). Qed.
Lemma lem4393249 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term2 _87967 _87968 P f s.
Proof. exact (@lem4393248 _87967 _87968 P f s). Qed.
Lemma lem4393250 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term2 _87967 _87968 P f s) = ((term3 _87967 _87968 f s P) = (term4 _87967 _87968 s P f)).
Proof. exact (eq_refl (term2 _87967 _87968 P f s)). Qed.
Lemma lem4393252 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4393253 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (eq_refl (term5 A s)). Qed.
Lemma lem4393254 {A : Type'} (s : A -> Prop) : term6 A s.
Proof. exact (EQ_MP (@lem4393253 A s) (@lem4393252 A s)). Qed.
Lemma lem4393255 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term7 A s t.
Proof. exact (@lem4393254 A s t). Qed.
Lemma lem4393256 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = ((@SUBSET A s t) = (term8 A s t)).
Proof. exact (eq_refl (term7 A s t)). Qed.
Lemma lem4393258 {A B : Type'} (s : A -> Prop) : term9 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4393259 {A B : Type'} (s : A -> Prop) : (term9 A B s) = (term10 A B s).
Proof. exact (eq_refl (term9 A B s)). Qed.
Lemma lem4393260 {A B : Type'} (s : A -> Prop) : term10 A B s.
Proof. exact (EQ_MP (@lem4393259 A B s) (@lem4393258 A B s)). Qed.
Lemma lem4393261 {A B : Type'} (s : A -> Prop) (f : A -> B) : term11 A B s f.
Proof. exact (@lem4393260 A B s f). Qed.
Lemma lem4393262 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B s f) = (term12 A B s f).
Proof. exact (eq_refl (term11 A B s f)). Qed.
Lemma lem4393263 {A B : Type'} (s : A -> Prop) (f : A -> B) : term12 A B s f.
Proof. exact (EQ_MP (@lem4393262 A B s f) (@lem4393261 A B s f)). Qed.
Lemma lem4393264 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term13 A B s f x.
Proof. exact (@lem4393263 A B s f x). Qed.
Lemma lem4393265 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term13 A B s f x) = ((@RESTRICTION A B s f x) = (term14 A B s f x)).
Proof. exact (eq_refl (term13 A B s f x)). Qed.
Lemma lem4393267 {A B C : Type'} (f : B -> C) : term15 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem4393268 {A B C : Type'} (f : B -> C) : (term15 A B C f) = (term16 A B C f).
Proof. exact (eq_refl (term15 A B C f)). Qed.
Lemma lem4393269 {A B C : Type'} (f : B -> C) : term16 A B C f.
Proof. exact (EQ_MP (@lem4393268 A B C f) (@lem4393267 A B C f)). Qed.
Lemma lem4393270 {A B C : Type'} (f : B -> C) (g : A -> B) : term17 A B C f g.
Proof. exact (@lem4393269 A B C f g). Qed.
Lemma lem4393271 {A B C : Type'} (f : B -> C) (g : A -> B) : (term17 A B C f g) = ((@o A B C f g) = (term18 A B C f g)).
Proof. exact (eq_refl (term17 A B C f g)). Qed.
Lemma lem4393273 {A B : Type'} (f : A -> B) : term19 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4393274 {A B : Type'} (f : A -> B) : (term19 A B f) = (term20 A B f).
Proof. exact (eq_refl (term19 A B f)). Qed.
Lemma lem4393275 {A B : Type'} (f : A -> B) : term20 A B f.
Proof. exact (EQ_MP (@lem4393274 A B f) (@lem4393273 A B f)). Qed.
Lemma lem4393276 {A B : Type'} (f : A -> B) (g : A -> B) : term21 A B f g.
Proof. exact (@lem4393275 A B f g). Qed.
Lemma lem4393277 {A B : Type'} (f : A -> B) (g : A -> B) : (term21 A B f g) = ((f = g) = (term22 A B f g)).
Proof. exact (eq_refl (term21 A B f g)). Qed.
Lemma lem4393300 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term22 A B f g).
Proof. exact (EQ_MP (@lem4393277 A B f g) (@lem4393276 A B f g)). Qed.
Lemma lem4393301 {A C : Type'} (f : A -> C) (g : A -> C) : (f = g) = (term22 A C f g).
Proof. exact (@lem4393300 A C f g). Qed.
Lemma lem4393302 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term23 A B C s t g f) = (term24 A B C s g f)) = (term25 A B C t s g f).
Proof. exact (@lem4393301 A C (term23 A B C s t g f) (term24 A B C s g f)). Qed.
Lemma lem4393312 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term14 A B s f x).
Proof. exact (EQ_MP (@lem4393265 A B s f x) (@lem4393264 A B s f x)). Qed.
Lemma lem4393313 {A C : Type'} (s : A -> Prop) (f : A -> C) (x : A) : (@RESTRICTION A C s f x) = (term14 A C s f x).
Proof. exact (@lem4393312 A C s f x). Qed.
Lemma lem4393314 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term26 A B C s t g f x) = (term27 A B C s t g f x).
Proof. exact (@lem4393313 A C s (term28 A B C t g f) x). Qed.
Lemma lem4393316 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term18 A B C f g).
Proof. exact (EQ_MP (@lem4393271 A B C f g) (@lem4393270 A B C f g)). Qed.
Lemma lem4393317 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term18 A B C f g).
Proof. exact (@lem4393316 A B C f g). Qed.
Lemma lem4393318 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) : (term28 A B C t g f) = (term29 A B C t g f).
Proof. exact (@lem4393317 A B C (@RESTRICTION B C t g) f). Qed.
Lemma lem4393320 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term14 A B s f x).
Proof. exact (EQ_MP (@lem4393265 A B s f x) (@lem4393264 A B s f x)). Qed.
Lemma lem4393321 {B C : Type'} (s : B -> Prop) (f : B -> C) (x : B) : (@RESTRICTION B C s f x) = (term14 B C s f x).
Proof. exact (@lem4393320 B C s f x). Qed.
Lemma lem4393322 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term30 A B C t g f x) = (term31 A B C t g f x).
Proof. exact (@lem4393321 B C t g (f x)). Qed.
Lemma lem4393323 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) : (term29 A B C t g f) = (term32 A B C t g f).
Proof. exact (fun_ext (fun x : A => @lem4393322 A B C t g f x)). Qed.
Lemma lem4393324 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) : (term28 A B C t g f) = (term32 A B C t g f).
Proof. exact (TRANS (@lem4393318 A B C t g f) (@lem4393323 A B C t g f)). Qed.
Lemma lem4393325 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4393326 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term33 A B C t g f x) = (term34 A B C t g f x).
Proof. exact (MK_COMB (@lem4393324 A B C t g f) (@lem4393325 A x)). Qed.
Lemma lem4393328 {A B : Type'} (f : A -> B) (y : A) : (term35 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4393329 {A C : Type'} (f : A -> C) (y : A) : (term35 A C f y) = (f y).
Proof. exact (@lem4393328 A C f y). Qed.
Lemma lem4393330 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term36 A B C t g f x) = (term34 A B C t g f x).
Proof. exact (@lem4393329 A C (term32 A B C t g f) x). Qed.
Lemma lem4393331 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term34 A B C t g f x) = (term31 A B C t g f x).
Proof. exact (eq_refl (term34 A B C t g f x)). Qed.
Lemma lem4393332 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) : (term37 A B C t g f) = (term32 A B C t g f).
Proof. exact (fun_ext (fun x : A => @lem4393331 A B C t g f x)). Qed.
Lemma lem4393333 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4393334 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term36 A B C t g f x) = (term34 A B C t g f x).
Proof. exact (MK_COMB (@lem4393332 A B C t g f) (@lem4393333 A x)). Qed.
Lemma lem4393335 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4393336 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term38 A B C t g f x) = (term39 A B C t g f x).
Proof. exact (MK_COMB (@lem4393335 C) (@lem4393334 A B C t g f x)). Qed.
Lemma lem4393337 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term34 A B C t g f x) = (term31 A B C t g f x).
Proof. exact (eq_refl (term34 A B C t g f x)). Qed.
Lemma lem4393338 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : ((term36 A B C t g f x) = (term34 A B C t g f x)) = ((term34 A B C t g f x) = (term31 A B C t g f x)).
Proof. exact (MK_COMB (@lem4393336 A B C t g f x) (@lem4393337 A B C t g f x)). Qed.
Lemma lem4393339 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term34 A B C t g f x) = (term31 A B C t g f x).
Proof. exact (EQ_MP (@lem4393338 A B C t g f x) (@lem4393330 A B C t g f x)). Qed.
Lemma lem4393340 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term33 A B C t g f x) = (term31 A B C t g f x).
Proof. exact (TRANS (@lem4393326 A B C t g f x) (@lem4393339 A B C t g f x)). Qed.
Lemma lem4393341 {A C : Type'} (x : A) (s : A -> Prop) : (term40 A C x s) = (term40 A C x s).
Proof. exact (eq_refl (term40 A C x s)). Qed.
Lemma lem4393342 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term41 A B C s t g f x) = (term42 A B C s t g f x).
Proof. exact (MK_COMB (@lem4393341 A C x s) (@lem4393340 A B C t g f x)). Qed.
Lemma lem4393343 {C : Type'} : (@ARB C) = (@ARB C).
Proof. exact (eq_refl (@ARB C)). Qed.
Lemma lem4393344 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term27 A B C s t g f x) = (term43 A B C s t g f x).
Proof. exact (MK_COMB (@lem4393342 A B C s t g f x) (@lem4393343 C)). Qed.
Lemma lem4393345 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term26 A B C s t g f x) = (term43 A B C s t g f x).
Proof. exact (TRANS (@lem4393314 A B C s t g f x) (@lem4393344 A B C s t g f x)). Qed.
Lemma lem4393346 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4393347 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term44 A B C s t g f x) = (term45 A B C s t g f x).
Proof. exact (MK_COMB (@lem4393346 C) (@lem4393345 A B C s t g f x)). Qed.
Lemma lem4393349 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term14 A B s f x).
Proof. exact (EQ_MP (@lem4393265 A B s f x) (@lem4393264 A B s f x)). Qed.
Lemma lem4393350 {A C : Type'} (s : A -> Prop) (f : A -> C) (x : A) : (@RESTRICTION A C s f x) = (term14 A C s f x).
Proof. exact (@lem4393349 A C s f x). Qed.
Lemma lem4393351 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term46 A B C s g f x) = (term47 A B C s g f x).
Proof. exact (@lem4393350 A C s (@o A B C g f) x). Qed.
Lemma lem4393353 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term18 A B C f g).
Proof. exact (EQ_MP (@lem4393271 A B C f g) (@lem4393270 A B C f g)). Qed.
Lemma lem4393354 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term18 A B C f g).
Proof. exact (@lem4393353 A B C f g). Qed.
Lemma lem4393355 {A B C : Type'} (g : B -> C) (f : A -> B) : (@o A B C g f) = (term18 A B C g f).
Proof. exact (@lem4393354 A B C g f). Qed.
Lemma lem4393356 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4393357 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (@o A B C g f x) = (term48 A B C g f x).
Proof. exact (MK_COMB (@lem4393355 A B C g f) (@lem4393356 A x)). Qed.
Lemma lem4393359 {A B : Type'} (f : A -> B) (y : A) : (term35 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4393360 {A C : Type'} (f : A -> C) (y : A) : (term35 A C f y) = (f y).
Proof. exact (@lem4393359 A C f y). Qed.
Lemma lem4393361 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term49 A B C g f x) = (term48 A B C g f x).
Proof. exact (@lem4393360 A C (term18 A B C g f) x). Qed.
Lemma lem4393362 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term48 A B C g f x) = (term50 A B C g f x).
Proof. exact (eq_refl (term48 A B C g f x)). Qed.
Lemma lem4393363 {A B C : Type'} (g : B -> C) (f : A -> B) : (term51 A B C g f) = (term18 A B C g f).
Proof. exact (fun_ext (fun x : A => @lem4393362 A B C g f x)). Qed.
Lemma lem4393364 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4393365 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term49 A B C g f x) = (term48 A B C g f x).
Proof. exact (MK_COMB (@lem4393363 A B C g f) (@lem4393364 A x)). Qed.
Lemma lem4393366 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4393367 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term52 A B C g f x) = (term53 A B C g f x).
Proof. exact (MK_COMB (@lem4393366 C) (@lem4393365 A B C g f x)). Qed.
Lemma lem4393368 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term48 A B C g f x) = (term50 A B C g f x).
Proof. exact (eq_refl (term48 A B C g f x)). Qed.
Lemma lem4393369 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : ((term49 A B C g f x) = (term48 A B C g f x)) = ((term48 A B C g f x) = (term50 A B C g f x)).
Proof. exact (MK_COMB (@lem4393367 A B C g f x) (@lem4393368 A B C g f x)). Qed.
Lemma lem4393370 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term48 A B C g f x) = (term50 A B C g f x).
Proof. exact (EQ_MP (@lem4393369 A B C g f x) (@lem4393361 A B C g f x)). Qed.
Lemma lem4393371 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (@o A B C g f x) = (term50 A B C g f x).
Proof. exact (TRANS (@lem4393357 A B C g f x) (@lem4393370 A B C g f x)). Qed.
Lemma lem4393372 {A C : Type'} (x : A) (s : A -> Prop) : (term40 A C x s) = (term40 A C x s).
Proof. exact (eq_refl (term40 A C x s)). Qed.
Lemma lem4393373 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term54 A B C s g f x) = (term55 A B C s g f x).
Proof. exact (MK_COMB (@lem4393372 A C x s) (@lem4393371 A B C g f x)). Qed.
Lemma lem4393374 {C : Type'} : (@ARB C) = (@ARB C).
Proof. exact (eq_refl (@ARB C)). Qed.
Lemma lem4393375 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term47 A B C s g f x) = (term56 A B C s g f x).
Proof. exact (MK_COMB (@lem4393373 A B C s g f x) (@lem4393374 C)). Qed.
Lemma lem4393376 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term46 A B C s g f x) = (term56 A B C s g f x).
Proof. exact (TRANS (@lem4393351 A B C s g f x) (@lem4393375 A B C s g f x)). Qed.
Lemma lem4393377 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : ((term26 A B C s t g f x) = (term46 A B C s g f x)) = ((term43 A B C s t g f x) = (term56 A B C s g f x)).
Proof. exact (MK_COMB (@lem4393347 A B C s t g f x) (@lem4393376 A B C s g f x)). Qed.
Lemma lem4393382 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term57 A B C t s g f) = (term58 A B C t s g f).
Proof. exact (fun_ext (fun x : A => @lem4393377 A B C t s g f x)). Qed.
Lemma lem4393383 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4393384 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term25 A B C t s g f) = (term59 A B C t s g f).
Proof. exact (MK_COMB (@lem4393383 A) (@lem4393382 A B C t s g f)). Qed.
Lemma lem4393389 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term23 A B C s t g f) = (term24 A B C s g f)) = (term59 A B C t s g f).
Proof. exact (TRANS (@lem4393302 A B C t s g f) (@lem4393384 A B C t s g f)). Qed.
Lemma lem4393390 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term60 A B f s t) = (term60 A B f s t).
Proof. exact (eq_refl (term60 A B f s t)). Qed.
Lemma lem4393391 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term61 A B C t s g f) = (term62 A B C t s g f).
Proof. exact (MK_COMB (@lem4393390 A B f s t) (@lem4393389 A B C t s g f)). Qed.
Lemma lem4393394 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term63 A B C s g f) = (term64 A B C s g f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4393391 A B C t s g f)). Qed.
Lemma lem4393395 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4393396 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term65 A B C s g f) = (term66 A B C s g f).
Proof. exact (MK_COMB (@lem4393395 B) (@lem4393394 A B C s g f)). Qed.
Lemma lem4393401 {A B C : Type'} (g : B -> C) (f : A -> B) : (term67 A B C g f) = (term68 A B C g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4393396 A B C s g f)). Qed.
Lemma lem4393402 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4393403 {A B C : Type'} (g : B -> C) (f : A -> B) : (term69 A B C g f) = (term70 A B C g f).
Proof. exact (MK_COMB (@lem4393402 A) (@lem4393401 A B C g f)). Qed.
Lemma lem4393408 {A B C : Type'} (f : A -> B) : (term71 A B C f) = (term72 A B C f).
Proof. exact (fun_ext (fun g : B -> C => @lem4393403 A B C g f)). Qed.
Lemma lem4393409 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem4393410 {A B C : Type'} (f : A -> B) : (term73 A B C f) = (term74 A B C f).
Proof. exact (MK_COMB (@lem4393409 B C) (@lem4393408 A B C f)). Qed.
Lemma lem4393415 {A B C : Type'} : (term75 A B C) = (term76 A B C).
Proof. exact (fun_ext (fun f : A -> B => @lem4393410 A B C f)). Qed.
Lemma lem4393416 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4393417 {A B C : Type'} : (term77 A B C) = (term78 A B C).
Proof. exact (MK_COMB (@lem4393416 A B) (@lem4393415 A B C)). Qed.
Lemma lem4393422 {A B C : Type'} : (term78 A B C) = (term77 A B C).
Proof. exact (SYM (@lem4393417 A B C)). Qed.
Lemma lem4393442 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term79 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4393443 (p : Prop) (q : Prop) (p' : Prop) : term80 p q p'.
Proof. exact (fun q' : Prop => @lem4393442 p q p' q'). Qed.
Lemma lem4393444 (p : Prop) (q : Prop) : term81 p q.
Proof. exact (fun p' : Prop => @lem4393443 p q p'). Qed.
Lemma lem4393445 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : term82 A B C t s g f.
Proof. exact (@lem4393444 (term83 A B f s t) (term59 A B C t s g f)). Qed.
Lemma lem4393446 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term84 A B C t s g f p'.
Proof. exact (@lem4393445 A B C t s g f p'). Qed.
Lemma lem4393447 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : (term84 A B C t s g f p') = (term85 A B C t s g f p').
Proof. exact (eq_refl (term84 A B C t s g f p')). Qed.
Lemma lem4393448 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) : term85 A B C t s g f p'.
Proof. exact (EQ_MP (@lem4393447 A B C t s g f p') (@lem4393446 A B C t s g f p')). Qed.
Lemma lem4393449 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term86 A B C t s g f p' q'.
Proof. exact (@lem4393448 A B C t s g f p' q'). Qed.
Lemma lem4393450 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : (term86 A B C t s g f p' q') = (term87 A B C t s g f p' q').
Proof. exact (eq_refl (term86 A B C t s g f p' q')). Qed.
Lemma lem4393451 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (p' : Prop) (q' : Prop) : term87 A B C t s g f p' q'.
Proof. exact (EQ_MP (@lem4393450 A B C t s g f p' q') (@lem4393449 A B C t s g f p' q')). Qed.
Lemma lem4393453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem4393256 A s t) (@lem4393255 A s t)). Qed.
Lemma lem4393454 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term8 B s t).
Proof. exact (@lem4393453 B s t). Qed.
Lemma lem4393455 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term83 A B f s t) = (term88 A B f s t).
Proof. exact (@lem4393454 B (@IMAGE A B f s) t). Qed.
Lemma lem4393457 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term3 _87967 _87968 f s P) = (term4 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4393250 _87967 _87968 s P f) (@lem4393249 _87967 _87968 P f s)). Qed.
Lemma lem4393458 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term89 A B f s P) = (term90 A B s P f).
Proof. exact (@lem4393457 B A s P f). Qed.
Lemma lem4393459 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term91 A B f s t) = (term92 A B s t f).
Proof. exact (@lem4393458 A B s (term93 B t) f). Qed.
Lemma lem4393460 {B : Type'} (x : B) (t : B -> Prop) : (term94 B t x) = (@IN B x t).
Proof. exact (eq_refl (term94 B t x)). Qed.
Lemma lem4393461 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term95 A B x f s) = (term95 A B x f s).
Proof. exact (eq_refl (term95 A B x f s)). Qed.
Lemma lem4393462 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : B) (t : B -> Prop) : (term96 A B f s t x) = (term97 A B f s x t).
Proof. exact (MK_COMB (@lem4393461 A B x f s) (@lem4393460 B x t)). Qed.
Lemma lem4393463 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term98 A B f s t) = (term99 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem4393462 A B f s x t)). Qed.
Lemma lem4393464 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4393465 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term91 A B f s t) = (term88 A B f s t).
Proof. exact (MK_COMB (@lem4393464 B) (@lem4393463 A B f s t)). Qed.
Lemma lem4393466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4393467 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term100 A B f s t) = (term101 A B f s t).
Proof. exact (MK_COMB (@lem4393466) (@lem4393465 A B f s t)). Qed.
Lemma lem4393468 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term102 A B t f x) = (term103 A B f x t).
Proof. exact (eq_refl (term102 A B t f x)). Qed.
Lemma lem4393469 {A : Type'} (x : A) (s : A -> Prop) : (term104 A x s) = (term104 A x s).
Proof. exact (eq_refl (term104 A x s)). Qed.
Lemma lem4393470 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term105 A B s t f x) = (term106 A B s f x t).
Proof. exact (MK_COMB (@lem4393469 A x s) (@lem4393468 A B f x t)). Qed.
Lemma lem4393471 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term107 A B s t f) = (term108 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem4393470 A B s f x t)). Qed.
Lemma lem4393472 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4393473 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term92 A B s t f) = (term109 A B s f t).
Proof. exact (MK_COMB (@lem4393472 A) (@lem4393471 A B s f t)). Qed.
Lemma lem4393474 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term91 A B f s t) = (term92 A B s t f)) = ((term88 A B f s t) = (term109 A B s f t)).
Proof. exact (MK_COMB (@lem4393467 A B f s t) (@lem4393473 A B s f t)). Qed.
Lemma lem4393475 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term88 A B f s t) = (term109 A B s f t).
Proof. exact (EQ_MP (@lem4393474 A B s f t) (@lem4393459 A B s t f)). Qed.
Lemma lem4393503 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term83 A B f s t) = (term109 A B s f t).
Proof. exact (TRANS (@lem4393455 A B f s t) (@lem4393475 A B s f t)). Qed.
Lemma lem4393504 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (q' : Prop) : term110 A B C g s f t q'.
Proof. exact (@lem4393451 A B C t s g f (term109 A B s f t) q'). Qed.
Lemma lem4393505 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (q' : Prop) : term111 A B C g s f t q'.
Proof. exact (@lem4393504 A B C g s f t q' (@lem4393503 A B s f t)). Qed.
Lemma lem4393506 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : term109 A B s f t.
Proof. exact (h1). Qed.
Lemma lem4393507 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : term112 A B s f t x.
Proof. exact (@lem4393506 A B s f t h1 x). Qed.
Lemma lem4393508 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term112 A B s f t x) = (term106 A B s f x t).
Proof. exact (eq_refl (term112 A B s f t x)). Qed.
Lemma lem4393509 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : term106 A B s f x t.
Proof. exact (EQ_MP (@lem4393508 A B s f x t) (@lem4393507 A B x s f t h1)). Qed.
Lemma lem4393510 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4393511 {A B : Type'} (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : term103 A B f x t.
Proof. exact (@lem4393509 A B x s f t h1 (@lem4393510 A x s h2)). Qed.
Lemma lem4393512 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term103 A B f x t) = ((term103 A B f x t) = True).
Proof. exact (@lem7 (term103 A B f x t)). Qed.
Lemma lem4393513 {A B : Type'} (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : (term103 A B f x t) = True.
Proof. exact (EQ_MP (@lem4393512 A B f x t) (@lem4393511 A B f t x s h1 h2)). Qed.
Lemma lem4393526 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term113 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4393527 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term114 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4393526 _2963 g t e g' t' e'). Qed.
Lemma lem4393528 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term115 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4393527 _2963 g t e g' t'). Qed.
Lemma lem4393529 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term116 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4393528 _2963 g t e g'). Qed.
Lemma lem4393530 {C : Type'} (g : Prop) (t : C) (e : C) : term116 C g t e.
Proof. exact (@lem4393529 C g t e). Qed.
Lemma lem4393531 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : term117 A B C s t g f x.
Proof. exact (@lem4393530 C (@IN A x s) (term31 A B C t g f x) (@ARB C)). Qed.
Lemma lem4393532 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) : term118 A B C s t g f x g'.
Proof. exact (@lem4393531 A B C s t g f x g'). Qed.
Lemma lem4393533 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) : (term118 A B C s t g f x g') = (term119 A B C s t g f x g').
Proof. exact (eq_refl (term118 A B C s t g f x g')). Qed.
Lemma lem4393534 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) : term119 A B C s t g f x g'.
Proof. exact (EQ_MP (@lem4393533 A B C s t g f x g') (@lem4393532 A B C s t g f x g')). Qed.
Lemma lem4393535 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) : term120 A B C s t g f x g' t'.
Proof. exact (@lem4393534 A B C s t g f x g' t'). Qed.
Lemma lem4393536 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) : (term120 A B C s t g f x g' t') = (term121 A B C s t g f x g' t').
Proof. exact (eq_refl (term120 A B C s t g f x g' t')). Qed.
Lemma lem4393537 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) : term121 A B C s t g f x g' t'.
Proof. exact (EQ_MP (@lem4393536 A B C s t g f x g' t') (@lem4393535 A B C s t g f x g' t')). Qed.
Lemma lem4393538 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : term122 A B C s t g f x g' t' e'.
Proof. exact (@lem4393537 A B C s t g f x g' t' e'). Qed.
Lemma lem4393539 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : (term122 A B C s t g f x g' t' e') = (term123 A B C s t g f x g' t' e').
Proof. exact (eq_refl (term122 A B C s t g f x g' t' e')). Qed.
Lemma lem4393540 {A B C : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : term123 A B C s t g f x g' t' e'.
Proof. exact (EQ_MP (@lem4393539 A B C s t g f x g' t' e') (@lem4393538 A B C s t g f x g' t' e')). Qed.
Lemma lem4393541 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4393542 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (t' : C) (e' : C) : term124 A B C t g f x s t' e'.
Proof. exact (@lem4393540 A B C s t g f x (@IN A x s) t' e'). Qed.
Lemma lem4393543 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (t' : C) (e' : C) : term125 A B C t g f x s t' e'.
Proof. exact (@lem4393542 A B C t g f x s t' e' (@lem4393541 A x s)). Qed.
Lemma lem4393544 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4393545 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4393548 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term113 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4393549 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term114 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4393548 _2963 g t e g' t' e'). Qed.
Lemma lem4393550 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term115 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4393549 _2963 g t e g' t'). Qed.
Lemma lem4393551 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term116 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4393550 _2963 g t e g'). Qed.
Lemma lem4393552 {C : Type'} (g : Prop) (t : C) (e : C) : term116 C g t e.
Proof. exact (@lem4393551 C g t e). Qed.
Lemma lem4393553 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) : term126 A B C t g f x.
Proof. exact (@lem4393552 C (term103 A B f x t) (term50 A B C g f x) (@ARB C)). Qed.
Lemma lem4393554 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) : term127 A B C t g f x g'.
Proof. exact (@lem4393553 A B C t g f x g'). Qed.
Lemma lem4393555 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) : (term127 A B C t g f x g') = (term128 A B C t g f x g').
Proof. exact (eq_refl (term127 A B C t g f x g')). Qed.
Lemma lem4393556 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) : term128 A B C t g f x g'.
Proof. exact (EQ_MP (@lem4393555 A B C t g f x g') (@lem4393554 A B C t g f x g')). Qed.
Lemma lem4393557 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) : term129 A B C t g f x g' t'.
Proof. exact (@lem4393556 A B C t g f x g' t'). Qed.
Lemma lem4393558 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) : (term129 A B C t g f x g' t') = (term130 A B C t g f x g' t').
Proof. exact (eq_refl (term129 A B C t g f x g' t')). Qed.
Lemma lem4393559 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) : term130 A B C t g f x g' t'.
Proof. exact (EQ_MP (@lem4393558 A B C t g f x g' t') (@lem4393557 A B C t g f x g' t')). Qed.
Lemma lem4393560 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : term131 A B C t g f x g' t' e'.
Proof. exact (@lem4393559 A B C t g f x g' t' e'). Qed.
Lemma lem4393561 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : (term131 A B C t g f x g' t' e') = (term132 A B C t g f x g' t' e').
Proof. exact (eq_refl (term131 A B C t g f x g' t' e')). Qed.
Lemma lem4393562 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : term132 A B C t g f x g' t' e'.
Proof. exact (EQ_MP (@lem4393561 A B C t g f x g' t' e') (@lem4393560 A B C t g f x g' t' e')). Qed.
Lemma lem4393564 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : term133 A B s f x t.
Proof. exact (fun h0 : @IN A x s => @lem4393513 A B f t x s h1 h0). Qed.
Lemma lem4393565 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : term133 A B s f x t.
Proof. exact (@lem4393564 A B x s f t h1). Qed.
Lemma lem4393567 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4393545 A x s) (@lem4393544 A x s h1)). Qed.
Lemma lem4393568 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem4393567 A x s h1)). Qed.
Lemma lem4393569 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem4393568 A x s h1) (@lem0)). Qed.
Lemma lem4393570 {A B : Type'} (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : (term103 A B f x t) = True.
Proof. exact (@lem4393565 A B x s f t h1 (@lem4393569 A x s h2)). Qed.
Lemma lem4393571 {A B C : Type'} (t : B -> Prop) (g : B -> C) (f : A -> B) (x : A) (t' : C) (e' : C) : term134 A B C t g f x t' e'.
Proof. exact (@lem4393562 A B C t g f x True t' e'). Qed.
Lemma lem4393572 {A B C : Type'} (g : B -> C) (t' : C) (e' : C) (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : term135 A B C t g f x t' e'.
Proof. exact (@lem4393571 A B C t g f x t' e' (@lem4393570 A B f t x s h1 h2)). Qed.
Lemma lem4393578 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term50 A B C g f x) = (term50 A B C g f x).
Proof. exact (eq_refl (term50 A B C g f x)). Qed.
Lemma lem4393579 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : term136 A B C g f x.
Proof. exact (fun h0 : True => @lem4393578 A B C g f x). Qed.
Lemma lem4393580 {A B C : Type'} (g : B -> C) (e' : C) (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : term137 A B C t g f x e'.
Proof. exact (@lem4393572 A B C g (term50 A B C g f x) e' f t x s h1 h2). Qed.
Lemma lem4393581 {A B C : Type'} (g : B -> C) (e' : C) (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : term138 A B C t g f x e'.
Proof. exact (@lem4393580 A B C g e' f t x s h1 h2 (@lem4393579 A B C g f x)). Qed.
Lemma lem4393585 {C : Type'} : (@ARB C) = (@ARB C).
Proof. exact (eq_refl (@ARB C)). Qed.
Lemma lem4393586 {C : Type'} : term139 C.
Proof. exact (fun h0 : ~ True => @lem4393585 C). Qed.
Lemma lem4393587 {A B C : Type'} (g : B -> C) (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : term140 A B C t g f x.
Proof. exact (@lem4393581 A B C g (@ARB C) f t x s h1 h2). Qed.
Lemma lem4393588 {A B C : Type'} (g : B -> C) (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : (term31 A B C t g f x) = (term141 A B C g f x).
Proof. exact (@lem4393587 A B C g f t x s h1 h2 (@lem4393586 C)). Qed.
Lemma lem4393590 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4393591 {C : Type'} (t2 : C) (t1 : C) : (@COND C True t1 t2) = t1.
Proof. exact (@lem4393590 C t2 t1). Qed.
Lemma lem4393592 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term141 A B C g f x) = (term50 A B C g f x).
Proof. exact (@lem4393591 C (@ARB C) (term50 A B C g f x)). Qed.
Lemma lem4393593 {A B C : Type'} (g : B -> C) (f : A -> B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term109 A B s f t) (h2 : @IN A x s) : (term31 A B C t g f x) = (term50 A B C g f x).
Proof. exact (TRANS (@lem4393588 A B C g f t x s h1 h2) (@lem4393592 A B C g f x)). Qed.
Lemma lem4393594 {A B C : Type'} (g : B -> C) (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : term142 A B C s t g f x.
Proof. exact (fun h0 : @IN A x s => @lem4393593 A B C g f t x s h1 h0). Qed.
Lemma lem4393595 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) (e' : C) : term143 A B C t s g f x e'.
Proof. exact (@lem4393543 A B C t g f x s (term50 A B C g f x) e'). Qed.
Lemma lem4393596 {A B C : Type'} (g : B -> C) (x : A) (e' : C) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : term144 A B C t s g f x e'.
Proof. exact (@lem4393595 A B C t s g f x e' (@lem4393594 A B C g x s f t h1)). Qed.
Lemma lem4393600 {C : Type'} : (@ARB C) = (@ARB C).
Proof. exact (eq_refl (@ARB C)). Qed.
Lemma lem4393601 {A C : Type'} (x : A) (s : A -> Prop) : term145 A C x s.
Proof. exact (fun h0 : term146 A x s => @lem4393600 C). Qed.
Lemma lem4393602 {A B C : Type'} (g : B -> C) (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : term147 A B C t s g f x.
Proof. exact (@lem4393596 A B C g x (@ARB C) s f t h1). Qed.
Lemma lem4393603 {A B C : Type'} (g : B -> C) (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : (term43 A B C s t g f x) = (term56 A B C s g f x).
Proof. exact (@lem4393602 A B C g x s f t h1 (@lem4393601 A C x s)). Qed.
Lemma lem4393637 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4393638 {A B C : Type'} (g : B -> C) (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : (term45 A B C s t g f x) = (term148 A B C s g f x).
Proof. exact (MK_COMB (@lem4393637 C) (@lem4393603 A B C g x s f t h1)). Qed.
Lemma lem4393705 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term56 A B C s g f x) = (term56 A B C s g f x).
Proof. exact (eq_refl (term56 A B C s g f x)). Qed.
Lemma lem4393706 {A B C : Type'} (g : B -> C) (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : ((term43 A B C s t g f x) = (term56 A B C s g f x)) = ((term56 A B C s g f x) = (term56 A B C s g f x)).
Proof. exact (MK_COMB (@lem4393638 A B C g x s f t h1) (@lem4393705 A B C s g f x)). Qed.
Lemma lem4393708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4393709 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem4393708 C x). Qed.
Lemma lem4393710 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : ((term56 A B C s g f x) = (term56 A B C s g f x)) = True.
Proof. exact (@lem4393709 C (term56 A B C s g f x)). Qed.
Lemma lem4393711 {A B C : Type'} (g : B -> C) (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : ((term43 A B C s t g f x) = (term56 A B C s g f x)) = True.
Proof. exact (TRANS (@lem4393706 A B C g x s f t h1) (@lem4393710 A B C s g f x)). Qed.
Lemma lem4393712 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : (term58 A B C t s g f) = (term149 A).
Proof. exact (fun_ext (fun x : A => @lem4393711 A B C g x s f t h1)). Qed.
Lemma lem4393713 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4393714 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : (term59 A B C t s g f) = (term150 A).
Proof. exact (MK_COMB (@lem4393713 A) (@lem4393712 A B C g s f t h1)). Qed.
Lemma lem4393716 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393717 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (@lem4393716 A t). Qed.
Lemma lem4393718 {A : Type'} : (term150 A) = True.
Proof. exact (@lem4393717 A True). Qed.
Lemma lem4393719 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term109 A B s f t) : (term59 A B C t s g f) = True.
Proof. exact (TRANS (@lem4393714 A B C g s f t h1) (@lem4393718 A)). Qed.
Lemma lem4393720 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : term152 A B C t s g f.
Proof. exact (fun h0 : term109 A B s f t => @lem4393719 A B C g s f t h0). Qed.
Lemma lem4393721 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term153 A B C g s f t.
Proof. exact (@lem4393505 A B C g s f t True). Qed.
Lemma lem4393722 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term62 A B C t s g f) = (term154 A B s f t).
Proof. exact (@lem4393721 A B C g s f t (@lem4393720 A B C t s g f)). Qed.
Lemma lem4393724 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4393725 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term154 A B s f t) = True.
Proof. exact (@lem4393724 (term109 A B s f t)). Qed.
Lemma lem4393726 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term62 A B C t s g f) = True.
Proof. exact (TRANS (@lem4393722 A B C g s f t) (@lem4393725 A B s f t)). Qed.
Lemma lem4393727 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term64 A B C s g f) = (term155 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4393726 A B C t s g f)). Qed.
Lemma lem4393728 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4393729 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term66 A B C s g f) = (term156 B).
Proof. exact (MK_COMB (@lem4393728 B) (@lem4393727 A B C s g f)). Qed.
Lemma lem4393731 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393732 {B : Type'} (t : Prop) : (term157 B t) = t.
Proof. exact (@lem4393731 (B -> Prop) t). Qed.
Lemma lem4393733 {B : Type'} : (term156 B) = True.
Proof. exact (@lem4393732 B True). Qed.
Lemma lem4393734 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term66 A B C s g f) = True.
Proof. exact (TRANS (@lem4393729 A B C s g f) (@lem4393733 B)). Qed.
Lemma lem4393735 {A B C : Type'} (g : B -> C) (f : A -> B) : (term68 A B C g f) = (term155 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4393734 A B C s g f)). Qed.
Lemma lem4393736 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4393737 {A B C : Type'} (g : B -> C) (f : A -> B) : (term70 A B C g f) = (term156 A).
Proof. exact (MK_COMB (@lem4393736 A) (@lem4393735 A B C g f)). Qed.
Lemma lem4393739 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393740 {A : Type'} (t : Prop) : (term157 A t) = t.
Proof. exact (@lem4393739 (A -> Prop) t). Qed.
Lemma lem4393741 {A : Type'} : (term156 A) = True.
Proof. exact (@lem4393740 A True). Qed.
Lemma lem4393742 {A B C : Type'} (g : B -> C) (f : A -> B) : (term70 A B C g f) = True.
Proof. exact (TRANS (@lem4393737 A B C g f) (@lem4393741 A)). Qed.
Lemma lem4393743 {A B C : Type'} (f : A -> B) : (term72 A B C f) = (term158 B C).
Proof. exact (fun_ext (fun g : B -> C => @lem4393742 A B C g f)). Qed.
Lemma lem4393744 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem4393745 {A B C : Type'} (f : A -> B) : (term74 A B C f) = (term159 B C).
Proof. exact (MK_COMB (@lem4393744 B C) (@lem4393743 A B C f)). Qed.
Lemma lem4393747 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393748 {B C : Type'} (t : Prop) : (term160 B C t) = t.
Proof. exact (@lem4393747 (B -> C) t). Qed.
Lemma lem4393749 {B C : Type'} : (term159 B C) = True.
Proof. exact (@lem4393748 B C True). Qed.
Lemma lem4393750 {A B C : Type'} (f : A -> B) : (term74 A B C f) = True.
Proof. exact (TRANS (@lem4393745 A B C f) (@lem4393749 B C)). Qed.
Lemma lem4393751 {A B C : Type'} : (term76 A B C) = (term158 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4393750 A B C f)). Qed.
Lemma lem4393752 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4393753 {A B C : Type'} : (term78 A B C) = (term159 A B).
Proof. exact (MK_COMB (@lem4393752 A B) (@lem4393751 A B C)). Qed.
Lemma lem4393755 {A : Type'} (t : Prop) : (term151 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393756 {A B : Type'} (t : Prop) : (term160 A B t) = t.
Proof. exact (@lem4393755 (A -> B) t). Qed.
Lemma lem4393757 {A B : Type'} : (term159 A B) = True.
Proof. exact (@lem4393756 A B True). Qed.
Lemma lem4393758 {A B C : Type'} : (term78 A B C) = True.
Proof. exact (TRANS (@lem4393753 A B C) (@lem4393757 A B)). Qed.
Lemma lem4393759 {A B C : Type'} : True = (term78 A B C).
Proof. exact (SYM (@lem4393758 A B C)). Qed.
Lemma lem4393760 {A B C : Type'} : term78 A B C.
Proof. exact (EQ_MP (@lem4393759 A B C) (@lem0)). Qed.
Lemma lem4393761 {A B C : Type'} : term77 A B C.
Proof. exact (EQ_MP (@lem4393422 A B C) (@lem4393760 A B C)). Qed.
