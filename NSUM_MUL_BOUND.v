Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_MUL_BOUND_term_abbrevs.
Require Import LE_MULT_RCANCEL_spec.
Require Import NSUM_LE_spec.
Require Import NSUM_LMUL_spec.
Require Import NSUM_SING_spec.
Require Import NSUM_SUBSET_SIMPLE_spec.
Require Import SING_SUBSET_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem7017400 {_128971 : Type'} (h1 : term0 _128971) : term0 _128971.
Proof. exact (h1). Qed.
Lemma lem7017401 {_128971 : Type'} (u : _128971 -> Prop) (h1 : term0 _128971) : term1 _128971 u.
Proof. exact (@lem7017400 _128971 h1 u). Qed.
Lemma lem7017402 {_128971 : Type'} (u : _128971 -> Prop) : (term1 _128971 u) = (term2 _128971 u).
Proof. exact (eq_refl (term1 _128971 u)). Qed.
Lemma lem7017403 {_128971 : Type'} (u : _128971 -> Prop) (h1 : term0 _128971) : term2 _128971 u.
Proof. exact (EQ_MP (@lem7017402 _128971 u) (@lem7017401 _128971 u h1)). Qed.
Lemma lem7017404 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term0 _128971) : term3 _128971 u v.
Proof. exact (@lem7017403 _128971 u h1 v). Qed.
Lemma lem7017405 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : (term3 _128971 u v) = (term4 _128971 u v).
Proof. exact (eq_refl (term3 _128971 u v)). Qed.
Lemma lem7017406 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term0 _128971) : term4 _128971 u v.
Proof. exact (EQ_MP (@lem7017405 _128971 u v) (@lem7017404 _128971 u v h1)). Qed.
Lemma lem7017407 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term0 _128971) : term5 _128971 u v f.
Proof. exact (@lem7017406 _128971 u v h1 f). Qed.
Lemma lem7017408 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term5 _128971 u v f) = (term6 _128971 u v f).
Proof. exact (eq_refl (term5 _128971 u v f)). Qed.
Lemma lem7017409 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term0 _128971) : term6 _128971 u v f.
Proof. exact (EQ_MP (@lem7017408 _128971 u v f) (@lem7017407 _128971 u v f h1)). Qed.
Lemma lem7017410 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term7 _128971 u v) : term7 _128971 u v.
Proof. exact (h1). Qed.
Lemma lem7017411 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term0 _128971) (h2 : term7 _128971 u v) : term8 _128971 u v f.
Proof. exact (@lem7017409 _128971 u v f h1 (@lem7017410 _128971 u v h2)). Qed.
Lemma lem7017412 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term7 _128971 u v) : term9 _128971 u v f.
Proof. exact (fun h0 : term0 _128971 => @lem7017411 _128971 f u v h0 h1). Qed.
Lemma lem7017413 {_128971 : Type'} (h1 : term0 _128971) : term0 _128971.
Proof. exact (h1). Qed.
Lemma lem7017414 {_128971 : Type'} (f : _128971 -> nat) (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term0 _128971) (h2 : term7 _128971 u v) : term8 _128971 u v f.
Proof. exact (@lem7017412 _128971 f u v h2 (@lem7017413 _128971 h1)). Qed.
Lemma lem7017415 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) (h1 : term0 _128971) : term6 _128971 u v f.
Proof. exact (fun h0 : term7 _128971 u v => @lem7017414 _128971 f u v h1 h0). Qed.
Lemma lem7017416 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (h1 : term0 _128971) : term4 _128971 u v.
Proof. exact (fun f : _128971 -> nat => @lem7017415 _128971 u v f h1). Qed.
Lemma lem7017417 {_128971 : Type'} (u : _128971 -> Prop) (h1 : term0 _128971) : term2 _128971 u.
Proof. exact (fun v : _128971 -> Prop => @lem7017416 _128971 u v h1). Qed.
Lemma lem7017418 {_128971 : Type'} (h1 : term0 _128971) : term0 _128971.
Proof. exact (fun u : _128971 -> Prop => @lem7017417 _128971 u h1). Qed.
Lemma lem7017419 {_128971 : Type'} : term10 _128971.
Proof. exact (fun h0 : term0 _128971 => @lem7017418 _128971 h0). Qed.
Lemma lem7017420 {_128971 : Type'} : term0 _128971.
Proof. exact (@lem7017419 _128971 (@lem7010399 _128971)). Qed.
Lemma lem7017421 {_128971 : Type'} (u : _128971 -> Prop) : term1 _128971 u.
Proof. exact (@lem7017420 _128971 u). Qed.
Lemma lem7017422 {_128971 : Type'} (u : _128971 -> Prop) : (term1 _128971 u) = (term2 _128971 u).
Proof. exact (eq_refl (term1 _128971 u)). Qed.
Lemma lem7017423 {_128971 : Type'} (u : _128971 -> Prop) : term2 _128971 u.
Proof. exact (EQ_MP (@lem7017422 _128971 u) (@lem7017421 _128971 u)). Qed.
Lemma lem7017424 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : term3 _128971 u v.
Proof. exact (@lem7017423 _128971 u v). Qed.
Lemma lem7017425 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : (term3 _128971 u v) = (term4 _128971 u v).
Proof. exact (eq_refl (term3 _128971 u v)). Qed.
Lemma lem7017426 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) : term4 _128971 u v.
Proof. exact (EQ_MP (@lem7017425 _128971 u v) (@lem7017424 _128971 u v)). Qed.
Lemma lem7017427 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term5 _128971 u v f.
Proof. exact (@lem7017426 _128971 u v f). Qed.
Lemma lem7017428 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : (term5 _128971 u v f) = (term6 _128971 u v f).
Proof. exact (eq_refl (term5 _128971 u v f)). Qed.
Lemma lem7017432 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) (h1 : (term11 _127448 x f) = (f x)) : (term11 _127448 x f) = (f x).
Proof. exact (h1). Qed.
Lemma lem7017433 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) (h1 : (term11 _127448 x f) = (f x)) : (f x) = (term11 _127448 x f).
Proof. exact (SYM (@lem7017432 _127448 f x h1)). Qed.
Lemma lem7017434 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (h1 : (f x) = (term11 _127448 x f)) : (f x) = (term11 _127448 x f).
Proof. exact (h1). Qed.
Lemma lem7017435 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) (h1 : (f x) = (term11 _127448 x f)) : (term11 _127448 x f) = (f x).
Proof. exact (SYM (@lem7017434 _127448 x f h1)). Qed.
Lemma lem7017436 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) : ((term11 _127448 x f) = (f x)) = ((f x) = (term11 _127448 x f)).
Proof. exact (prop_ext (fun h1 : (term11 _127448 x f) = (f x) => @lem7017433 _127448 f x h1) (fun h1 : (f x) = (term11 _127448 x f) => @lem7017435 _127448 x f h1)). Qed.
Lemma lem7017437 {_127448 : Type'} (f : _127448 -> nat) : (term12 _127448 f) = (term13 _127448 f).
Proof. exact (fun_ext (fun x : _127448 => @lem7017436 _127448 x f)). Qed.
Lemma lem7017438 {_127448 : Type'} : (@all _127448) = (@all _127448).
Proof. exact (eq_refl (@all _127448)). Qed.
Lemma lem7017439 {_127448 : Type'} (f : _127448 -> nat) : (term14 _127448 f) = (term15 _127448 f).
Proof. exact (MK_COMB (@lem7017438 _127448) (@lem7017437 _127448 f)). Qed.
Lemma lem7017440 {_127448 : Type'} : (term16 _127448) = (term17 _127448).
Proof. exact (fun_ext (fun f : _127448 -> nat => @lem7017439 _127448 f)). Qed.
Lemma lem7017441 {_127448 : Type'} : (@all (_127448 -> nat)) = (@all (_127448 -> nat)).
Proof. exact (eq_refl (@all (_127448 -> nat))). Qed.
Lemma lem7017442 {_127448 : Type'} : (term18 _127448) = (term19 _127448).
Proof. exact (MK_COMB (@lem7017441 _127448) (@lem7017440 _127448)). Qed.
Lemma lem7017443 {_127448 : Type'} : term19 _127448.
Proof. exact (EQ_MP (@lem7017442 _127448) (@lem6960691 _127448)). Qed.
Lemma lem7017444 {_127448 : Type'} (f : _127448 -> nat) : term20 _127448 f.
Proof. exact (@lem7017443 _127448 f). Qed.
Lemma lem7017445 {_127448 : Type'} (f : _127448 -> nat) : (term20 _127448 f) = (term15 _127448 f).
Proof. exact (eq_refl (term20 _127448 f)). Qed.
Lemma lem7017446 {_127448 : Type'} (f : _127448 -> nat) : term15 _127448 f.
Proof. exact (EQ_MP (@lem7017445 _127448 f) (@lem7017444 _127448 f)). Qed.
Lemma lem7017447 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : term21 _127448 f x.
Proof. exact (@lem7017446 _127448 f x). Qed.
Lemma lem7017448 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) : (term21 _127448 f x) = ((f x) = (term11 _127448 x f)).
Proof. exact (eq_refl (term21 _127448 f x)). Qed.
Lemma lem7017450 {_127006 : Type'} (h1 : term22 _127006) : term22 _127006.
Proof. exact (h1). Qed.
Lemma lem7017451 {_127006 : Type'} (f : _127006 -> nat) (h1 : term22 _127006) : term23 _127006 f.
Proof. exact (@lem7017450 _127006 h1 f). Qed.
Lemma lem7017452 {_127006 : Type'} (f : _127006 -> nat) : (term23 _127006 f) = (term24 _127006 f).
Proof. exact (eq_refl (term23 _127006 f)). Qed.
Lemma lem7017453 {_127006 : Type'} (f : _127006 -> nat) (h1 : term22 _127006) : term24 _127006 f.
Proof. exact (EQ_MP (@lem7017452 _127006 f) (@lem7017451 _127006 f h1)). Qed.
Lemma lem7017454 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term22 _127006) : term25 _127006 f g.
Proof. exact (@lem7017453 _127006 f h1 g). Qed.
Lemma lem7017455 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term25 _127006 f g) = (term26 _127006 f g).
Proof. exact (eq_refl (term25 _127006 f g)). Qed.
Lemma lem7017456 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term22 _127006) : term26 _127006 f g.
Proof. exact (EQ_MP (@lem7017455 _127006 f g) (@lem7017454 _127006 f g h1)). Qed.
Lemma lem7017457 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (s : _127006 -> Prop) (h1 : term22 _127006) : term27 _127006 f g s.
Proof. exact (@lem7017456 _127006 f g h1 s). Qed.
Lemma lem7017458 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term27 _127006 f g s) = (term28 _127006 f s g).
Proof. exact (eq_refl (term27 _127006 f g s)). Qed.
Lemma lem7017459 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) (h1 : term22 _127006) : term28 _127006 f s g.
Proof. exact (EQ_MP (@lem7017458 _127006 f s g) (@lem7017457 _127006 f g s h1)). Qed.
Lemma lem7017460 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term29 _127006 s f g) : term29 _127006 s f g.
Proof. exact (h1). Qed.
Lemma lem7017461 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term22 _127006) (h2 : term29 _127006 s f g) : term30 _127006 f s g.
Proof. exact (@lem7017459 _127006 f s g h1 (@lem7017460 _127006 s f g h2)). Qed.
Lemma lem7017462 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term29 _127006 s f g) : term31 _127006 f s g.
Proof. exact (fun h0 : term22 _127006 => @lem7017461 _127006 s f g h0 h1). Qed.
Lemma lem7017463 {_127006 : Type'} (h1 : term22 _127006) : term22 _127006.
Proof. exact (h1). Qed.
Lemma lem7017464 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term22 _127006) (h2 : term29 _127006 s f g) : term30 _127006 f s g.
Proof. exact (@lem7017462 _127006 s f g h2 (@lem7017463 _127006 h1)). Qed.
Lemma lem7017465 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) (h1 : term22 _127006) : term28 _127006 f s g.
Proof. exact (fun h0 : term29 _127006 s f g => @lem7017464 _127006 s f g h1 h0). Qed.
Lemma lem7017466 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (h1 : term22 _127006) : term32 _127006 f s.
Proof. exact (fun g : _127006 -> nat => @lem7017465 _127006 f s g h1). Qed.
Lemma lem7017467 {_127006 : Type'} (f : _127006 -> nat) (h1 : term22 _127006) : term33 _127006 f.
Proof. exact (fun s : _127006 -> Prop => @lem7017466 _127006 f s h1). Qed.
Lemma lem7017468 {_127006 : Type'} (h1 : term22 _127006) : term34 _127006.
Proof. exact (fun f : _127006 -> nat => @lem7017467 _127006 f h1). Qed.
Lemma lem7017469 {_127006 : Type'} : term35 _127006.
Proof. exact (fun h0 : term22 _127006 => @lem7017468 _127006 h0). Qed.
Lemma lem7017470 {_127006 : Type'} : term34 _127006.
Proof. exact (@lem7017469 _127006 (@lem6933015 _127006)). Qed.
Lemma lem7017471 {_127006 : Type'} (f : _127006 -> nat) : term36 _127006 f.
Proof. exact (@lem7017470 _127006 f). Qed.
Lemma lem7017472 {_127006 : Type'} (f : _127006 -> nat) : (term36 _127006 f) = (term33 _127006 f).
Proof. exact (eq_refl (term36 _127006 f)). Qed.
Lemma lem7017473 {_127006 : Type'} (f : _127006 -> nat) : term33 _127006 f.
Proof. exact (EQ_MP (@lem7017472 _127006 f) (@lem7017471 _127006 f)). Qed.
Lemma lem7017474 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) : term37 _127006 f s.
Proof. exact (@lem7017473 _127006 f s). Qed.
Lemma lem7017475 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) : (term37 _127006 f s) = (term32 _127006 f s).
Proof. exact (eq_refl (term37 _127006 f s)). Qed.
Lemma lem7017476 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) : term32 _127006 f s.
Proof. exact (EQ_MP (@lem7017475 _127006 f s) (@lem7017474 _127006 f s)). Qed.
Lemma lem7017477 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term38 _127006 f s g.
Proof. exact (@lem7017476 _127006 f s g). Qed.
Lemma lem7017478 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term38 _127006 f s g) = (term28 _127006 f s g).
Proof. exact (eq_refl (term38 _127006 f s g)). Qed.
Lemma lem7017483 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) (h1 : (term39 A s c f) = (term40 A c s f)) : (term39 A s c f) = (term40 A c s f).
Proof. exact (h1). Qed.
Lemma lem7017484 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) (h1 : (term39 A s c f) = (term40 A c s f)) : (term40 A c s f) = (term39 A s c f).
Proof. exact (SYM (@lem7017483 A c s f h1)). Qed.
Lemma lem7017485 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) (h1 : (term40 A c s f) = (term39 A s c f)) : (term40 A c s f) = (term39 A s c f).
Proof. exact (h1). Qed.
Lemma lem7017486 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) (h1 : (term40 A c s f) = (term39 A s c f)) : (term39 A s c f) = (term40 A c s f).
Proof. exact (SYM (@lem7017485 A s c f h1)). Qed.
Lemma lem7017487 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : ((term39 A s c f) = (term40 A c s f)) = ((term40 A c s f) = (term39 A s c f)).
Proof. exact (prop_ext (fun h1 : (term39 A s c f) = (term40 A c s f) => @lem7017484 A c s f h1) (fun h1 : (term40 A c s f) = (term39 A s c f) => @lem7017486 A s c f h1)). Qed.
Lemma lem7017488 {A : Type'} (c : nat) (f : A -> nat) : (term41 A c f) = (term42 A c f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7017487 A s c f)). Qed.
Lemma lem7017489 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7017490 {A : Type'} (c : nat) (f : A -> nat) : (term43 A c f) = (term44 A c f).
Proof. exact (MK_COMB (@lem7017489 A) (@lem7017488 A c f)). Qed.
Lemma lem7017491 {A : Type'} (f : A -> nat) : (term45 A f) = (term46 A f).
Proof. exact (fun_ext (fun c : nat => @lem7017490 A c f)). Qed.
Lemma lem7017492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7017493 {A : Type'} (f : A -> nat) : (term47 A f) = (term48 A f).
Proof. exact (MK_COMB (@lem7017492) (@lem7017491 A f)). Qed.
Lemma lem7017494 {A : Type'} : (term49 A) = (term50 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7017493 A f)). Qed.
Lemma lem7017495 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7017496 {A : Type'} : (term51 A) = (term52 A).
Proof. exact (MK_COMB (@lem7017495 A) (@lem7017494 A)). Qed.
Lemma lem7017497 {A : Type'} : term52 A.
Proof. exact (EQ_MP (@lem7017496 A) (@lem6932066 A)). Qed.
Lemma lem7017498 {A : Type'} (f : A -> nat) : term53 A f.
Proof. exact (@lem7017497 A f). Qed.
Lemma lem7017499 {A : Type'} (f : A -> nat) : (term53 A f) = (term48 A f).
Proof. exact (eq_refl (term53 A f)). Qed.
Lemma lem7017500 {A : Type'} (f : A -> nat) : term48 A f.
Proof. exact (EQ_MP (@lem7017499 A f) (@lem7017498 A f)). Qed.
Lemma lem7017501 {A : Type'} (f : A -> nat) (c : nat) : term54 A f c.
Proof. exact (@lem7017500 A f c). Qed.
Lemma lem7017502 {A : Type'} (c : nat) (f : A -> nat) : (term54 A f c) = (term44 A c f).
Proof. exact (eq_refl (term54 A f c)). Qed.
Lemma lem7017503 {A : Type'} (c : nat) (f : A -> nat) : term44 A c f.
Proof. exact (EQ_MP (@lem7017502 A c f) (@lem7017501 A f c)). Qed.
Lemma lem7017504 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) : term55 A c f s.
Proof. exact (@lem7017503 A c f s). Qed.
Lemma lem7017505 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term55 A c f s) = ((term40 A c s f) = (term39 A s c f)).
Proof. exact (eq_refl (term55 A c f s)). Qed.
Lemma lem7017507 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7017509 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term40 A c s f) = (term39 A s c f).
Proof. exact (EQ_MP (@lem7017505 A s c f) (@lem7017504 A c f s)). Qed.
Lemma lem7017510 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term40 A c s f) = (term39 A s c f).
Proof. exact (@lem7017509 A s c f). Qed.
Lemma lem7017511 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) : (term56 A a s b) = (term57 A s a b).
Proof. exact (@lem7017510 A s (@nsum A s a) b). Qed.
Lemma lem7017512 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) : (term58 A s a b) = (term58 A s a b).
Proof. exact (eq_refl (term58 A s a b)). Qed.
Lemma lem7017513 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) : (term59 A a s b) = (term60 A s a b).
Proof. exact (MK_COMB (@lem7017512 A s a b) (@lem7017511 A s a b)). Qed.
Lemma lem7017514 {A : Type'} (a : A -> nat) (s : A -> Prop) (b : A -> nat) : (term60 A s a b) = (term59 A a s b).
Proof. exact (SYM (@lem7017513 A s a b)). Qed.
Lemma lem7017516 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term28 _127006 f s g.
Proof. exact (EQ_MP (@lem7017478 _127006 f s g) (@lem7017477 _127006 f s g)). Qed.
Lemma lem7017517 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term28 A f s g.
Proof. exact (@lem7017516 A f s g). Qed.
Lemma lem7017518 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) : term61 A s a b.
Proof. exact (@lem7017517 A (term62 A a b) s (term63 A s a b)). Qed.
Lemma lem7017519 (m : nat) : term64 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem7017520 (m : nat) : (term64 m) = (term65 m).
Proof. exact (eq_refl (term64 m)). Qed.
Lemma lem7017521 (m : nat) : term65 m.
Proof. exact (EQ_MP (@lem7017520 m) (@lem7017519 m)). Qed.
Lemma lem7017522 (m : nat) (n : nat) : term66 m n.
Proof. exact (@lem7017521 m n). Qed.
Lemma lem7017523 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (eq_refl (term66 m n)). Qed.
Lemma lem7017524 (m : nat) (n : nat) : term67 m n.
Proof. exact (EQ_MP (@lem7017523 m n) (@lem7017522 m n)). Qed.
Lemma lem7017525 (m : nat) (n : nat) (p : nat) : term68 m n p.
Proof. exact (@lem7017524 m n p). Qed.
Lemma lem7017526 (m : nat) (n : nat) (p : nat) : (term68 m n p) = ((term69 m n p) = (term70 m n p)).
Proof. exact (eq_refl (term68 m n p)). Qed.
Lemma lem7017528 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7017533 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7017528 A s) (@lem7017507 A s h1)). Qed.
Lemma lem7017534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7017535 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term71 A s) = (and True).
Proof. exact (MK_COMB (@lem7017534) (@lem7017533 A s h1)). Qed.
Lemma lem7017543 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7017544 {A : Type'} (f : A -> nat) (y : A) : (term73 A f y) = (f y).
Proof. exact (@lem7017543 A nat f y). Qed.
Lemma lem7017545 {A : Type'} (a : A -> nat) (b : A -> nat) (x : A) : (term74 A a b x) = (term75 A a b x).
Proof. exact (@lem7017544 A (term62 A a b) x). Qed.
Lemma lem7017546 {A : Type'} (a : A -> nat) (b : A -> nat) (i : A) : (term75 A a b i) = (term76 A a b i).
Proof. exact (eq_refl (term75 A a b i)). Qed.
Lemma lem7017547 {A : Type'} (a : A -> nat) (b : A -> nat) : (term77 A a b) = (term62 A a b).
Proof. exact (fun_ext (fun i : A => @lem7017546 A a b i)). Qed.
Lemma lem7017548 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7017549 {A : Type'} (a : A -> nat) (b : A -> nat) (x : A) : (term74 A a b x) = (term75 A a b x).
Proof. exact (MK_COMB (@lem7017547 A a b) (@lem7017548 A x)). Qed.
Lemma lem7017550 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7017551 {A : Type'} (a : A -> nat) (b : A -> nat) (x : A) : (term78 A a b x) = (term79 A a b x).
Proof. exact (MK_COMB (@lem7017550) (@lem7017549 A a b x)). Qed.
Lemma lem7017552 {A : Type'} (a : A -> nat) (b : A -> nat) (x : A) : (term75 A a b x) = (term76 A a b x).
Proof. exact (eq_refl (term75 A a b x)). Qed.
Lemma lem7017553 {A : Type'} (a : A -> nat) (b : A -> nat) (x : A) : ((term74 A a b x) = (term75 A a b x)) = ((term75 A a b x) = (term76 A a b x)).
Proof. exact (MK_COMB (@lem7017551 A a b x) (@lem7017552 A a b x)). Qed.
Lemma lem7017554 {A : Type'} (a : A -> nat) (b : A -> nat) (x : A) : (term75 A a b x) = (term76 A a b x).
Proof. exact (EQ_MP (@lem7017553 A a b x) (@lem7017545 A a b x)). Qed.
Lemma lem7017555 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7017556 {A : Type'} (a : A -> nat) (b : A -> nat) (x : A) : (term80 A a b x) = (term81 A a b x).
Proof. exact (MK_COMB (@lem7017555) (@lem7017554 A a b x)). Qed.
Lemma lem7017558 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7017559 {A : Type'} (f : A -> nat) (y : A) : (term73 A f y) = (f y).
Proof. exact (@lem7017558 A nat f y). Qed.
Lemma lem7017560 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term82 A s a b x) = (term83 A s a b x).
Proof. exact (@lem7017559 A (term63 A s a b) x). Qed.
Lemma lem7017561 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term83 A s a b x) = (term84 A s a b x).
Proof. exact (eq_refl (term83 A s a b x)). Qed.
Lemma lem7017562 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) : (term85 A s a b) = (term63 A s a b).
Proof. exact (fun_ext (fun x : A => @lem7017561 A s a b x)). Qed.
Lemma lem7017563 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7017564 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term82 A s a b x) = (term83 A s a b x).
Proof. exact (MK_COMB (@lem7017562 A s a b) (@lem7017563 A x)). Qed.
Lemma lem7017565 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7017566 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term86 A s a b x) = (term87 A s a b x).
Proof. exact (MK_COMB (@lem7017565) (@lem7017564 A s a b x)). Qed.
Lemma lem7017567 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term83 A s a b x) = (term84 A s a b x).
Proof. exact (eq_refl (term83 A s a b x)). Qed.
Lemma lem7017568 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : ((term82 A s a b x) = (term83 A s a b x)) = ((term83 A s a b x) = (term84 A s a b x)).
Proof. exact (MK_COMB (@lem7017566 A s a b x) (@lem7017567 A s a b x)). Qed.
Lemma lem7017569 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term83 A s a b x) = (term84 A s a b x).
Proof. exact (EQ_MP (@lem7017568 A s a b x) (@lem7017560 A s a b x)). Qed.
Lemma lem7017570 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term88 A s a b x) = (term89 A s a b x).
Proof. exact (MK_COMB (@lem7017556 A a b x) (@lem7017569 A s a b x)). Qed.
Lemma lem7017572 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term70 m n p).
Proof. exact (EQ_MP (@lem7017526 m n p) (@lem7017525 m n p)). Qed.
Lemma lem7017573 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term89 A s a b x) = (term90 A s a b x).
Proof. exact (@lem7017572 (a x) (@nsum A s a) (b x)). Qed.
Lemma lem7017578 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term88 A s a b x) = (term90 A s a b x).
Proof. exact (TRANS (@lem7017570 A s a b x) (@lem7017573 A s a b x)). Qed.
Lemma lem7017579 {A : Type'} (x : A) (s : A -> Prop) : (term91 A x s) = (term91 A x s).
Proof. exact (eq_refl (term91 A x s)). Qed.
Lemma lem7017580 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) (x : A) : (term92 A s a b x) = (term93 A s a b x).
Proof. exact (MK_COMB (@lem7017579 A x s) (@lem7017578 A s a b x)). Qed.
Lemma lem7017583 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) : (term94 A s a b) = (term95 A s a b).
Proof. exact (fun_ext (fun x : A => @lem7017580 A s a b x)). Qed.
Lemma lem7017584 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7017585 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) : (term96 A s a b) = (term97 A s a b).
Proof. exact (MK_COMB (@lem7017584 A) (@lem7017583 A s a b)). Qed.
Lemma lem7017590 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term98 A s a b) = (term99 A s a b).
Proof. exact (MK_COMB (@lem7017535 A s h1) (@lem7017585 A s a b)). Qed.
Lemma lem7017592 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7017593 {A : Type'} (s : A -> Prop) (a : A -> nat) (b : A -> nat) : (term99 A s a b) = (term97 A s a b).
Proof. exact (@lem7017592 (term97 A s a b)). Qed.
Lemma lem7017604 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term98 A s a b) = (term97 A s a b).
Proof. exact (TRANS (@lem7017590 A a b s h1) (@lem7017593 A s a b)). Qed.
Lemma lem7017605 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term97 A s a b) = (term98 A s a b).
Proof. exact (SYM (@lem7017604 A a b s h1)). Qed.
Lemma lem7017606 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (h1). Qed.
Lemma lem7017614 {_127448 : Type'} (x : _127448) (f : _127448 -> nat) : (f x) = (term11 _127448 x f).
Proof. exact (EQ_MP (@lem7017448 _127448 x f) (@lem7017447 _127448 f x)). Qed.
Lemma lem7017615 {A : Type'} (x : A) (f : A -> nat) : (f x) = (term11 A x f).
Proof. exact (@lem7017614 A x f). Qed.
Lemma lem7017616 {A : Type'} (i : A) (a : A -> nat) : (a i) = (term11 A i a).
Proof. exact (@lem7017615 A i a). Qed.
Lemma lem7017617 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7017618 {A : Type'} (i : A) (a : A -> nat) : (term100 A a i) = (term101 A i a).
Proof. exact (MK_COMB (@lem7017617) (@lem7017616 A i a)). Qed.
Lemma lem7017619 {A : Type'} (s : A -> Prop) (a : A -> nat) : (@nsum A s a) = (@nsum A s a).
Proof. exact (eq_refl (@nsum A s a)). Qed.
Lemma lem7017620 {A : Type'} (i : A) (s : A -> Prop) (a : A -> nat) : (term102 A i s a) = (term103 A i s a).
Proof. exact (MK_COMB (@lem7017618 A i a) (@lem7017619 A s a)). Qed.
Lemma lem7017621 {A : Type'} (i : A) (s : A -> Prop) (a : A -> nat) : (term103 A i s a) = (term102 A i s a).
Proof. exact (SYM (@lem7017620 A i s a)). Qed.
Lemma lem7017623 {_128971 : Type'} (u : _128971 -> Prop) (v : _128971 -> Prop) (f : _128971 -> nat) : term6 _128971 u v f.
Proof. exact (EQ_MP (@lem7017428 _128971 u v f) (@lem7017427 _128971 u v f)). Qed.
Lemma lem7017624 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term6 A u v f.
Proof. exact (@lem7017623 A u v f). Qed.
Lemma lem7017625 {A : Type'} (i : A) (s : A -> Prop) (a : A -> nat) : term104 A i s a.
Proof. exact (@lem7017624 A (@INSERT A i (@EMPTY A)) s a). Qed.
Lemma lem7017635 {_84443 : Type'} (s : _84443 -> Prop) : term105 _84443 s.
Proof. exact (@lem3221020 _84443 s). Qed.
Lemma lem7017636 {_84443 : Type'} (s : _84443 -> Prop) : (term105 _84443 s) = (term106 _84443 s).
Proof. exact (eq_refl (term105 _84443 s)). Qed.
Lemma lem7017637 {_84443 : Type'} (s : _84443 -> Prop) : term106 _84443 s.
Proof. exact (EQ_MP (@lem7017636 _84443 s) (@lem7017635 _84443 s)). Qed.
Lemma lem7017638 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : term107 _84443 s x.
Proof. exact (@lem7017637 _84443 s x). Qed.
Lemma lem7017639 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term107 _84443 s x) = ((term108 _84443 x s) = (@IN _84443 x s)).
Proof. exact (eq_refl (term107 _84443 s x)). Qed.
Lemma lem7017641 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7017643 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = ((@IN A i s) = True).
Proof. exact (@lem7 (@IN A i s)). Qed.
Lemma lem7017648 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7017641 A s) (@lem7017507 A s h1)). Qed.
Lemma lem7017649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7017650 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term71 A s) = (and True).
Proof. exact (MK_COMB (@lem7017649) (@lem7017648 A s h1)). Qed.
Lemma lem7017652 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term108 _84443 x s) = (@IN _84443 x s).
Proof. exact (EQ_MP (@lem7017639 _84443 x s) (@lem7017638 _84443 s x)). Qed.
Lemma lem7017653 {A : Type'} (x : A) (s : A -> Prop) : (term108 A x s) = (@IN A x s).
Proof. exact (@lem7017652 A x s). Qed.
Lemma lem7017654 {A : Type'} (i : A) (s : A -> Prop) : (term108 A i s) = (@IN A i s).
Proof. exact (@lem7017653 A i s). Qed.
Lemma lem7017656 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (@IN A i s) = True.
Proof. exact (EQ_MP (@lem7017643 A i s) (@lem7017606 A i s h1)). Qed.
Lemma lem7017657 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (term108 A i s) = True.
Proof. exact (TRANS (@lem7017654 A i s) (@lem7017656 A i s h1)). Qed.
Lemma lem7017658 {A : Type'} (i : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A i s) : (term109 A i s) = (True /\ True).
Proof. exact (MK_COMB (@lem7017650 A s h1) (@lem7017657 A i s h2)). Qed.
Lemma lem7017660 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7017661 : (True /\ True) = True.
Proof. exact (@lem7017660 True). Qed.
Lemma lem7017662 {A : Type'} (i : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A i s) : (term109 A i s) = True.
Proof. exact (TRANS (@lem7017658 A i s h1 h2) (@lem7017661)). Qed.
Lemma lem7017663 {A : Type'} (i : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A i s) : True = (term109 A i s).
Proof. exact (SYM (@lem7017662 A i s h1 h2)). Qed.
Lemma lem7017664 {A : Type'} (i : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A i s) : term109 A i s.
Proof. exact (EQ_MP (@lem7017663 A i s h1 h2) (@lem0)). Qed.
Lemma lem7017665 {A : Type'} (a : A -> nat) (i : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A i s) : term103 A i s a.
Proof. exact (@lem7017625 A i s a (@lem7017664 A i s h1 h2)). Qed.
Lemma lem7017667 {A : Type'} (a : A -> nat) (i : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A i s) : term102 A i s a.
Proof. exact (EQ_MP (@lem7017621 A i s a) (@lem7017665 A a i s h1 h2)). Qed.
Lemma lem7017668 {A : Type'} (a : A -> nat) (b : A -> nat) (i : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A i s) : term90 A s a b i.
Proof. exact (or_intro1 (@lem7017667 A a i s h1 h2) ((b i) = (NUMERAL 0))). Qed.
Lemma lem7017669 {A : Type'} (a : A -> nat) (b : A -> nat) (i : A) (s : A -> Prop) (h1 : @FINITE A s) : term93 A s a b i.
Proof. exact (fun h0 : @IN A i s => @lem7017668 A a b i s h1 h0). Qed.
Lemma lem7017674 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : term97 A s a b.
Proof. exact (fun i : A => @lem7017669 A a b i s h1). Qed.
Lemma lem7017675 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : term98 A s a b.
Proof. exact (EQ_MP (@lem7017605 A a b s h1) (@lem7017674 A a b s h1)). Qed.
Lemma lem7017676 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : term60 A s a b.
Proof. exact (@lem7017518 A s a b (@lem7017675 A a b s h1)). Qed.
Lemma lem7017677 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : term59 A a s b.
Proof. exact (EQ_MP (@lem7017514 A a s b) (@lem7017676 A a b s h1)). Qed.
Lemma lem7017678 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = (term59 A a s b).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7017677 A a b s h1) (fun h2 : term59 A a s b => @lem7017507 A s h1)). Qed.
Lemma lem7017679 {A : Type'} (a : A -> nat) (b : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : term59 A a s b.
Proof. exact (EQ_MP (@lem7017678 A a b s h1) (@lem7017507 A s h1)). Qed.
Lemma lem7017680 {A : Type'} (a : A -> nat) (s : A -> Prop) (b : A -> nat) : term110 A a s b.
Proof. exact (fun h0 : @FINITE A s => @lem7017679 A a b s h0). Qed.
Lemma lem7017685 {A : Type'} (a : A -> nat) (b : A -> nat) : term111 A a b.
Proof. exact (fun s : A -> Prop => @lem7017680 A a s b). Qed.
Lemma lem7017690 {A : Type'} (a : A -> nat) : term112 A a.
Proof. exact (fun b : A -> nat => @lem7017685 A a b). Qed.
Lemma lem7017695 {A : Type'} : term113 A.
Proof. exact (fun a : A -> nat => @lem7017690 A a). Qed.
