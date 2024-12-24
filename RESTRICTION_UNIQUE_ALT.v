Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_UNIQUE_ALT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSIONAL_spec.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Lemma lem4396274 {_83152 : Type'} : term0 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4396275 {_83152 : Type'} (p : _83152 -> Prop) : term1 _83152 p.
Proof. exact (@lem4396274 _83152 p). Qed.
Lemma lem4396276 {_83152 : Type'} (p : _83152 -> Prop) : (term1 _83152 p) = (term2 _83152 p).
Proof. exact (eq_refl (term1 _83152 p)). Qed.
Lemma lem4396277 {_83152 : Type'} (p : _83152 -> Prop) : term2 _83152 p.
Proof. exact (EQ_MP (@lem4396276 _83152 p) (@lem4396275 _83152 p)). Qed.
Lemma lem4396278 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term3 _83152 p x.
Proof. exact (@lem4396277 _83152 p x). Qed.
Lemma lem4396279 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = ((term4 _83152 p x) = (p x)).
Proof. exact (eq_refl (term3 _83152 p x)). Qed.
Lemma lem4396302 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4396303 {A B : Type'} (s : A -> Prop) : (term5 A B s) = ((@EXTENSIONAL A B s) = (term6 A B s)).
Proof. exact (eq_refl (term5 A B s)). Qed.
Lemma lem4396305 {A B : Type'} (s : A -> Prop) : term7 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4396306 {A B : Type'} (s : A -> Prop) : (term7 A B s) = (term8 A B s).
Proof. exact (eq_refl (term7 A B s)). Qed.
Lemma lem4396307 {A B : Type'} (s : A -> Prop) : term8 A B s.
Proof. exact (EQ_MP (@lem4396306 A B s) (@lem4396305 A B s)). Qed.
Lemma lem4396308 {A B : Type'} (s : A -> Prop) (f : A -> B) : term9 A B s f.
Proof. exact (@lem4396307 A B s f). Qed.
Lemma lem4396309 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term9 A B s f) = (term10 A B s f).
Proof. exact (eq_refl (term9 A B s f)). Qed.
Lemma lem4396310 {A B : Type'} (s : A -> Prop) (f : A -> B) : term10 A B s f.
Proof. exact (EQ_MP (@lem4396309 A B s f) (@lem4396308 A B s f)). Qed.
Lemma lem4396311 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term11 A B s f x.
Proof. exact (@lem4396310 A B s f x). Qed.
Lemma lem4396312 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term11 A B s f x) = ((@RESTRICTION A B s f x) = (term12 A B s f x)).
Proof. exact (eq_refl (term11 A B s f x)). Qed.
Lemma lem4396314 {A B : Type'} (f : A -> B) : term13 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4396315 {A B : Type'} (f : A -> B) : (term13 A B f) = (term14 A B f).
Proof. exact (eq_refl (term13 A B f)). Qed.
Lemma lem4396316 {A B : Type'} (f : A -> B) : term14 A B f.
Proof. exact (EQ_MP (@lem4396315 A B f) (@lem4396314 A B f)). Qed.
Lemma lem4396317 {A B : Type'} (f : A -> B) (g : A -> B) : term15 A B f g.
Proof. exact (@lem4396316 A B f g). Qed.
Lemma lem4396318 {A B : Type'} (f : A -> B) (g : A -> B) : (term15 A B f g) = ((f = g) = (term16 A B f g)).
Proof. exact (eq_refl (term15 A B f g)). Qed.
Lemma lem4396339 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term16 A B f g).
Proof. exact (EQ_MP (@lem4396318 A B f g) (@lem4396317 A B f g)). Qed.
Lemma lem4396340 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term16 A B f g).
Proof. exact (@lem4396339 A B f g). Qed.
Lemma lem4396341 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (f = (@RESTRICTION A B s g)) = (term17 A B f s g).
Proof. exact (@lem4396340 A B f (@RESTRICTION A B s g)). Qed.
Lemma lem4396351 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term12 A B s f x).
Proof. exact (EQ_MP (@lem4396312 A B s f x) (@lem4396311 A B s f x)). Qed.
Lemma lem4396352 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term12 A B s f x).
Proof. exact (@lem4396351 A B s f x). Qed.
Lemma lem4396353 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (@RESTRICTION A B s g x) = (term12 A B s g x).
Proof. exact (@lem4396352 A B s g x). Qed.
Lemma lem4396354 {A B : Type'} (f : A -> B) (x : A) : (term18 A B f x) = (term18 A B f x).
Proof. exact (eq_refl (term18 A B f x)). Qed.
Lemma lem4396355 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : ((f x) = (@RESTRICTION A B s g x)) = ((f x) = (term12 A B s g x)).
Proof. exact (MK_COMB (@lem4396354 A B f x) (@lem4396353 A B s g x)). Qed.
Lemma lem4396360 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term19 A B f s g) = (term20 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4396355 A B f s g x)). Qed.
Lemma lem4396361 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396362 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term17 A B f s g) = (term21 A B f s g).
Proof. exact (MK_COMB (@lem4396361 A) (@lem4396360 A B f s g)). Qed.
Lemma lem4396367 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (f = (@RESTRICTION A B s g)) = (term21 A B f s g).
Proof. exact (TRANS (@lem4396341 A B f s g) (@lem4396362 A B f s g)). Qed.
Lemma lem4396368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4396369 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term22 A B f s g) = (term23 A B f s g).
Proof. exact (MK_COMB (@lem4396368) (@lem4396367 A B f s g)). Qed.
Lemma lem4396373 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (EQ_MP (@lem4396303 A B s) (@lem4396302 A B s)). Qed.
Lemma lem4396374 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (@lem4396373 A B s). Qed.
Lemma lem4396389 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4396390 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@EXTENSIONAL A B s f) = (term24 A B s f).
Proof. exact (MK_COMB (@lem4396374 A B s) (@lem4396389 A B f)). Qed.
Lemma lem4396392 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term4 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4396279 _83152 p x) (@lem4396278 _83152 p x)). Qed.
Lemma lem4396393 {A B : Type'} (p : type572 A B) (x : A -> B) : (term25 A B p x) = (p x).
Proof. exact (@lem4396392 (A -> B) p x). Qed.
Lemma lem4396394 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term26 A B s f) = (term27 A B s f).
Proof. exact (@lem4396393 A B (term28 A B s) f). Qed.
Lemma lem4396395 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term27 A B s f) = (term29 A B s f).
Proof. exact (eq_refl (term27 A B s f)). Qed.
Lemma lem4396396 {A B : Type'} (GEN_PVAR_139 : A -> B) : (@SETSPEC (A -> B) GEN_PVAR_139) = (@SETSPEC (A -> B) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (A -> B) GEN_PVAR_139)). Qed.
Lemma lem4396397 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) (f : A -> B) : (term30 A B GEN_PVAR_139 s f) = (term31 A B GEN_PVAR_139 s f).
Proof. exact (MK_COMB (@lem4396396 A B GEN_PVAR_139) (@lem4396395 A B s f)). Qed.
Lemma lem4396398 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4396399 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) (f : A -> B) : (term32 A B GEN_PVAR_139 s f) = (term33 A B GEN_PVAR_139 s f).
Proof. exact (MK_COMB (@lem4396397 A B GEN_PVAR_139 s f) (@lem4396398 A B f)). Qed.
Lemma lem4396400 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) : (term34 A B GEN_PVAR_139 s) = (term35 A B GEN_PVAR_139 s).
Proof. exact (fun_ext (fun f : A -> B => @lem4396399 A B GEN_PVAR_139 s f)). Qed.
Lemma lem4396401 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4396402 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) : (term36 A B GEN_PVAR_139 s) = (term37 A B GEN_PVAR_139 s).
Proof. exact (MK_COMB (@lem4396401 A B) (@lem4396400 A B GEN_PVAR_139 s)). Qed.
Lemma lem4396403 {A B : Type'} (s : A -> Prop) : (term38 A B s) = (term39 A B s).
Proof. exact (fun_ext (fun GEN_PVAR_139 : A -> B => @lem4396402 A B GEN_PVAR_139 s)). Qed.
Lemma lem4396404 {A B : Type'} : (@GSPEC (A -> B)) = (@GSPEC (A -> B)).
Proof. exact (eq_refl (@GSPEC (A -> B))). Qed.
Lemma lem4396405 {A B : Type'} (s : A -> Prop) : (term40 A B s) = (term6 A B s).
Proof. exact (MK_COMB (@lem4396404 A B) (@lem4396403 A B s)). Qed.
Lemma lem4396406 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4396407 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term26 A B s f) = (term24 A B s f).
Proof. exact (MK_COMB (@lem4396405 A B s) (@lem4396406 A B f)). Qed.
Lemma lem4396408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4396409 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term41 A B s f) = (term42 A B s f).
Proof. exact (MK_COMB (@lem4396408) (@lem4396407 A B s f)). Qed.
Lemma lem4396410 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term27 A B s f) = (term29 A B s f).
Proof. exact (eq_refl (term27 A B s f)). Qed.
Lemma lem4396411 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term26 A B s f) = (term27 A B s f)) = ((term24 A B s f) = (term29 A B s f)).
Proof. exact (MK_COMB (@lem4396409 A B s f) (@lem4396410 A B s f)). Qed.
Lemma lem4396412 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term24 A B s f) = (term29 A B s f).
Proof. exact (EQ_MP (@lem4396411 A B s f) (@lem4396394 A B s f)). Qed.
Lemma lem4396423 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@EXTENSIONAL A B s f) = (term29 A B s f).
Proof. exact (TRANS (@lem4396390 A B s f) (@lem4396412 A B s f)). Qed.
Lemma lem4396424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396425 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term43 A B s f) = (term44 A B s f).
Proof. exact (MK_COMB (@lem4396424) (@lem4396423 A B s f)). Qed.
Lemma lem4396436 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term45 A B s f g) = (term45 A B s f g).
Proof. exact (eq_refl (term45 A B s f g)). Qed.
Lemma lem4396437 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term46 A B s f g) = (term47 A B s f g).
Proof. exact (MK_COMB (@lem4396425 A B s f) (@lem4396436 A B s f g)). Qed.
Lemma lem4396440 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((f = (@RESTRICTION A B s g)) = (term46 A B s f g)) = ((term21 A B f s g) = (term47 A B s f g)).
Proof. exact (MK_COMB (@lem4396369 A B f s g) (@lem4396437 A B s f g)). Qed.
Lemma lem4396445 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term48 A B s f) = (term49 A B s f).
Proof. exact (fun_ext (fun g : A -> B => @lem4396440 A B s f g)). Qed.
Lemma lem4396446 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4396447 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term50 A B s f) = (term51 A B s f).
Proof. exact (MK_COMB (@lem4396446 A B) (@lem4396445 A B s f)). Qed.
Lemma lem4396452 {A B : Type'} (s : A -> Prop) : (term52 A B s) = (term53 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4396447 A B s f)). Qed.
Lemma lem4396453 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4396454 {A B : Type'} (s : A -> Prop) : (term54 A B s) = (term55 A B s).
Proof. exact (MK_COMB (@lem4396453 A B) (@lem4396452 A B s)). Qed.
Lemma lem4396459 {A B : Type'} : (term56 A B) = (term57 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4396454 A B s)). Qed.
Lemma lem4396460 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4396461 {A B : Type'} : (term58 A B) = (term59 A B).
Proof. exact (MK_COMB (@lem4396460 A) (@lem4396459 A B)). Qed.
Lemma lem4396466 {A B : Type'} : (term59 A B) = (term58 A B).
Proof. exact (SYM (@lem4396461 A B)). Qed.
Lemma lem4396468 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4396469 {A B : Type'} : (term59 A B) = (term61 A B).
Proof. exact (@lem4396468 (term59 A B)). Qed.
Lemma lem4396470 {A B : Type'} : (term61 A B) = (term59 A B).
Proof. exact (SYM (@lem4396469 A B)). Qed.
Lemma lem4396471 {A B : Type'} (h1 : term62 A B) : term62 A B.
Proof. exact (h1). Qed.
Lemma lem4396474 {A B : Type'} (h1 : term61 A B) : term61 A B.
Proof. exact (h1). Qed.
Lemma lem4396475 {A B : Type'} : term63 A B.
Proof. exact (fun h0 : term61 A B => @lem4396474 A B h0). Qed.
Lemma lem4396476 {A B : Type'} (h1 : term63 A B) : term63 A B.
Proof. exact (h1). Qed.
Lemma lem4396477 {A B : Type'} (h1 : term61 A B) : term61 A B.
Proof. exact (h1). Qed.
Lemma lem4396478 {A B : Type'} (h1 : term61 A B) (h2 : term63 A B) : term61 A B.
Proof. exact (@lem4396476 A B h2 (@lem4396477 A B h1)). Qed.
Lemma lem4396479 {A B : Type'} (h1 : term61 A B) : term64 A B.
Proof. exact (fun h0 : term63 A B => @lem4396478 A B h1 h0). Qed.
Lemma lem4396480 {A B : Type'} (h1 : term63 A B) : term63 A B.
Proof. exact (h1). Qed.
Lemma lem4396481 {A B : Type'} (h1 : term61 A B) (h2 : term63 A B) : term61 A B.
Proof. exact (@lem4396479 A B h1 (@lem4396480 A B h2)). Qed.
Lemma lem4396482 {A B : Type'} (h1 : term63 A B) : term63 A B.
Proof. exact (fun h0 : term61 A B => @lem4396481 A B h0 h1). Qed.
Lemma lem4396483 {A B : Type'} : term65 A B.
Proof. exact (fun h0 : term63 A B => @lem4396482 A B h0). Qed.
Lemma lem4396486 {A B : Type'} : term63 A B.
Proof. exact (@lem4396483 A B (@lem4396475 A B)). Qed.
Lemma lem4396487 {A B : Type'} : term63 A B.
Proof. exact (@lem4396486 A B). Qed.
Lemma lem4396489 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4396490 {A B : Type'} : (term61 A B) = (term66 A B).
Proof. exact (@lem4396489 (term62 A B)). Qed.
Lemma lem4396492 (t : Prop) : (term67 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4396493 {A B : Type'} : (term66 A B) = (term59 A B).
Proof. exact (@lem4396492 (term59 A B)). Qed.
Lemma lem4396528 {A B : Type'} : (term61 A B) = (term59 A B).
Proof. exact (TRANS (@lem4396490 A B) (@lem4396493 A B)). Qed.
Lemma lem4396533 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term68 A B s f g x) = (term68 A B s f g x).
Proof. exact (eq_refl (term68 A B s f g x)). Qed.
Lemma lem4396534 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term69 A B s f g) = (term69 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4396533 A B s f g x)). Qed.
Lemma lem4396535 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396536 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term45 A B s f g) = (term45 A B s f g).
Proof. exact (MK_COMB (@lem4396535 A) (@lem4396534 A B s f g)). Qed.
Lemma lem4396543 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term70 A B s f x) = (term70 A B s f x).
Proof. exact (eq_refl (term70 A B s f x)). Qed.
Lemma lem4396544 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term71 A B s f) = (term71 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4396543 A B s f x)). Qed.
Lemma lem4396545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396546 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term29 A B s f) = (term29 A B s f).
Proof. exact (MK_COMB (@lem4396545 A) (@lem4396544 A B s f)). Qed.
Lemma lem4396547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396548 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term44 A B s f) = (term44 A B s f).
Proof. exact (MK_COMB (@lem4396547) (@lem4396546 A B s f)). Qed.
Lemma lem4396549 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term47 A B s f g) = (term47 A B s f g).
Proof. exact (MK_COMB (@lem4396548 A B s f) (@lem4396536 A B s f g)). Qed.
Lemma lem4396553 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem4396554 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4396555 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term72 A B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem4396554 B) (@lem4396553 A x s h1)). Qed.
Lemma lem4396556 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem4396557 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term73 A B s g x) = (term74 A B g x).
Proof. exact (MK_COMB (@lem4396555 A B x s h1) (@lem4396556 A B g x)). Qed.
Lemma lem4396558 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4396559 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term12 A B s g x) = (term75 A B g x).
Proof. exact (MK_COMB (@lem4396557 A B g x s h1) (@lem4396558 B)). Qed.
Lemma lem4396561 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4396562 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4396561 B t1 t2). Qed.
Lemma lem4396563 {A B : Type'} (g : A -> B) (x : A) : (term75 A B g x) = (@ARB B).
Proof. exact (@lem4396562 B (g x) (@ARB B)). Qed.
Lemma lem4396564 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term12 A B s g x) = (@ARB B).
Proof. exact (TRANS (@lem4396559 A B g x s h1) (@lem4396563 A B g x)). Qed.
Lemma lem4396565 {A B : Type'} (f : A -> B) (x : A) : (term18 A B f x) = (term18 A B f x).
Proof. exact (eq_refl (term18 A B f x)). Qed.
Lemma lem4396566 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((f x) = (term12 A B s g x)) = ((f x) = (@ARB B)).
Proof. exact (MK_COMB (@lem4396565 A B f x) (@lem4396564 A B g x s h1)). Qed.
Lemma lem4396569 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> B) (x : A) : term76 A B s g f x.
Proof. exact (fun h0 : (@IN A x s) = False => @lem4396566 A B g f x s h0). Qed.
Lemma lem4396571 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem4396572 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4396573 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term72 A B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem4396572 B) (@lem4396571 A x s h1)). Qed.
Lemma lem4396574 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem4396575 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term73 A B s g x) = (term77 A B g x).
Proof. exact (MK_COMB (@lem4396573 A B x s h1) (@lem4396574 A B g x)). Qed.
Lemma lem4396576 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4396577 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term12 A B s g x) = (term78 A B g x).
Proof. exact (MK_COMB (@lem4396575 A B g x s h1) (@lem4396576 B)). Qed.
Lemma lem4396579 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4396580 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4396579 B t2 t1). Qed.
Lemma lem4396581 {A B : Type'} (g : A -> B) (x : A) : (term78 A B g x) = (g x).
Proof. exact (@lem4396580 B (@ARB B) (g x)). Qed.
Lemma lem4396582 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term12 A B s g x) = (g x).
Proof. exact (TRANS (@lem4396577 A B g x s h1) (@lem4396581 A B g x)). Qed.
Lemma lem4396583 {A B : Type'} (f : A -> B) (x : A) : (term18 A B f x) = (term18 A B f x).
Proof. exact (eq_refl (term18 A B f x)). Qed.
Lemma lem4396584 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((f x) = (term12 A B s g x)) = ((f x) = (g x)).
Proof. exact (MK_COMB (@lem4396583 A B f x) (@lem4396582 A B g x s h1)). Qed.
Lemma lem4396587 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term79 A B s f g x.
Proof. exact (fun h0 : (@IN A x s) = True => @lem4396584 A B f g x s h0). Qed.
Lemma lem4396588 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term80 A B s f g x.
Proof. exact (conj (@lem4396569 A B s g f x) (@lem4396587 A B s f g x)). Qed.
Lemma lem4396590 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term81 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4396591 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : term82 A B g s f x.
Proof. exact (@lem4396590 ((f x) = (term12 A B s g x)) ((f x) = (g x)) (@IN A x s) ((f x) = (@ARB B))). Qed.
Lemma lem4396624 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : ((f x) = (term12 A B s g x)) = (term83 A B g s f x).
Proof. exact (@lem4396591 A B g s f x (@lem4396588 A B s f g x)). Qed.
Lemma lem4396625 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term20 A B f s g) = (term84 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem4396624 A B g s f x)). Qed.
Lemma lem4396626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396627 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term21 A B f s g) = (term85 A B g s f).
Proof. exact (MK_COMB (@lem4396626 A) (@lem4396625 A B g s f)). Qed.
Lemma lem4396628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4396629 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term23 A B f s g) = (term86 A B g s f).
Proof. exact (MK_COMB (@lem4396628) (@lem4396627 A B g s f)). Qed.
Lemma lem4396630 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term21 A B f s g) = (term47 A B s f g)) = ((term85 A B g s f) = (term47 A B s f g)).
Proof. exact (MK_COMB (@lem4396629 A B g s f) (@lem4396549 A B s f g)). Qed.
Lemma lem4396631 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term49 A B s f) = (term87 A B s f).
Proof. exact (fun_ext (fun g : A -> B => @lem4396630 A B s f g)). Qed.
Lemma lem4396632 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4396633 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term51 A B s f) = (term88 A B s f).
Proof. exact (MK_COMB (@lem4396632 A B) (@lem4396631 A B s f)). Qed.
Lemma lem4396634 {A B : Type'} (s : A -> Prop) : (term53 A B s) = (term89 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4396633 A B s f)). Qed.
Lemma lem4396635 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4396636 {A B : Type'} (s : A -> Prop) : (term55 A B s) = (term90 A B s).
Proof. exact (MK_COMB (@lem4396635 A B) (@lem4396634 A B s)). Qed.
Lemma lem4396637 {A B : Type'} : (term57 A B) = (term91 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4396636 A B s)). Qed.
Lemma lem4396638 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4396639 {A B : Type'} : (term59 A B) = (term92 A B).
Proof. exact (MK_COMB (@lem4396638 A) (@lem4396637 A B)). Qed.
Lemma lem4396690 {A B : Type'} : (term61 A B) = (term92 A B).
Proof. exact (TRANS (@lem4396528 A B) (@lem4396639 A B)). Qed.
Lemma lem4396691 {A B : Type'} : (term92 A B) = (term61 A B).
Proof. exact (SYM (@lem4396690 A B)). Qed.
Lemma lem4396693 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4396694 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term85 A B g s f) = (term47 A B s f g)) = (term93 A B s f g).
Proof. exact (@lem4396693 ((term85 A B g s f) = (term47 A B s f g))). Qed.
Lemma lem4396695 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term93 A B s f g) = ((term85 A B g s f) = (term47 A B s f g)).
Proof. exact (SYM (@lem4396694 A B s f g)). Qed.
Lemma lem4396696 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term94 A B s f g) : term94 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4396700 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (@IN A x s).
Proof. exact (@lem16933 (@IN A x s)). Qed.
Lemma lem4396701 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term96 A B f g x) = (term96 A B f g x).
Proof. exact (eq_refl (term96 A B f g x)). Qed.
Lemma lem4396703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396704 {A : Type'} (x : A) (s : A -> Prop) : (term97 A x s) = (term98 A x s).
Proof. exact (MK_COMB (@lem4396703) (@lem4396700 A x s)). Qed.
Lemma lem4396705 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term99 A B s f g x) = (term100 A B s f g x).
Proof. exact (MK_COMB (@lem4396704 A x s) (@lem4396701 A B f g x)). Qed.
Lemma lem4396706 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term101 A B s f g x) = (term99 A B s f g x).
Proof. exact (@lem17160 (term102 A x s) ((f x) = (g x))). Qed.
Lemma lem4396707 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term101 A B s f g x) = (term100 A B s f g x).
Proof. exact (TRANS (@lem4396706 A B s f g x) (@lem4396705 A B s f g x)). Qed.
Lemma lem4396719 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term103 A B s f x) = (term104 A B s f x).
Proof. exact (@lem17160 (@IN A x s) ((f x) = (@ARB B))). Qed.
Lemma lem4396723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4396724 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term105 A B s f g x) = (term106 A B s f g x).
Proof. exact (MK_COMB (@lem4396723) (@lem4396707 A B s f g x)). Qed.
Lemma lem4396725 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term107 A B g s f x) = (term108 A B g s f x).
Proof. exact (MK_COMB (@lem4396724 A B s f g x) (@lem4396719 A B s f x)). Qed.
Lemma lem4396726 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B g s f x) = (term107 A B g s f x).
Proof. exact (@lem17045 (term110 A B s f g x) (term111 A B s f x)). Qed.
Lemma lem4396727 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B g s f x) = (term108 A B g s f x).
Proof. exact (TRANS (@lem4396726 A B g s f x) (@lem4396725 A B g s f x)). Qed.
Lemma lem4396730 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term83 A B g s f x) = (term83 A B g s f x).
Proof. exact (eq_refl (term83 A B g s f x)). Qed.
Lemma lem4396731 {A : Type'} (P : A -> Prop) : (term112 A P) = (term113 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4396732 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term114 A B g s f) = (term115 A B g s f).
Proof. exact (@lem4396731 A (term84 A B g s f)). Qed.
Lemma lem4396733 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term116 A B g s f x) = (term83 A B g s f x).
Proof. exact (eq_refl (term116 A B g s f x)). Qed.
Lemma lem4396734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4396735 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term117 A B g s f x) = (term109 A B g s f x).
Proof. exact (MK_COMB (@lem4396734) (@lem4396733 A B g s f x)). Qed.
Lemma lem4396736 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term117 A B g s f x) = (term108 A B g s f x).
Proof. exact (TRANS (@lem4396735 A B g s f x) (@lem4396727 A B g s f x)). Qed.
Lemma lem4396737 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term118 A B g s f) = (term119 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem4396736 A B g s f x)). Qed.
Lemma lem4396738 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4396739 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term115 A B g s f) = (term120 A B g s f).
Proof. exact (MK_COMB (@lem4396738 A) (@lem4396737 A B g s f)). Qed.
Lemma lem4396740 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term114 A B g s f) = (term120 A B g s f).
Proof. exact (TRANS (@lem4396732 A B g s f) (@lem4396739 A B g s f)). Qed.
Lemma lem4396741 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term84 A B g s f) = (term84 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem4396730 A B g s f x)). Qed.
Lemma lem4396742 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396743 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term85 A B g s f) = (term85 A B g s f).
Proof. exact (MK_COMB (@lem4396742 A) (@lem4396741 A B g s f)). Qed.
Lemma lem4396747 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (@IN A x s).
Proof. exact (@lem16933 (@IN A x s)). Qed.
Lemma lem4396749 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (@ARB B)) = ((f x) = (@ARB B)).
Proof. exact (eq_refl ((f x) = (@ARB B))). Qed.
Lemma lem4396754 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term121 A B s f x) = (term104 A B s f x).
Proof. exact (@lem17362 (term102 A x s) ((f x) = (@ARB B))). Qed.
Lemma lem4396755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4396756 {A : Type'} (x : A) (s : A -> Prop) : (term122 A x s) = (term123 A x s).
Proof. exact (MK_COMB (@lem4396755) (@lem4396747 A x s)). Qed.
Lemma lem4396757 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term124 A B s f x) = (term111 A B s f x).
Proof. exact (MK_COMB (@lem4396756 A x s) (@lem4396749 A B f x)). Qed.
Lemma lem4396758 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term70 A B s f x) = (term124 A B s f x).
Proof. exact (@lem17265 (term102 A x s) ((f x) = (@ARB B))). Qed.
Lemma lem4396759 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term70 A B s f x) = (term111 A B s f x).
Proof. exact (TRANS (@lem4396758 A B s f x) (@lem4396757 A B s f x)). Qed.
Lemma lem4396760 {A : Type'} (P : A -> Prop) : (term112 A P) = (term113 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4396761 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term125 A B s f) = (term126 A B s f).
Proof. exact (@lem4396760 A (term71 A B s f)). Qed.
Lemma lem4396762 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term127 A B s f x) = (term70 A B s f x).
Proof. exact (eq_refl (term127 A B s f x)). Qed.
Lemma lem4396763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4396764 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term128 A B s f x) = (term121 A B s f x).
Proof. exact (MK_COMB (@lem4396763) (@lem4396762 A B s f x)). Qed.
Lemma lem4396765 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term128 A B s f x) = (term104 A B s f x).
Proof. exact (TRANS (@lem4396764 A B s f x) (@lem4396754 A B s f x)). Qed.
Lemma lem4396766 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term129 A B s f) = (term130 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4396765 A B s f x)). Qed.
Lemma lem4396767 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4396768 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term126 A B s f) = (term131 A B s f).
Proof. exact (MK_COMB (@lem4396767 A) (@lem4396766 A B s f)). Qed.
Lemma lem4396769 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term125 A B s f) = (term131 A B s f).
Proof. exact (TRANS (@lem4396761 A B s f) (@lem4396768 A B s f)). Qed.
Lemma lem4396770 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term71 A B s f) = (term132 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4396759 A B s f x)). Qed.
Lemma lem4396771 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396772 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term29 A B s f) = (term133 A B s f).
Proof. exact (MK_COMB (@lem4396771 A) (@lem4396770 A B s f)). Qed.
Lemma lem4396781 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term134 A B s f g x) = (term100 A B s f g x).
Proof. exact (@lem17362 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem4396786 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term68 A B s f g x) = (term110 A B s f g x).
Proof. exact (@lem17265 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem4396787 {A : Type'} (P : A -> Prop) : (term112 A P) = (term113 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4396788 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term135 A B s f g) = (term136 A B s f g).
Proof. exact (@lem4396787 A (term69 A B s f g)). Qed.
Lemma lem4396789 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term137 A B s f g x) = (term68 A B s f g x).
Proof. exact (eq_refl (term137 A B s f g x)). Qed.
Lemma lem4396790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4396791 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term138 A B s f g x) = (term134 A B s f g x).
Proof. exact (MK_COMB (@lem4396790) (@lem4396789 A B s f g x)). Qed.
Lemma lem4396792 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term138 A B s f g x) = (term100 A B s f g x).
Proof. exact (TRANS (@lem4396791 A B s f g x) (@lem4396781 A B s f g x)). Qed.
Lemma lem4396793 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term139 A B s f g) = (term140 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4396792 A B s f g x)). Qed.
Lemma lem4396794 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4396795 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term136 A B s f g) = (term141 A B s f g).
Proof. exact (MK_COMB (@lem4396794 A) (@lem4396793 A B s f g)). Qed.
Lemma lem4396796 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term135 A B s f g) = (term141 A B s f g).
Proof. exact (TRANS (@lem4396788 A B s f g) (@lem4396795 A B s f g)). Qed.
Lemma lem4396797 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term69 A B s f g) = (term142 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4396786 A B s f g x)). Qed.
Lemma lem4396798 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396799 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term45 A B s f g) = (term143 A B s f g).
Proof. exact (MK_COMB (@lem4396798 A) (@lem4396797 A B s f g)). Qed.
Lemma lem4396800 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4396801 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term144 A B s f) = (term145 A B s f).
Proof. exact (MK_COMB (@lem4396800) (@lem4396769 A B s f)). Qed.
Lemma lem4396802 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term146 A B s f g) = (term147 A B s f g).
Proof. exact (MK_COMB (@lem4396801 A B s f) (@lem4396796 A B s f g)). Qed.
Lemma lem4396803 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term148 A B s f g) = (term146 A B s f g).
Proof. exact (@lem17045 (term29 A B s f) (term45 A B s f g)). Qed.
Lemma lem4396804 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term148 A B s f g) = (term147 A B s f g).
Proof. exact (TRANS (@lem4396803 A B s f g) (@lem4396802 A B s f g)). Qed.
Lemma lem4396805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396806 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term44 A B s f) = (term149 A B s f).
Proof. exact (MK_COMB (@lem4396805) (@lem4396772 A B s f)). Qed.
Lemma lem4396807 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term47 A B s f g) = (term150 A B s f g).
Proof. exact (MK_COMB (@lem4396806 A B s f) (@lem4396799 A B s f g)). Qed.
Lemma lem4396808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396809 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term151 A B g s f) = (term152 A B g s f).
Proof. exact (MK_COMB (@lem4396808) (@lem4396740 A B g s f)). Qed.
Lemma lem4396810 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term153 A B s f g) = (term154 A B s f g).
Proof. exact (MK_COMB (@lem4396809 A B g s f) (@lem4396807 A B s f g)). Qed.
Lemma lem4396811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396812 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term155 A B g s f) = (term155 A B g s f).
Proof. exact (MK_COMB (@lem4396811) (@lem4396743 A B g s f)). Qed.
Lemma lem4396813 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term156 A B s f g) = (term157 A B s f g).
Proof. exact (MK_COMB (@lem4396812 A B g s f) (@lem4396804 A B s f g)). Qed.
Lemma lem4396814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4396815 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term158 A B s f g) = (term159 A B s f g).
Proof. exact (MK_COMB (@lem4396814) (@lem4396813 A B s f g)). Qed.
Lemma lem4396816 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term160 A B s f g) = (term161 A B s f g).
Proof. exact (MK_COMB (@lem4396815 A B s f g) (@lem4396810 A B s f g)). Qed.
Lemma lem4396817 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term94 A B s f g) = (term160 A B s f g).
Proof. exact (@lem17646 (term85 A B g s f) (term47 A B s f g)). Qed.
Lemma lem4396818 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term94 A B s f g) = (term161 A B s f g).
Proof. exact (TRANS (@lem4396817 A B s f g) (@lem4396816 A B s f g)). Qed.
Lemma lem4396820 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4396821 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (@lem4396820 A P Q). Qed.
Lemma lem4396822 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term164 A B g s f) = (term165 A B g s f).
Proof. exact (@lem4396821 A (term142 A B s f g) (term132 A B s f)). Qed.
Lemma lem4396823 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term166 A B s f g x) = (term110 A B s f g x).
Proof. exact (eq_refl (term166 A B s f g x)). Qed.
Lemma lem4396824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396825 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term167 A B s f g x) = (term168 A B s f g x).
Proof. exact (MK_COMB (@lem4396824) (@lem4396823 A B s f g x)). Qed.
Lemma lem4396826 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term169 A B s f x) = (term111 A B s f x).
Proof. exact (eq_refl (term169 A B s f x)). Qed.
Lemma lem4396827 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term170 A B g s f x) = (term83 A B g s f x).
Proof. exact (MK_COMB (@lem4396825 A B s f g x) (@lem4396826 A B s f x)). Qed.
Lemma lem4396828 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term171 A B g s f) = (term84 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem4396827 A B g s f x)). Qed.
Lemma lem4396829 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396830 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term164 A B g s f) = (term85 A B g s f).
Proof. exact (MK_COMB (@lem4396829 A) (@lem4396828 A B g s f)). Qed.
Lemma lem4396831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4396832 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term172 A B g s f) = (term86 A B g s f).
Proof. exact (MK_COMB (@lem4396831) (@lem4396830 A B g s f)). Qed.
Lemma lem4396833 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term166 A B s f g x) = (term110 A B s f g x).
Proof. exact (eq_refl (term166 A B s f g x)). Qed.
Lemma lem4396834 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term173 A B s f g) = (term142 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4396833 A B s f g x)). Qed.
Lemma lem4396835 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396836 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term174 A B s f g) = (term143 A B s f g).
Proof. exact (MK_COMB (@lem4396835 A) (@lem4396834 A B s f g)). Qed.
Lemma lem4396837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396838 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term175 A B s f g) = (term176 A B s f g).
Proof. exact (MK_COMB (@lem4396837) (@lem4396836 A B s f g)). Qed.
Lemma lem4396839 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term169 A B s f x) = (term111 A B s f x).
Proof. exact (eq_refl (term169 A B s f x)). Qed.
Lemma lem4396840 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term177 A B s f) = (term132 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4396839 A B s f x)). Qed.
Lemma lem4396841 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4396842 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term178 A B s f) = (term133 A B s f).
Proof. exact (MK_COMB (@lem4396841 A) (@lem4396840 A B s f)). Qed.
Lemma lem4396843 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term165 A B g s f) = (term179 A B g s f).
Proof. exact (MK_COMB (@lem4396838 A B s f g) (@lem4396842 A B s f)). Qed.
Lemma lem4396844 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : ((term164 A B g s f) = (term165 A B g s f)) = ((term85 A B g s f) = (term179 A B g s f)).
Proof. exact (MK_COMB (@lem4396832 A B g s f) (@lem4396843 A B g s f)). Qed.
Lemma lem4396845 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term85 A B g s f) = (term179 A B g s f).
Proof. exact (EQ_MP (@lem4396844 A B g s f) (@lem4396822 A B g s f)). Qed.
Lemma lem4396942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396943 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term155 A B g s f) = (term180 A B g s f).
Proof. exact (MK_COMB (@lem4396942) (@lem4396845 A B g s f)). Qed.
Lemma lem4397040 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term147 A B s f g) = (term147 A B s f g).
Proof. exact (eq_refl (term147 A B s f g)). Qed.
Lemma lem4397041 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term157 A B s f g) = (term181 A B s f g).
Proof. exact (MK_COMB (@lem4396943 A B g s f) (@lem4397040 A B s f g)). Qed.
Lemma lem4397042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397043 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term159 A B s f g) = (term182 A B s f g).
Proof. exact (MK_COMB (@lem4397042) (@lem4397041 A B s f g)). Qed.
Lemma lem4397045 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4397046 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (@lem4397045 A P Q). Qed.
Lemma lem4397047 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term185 A B g s f) = (term186 A B g s f).
Proof. exact (@lem4397046 A (term140 A B s f g) (term130 A B s f)). Qed.
Lemma lem4397048 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term187 A B s f g x) = (term100 A B s f g x).
Proof. exact (eq_refl (term187 A B s f g x)). Qed.
Lemma lem4397049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397050 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term188 A B s f g x) = (term106 A B s f g x).
Proof. exact (MK_COMB (@lem4397049) (@lem4397048 A B s f g x)). Qed.
Lemma lem4397051 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term189 A B s f x) = (term104 A B s f x).
Proof. exact (eq_refl (term189 A B s f x)). Qed.
Lemma lem4397052 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term190 A B g s f x) = (term108 A B g s f x).
Proof. exact (MK_COMB (@lem4397050 A B s f g x) (@lem4397051 A B s f x)). Qed.
Lemma lem4397053 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term191 A B g s f) = (term119 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem4397052 A B g s f x)). Qed.
Lemma lem4397054 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397055 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term185 A B g s f) = (term120 A B g s f).
Proof. exact (MK_COMB (@lem4397054 A) (@lem4397053 A B g s f)). Qed.
Lemma lem4397056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4397057 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term192 A B g s f) = (term193 A B g s f).
Proof. exact (MK_COMB (@lem4397056) (@lem4397055 A B g s f)). Qed.
Lemma lem4397058 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term187 A B s f g x) = (term100 A B s f g x).
Proof. exact (eq_refl (term187 A B s f g x)). Qed.
Lemma lem4397059 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term194 A B s f g) = (term140 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397058 A B s f g x)). Qed.
Lemma lem4397060 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397061 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term195 A B s f g) = (term141 A B s f g).
Proof. exact (MK_COMB (@lem4397060 A) (@lem4397059 A B s f g)). Qed.
Lemma lem4397062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397063 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term196 A B s f g) = (term197 A B s f g).
Proof. exact (MK_COMB (@lem4397062) (@lem4397061 A B s f g)). Qed.
Lemma lem4397064 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term189 A B s f x) = (term104 A B s f x).
Proof. exact (eq_refl (term189 A B s f x)). Qed.
Lemma lem4397065 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term198 A B s f) = (term130 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4397064 A B s f x)). Qed.
Lemma lem4397066 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397067 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term199 A B s f) = (term131 A B s f).
Proof. exact (MK_COMB (@lem4397066 A) (@lem4397065 A B s f)). Qed.
Lemma lem4397068 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term186 A B g s f) = (term200 A B g s f).
Proof. exact (MK_COMB (@lem4397063 A B s f g) (@lem4397067 A B s f)). Qed.
Lemma lem4397069 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : ((term185 A B g s f) = (term186 A B g s f)) = ((term120 A B g s f) = (term200 A B g s f)).
Proof. exact (MK_COMB (@lem4397057 A B g s f) (@lem4397068 A B g s f)). Qed.
Lemma lem4397070 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term120 A B g s f) = (term200 A B g s f).
Proof. exact (EQ_MP (@lem4397069 A B g s f) (@lem4397047 A B g s f)). Qed.
Lemma lem4397167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4397168 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term152 A B g s f) = (term201 A B g s f).
Proof. exact (MK_COMB (@lem4397167) (@lem4397070 A B g s f)). Qed.
Lemma lem4397265 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term150 A B s f g) = (term150 A B s f g).
Proof. exact (eq_refl (term150 A B s f g)). Qed.
Lemma lem4397266 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term154 A B s f g) = (term202 A B s f g).
Proof. exact (MK_COMB (@lem4397168 A B g s f) (@lem4397265 A B s f g)). Qed.
Lemma lem4397267 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term161 A B s f g) = (term203 A B s f g).
Proof. exact (MK_COMB (@lem4397043 A B s f g) (@lem4397266 A B s f g)). Qed.
Lemma lem4397269 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4397270 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (@lem4397269 A P Q). Qed.
Lemma lem4397271 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term204 A B s f g) = (term205 A B s f g).
Proof. exact (@lem4397270 A (term130 A B s f) (term140 A B s f g)). Qed.
Lemma lem4397272 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term189 A B s f x) = (term104 A B s f x).
Proof. exact (eq_refl (term189 A B s f x)). Qed.
Lemma lem4397273 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term198 A B s f) = (term130 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4397272 A B s f x)). Qed.
Lemma lem4397274 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397275 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term199 A B s f) = (term131 A B s f).
Proof. exact (MK_COMB (@lem4397274 A) (@lem4397273 A B s f)). Qed.
Lemma lem4397276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397277 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term206 A B s f) = (term145 A B s f).
Proof. exact (MK_COMB (@lem4397276) (@lem4397275 A B s f)). Qed.
Lemma lem4397278 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term187 A B s f g x) = (term100 A B s f g x).
Proof. exact (eq_refl (term187 A B s f g x)). Qed.
Lemma lem4397279 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term194 A B s f g) = (term140 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397278 A B s f g x)). Qed.
Lemma lem4397280 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397281 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term195 A B s f g) = (term141 A B s f g).
Proof. exact (MK_COMB (@lem4397280 A) (@lem4397279 A B s f g)). Qed.
Lemma lem4397282 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term204 A B s f g) = (term147 A B s f g).
Proof. exact (MK_COMB (@lem4397277 A B s f) (@lem4397281 A B s f g)). Qed.
Lemma lem4397283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4397284 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term207 A B s f g) = (term208 A B s f g).
Proof. exact (MK_COMB (@lem4397283) (@lem4397282 A B s f g)). Qed.
Lemma lem4397285 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term189 A B s f x) = (term104 A B s f x).
Proof. exact (eq_refl (term189 A B s f x)). Qed.
Lemma lem4397286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397287 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term209 A B s f x) = (term210 A B s f x).
Proof. exact (MK_COMB (@lem4397286) (@lem4397285 A B s f x)). Qed.
Lemma lem4397288 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term187 A B s f g x) = (term100 A B s f g x).
Proof. exact (eq_refl (term187 A B s f g x)). Qed.
Lemma lem4397289 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term211 A B s f g x) = (term212 A B s f g x).
Proof. exact (MK_COMB (@lem4397287 A B s f x) (@lem4397288 A B s f g x)). Qed.
Lemma lem4397290 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term213 A B s f g) = (term214 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397289 A B s f g x)). Qed.
Lemma lem4397291 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397292 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term205 A B s f g) = (term215 A B s f g).
Proof. exact (MK_COMB (@lem4397291 A) (@lem4397290 A B s f g)). Qed.
Lemma lem4397293 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term204 A B s f g) = (term205 A B s f g)) = ((term147 A B s f g) = (term215 A B s f g)).
Proof. exact (MK_COMB (@lem4397284 A B s f g) (@lem4397292 A B s f g)). Qed.
Lemma lem4397294 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term147 A B s f g) = (term215 A B s f g).
Proof. exact (EQ_MP (@lem4397293 A B s f g) (@lem4397271 A B s f g)). Qed.
Lemma lem4397295 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term180 A B g s f) = (term180 A B g s f).
Proof. exact (eq_refl (term180 A B g s f)). Qed.
Lemma lem4397296 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term181 A B s f g) = (term216 A B s f g).
Proof. exact (MK_COMB (@lem4397295 A B g s f) (@lem4397294 A B s f g)). Qed.
Lemma lem4397298 {A : Type'} (P : Prop) (Q : A -> Prop) : (term217 A P Q) = (term218 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4397299 {A : Type'} (P : Prop) (Q : A -> Prop) : (term217 A P Q) = (term218 A P Q).
Proof. exact (@lem4397298 A P Q). Qed.
Lemma lem4397300 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term219 A B s f g) = (term220 A B s f g).
Proof. exact (@lem4397299 A (term179 A B g s f) (term214 A B s f g)). Qed.
Lemma lem4397301 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term221 A B s f g x) = (term212 A B s f g x).
Proof. exact (eq_refl (term221 A B s f g x)). Qed.
Lemma lem4397302 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term222 A B s f g) = (term214 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397301 A B s f g x)). Qed.
Lemma lem4397303 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397304 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term223 A B s f g) = (term215 A B s f g).
Proof. exact (MK_COMB (@lem4397303 A) (@lem4397302 A B s f g)). Qed.
Lemma lem4397305 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term180 A B g s f) = (term180 A B g s f).
Proof. exact (eq_refl (term180 A B g s f)). Qed.
Lemma lem4397306 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term219 A B s f g) = (term216 A B s f g).
Proof. exact (MK_COMB (@lem4397305 A B g s f) (@lem4397304 A B s f g)). Qed.
Lemma lem4397307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4397308 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term224 A B s f g) = (term225 A B s f g).
Proof. exact (MK_COMB (@lem4397307) (@lem4397306 A B s f g)). Qed.
Lemma lem4397309 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term221 A B s f g x) = (term212 A B s f g x).
Proof. exact (eq_refl (term221 A B s f g x)). Qed.
Lemma lem4397310 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term180 A B g s f) = (term180 A B g s f).
Proof. exact (eq_refl (term180 A B g s f)). Qed.
Lemma lem4397311 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term226 A B s f g x) = (term227 A B s f g x).
Proof. exact (MK_COMB (@lem4397310 A B g s f) (@lem4397309 A B s f g x)). Qed.
Lemma lem4397312 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term228 A B s f g) = (term229 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397311 A B s f g x)). Qed.
Lemma lem4397313 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397314 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term220 A B s f g) = (term230 A B s f g).
Proof. exact (MK_COMB (@lem4397313 A) (@lem4397312 A B s f g)). Qed.
Lemma lem4397315 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term219 A B s f g) = (term220 A B s f g)) = ((term216 A B s f g) = (term230 A B s f g)).
Proof. exact (MK_COMB (@lem4397308 A B s f g) (@lem4397314 A B s f g)). Qed.
Lemma lem4397316 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term216 A B s f g) = (term230 A B s f g).
Proof. exact (EQ_MP (@lem4397315 A B s f g) (@lem4397300 A B s f g)). Qed.
Lemma lem4397317 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term181 A B s f g) = (term230 A B s f g).
Proof. exact (TRANS (@lem4397296 A B s f g) (@lem4397316 A B s f g)). Qed.
Lemma lem4397318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397319 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term182 A B s f g) = (term231 A B s f g).
Proof. exact (MK_COMB (@lem4397318) (@lem4397317 A B s f g)). Qed.
Lemma lem4397321 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4397322 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (@lem4397321 A P Q). Qed.
Lemma lem4397323 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term186 A B g s f) = (term185 A B g s f).
Proof. exact (@lem4397322 A (term140 A B s f g) (term130 A B s f)). Qed.
Lemma lem4397324 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term187 A B s f g x) = (term100 A B s f g x).
Proof. exact (eq_refl (term187 A B s f g x)). Qed.
Lemma lem4397325 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term194 A B s f g) = (term140 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397324 A B s f g x)). Qed.
Lemma lem4397326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397327 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term195 A B s f g) = (term141 A B s f g).
Proof. exact (MK_COMB (@lem4397326 A) (@lem4397325 A B s f g)). Qed.
Lemma lem4397328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397329 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term196 A B s f g) = (term197 A B s f g).
Proof. exact (MK_COMB (@lem4397328) (@lem4397327 A B s f g)). Qed.
Lemma lem4397330 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term189 A B s f x) = (term104 A B s f x).
Proof. exact (eq_refl (term189 A B s f x)). Qed.
Lemma lem4397331 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term198 A B s f) = (term130 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4397330 A B s f x)). Qed.
Lemma lem4397332 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397333 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term199 A B s f) = (term131 A B s f).
Proof. exact (MK_COMB (@lem4397332 A) (@lem4397331 A B s f)). Qed.
Lemma lem4397334 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term186 A B g s f) = (term200 A B g s f).
Proof. exact (MK_COMB (@lem4397329 A B s f g) (@lem4397333 A B s f)). Qed.
Lemma lem4397335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4397336 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term232 A B g s f) = (term233 A B g s f).
Proof. exact (MK_COMB (@lem4397335) (@lem4397334 A B g s f)). Qed.
Lemma lem4397337 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term187 A B s f g x) = (term100 A B s f g x).
Proof. exact (eq_refl (term187 A B s f g x)). Qed.
Lemma lem4397338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397339 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term188 A B s f g x) = (term106 A B s f g x).
Proof. exact (MK_COMB (@lem4397338) (@lem4397337 A B s f g x)). Qed.
Lemma lem4397340 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term189 A B s f x) = (term104 A B s f x).
Proof. exact (eq_refl (term189 A B s f x)). Qed.
Lemma lem4397341 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term190 A B g s f x) = (term108 A B g s f x).
Proof. exact (MK_COMB (@lem4397339 A B s f g x) (@lem4397340 A B s f x)). Qed.
Lemma lem4397342 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term191 A B g s f) = (term119 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem4397341 A B g s f x)). Qed.
Lemma lem4397343 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397344 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term185 A B g s f) = (term120 A B g s f).
Proof. exact (MK_COMB (@lem4397343 A) (@lem4397342 A B g s f)). Qed.
Lemma lem4397345 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : ((term186 A B g s f) = (term185 A B g s f)) = ((term200 A B g s f) = (term120 A B g s f)).
Proof. exact (MK_COMB (@lem4397336 A B g s f) (@lem4397344 A B g s f)). Qed.
Lemma lem4397346 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term200 A B g s f) = (term120 A B g s f).
Proof. exact (EQ_MP (@lem4397345 A B g s f) (@lem4397323 A B g s f)). Qed.
Lemma lem4397347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4397348 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term201 A B g s f) = (term152 A B g s f).
Proof. exact (MK_COMB (@lem4397347) (@lem4397346 A B g s f)). Qed.
Lemma lem4397349 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term150 A B s f g) = (term150 A B s f g).
Proof. exact (eq_refl (term150 A B s f g)). Qed.
Lemma lem4397350 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term202 A B s f g) = (term154 A B s f g).
Proof. exact (MK_COMB (@lem4397348 A B g s f) (@lem4397349 A B s f g)). Qed.
Lemma lem4397352 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4397353 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4397352 A P Q). Qed.
Lemma lem4397354 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term236 A B s f g) = (term237 A B s f g).
Proof. exact (@lem4397353 A (term119 A B g s f) (term150 A B s f g)). Qed.
Lemma lem4397355 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term238 A B g s f x) = (term108 A B g s f x).
Proof. exact (eq_refl (term238 A B g s f x)). Qed.
Lemma lem4397356 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term239 A B g s f) = (term119 A B g s f).
Proof. exact (fun_ext (fun x : A => @lem4397355 A B g s f x)). Qed.
Lemma lem4397357 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397358 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term240 A B g s f) = (term120 A B g s f).
Proof. exact (MK_COMB (@lem4397357 A) (@lem4397356 A B g s f)). Qed.
Lemma lem4397359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4397360 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term241 A B g s f) = (term152 A B g s f).
Proof. exact (MK_COMB (@lem4397359) (@lem4397358 A B g s f)). Qed.
Lemma lem4397361 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term150 A B s f g) = (term150 A B s f g).
Proof. exact (eq_refl (term150 A B s f g)). Qed.
Lemma lem4397362 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term236 A B s f g) = (term154 A B s f g).
Proof. exact (MK_COMB (@lem4397360 A B g s f) (@lem4397361 A B s f g)). Qed.
Lemma lem4397363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4397364 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term242 A B s f g) = (term243 A B s f g).
Proof. exact (MK_COMB (@lem4397363) (@lem4397362 A B s f g)). Qed.
Lemma lem4397365 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term238 A B g s f x) = (term108 A B g s f x).
Proof. exact (eq_refl (term238 A B g s f x)). Qed.
Lemma lem4397366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4397367 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term244 A B g s f x) = (term245 A B g s f x).
Proof. exact (MK_COMB (@lem4397366) (@lem4397365 A B g s f x)). Qed.
Lemma lem4397368 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term150 A B s f g) = (term150 A B s f g).
Proof. exact (eq_refl (term150 A B s f g)). Qed.
Lemma lem4397369 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term246 A B x s f g) = (term247 A B x s f g).
Proof. exact (MK_COMB (@lem4397367 A B g s f x) (@lem4397368 A B s f g)). Qed.
Lemma lem4397370 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term248 A B s f g) = (term249 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397369 A B x s f g)). Qed.
Lemma lem4397371 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397372 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term237 A B s f g) = (term250 A B s f g).
Proof. exact (MK_COMB (@lem4397371 A) (@lem4397370 A B s f g)). Qed.
Lemma lem4397373 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term236 A B s f g) = (term237 A B s f g)) = ((term154 A B s f g) = (term250 A B s f g)).
Proof. exact (MK_COMB (@lem4397364 A B s f g) (@lem4397372 A B s f g)). Qed.
Lemma lem4397374 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term154 A B s f g) = (term250 A B s f g).
Proof. exact (EQ_MP (@lem4397373 A B s f g) (@lem4397354 A B s f g)). Qed.
Lemma lem4397375 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term202 A B s f g) = (term250 A B s f g).
Proof. exact (TRANS (@lem4397350 A B s f g) (@lem4397374 A B s f g)). Qed.
Lemma lem4397376 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term203 A B s f g) = (term251 A B s f g).
Proof. exact (MK_COMB (@lem4397319 A B s f g) (@lem4397375 A B s f g)). Qed.
Lemma lem4397378 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4397379 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term184 A P Q) = (term183 A P Q).
Proof. exact (@lem4397378 A P Q). Qed.
Lemma lem4397380 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term252 A B s f g) = (term253 A B s f g).
Proof. exact (@lem4397379 A (term229 A B s f g) (term249 A B s f g)). Qed.
Lemma lem4397381 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term254 A B s f g x) = (term227 A B s f g x).
Proof. exact (eq_refl (term254 A B s f g x)). Qed.
Lemma lem4397382 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term255 A B s f g) = (term229 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397381 A B s f g x)). Qed.
Lemma lem4397383 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397384 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term256 A B s f g) = (term230 A B s f g).
Proof. exact (MK_COMB (@lem4397383 A) (@lem4397382 A B s f g)). Qed.
Lemma lem4397385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397386 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term257 A B s f g) = (term231 A B s f g).
Proof. exact (MK_COMB (@lem4397385) (@lem4397384 A B s f g)). Qed.
Lemma lem4397387 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term258 A B s f g x) = (term247 A B x s f g).
Proof. exact (eq_refl (term258 A B s f g x)). Qed.
Lemma lem4397388 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term259 A B s f g) = (term249 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397387 A B x s f g)). Qed.
Lemma lem4397389 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397390 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term260 A B s f g) = (term250 A B s f g).
Proof. exact (MK_COMB (@lem4397389 A) (@lem4397388 A B s f g)). Qed.
Lemma lem4397391 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term252 A B s f g) = (term251 A B s f g).
Proof. exact (MK_COMB (@lem4397386 A B s f g) (@lem4397390 A B s f g)). Qed.
Lemma lem4397392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4397393 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term261 A B s f g) = (term262 A B s f g).
Proof. exact (MK_COMB (@lem4397392) (@lem4397391 A B s f g)). Qed.
Lemma lem4397394 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term254 A B s f g x) = (term227 A B s f g x).
Proof. exact (eq_refl (term254 A B s f g x)). Qed.
Lemma lem4397395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397396 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term263 A B s f g x) = (term264 A B s f g x).
Proof. exact (MK_COMB (@lem4397395) (@lem4397394 A B s f g x)). Qed.
Lemma lem4397397 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term258 A B s f g x) = (term247 A B x s f g).
Proof. exact (eq_refl (term258 A B s f g x)). Qed.
Lemma lem4397398 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term265 A B s f g x) = (term266 A B x s f g).
Proof. exact (MK_COMB (@lem4397396 A B s f g x) (@lem4397397 A B x s f g)). Qed.
Lemma lem4397399 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term267 A B s f g) = (term268 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397398 A B x s f g)). Qed.
Lemma lem4397400 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4397401 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term253 A B s f g) = (term269 A B s f g).
Proof. exact (MK_COMB (@lem4397400 A) (@lem4397399 A B s f g)). Qed.
Lemma lem4397402 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term252 A B s f g) = (term253 A B s f g)) = ((term251 A B s f g) = (term269 A B s f g)).
Proof. exact (MK_COMB (@lem4397393 A B s f g) (@lem4397401 A B s f g)). Qed.
Lemma lem4397403 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term251 A B s f g) = (term269 A B s f g).
Proof. exact (EQ_MP (@lem4397402 A B s f g) (@lem4397380 A B s f g)). Qed.
Lemma lem4397404 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term203 A B s f g) = (term269 A B s f g).
Proof. exact (TRANS (@lem4397376 A B s f g) (@lem4397403 A B s f g)). Qed.
Lemma lem4397405 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term161 A B s f g) = (term269 A B s f g).
Proof. exact (TRANS (@lem4397267 A B s f g) (@lem4397404 A B s f g)). Qed.
Lemma lem4397406 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term94 A B s f g) = (term269 A B s f g).
Proof. exact (TRANS (@lem4396818 A B s f g) (@lem4397405 A B s f g)). Qed.
Lemma lem4397407 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term94 A B s f g) : term269 A B s f g.
Proof. exact (EQ_MP (@lem4397406 A B s f g) (@lem4396696 A B s f g h1)). Qed.
Lemma lem4397408 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term266 A B x s f g) : term266 A B x s f g.
Proof. exact (h1). Qed.
Lemma lem4397427 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term110 A B s f g x) = (term110 A B s f g x).
Proof. exact (eq_refl (term110 A B s f g x)). Qed.
Lemma lem4397428 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term142 A B s f g) = (term142 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397427 A B s f g x)). Qed.
Lemma lem4397429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397430 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term143 A B s f g) = (term143 A B s f g).
Proof. exact (MK_COMB (@lem4397429 A) (@lem4397428 A B s f g)). Qed.
Lemma lem4397445 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term111 A B s f x) = (term111 A B s f x).
Proof. exact (eq_refl (term111 A B s f x)). Qed.
Lemma lem4397446 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term132 A B s f) = (term132 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4397445 A B s f x)). Qed.
Lemma lem4397447 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397448 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term133 A B s f) = (term133 A B s f).
Proof. exact (MK_COMB (@lem4397447 A) (@lem4397446 A B s f)). Qed.
Lemma lem4397449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4397450 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term149 A B s f) = (term149 A B s f).
Proof. exact (MK_COMB (@lem4397449) (@lem4397448 A B s f)). Qed.
Lemma lem4397451 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term150 A B s f g) = (term150 A B s f g).
Proof. exact (MK_COMB (@lem4397450 A B s f) (@lem4397430 A B s f g)). Qed.
Lemma lem4397494 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) : (term245 A B g s f x) = (term245 A B g s f x).
Proof. exact (eq_refl (term245 A B g s f x)). Qed.
Lemma lem4397495 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term247 A B x s f g) = (term247 A B x s f g).
Proof. exact (MK_COMB (@lem4397494 A B g s f x) (@lem4397451 A B s f g)). Qed.
Lemma lem4397536 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term212 A B s f g x) = (term212 A B s f g x).
Proof. exact (eq_refl (term212 A B s f g x)). Qed.
Lemma lem4397551 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term111 A B s f x) = (term111 A B s f x).
Proof. exact (eq_refl (term111 A B s f x)). Qed.
Lemma lem4397552 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term132 A B s f) = (term132 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4397551 A B s f x)). Qed.
Lemma lem4397553 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397554 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term133 A B s f) = (term133 A B s f).
Proof. exact (MK_COMB (@lem4397553 A) (@lem4397552 A B s f)). Qed.
Lemma lem4397573 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term110 A B s f g x) = (term110 A B s f g x).
Proof. exact (eq_refl (term110 A B s f g x)). Qed.
Lemma lem4397574 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term142 A B s f g) = (term142 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397573 A B s f g x)). Qed.
Lemma lem4397575 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397576 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term143 A B s f g) = (term143 A B s f g).
Proof. exact (MK_COMB (@lem4397575 A) (@lem4397574 A B s f g)). Qed.
Lemma lem4397577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4397578 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term176 A B s f g) = (term176 A B s f g).
Proof. exact (MK_COMB (@lem4397577) (@lem4397576 A B s f g)). Qed.
Lemma lem4397579 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term179 A B g s f) = (term179 A B g s f).
Proof. exact (MK_COMB (@lem4397578 A B s f g) (@lem4397554 A B s f)). Qed.
Lemma lem4397580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4397581 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) : (term180 A B g s f) = (term180 A B g s f).
Proof. exact (MK_COMB (@lem4397580) (@lem4397579 A B g s f)). Qed.
Lemma lem4397582 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term227 A B s f g x) = (term227 A B s f g x).
Proof. exact (MK_COMB (@lem4397581 A B g s f) (@lem4397536 A B s f g x)). Qed.
Lemma lem4397583 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4397584 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term264 A B s f g x) = (term264 A B s f g x).
Proof. exact (MK_COMB (@lem4397583) (@lem4397582 A B s f g x)). Qed.
Lemma lem4397585 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term266 A B x s f g) = (term266 A B x s f g).
Proof. exact (MK_COMB (@lem4397584 A B s f g x) (@lem4397495 A B x s f g)). Qed.
Lemma lem4397586 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term266 A B x s f g) : term266 A B x s f g.
Proof. exact (EQ_MP (@lem4397585 A B x s f g) (@lem4397408 A B x s f g h1)). Qed.
Lemma lem4397587 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term227 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4397588 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term247 A B x s f g.
Proof. exact (h1). Qed.
Lemma lem4397589 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term212 A B s f g x.
Proof. exact (proj2 (@lem4397587 A B s f g x h1)). Qed.
Lemma lem4397590 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term179 A B g s f.
Proof. exact (proj1 (@lem4397587 A B s f g x h1)). Qed.
Lemma lem4397591 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term133 A B s f.
Proof. exact (proj2 (@lem4397590 A B s f g x h1)). Qed.
Lemma lem4397592 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term143 A B s f g.
Proof. exact (proj1 (@lem4397590 A B s f g x h1)). Qed.
Lemma lem4397593 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term104 A B s f x.
Proof. exact (h1). Qed.
Lemma lem4397594 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : term100 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4397599 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term150 A B s f g.
Proof. exact (proj2 (@lem4397588 A B x s f g h1)). Qed.
Lemma lem4397600 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term108 A B g s f x.
Proof. exact (proj1 (@lem4397588 A B x s f g h1)). Qed.
Lemma lem4397601 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term143 A B s f g.
Proof. exact (proj2 (@lem4397599 A B x s f g h1)). Qed.
Lemma lem4397602 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term133 A B s f.
Proof. exact (proj1 (@lem4397599 A B x s f g h1)). Qed.
Lemma lem4397603 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : term100 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4397604 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term104 A B s f x.
Proof. exact (h1). Qed.
Lemma lem4397629 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term111 A B s f x) = (term111 A B s f x).
Proof. exact (eq_refl (term111 A B s f x)). Qed.
Lemma lem4397630 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term132 A B s f) = (term132 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4397629 A B s f x)). Qed.
Lemma lem4397631 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397633 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term133 A B s f) = (term133 A B s f).
Proof. exact (MK_COMB (@lem4397631 A) (@lem4397630 A B s f)). Qed.
Lemma lem4397634 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term133 A B s f.
Proof. exact (EQ_MP (@lem4397633 A B s f) (@lem4397591 A B s f g x h1)). Qed.
Lemma lem4397650 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term110 A B s f g x) = (term110 A B s f g x).
Proof. exact (eq_refl (term110 A B s f g x)). Qed.
Lemma lem4397651 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term142 A B s f g) = (term142 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397650 A B s f g x)). Qed.
Lemma lem4397652 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397654 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term143 A B s f g) = (term143 A B s f g).
Proof. exact (MK_COMB (@lem4397652 A) (@lem4397651 A B s f g)). Qed.
Lemma lem4397655 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term143 A B s f g.
Proof. exact (EQ_MP (@lem4397654 A B s f g) (@lem4397592 A B s f g x h1)). Qed.
Lemma lem4397697 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term110 A B s f g x) = (term110 A B s f g x).
Proof. exact (eq_refl (term110 A B s f g x)). Qed.
Lemma lem4397698 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term142 A B s f g) = (term142 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4397697 A B s f g x)). Qed.
Lemma lem4397699 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397701 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term143 A B s f g) = (term143 A B s f g).
Proof. exact (MK_COMB (@lem4397699 A) (@lem4397698 A B s f g)). Qed.
Lemma lem4397702 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term143 A B s f g.
Proof. exact (EQ_MP (@lem4397701 A B s f g) (@lem4397601 A B x s f g h1)). Qed.
Lemma lem4397718 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term111 A B s f x) = (term111 A B s f x).
Proof. exact (eq_refl (term111 A B s f x)). Qed.
Lemma lem4397719 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term132 A B s f) = (term132 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4397718 A B s f x)). Qed.
Lemma lem4397720 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397722 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term133 A B s f) = (term133 A B s f).
Proof. exact (MK_COMB (@lem4397720 A) (@lem4397719 A B s f)). Qed.
Lemma lem4397723 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term133 A B s f.
Proof. exact (EQ_MP (@lem4397722 A B s f) (@lem4397602 A B x s f g h1)). Qed.
Lemma lem4397748 {A B : Type'} (_50254 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term169 A B s f _50254.
Proof. exact (@lem4397634 A B s f g x h1 _50254). Qed.
Lemma lem4397749 {A B : Type'} (s : A -> Prop) (f : A -> B) (_50254 : A) : (term169 A B s f _50254) = (term111 A B s f _50254).
Proof. exact (eq_refl (term169 A B s f _50254)). Qed.
Lemma lem4397751 {A B : Type'} (_50255 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term166 A B s f g _50255.
Proof. exact (@lem4397655 A B s f g x h1 _50255). Qed.
Lemma lem4397752 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50255 : A) : (term166 A B s f g _50255) = (term110 A B s f g _50255).
Proof. exact (eq_refl (term166 A B s f g _50255)). Qed.
Lemma lem4397760 {A B : Type'} (_50258 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term166 A B s f g _50258.
Proof. exact (@lem4397702 A B x s f g h1 _50258). Qed.
Lemma lem4397761 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50258 : A) : (term166 A B s f g _50258) = (term110 A B s f g _50258).
Proof. exact (eq_refl (term166 A B s f g _50258)). Qed.
Lemma lem4397763 {A B : Type'} (_50259 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term169 A B s f _50259.
Proof. exact (@lem4397723 A B x s f g h1 _50259). Qed.
Lemma lem4397764 {A B : Type'} (s : A -> Prop) (f : A -> B) (_50259 : A) : (term169 A B s f _50259) = (term111 A B s f _50259).
Proof. exact (eq_refl (term169 A B s f _50259)). Qed.
Lemma lem4397780 {A B : Type'} (_50254 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term111 A B s f _50254.
Proof. exact (EQ_MP (@lem4397749 A B s f _50254) (@lem4397748 A B _50254 s f g x h1)). Qed.
Lemma lem4397784 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term270 A B f x.
Proof. exact (proj2 (@lem4397593 A B s f x h1)). Qed.
Lemma lem4397790 {A B : Type'} (_50255 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term110 A B s f g _50255.
Proof. exact (EQ_MP (@lem4397752 A B s f g _50255) (@lem4397751 A B _50255 s f g x h1)). Qed.
Lemma lem4397800 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : term96 A B f g x.
Proof. exact (proj2 (@lem4397594 A B s f g x h1)). Qed.
Lemma lem4397812 {A B : Type'} (_50258 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term110 A B s f g _50258.
Proof. exact (EQ_MP (@lem4397761 A B s f g _50258) (@lem4397760 A B _50258 x s f g h1)). Qed.
Lemma lem4397816 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : term96 A B f g x.
Proof. exact (proj2 (@lem4397603 A B s f g x h1)). Qed.
Lemma lem4397822 {A B : Type'} (_50259 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term111 A B s f _50259.
Proof. exact (EQ_MP (@lem4397764 A B s f _50259) (@lem4397763 A B _50259 x s f g h1)). Qed.
Lemma lem4397832 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term270 A B f x.
Proof. exact (proj2 (@lem4397604 A B s f x h1)). Qed.
Lemma lem4397875 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term102 A x s.
Proof. exact (proj1 (@lem4397593 A B s f x h1)). Qed.
Lemma lem4397876 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term271 A x s.
Proof. exact (fun h0 : @IN A x s => @lem4397875 A B s f x h1). Qed.
Lemma lem4397878 (p : Prop) : (term272 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4397879 {A : Type'} (x : A) (s : A -> Prop) : (term271 A x s) = (term102 A x s).
Proof. exact (@lem4397878 (@IN A x s)). Qed.
Lemma lem4397880 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term102 A x s.
Proof. exact (EQ_MP (@lem4397879 A x s) (@lem4397876 A B s f x h1)). Qed.
Lemma lem4397886 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4397887 {A B : Type'} (f : A -> B) (_50254 : A) (s : A -> Prop) : (term111 A B s f _50254) = (term273 A B f _50254 s).
Proof. exact (@lem4397886 ((f _50254) = (@ARB B)) (@IN A _50254 s)). Qed.
Lemma lem4397895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4397896 {A B : Type'} (f : A -> B) (_50254 : A) (s : A -> Prop) : (term274 A B s f _50254) = (term275 A B f _50254 s).
Proof. exact (MK_COMB (@lem4397895) (@lem4397887 A B f _50254 s)). Qed.
Lemma lem4397904 {A B : Type'} (f : A -> B) (_50254 : A) (s : A -> Prop) : (term273 A B f _50254 s) = (term273 A B f _50254 s).
Proof. exact (eq_refl (term273 A B f _50254 s)). Qed.
Lemma lem4397905 {A B : Type'} (f : A -> B) (_50254 : A) (s : A -> Prop) : ((term111 A B s f _50254) = (term273 A B f _50254 s)) = ((term273 A B f _50254 s) = (term273 A B f _50254 s)).
Proof. exact (MK_COMB (@lem4397896 A B f _50254 s) (@lem4397904 A B f _50254 s)). Qed.
Lemma lem4397907 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4397908 (x : Prop) : (x = x) = True.
Proof. exact (@lem4397907 Prop x). Qed.
Lemma lem4397909 {A B : Type'} (f : A -> B) (_50254 : A) (s : A -> Prop) : ((term273 A B f _50254 s) = (term273 A B f _50254 s)) = True.
Proof. exact (@lem4397908 (term273 A B f _50254 s)). Qed.
Lemma lem4397910 {A B : Type'} (f : A -> B) (_50254 : A) (s : A -> Prop) : ((term111 A B s f _50254) = (term273 A B f _50254 s)) = True.
Proof. exact (TRANS (@lem4397905 A B f _50254 s) (@lem4397909 A B f _50254 s)). Qed.
Lemma lem4397911 {A B : Type'} (f : A -> B) (_50254 : A) (s : A -> Prop) : True = ((term111 A B s f _50254) = (term273 A B f _50254 s)).
Proof. exact (SYM (@lem4397910 A B f _50254 s)). Qed.
Lemma lem4397912 {A B : Type'} (f : A -> B) (_50254 : A) (s : A -> Prop) : (term111 A B s f _50254) = (term273 A B f _50254 s).
Proof. exact (EQ_MP (@lem4397911 A B f _50254 s) (@lem0)). Qed.
Lemma lem4397913 {A B : Type'} (_50254 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term273 A B f _50254 s.
Proof. exact (EQ_MP (@lem4397912 A B f _50254 s) (@lem4397780 A B _50254 s f g x h1)). Qed.
Lemma lem4397915 (b : Prop) (a : Prop) : (a \/ b) = (term276 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4397918 {A B : Type'} (s : A -> Prop) (f : A -> B) (_50254 : A) : (term273 A B f _50254 s) = (term70 A B s f _50254).
Proof. exact (@lem4397915 (@IN A _50254 s) ((f _50254) = (@ARB B))). Qed.
Lemma lem4397921 {A B : Type'} (_50254 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term70 A B s f _50254.
Proof. exact (EQ_MP (@lem4397918 A B s f _50254) (@lem4397913 A B _50254 s f g x h1)). Qed.
Lemma lem4397922 {A B : Type'} (_50254 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term70 A B s f _50254.
Proof. exact (@lem4397921 A B _50254 s f g x h1). Qed.
Lemma lem4397923 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term70 A B s f x.
Proof. exact (@lem4397922 A B x s f g x h1). Qed.
Lemma lem4397926 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term104 A B s f x) (h2 : term227 A B s f g x) : (f x) = (@ARB B).
Proof. exact (@lem4397923 A B s f g x h2 (@lem4397880 A B s f x h1)). Qed.
Lemma lem4397927 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term104 A B s f x) (h2 : term227 A B s f g x) : term277 A B f x.
Proof. exact (fun h0 : term270 A B f x => @lem4397926 A B s f g x h1 h2). Qed.
Lemma lem4397929 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4397930 {A B : Type'} (f : A -> B) (x : A) : (term277 A B f x) = ((f x) = (@ARB B)).
Proof. exact (@lem4397929 ((f x) = (@ARB B))). Qed.
Lemma lem4397931 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term104 A B s f x) (h2 : term227 A B s f g x) : (f x) = (@ARB B).
Proof. exact (EQ_MP (@lem4397930 A B f x) (@lem4397927 A B s f g x h1 h2)). Qed.
Lemma lem4397934 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4397936 {A B : Type'} (f : A -> B) (x : A) : (term270 A B f x) = (term279 A B f x).
Proof. exact (@lem4397934 ((f x) = (@ARB B))). Qed.
Lemma lem4397939 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term279 A B f x.
Proof. exact (EQ_MP (@lem4397936 A B f x) (@lem4397784 A B s f x h1)). Qed.
Lemma lem4397942 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term104 A B s f x) (h2 : term227 A B s f g x) : False.
Proof. exact (@lem4397939 A B s f x h1 (@lem4397931 A B s f g x h1 h2)). Qed.
Lemma lem4397943 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term104 A B s f x) (h2 : term227 A B s f g x) : term280.
Proof. exact (fun h0 : ~ False => @lem4397942 A B s f g x h1 h2). Qed.
Lemma lem4397945 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4397946 : term280 = False.
Proof. exact (@lem4397945 False). Qed.
Lemma lem4397947 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term104 A B s f x) (h2 : term227 A B s f g x) : False.
Proof. exact (EQ_MP (@lem4397946) (@lem4397943 A B s f g x h1 h2)). Qed.
Lemma lem4397990 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : @IN A x s.
Proof. exact (proj1 (@lem4397594 A B s f g x h1)). Qed.
Lemma lem4397991 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : term281 A x s.
Proof. exact (fun h0 : term102 A x s => @lem4397990 A B s f g x h1). Qed.
Lemma lem4397993 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4397994 {A : Type'} (x : A) (s : A -> Prop) : (term281 A x s) = (@IN A x s).
Proof. exact (@lem4397993 (@IN A x s)). Qed.
Lemma lem4397995 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : @IN A x s.
Proof. exact (EQ_MP (@lem4397994 A x s) (@lem4397991 A B s f g x h1)). Qed.
Lemma lem4398001 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4398002 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) (s : A -> Prop) : (term110 A B s f g _50255) = (term282 A B f g _50255 s).
Proof. exact (@lem4398001 ((f _50255) = (g _50255)) (term102 A _50255 s)). Qed.
Lemma lem4398010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4398011 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) (s : A -> Prop) : (term283 A B s f g _50255) = (term284 A B f g _50255 s).
Proof. exact (MK_COMB (@lem4398010) (@lem4398002 A B f g _50255 s)). Qed.
Lemma lem4398019 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) (s : A -> Prop) : (term282 A B f g _50255 s) = (term282 A B f g _50255 s).
Proof. exact (eq_refl (term282 A B f g _50255 s)). Qed.
Lemma lem4398020 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) (s : A -> Prop) : ((term110 A B s f g _50255) = (term282 A B f g _50255 s)) = ((term282 A B f g _50255 s) = (term282 A B f g _50255 s)).
Proof. exact (MK_COMB (@lem4398011 A B f g _50255 s) (@lem4398019 A B f g _50255 s)). Qed.
Lemma lem4398022 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4398023 (x : Prop) : (x = x) = True.
Proof. exact (@lem4398022 Prop x). Qed.
Lemma lem4398024 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) (s : A -> Prop) : ((term282 A B f g _50255 s) = (term282 A B f g _50255 s)) = True.
Proof. exact (@lem4398023 (term282 A B f g _50255 s)). Qed.
Lemma lem4398025 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) (s : A -> Prop) : ((term110 A B s f g _50255) = (term282 A B f g _50255 s)) = True.
Proof. exact (TRANS (@lem4398020 A B f g _50255 s) (@lem4398024 A B f g _50255 s)). Qed.
Lemma lem4398026 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) (s : A -> Prop) : True = ((term110 A B s f g _50255) = (term282 A B f g _50255 s)).
Proof. exact (SYM (@lem4398025 A B f g _50255 s)). Qed.
Lemma lem4398027 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) (s : A -> Prop) : (term110 A B s f g _50255) = (term282 A B f g _50255 s).
Proof. exact (EQ_MP (@lem4398026 A B f g _50255 s) (@lem0)). Qed.
Lemma lem4398028 {A B : Type'} (_50255 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term282 A B f g _50255 s.
Proof. exact (EQ_MP (@lem4398027 A B f g _50255 s) (@lem4397790 A B _50255 s f g x h1)). Qed.
Lemma lem4398030 (b : Prop) (a : Prop) : (a \/ b) = (term276 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4398031 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50255 : A) : (term282 A B f g _50255 s) = (term285 A B s f g _50255).
Proof. exact (@lem4398030 (term102 A _50255 s) ((f _50255) = (g _50255))). Qed.
Lemma lem4398033 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4398034 {A : Type'} (_50255 : A) (s : A -> Prop) : (term95 A _50255 s) = (@IN A _50255 s).
Proof. exact (@lem4398033 (@IN A _50255 s)). Qed.
Lemma lem4398035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4398036 {A : Type'} (_50255 : A) (s : A -> Prop) : (term286 A _50255 s) = (term287 A _50255 s).
Proof. exact (MK_COMB (@lem4398035) (@lem4398034 A _50255 s)). Qed.
Lemma lem4398037 {A B : Type'} (f : A -> B) (g : A -> B) (_50255 : A) : ((f _50255) = (g _50255)) = ((f _50255) = (g _50255)).
Proof. exact (eq_refl ((f _50255) = (g _50255))). Qed.
Lemma lem4398038 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50255 : A) : (term285 A B s f g _50255) = (term68 A B s f g _50255).
Proof. exact (MK_COMB (@lem4398036 A _50255 s) (@lem4398037 A B f g _50255)). Qed.
Lemma lem4398039 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50255 : A) : (term282 A B f g _50255 s) = (term68 A B s f g _50255).
Proof. exact (TRANS (@lem4398031 A B s f g _50255) (@lem4398038 A B s f g _50255)). Qed.
Lemma lem4398042 {A B : Type'} (_50255 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term68 A B s f g _50255.
Proof. exact (EQ_MP (@lem4398039 A B s f g _50255) (@lem4398028 A B _50255 s f g x h1)). Qed.
Lemma lem4398043 {A B : Type'} (_50255 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term68 A B s f g _50255.
Proof. exact (@lem4398042 A B _50255 s f g x h1). Qed.
Lemma lem4398044 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : term68 A B s f g x.
Proof. exact (@lem4398043 A B x s f g x h1). Qed.
Lemma lem4398047 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) (h2 : term100 A B s f g x) : (f x) = (g x).
Proof. exact (@lem4398044 A B s f g x h1 (@lem4397995 A B s f g x h2)). Qed.
Lemma lem4398048 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) (h2 : term100 A B s f g x) : term288 A B f g x.
Proof. exact (fun h0 : term96 A B f g x => @lem4398047 A B s f g x h1 h2). Qed.
Lemma lem4398050 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4398051 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term288 A B f g x) = ((f x) = (g x)).
Proof. exact (@lem4398050 ((f x) = (g x))). Qed.
Lemma lem4398052 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) (h2 : term100 A B s f g x) : (f x) = (g x).
Proof. exact (EQ_MP (@lem4398051 A B f g x) (@lem4398048 A B s f g x h1 h2)). Qed.
Lemma lem4398055 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4398057 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term96 A B f g x) = (term289 A B f g x).
Proof. exact (@lem4398055 ((f x) = (g x))). Qed.
Lemma lem4398060 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : term289 A B f g x.
Proof. exact (EQ_MP (@lem4398057 A B f g x) (@lem4397800 A B s f g x h1)). Qed.
Lemma lem4398063 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) (h2 : term100 A B s f g x) : False.
Proof. exact (@lem4398060 A B s f g x h2 (@lem4398052 A B s f g x h1 h2)). Qed.
Lemma lem4398064 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) (h2 : term100 A B s f g x) : term280.
Proof. exact (fun h0 : ~ False => @lem4398063 A B s f g x h1 h2). Qed.
Lemma lem4398066 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4398067 : term280 = False.
Proof. exact (@lem4398066 False). Qed.
Lemma lem4398068 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) (h2 : term100 A B s f g x) : False.
Proof. exact (EQ_MP (@lem4398067) (@lem4398064 A B s f g x h1 h2)). Qed.
Lemma lem4398111 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : @IN A x s.
Proof. exact (proj1 (@lem4397603 A B s f g x h1)). Qed.
Lemma lem4398112 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : term281 A x s.
Proof. exact (fun h0 : term102 A x s => @lem4398111 A B s f g x h1). Qed.
Lemma lem4398114 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4398115 {A : Type'} (x : A) (s : A -> Prop) : (term281 A x s) = (@IN A x s).
Proof. exact (@lem4398114 (@IN A x s)). Qed.
Lemma lem4398116 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : @IN A x s.
Proof. exact (EQ_MP (@lem4398115 A x s) (@lem4398112 A B s f g x h1)). Qed.
Lemma lem4398122 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4398123 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) (s : A -> Prop) : (term110 A B s f g _50258) = (term282 A B f g _50258 s).
Proof. exact (@lem4398122 ((f _50258) = (g _50258)) (term102 A _50258 s)). Qed.
Lemma lem4398131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4398132 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) (s : A -> Prop) : (term283 A B s f g _50258) = (term284 A B f g _50258 s).
Proof. exact (MK_COMB (@lem4398131) (@lem4398123 A B f g _50258 s)). Qed.
Lemma lem4398140 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) (s : A -> Prop) : (term282 A B f g _50258 s) = (term282 A B f g _50258 s).
Proof. exact (eq_refl (term282 A B f g _50258 s)). Qed.
Lemma lem4398141 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) (s : A -> Prop) : ((term110 A B s f g _50258) = (term282 A B f g _50258 s)) = ((term282 A B f g _50258 s) = (term282 A B f g _50258 s)).
Proof. exact (MK_COMB (@lem4398132 A B f g _50258 s) (@lem4398140 A B f g _50258 s)). Qed.
Lemma lem4398143 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4398144 (x : Prop) : (x = x) = True.
Proof. exact (@lem4398143 Prop x). Qed.
Lemma lem4398145 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) (s : A -> Prop) : ((term282 A B f g _50258 s) = (term282 A B f g _50258 s)) = True.
Proof. exact (@lem4398144 (term282 A B f g _50258 s)). Qed.
Lemma lem4398146 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) (s : A -> Prop) : ((term110 A B s f g _50258) = (term282 A B f g _50258 s)) = True.
Proof. exact (TRANS (@lem4398141 A B f g _50258 s) (@lem4398145 A B f g _50258 s)). Qed.
Lemma lem4398147 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) (s : A -> Prop) : True = ((term110 A B s f g _50258) = (term282 A B f g _50258 s)).
Proof. exact (SYM (@lem4398146 A B f g _50258 s)). Qed.
Lemma lem4398148 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) (s : A -> Prop) : (term110 A B s f g _50258) = (term282 A B f g _50258 s).
Proof. exact (EQ_MP (@lem4398147 A B f g _50258 s) (@lem0)). Qed.
Lemma lem4398149 {A B : Type'} (_50258 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term282 A B f g _50258 s.
Proof. exact (EQ_MP (@lem4398148 A B f g _50258 s) (@lem4397812 A B _50258 x s f g h1)). Qed.
Lemma lem4398151 (b : Prop) (a : Prop) : (a \/ b) = (term276 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4398152 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50258 : A) : (term282 A B f g _50258 s) = (term285 A B s f g _50258).
Proof. exact (@lem4398151 (term102 A _50258 s) ((f _50258) = (g _50258))). Qed.
Lemma lem4398154 (a : Prop) : (term67 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4398155 {A : Type'} (_50258 : A) (s : A -> Prop) : (term95 A _50258 s) = (@IN A _50258 s).
Proof. exact (@lem4398154 (@IN A _50258 s)). Qed.
Lemma lem4398156 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4398157 {A : Type'} (_50258 : A) (s : A -> Prop) : (term286 A _50258 s) = (term287 A _50258 s).
Proof. exact (MK_COMB (@lem4398156) (@lem4398155 A _50258 s)). Qed.
Lemma lem4398158 {A B : Type'} (f : A -> B) (g : A -> B) (_50258 : A) : ((f _50258) = (g _50258)) = ((f _50258) = (g _50258)).
Proof. exact (eq_refl ((f _50258) = (g _50258))). Qed.
Lemma lem4398159 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50258 : A) : (term285 A B s f g _50258) = (term68 A B s f g _50258).
Proof. exact (MK_COMB (@lem4398157 A _50258 s) (@lem4398158 A B f g _50258)). Qed.
Lemma lem4398160 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50258 : A) : (term282 A B f g _50258 s) = (term68 A B s f g _50258).
Proof. exact (TRANS (@lem4398152 A B s f g _50258) (@lem4398159 A B s f g _50258)). Qed.
Lemma lem4398163 {A B : Type'} (_50258 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term68 A B s f g _50258.
Proof. exact (EQ_MP (@lem4398160 A B s f g _50258) (@lem4398149 A B _50258 x s f g h1)). Qed.
Lemma lem4398164 {A B : Type'} (_50258 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term68 A B s f g _50258.
Proof. exact (@lem4398163 A B _50258 x s f g h1). Qed.
Lemma lem4398165 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term68 A B s f g x.
Proof. exact (@lem4398164 A B x x s f g h1). Qed.
Lemma lem4398168 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term100 A B s f g x) (h2 : term247 A B x s f g) : (f x) = (g x).
Proof. exact (@lem4398165 A B x s f g h2 (@lem4398116 A B s f g x h1)). Qed.
Lemma lem4398169 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term100 A B s f g x) (h2 : term247 A B x s f g) : term288 A B f g x.
Proof. exact (fun h0 : term96 A B f g x => @lem4398168 A B x s f g h1 h2). Qed.
Lemma lem4398171 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4398172 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term288 A B f g x) = ((f x) = (g x)).
Proof. exact (@lem4398171 ((f x) = (g x))). Qed.
Lemma lem4398173 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term100 A B s f g x) (h2 : term247 A B x s f g) : (f x) = (g x).
Proof. exact (EQ_MP (@lem4398172 A B f g x) (@lem4398169 A B x s f g h1 h2)). Qed.
Lemma lem4398176 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4398178 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term96 A B f g x) = (term289 A B f g x).
Proof. exact (@lem4398176 ((f x) = (g x))). Qed.
Lemma lem4398181 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term100 A B s f g x) : term289 A B f g x.
Proof. exact (EQ_MP (@lem4398178 A B f g x) (@lem4397816 A B s f g x h1)). Qed.
Lemma lem4398184 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term100 A B s f g x) (h2 : term247 A B x s f g) : False.
Proof. exact (@lem4398181 A B s f g x h1 (@lem4398173 A B x s f g h1 h2)). Qed.
Lemma lem4398185 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term100 A B s f g x) (h2 : term247 A B x s f g) : term280.
Proof. exact (fun h0 : ~ False => @lem4398184 A B x s f g h1 h2). Qed.
Lemma lem4398187 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4398188 : term280 = False.
Proof. exact (@lem4398187 False). Qed.
Lemma lem4398189 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term100 A B s f g x) (h2 : term247 A B x s f g) : False.
Proof. exact (EQ_MP (@lem4398188) (@lem4398185 A B x s f g h1 h2)). Qed.
Lemma lem4398232 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term102 A x s.
Proof. exact (proj1 (@lem4397604 A B s f x h1)). Qed.
Lemma lem4398233 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term271 A x s.
Proof. exact (fun h0 : @IN A x s => @lem4398232 A B s f x h1). Qed.
Lemma lem4398235 (p : Prop) : (term272 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4398236 {A : Type'} (x : A) (s : A -> Prop) : (term271 A x s) = (term102 A x s).
Proof. exact (@lem4398235 (@IN A x s)). Qed.
Lemma lem4398237 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term102 A x s.
Proof. exact (EQ_MP (@lem4398236 A x s) (@lem4398233 A B s f x h1)). Qed.
Lemma lem4398243 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4398244 {A B : Type'} (f : A -> B) (_50259 : A) (s : A -> Prop) : (term111 A B s f _50259) = (term273 A B f _50259 s).
Proof. exact (@lem4398243 ((f _50259) = (@ARB B)) (@IN A _50259 s)). Qed.
Lemma lem4398252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4398253 {A B : Type'} (f : A -> B) (_50259 : A) (s : A -> Prop) : (term274 A B s f _50259) = (term275 A B f _50259 s).
Proof. exact (MK_COMB (@lem4398252) (@lem4398244 A B f _50259 s)). Qed.
Lemma lem4398261 {A B : Type'} (f : A -> B) (_50259 : A) (s : A -> Prop) : (term273 A B f _50259 s) = (term273 A B f _50259 s).
Proof. exact (eq_refl (term273 A B f _50259 s)). Qed.
Lemma lem4398262 {A B : Type'} (f : A -> B) (_50259 : A) (s : A -> Prop) : ((term111 A B s f _50259) = (term273 A B f _50259 s)) = ((term273 A B f _50259 s) = (term273 A B f _50259 s)).
Proof. exact (MK_COMB (@lem4398253 A B f _50259 s) (@lem4398261 A B f _50259 s)). Qed.
Lemma lem4398264 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4398265 (x : Prop) : (x = x) = True.
Proof. exact (@lem4398264 Prop x). Qed.
Lemma lem4398266 {A B : Type'} (f : A -> B) (_50259 : A) (s : A -> Prop) : ((term273 A B f _50259 s) = (term273 A B f _50259 s)) = True.
Proof. exact (@lem4398265 (term273 A B f _50259 s)). Qed.
Lemma lem4398267 {A B : Type'} (f : A -> B) (_50259 : A) (s : A -> Prop) : ((term111 A B s f _50259) = (term273 A B f _50259 s)) = True.
Proof. exact (TRANS (@lem4398262 A B f _50259 s) (@lem4398266 A B f _50259 s)). Qed.
Lemma lem4398268 {A B : Type'} (f : A -> B) (_50259 : A) (s : A -> Prop) : True = ((term111 A B s f _50259) = (term273 A B f _50259 s)).
Proof. exact (SYM (@lem4398267 A B f _50259 s)). Qed.
Lemma lem4398269 {A B : Type'} (f : A -> B) (_50259 : A) (s : A -> Prop) : (term111 A B s f _50259) = (term273 A B f _50259 s).
Proof. exact (EQ_MP (@lem4398268 A B f _50259 s) (@lem0)). Qed.
Lemma lem4398270 {A B : Type'} (_50259 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term273 A B f _50259 s.
Proof. exact (EQ_MP (@lem4398269 A B f _50259 s) (@lem4397822 A B _50259 x s f g h1)). Qed.
Lemma lem4398272 (b : Prop) (a : Prop) : (a \/ b) = (term276 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4398275 {A B : Type'} (s : A -> Prop) (f : A -> B) (_50259 : A) : (term273 A B f _50259 s) = (term70 A B s f _50259).
Proof. exact (@lem4398272 (@IN A _50259 s) ((f _50259) = (@ARB B))). Qed.
Lemma lem4398278 {A B : Type'} (_50259 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term70 A B s f _50259.
Proof. exact (EQ_MP (@lem4398275 A B s f _50259) (@lem4398270 A B _50259 x s f g h1)). Qed.
Lemma lem4398279 {A B : Type'} (_50259 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term70 A B s f _50259.
Proof. exact (@lem4398278 A B _50259 x s f g h1). Qed.
Lemma lem4398280 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : term70 A B s f x.
Proof. exact (@lem4398279 A B x x s f g h1). Qed.
Lemma lem4398283 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term104 A B s f x) (h2 : term247 A B x s f g) : (f x) = (@ARB B).
Proof. exact (@lem4398280 A B x s f g h2 (@lem4398237 A B s f x h1)). Qed.
Lemma lem4398284 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term104 A B s f x) (h2 : term247 A B x s f g) : term277 A B f x.
Proof. exact (fun h0 : term270 A B f x => @lem4398283 A B x s f g h1 h2). Qed.
Lemma lem4398286 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4398287 {A B : Type'} (f : A -> B) (x : A) : (term277 A B f x) = ((f x) = (@ARB B)).
Proof. exact (@lem4398286 ((f x) = (@ARB B))). Qed.
Lemma lem4398288 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term104 A B s f x) (h2 : term247 A B x s f g) : (f x) = (@ARB B).
Proof. exact (EQ_MP (@lem4398287 A B f x) (@lem4398284 A B x s f g h1 h2)). Qed.
Lemma lem4398291 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4398293 {A B : Type'} (f : A -> B) (x : A) : (term270 A B f x) = (term279 A B f x).
Proof. exact (@lem4398291 ((f x) = (@ARB B))). Qed.
Lemma lem4398296 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term104 A B s f x) : term279 A B f x.
Proof. exact (EQ_MP (@lem4398293 A B f x) (@lem4397832 A B s f x h1)). Qed.
Lemma lem4398299 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term104 A B s f x) (h2 : term247 A B x s f g) : False.
Proof. exact (@lem4398296 A B s f x h1 (@lem4398288 A B x s f g h1 h2)). Qed.
Lemma lem4398300 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term104 A B s f x) (h2 : term247 A B x s f g) : term280.
Proof. exact (fun h0 : ~ False => @lem4398299 A B x s f g h1 h2). Qed.
Lemma lem4398302 (p : Prop) : (term278 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4398303 : term280 = False.
Proof. exact (@lem4398302 False). Qed.
Lemma lem4398304 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term104 A B s f x) (h2 : term247 A B x s f g) : False.
Proof. exact (EQ_MP (@lem4398303) (@lem4398300 A B x s f g h1 h2)). Qed.
Lemma lem4398305 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term247 A B x s f g) : False.
Proof. exact (or_elim (@lem4397600 A B x s f g h1) (fun h0 : term100 A B s f g x => @lem4398189 A B x s f g h0 h1) (fun h0 : term104 A B s f x => @lem4398304 A B x s f g h0 h1)). Qed.
Lemma lem4398306 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term227 A B s f g x) : False.
Proof. exact (or_elim (@lem4397589 A B s f g x h1) (fun h0 : term104 A B s f x => @lem4397947 A B s f g x h0 h1) (fun h0 : term100 A B s f g x => @lem4398068 A B s f g x h1 h0)). Qed.
Lemma lem4398307 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term266 A B x s f g) : False.
Proof. exact (or_elim (@lem4397586 A B x s f g h1) (fun h0 : term227 A B s f g x => @lem4398306 A B s f g x h0) (fun h0 : term247 A B x s f g => @lem4398305 A B x s f g h0)). Qed.
Lemma lem4398308 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term266 A B x s f g) : (term266 A B x s f g) = False.
Proof. exact (prop_ext (fun h2 : term266 A B x s f g => @lem4398307 A B x s f g h1) (fun h2 : False => @lem4397586 A B x s f g h1)). Qed.
Lemma lem4398309 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term266 A B x s f g) : False.
Proof. exact (EQ_MP (@lem4398308 A B x s f g h1) (@lem4397586 A B x s f g h1)). Qed.
Lemma lem4398310 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term94 A B s f g) : False.
Proof. exact (ex_elim (@lem4397407 A B s f g h1) (fun x : A => fun h0 : term268 A B s f g x => @lem4398309 A B x s f g h0)). Qed.
Lemma lem4398311 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term94 A B s f g) : (term94 A B s f g) = False.
Proof. exact (prop_ext (fun h2 : term94 A B s f g => @lem4398310 A B s f g h1) (fun h2 : False => @lem4396696 A B s f g h1)). Qed.
Lemma lem4398312 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term94 A B s f g) : False.
Proof. exact (EQ_MP (@lem4398311 A B s f g h1) (@lem4396696 A B s f g h1)). Qed.
Lemma lem4398313 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term93 A B s f g.
Proof. exact (fun h0 : term94 A B s f g => @lem4398312 A B s f g h0). Qed.
Lemma lem4398314 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term85 A B g s f) = (term47 A B s f g).
Proof. exact (EQ_MP (@lem4396695 A B s f g) (@lem4398313 A B s f g)). Qed.
Lemma lem4398319 {A B : Type'} (s : A -> Prop) (f : A -> B) : term88 A B s f.
Proof. exact (fun g : A -> B => @lem4398314 A B s f g). Qed.
Lemma lem4398324 {A B : Type'} (s : A -> Prop) : term90 A B s.
Proof. exact (fun f : A -> B => @lem4398319 A B s f). Qed.
Lemma lem4398329 {A B : Type'} : term92 A B.
Proof. exact (fun s : A -> Prop => @lem4398324 A B s). Qed.
Lemma lem4398330 {A B : Type'} : term61 A B.
Proof. exact (EQ_MP (@lem4396691 A B) (@lem4398329 A B)). Qed.
Lemma lem4398332 {A B : Type'} : term61 A B.
Proof. exact (@lem4396487 A B (@lem4398330 A B)). Qed.
Lemma lem4398333 {A B : Type'} (h1 : term62 A B) : False.
Proof. exact (@lem4398332 A B (@lem4396471 A B h1)). Qed.
Lemma lem4398334 {A B : Type'} (h1 : term62 A B) : (term62 A B) = False.
Proof. exact (prop_ext (fun h2 : term62 A B => @lem4398333 A B h1) (fun h2 : False => @lem4396471 A B h1)). Qed.
Lemma lem4398335 {A B : Type'} (h1 : term62 A B) : False.
Proof. exact (EQ_MP (@lem4398334 A B h1) (@lem4396471 A B h1)). Qed.
Lemma lem4398336 {A B : Type'} : term61 A B.
Proof. exact (fun h0 : term62 A B => @lem4398335 A B h0). Qed.
Lemma lem4398337 {A B : Type'} : term59 A B.
Proof. exact (EQ_MP (@lem4396470 A B) (@lem4398336 A B)). Qed.
Lemma lem4398338 {A B : Type'} : term58 A B.
Proof. exact (EQ_MP (@lem4396466 A B) (@lem4398337 A B)). Qed.
