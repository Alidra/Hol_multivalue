Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_ADD_term_abbrevs.
Require Import ITERATE_OP_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6930331 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6930333 {_122572 _122573 : Type'} (op : type1400 _122573) : term0 _122572 _122573 op.
Proof. exact (@lem6013661 _122572 _122573 op). Qed.
Lemma lem6930334 {_122572 _122573 : Type'} (op : type1400 _122573) : (term0 _122572 _122573 op) = (term1 _122572 _122573 op).
Proof. exact (eq_refl (term0 _122572 _122573 op)). Qed.
Lemma lem6930335 {_122572 _122573 : Type'} (op : type1400 _122573) : term1 _122572 _122573 op.
Proof. exact (EQ_MP (@lem6930334 _122572 _122573 op) (@lem6930333 _122572 _122573 op)). Qed.
Lemma lem6930336 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (h1). Qed.
Lemma lem6930337 {_122572 _122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : term2 _122572 _122573 op.
Proof. exact (@lem6930335 _122572 _122573 op (@lem6930336 _122573 op h1)). Qed.
Lemma lem6930338 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term3 _122572 _122573 op f.
Proof. exact (@lem6930337 _122572 _122573 op h1 f). Qed.
Lemma lem6930339 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) : (term3 _122572 _122573 op f) = (term4 _122572 _122573 f op).
Proof. exact (eq_refl (term3 _122572 _122573 op f)). Qed.
Lemma lem6930340 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term4 _122572 _122573 f op.
Proof. exact (EQ_MP (@lem6930339 _122572 _122573 f op) (@lem6930338 _122572 _122573 f op h1)). Qed.
Lemma lem6930341 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term5 _122572 _122573 f op g.
Proof. exact (@lem6930340 _122572 _122573 f op h1 g). Qed.
Lemma lem6930342 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term5 _122572 _122573 f op g) = (term6 _122572 _122573 f op g).
Proof. exact (eq_refl (term5 _122572 _122573 f op g)). Qed.
Lemma lem6930343 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term6 _122572 _122573 f op g.
Proof. exact (EQ_MP (@lem6930342 _122572 _122573 f op g) (@lem6930341 _122572 _122573 f g op h1)). Qed.
Lemma lem6930344 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term7 _122572 _122573 f op g s.
Proof. exact (@lem6930343 _122572 _122573 f g op h1 s). Qed.
Lemma lem6930345 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term7 _122572 _122573 f op g s) = (term8 _122572 _122573 f op s g).
Proof. exact (eq_refl (term7 _122572 _122573 f op g s)). Qed.
Lemma lem6930346 {_122572 _122573 : Type'} (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term8 _122572 _122573 f op s g.
Proof. exact (EQ_MP (@lem6930345 _122572 _122573 f op s g) (@lem6930344 _122572 _122573 f g s op h1)). Qed.
Lemma lem6930347 {_122572 : Type'} (s : _122572 -> Prop) (h1 : @FINITE _122572 s) : @FINITE _122572 s.
Proof. exact (h1). Qed.
Lemma lem6930348 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @FINITE _122572 s) (h2 : @monoidal _122573 op) : (term9 _122572 _122573 s op f g) = (term10 _122572 _122573 f op s g).
Proof. exact (@lem6930346 _122572 _122573 f s g op h2 (@lem6930347 _122572 s h1)). Qed.
Lemma lem6930349 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (h1 : @FINITE _122572 s) : term11 _122572 _122573 f op s g.
Proof. exact (fun h0 : @monoidal _122573 op => @lem6930348 _122572 _122573 f g s op h1 h0). Qed.
Lemma lem6930350 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term12 _122572 _122573 f op s g.
Proof. exact (fun h0 : @FINITE _122572 s => @lem6930349 _122572 _122573 f op g s h0). Qed.
Lemma lem6930352 (p : Prop) (q : Prop) (r : Prop) : (term13 p q r) = (term14 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6930357 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term12 _122572 _122573 f op s g) = (term15 _122572 _122573 f op s g).
Proof. exact (@lem6930352 (@FINITE _122572 s) (@monoidal _122573 op) ((term9 _122572 _122573 s op f g) = (term10 _122572 _122573 f op s g))). Qed.
Lemma lem6930374 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6930375 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem6930374 p q p' q'). Qed.
Lemma lem6930376 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem6930375 p q p'). Qed.
Lemma lem6930377 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : term19 _126729 f s g.
Proof. exact (@lem6930376 (@FINITE _126729 s) ((term20 _126729 s f g) = (term21 _126729 f s g))). Qed.
Lemma lem6930378 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) (p' : Prop) : term22 _126729 f s g p'.
Proof. exact (@lem6930377 _126729 f s g p'). Qed.
Lemma lem6930379 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) (p' : Prop) : (term22 _126729 f s g p') = (term23 _126729 f s g p').
Proof. exact (eq_refl (term22 _126729 f s g p')). Qed.
Lemma lem6930380 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) (p' : Prop) : term23 _126729 f s g p'.
Proof. exact (EQ_MP (@lem6930379 _126729 f s g p') (@lem6930378 _126729 f s g p')). Qed.
Lemma lem6930381 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) (p' : Prop) (q' : Prop) : term24 _126729 f s g p' q'.
Proof. exact (@lem6930380 _126729 f s g p' q'). Qed.
Lemma lem6930382 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) (p' : Prop) (q' : Prop) : (term24 _126729 f s g p' q') = (term25 _126729 f s g p' q').
Proof. exact (eq_refl (term24 _126729 f s g p' q')). Qed.
Lemma lem6930383 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) (p' : Prop) (q' : Prop) : term25 _126729 f s g p' q'.
Proof. exact (EQ_MP (@lem6930382 _126729 f s g p' q') (@lem6930381 _126729 f s g p' q')). Qed.
Lemma lem6930384 {_126729 : Type'} (s : _126729 -> Prop) : (@FINITE _126729 s) = (@FINITE _126729 s).
Proof. exact (eq_refl (@FINITE _126729 s)). Qed.
Lemma lem6930385 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (q' : Prop) : term26 _126729 f g s q'.
Proof. exact (@lem6930383 _126729 f s g (@FINITE _126729 s) q'). Qed.
Lemma lem6930386 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (q' : Prop) : term27 _126729 f g s q'.
Proof. exact (@lem6930385 _126729 f g s q' (@lem6930384 _126729 s)). Qed.
Lemma lem6930387 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : @FINITE _126729 s.
Proof. exact (h1). Qed.
Lemma lem6930388 {_126729 : Type'} (s : _126729 -> Prop) : (@FINITE _126729 s) = ((@FINITE _126729 s) = True).
Proof. exact (@lem7 (@FINITE _126729 s)). Qed.
Lemma lem6930393 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930394 {_126729 : Type'} : (@nsum _126729) = (@iterate nat _126729 Nat.add).
Proof. exact (@lem6930393 _126729). Qed.
Lemma lem6930395 {_126729 : Type'} (s : _126729 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930396 {_126729 : Type'} (s : _126729 -> Prop) : (@nsum _126729 s) = (@iterate nat _126729 Nat.add s).
Proof. exact (MK_COMB (@lem6930394 _126729) (@lem6930395 _126729 s)). Qed.
Lemma lem6930397 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : (term28 _126729 f g) = (term28 _126729 f g).
Proof. exact (eq_refl (term28 _126729 f g)). Qed.
Lemma lem6930398 {_126729 : Type'} (s : _126729 -> Prop) (f : _126729 -> nat) (g : _126729 -> nat) : (term20 _126729 s f g) = (term29 _126729 s f g).
Proof. exact (MK_COMB (@lem6930396 _126729 s) (@lem6930397 _126729 f g)). Qed.
Lemma lem6930400 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term15 _122572 _122573 f op s g.
Proof. exact (EQ_MP (@lem6930357 _122572 _122573 f op s g) (@lem6930350 _122572 _122573 f op s g)). Qed.
Lemma lem6930401 {_126729 : Type'} (f : _126729 -> nat) (op : type1606) (s : _126729 -> Prop) (g : _126729 -> nat) : term30 _126729 f op s g.
Proof. exact (@lem6930400 _126729 nat f op s g). Qed.
Lemma lem6930402 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : term31 _126729 f s g.
Proof. exact (@lem6930401 _126729 f Nat.add s g). Qed.
Lemma lem6930406 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (@FINITE _126729 s) = True.
Proof. exact (EQ_MP (@lem6930388 _126729 s) (@lem6930387 _126729 s h1)). Qed.
Lemma lem6930407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6930408 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (term32 _126729 s) = (and True).
Proof. exact (MK_COMB (@lem6930407) (@lem6930406 _126729 s h1)). Qed.
Lemma lem6930410 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6930331) (@lem6924403)). Qed.
Lemma lem6930411 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (term33 _126729 s) = (True /\ True).
Proof. exact (MK_COMB (@lem6930408 _126729 s h1) (@lem6930410)). Qed.
Lemma lem6930413 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6930414 : (True /\ True) = True.
Proof. exact (@lem6930413 True). Qed.
Lemma lem6930415 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (term33 _126729 s) = True.
Proof. exact (TRANS (@lem6930411 _126729 s h1) (@lem6930414)). Qed.
Lemma lem6930416 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : True = (term33 _126729 s).
Proof. exact (SYM (@lem6930415 _126729 s h1)). Qed.
Lemma lem6930417 {_126729 : Type'} (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : term33 _126729 s.
Proof. exact (EQ_MP (@lem6930416 _126729 s h1) (@lem0)). Qed.
Lemma lem6930418 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (term29 _126729 s f g) = (term34 _126729 f s g).
Proof. exact (@lem6930402 _126729 f s g (@lem6930417 _126729 s h1)). Qed.
Lemma lem6930419 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (term20 _126729 s f g) = (term34 _126729 f s g).
Proof. exact (TRANS (@lem6930398 _126729 s f g) (@lem6930418 _126729 f g s h1)). Qed.
Lemma lem6930420 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6930421 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : (term35 _126729 s f g) = (term36 _126729 f s g).
Proof. exact (MK_COMB (@lem6930420) (@lem6930419 _126729 f g s h1)). Qed.
Lemma lem6930423 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930424 {_126729 : Type'} : (@nsum _126729) = (@iterate nat _126729 Nat.add).
Proof. exact (@lem6930423 _126729). Qed.
Lemma lem6930425 {_126729 : Type'} (s : _126729 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930426 {_126729 : Type'} (s : _126729 -> Prop) : (@nsum _126729 s) = (@iterate nat _126729 Nat.add s).
Proof. exact (MK_COMB (@lem6930424 _126729) (@lem6930425 _126729 s)). Qed.
Lemma lem6930427 {_126729 : Type'} (f : _126729 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930428 {_126729 : Type'} (s : _126729 -> Prop) (f : _126729 -> nat) : (@nsum _126729 s f) = (@iterate nat _126729 Nat.add s f).
Proof. exact (MK_COMB (@lem6930426 _126729 s) (@lem6930427 _126729 f)). Qed.
Lemma lem6930429 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6930430 {_126729 : Type'} (s : _126729 -> Prop) (f : _126729 -> nat) : (term37 _126729 s f) = (term38 _126729 s f).
Proof. exact (MK_COMB (@lem6930429) (@lem6930428 _126729 s f)). Qed.
Lemma lem6930432 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930433 {_126729 : Type'} : (@nsum _126729) = (@iterate nat _126729 Nat.add).
Proof. exact (@lem6930432 _126729). Qed.
Lemma lem6930434 {_126729 : Type'} (s : _126729 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930435 {_126729 : Type'} (s : _126729 -> Prop) : (@nsum _126729 s) = (@iterate nat _126729 Nat.add s).
Proof. exact (MK_COMB (@lem6930433 _126729) (@lem6930434 _126729 s)). Qed.
Lemma lem6930436 {_126729 : Type'} (g : _126729 -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6930437 {_126729 : Type'} (s : _126729 -> Prop) (g : _126729 -> nat) : (@nsum _126729 s g) = (@iterate nat _126729 Nat.add s g).
Proof. exact (MK_COMB (@lem6930435 _126729 s) (@lem6930436 _126729 g)). Qed.
Lemma lem6930438 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : (term21 _126729 f s g) = (term34 _126729 f s g).
Proof. exact (MK_COMB (@lem6930430 _126729 s f) (@lem6930437 _126729 s g)). Qed.
Lemma lem6930439 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : ((term20 _126729 s f g) = (term21 _126729 f s g)) = ((term34 _126729 f s g) = (term34 _126729 f s g)).
Proof. exact (MK_COMB (@lem6930421 _126729 f g s h1) (@lem6930438 _126729 f s g)). Qed.
Lemma lem6930441 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6930442 (x : nat) : (x = x) = True.
Proof. exact (@lem6930441 nat x). Qed.
Lemma lem6930443 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : ((term34 _126729 f s g) = (term34 _126729 f s g)) = True.
Proof. exact (@lem6930442 (term34 _126729 f s g)). Qed.
Lemma lem6930444 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) (h1 : @FINITE _126729 s) : ((term20 _126729 s f g) = (term21 _126729 f s g)) = True.
Proof. exact (TRANS (@lem6930439 _126729 f g s h1) (@lem6930443 _126729 f s g)). Qed.
Lemma lem6930445 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : term39 _126729 f s g.
Proof. exact (fun h0 : @FINITE _126729 s => @lem6930444 _126729 f g s h0). Qed.
Lemma lem6930446 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) : term40 _126729 f g s.
Proof. exact (@lem6930386 _126729 f g s True). Qed.
Lemma lem6930447 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) (s : _126729 -> Prop) : (term41 _126729 f s g) = (term42 _126729 s).
Proof. exact (@lem6930446 _126729 f g s (@lem6930445 _126729 f s g)). Qed.
Lemma lem6930449 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6930450 {_126729 : Type'} (s : _126729 -> Prop) : (term42 _126729 s) = True.
Proof. exact (@lem6930449 (@FINITE _126729 s)). Qed.
Lemma lem6930451 {_126729 : Type'} (f : _126729 -> nat) (s : _126729 -> Prop) (g : _126729 -> nat) : (term41 _126729 f s g) = True.
Proof. exact (TRANS (@lem6930447 _126729 f g s) (@lem6930450 _126729 s)). Qed.
Lemma lem6930452 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : (term43 _126729 f g) = (term44 _126729).
Proof. exact (fun_ext (fun s : _126729 -> Prop => @lem6930451 _126729 f s g)). Qed.
Lemma lem6930453 {_126729 : Type'} : (@all (_126729 -> Prop)) = (@all (_126729 -> Prop)).
Proof. exact (eq_refl (@all (_126729 -> Prop))). Qed.
Lemma lem6930454 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : (term45 _126729 f g) = (term46 _126729).
Proof. exact (MK_COMB (@lem6930453 _126729) (@lem6930452 _126729 f g)). Qed.
Lemma lem6930456 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6930457 {_126729 : Type'} (t : Prop) : (term48 _126729 t) = t.
Proof. exact (@lem6930456 (_126729 -> Prop) t). Qed.
Lemma lem6930458 {_126729 : Type'} : (term46 _126729) = True.
Proof. exact (@lem6930457 _126729 True). Qed.
Lemma lem6930459 {_126729 : Type'} (f : _126729 -> nat) (g : _126729 -> nat) : (term45 _126729 f g) = True.
Proof. exact (TRANS (@lem6930454 _126729 f g) (@lem6930458 _126729)). Qed.
Lemma lem6930460 {_126729 : Type'} (f : _126729 -> nat) : (term49 _126729 f) = (term50 _126729).
Proof. exact (fun_ext (fun g : _126729 -> nat => @lem6930459 _126729 f g)). Qed.
Lemma lem6930461 {_126729 : Type'} : (@all (_126729 -> nat)) = (@all (_126729 -> nat)).
Proof. exact (eq_refl (@all (_126729 -> nat))). Qed.
Lemma lem6930462 {_126729 : Type'} (f : _126729 -> nat) : (term51 _126729 f) = (term52 _126729).
Proof. exact (MK_COMB (@lem6930461 _126729) (@lem6930460 _126729 f)). Qed.
Lemma lem6930464 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6930465 {_126729 : Type'} (t : Prop) : (term53 _126729 t) = t.
Proof. exact (@lem6930464 (_126729 -> nat) t). Qed.
Lemma lem6930466 {_126729 : Type'} : (term52 _126729) = True.
Proof. exact (@lem6930465 _126729 True). Qed.
Lemma lem6930467 {_126729 : Type'} (f : _126729 -> nat) : (term51 _126729 f) = True.
Proof. exact (TRANS (@lem6930462 _126729 f) (@lem6930466 _126729)). Qed.
Lemma lem6930468 {_126729 : Type'} : (term54 _126729) = (term50 _126729).
Proof. exact (fun_ext (fun f : _126729 -> nat => @lem6930467 _126729 f)). Qed.
Lemma lem6930469 {_126729 : Type'} : (@all (_126729 -> nat)) = (@all (_126729 -> nat)).
Proof. exact (eq_refl (@all (_126729 -> nat))). Qed.
Lemma lem6930470 {_126729 : Type'} : (term55 _126729) = (term52 _126729).
Proof. exact (MK_COMB (@lem6930469 _126729) (@lem6930468 _126729)). Qed.
Lemma lem6930472 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6930473 {_126729 : Type'} (t : Prop) : (term53 _126729 t) = t.
Proof. exact (@lem6930472 (_126729 -> nat) t). Qed.
Lemma lem6930474 {_126729 : Type'} : (term52 _126729) = True.
Proof. exact (@lem6930473 _126729 True). Qed.
Lemma lem6930475 {_126729 : Type'} : (term55 _126729) = True.
Proof. exact (TRANS (@lem6930470 _126729) (@lem6930474 _126729)). Qed.
Lemma lem6930476 {_126729 : Type'} : True = (term55 _126729).
Proof. exact (SYM (@lem6930475 _126729)). Qed.
Lemma lem6930477 {_126729 : Type'} : term55 _126729.
Proof. exact (EQ_MP (@lem6930476 _126729) (@lem0)). Qed.
