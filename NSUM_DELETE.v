Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_DELETE_term_abbrevs.
Require Import ITERATE_DELETE_spec.
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
Lemma lem6960119 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6960121 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem5824997 A B op). Qed.
Lemma lem6960122 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem6960123 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem6960122 A B op) (@lem6960121 A B op)). Qed.
Lemma lem6960124 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6960125 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term2 A B op.
Proof. exact (@lem6960123 A B op (@lem6960124 B op h1)). Qed.
Lemma lem6960126 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term3 A B op f.
Proof. exact (@lem6960125 A B op h1 f). Qed.
Lemma lem6960127 {A B : Type'} (op : type1400 B) (f : A -> B) : (term3 A B op f) = (term4 A B op f).
Proof. exact (eq_refl (term3 A B op f)). Qed.
Lemma lem6960128 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term4 A B op f.
Proof. exact (EQ_MP (@lem6960127 A B op f) (@lem6960126 A B f op h1)). Qed.
Lemma lem6960129 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term5 A B op f s.
Proof. exact (@lem6960128 A B f op h1 s). Qed.
Lemma lem6960130 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term5 A B op f s) = (term6 A B op s f).
Proof. exact (eq_refl (term5 A B op f s)). Qed.
Lemma lem6960131 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term6 A B op s f.
Proof. exact (EQ_MP (@lem6960130 A B op s f) (@lem6960129 A B f s op h1)). Qed.
Lemma lem6960132 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) (op : type1400 B) (h1 : @monoidal B op) : term7 A B op s f a.
Proof. exact (@lem6960131 A B s f op h1 a). Qed.
Lemma lem6960133 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term7 A B op s f a) = (term8 A B a op s f).
Proof. exact (eq_refl (term7 A B op s f a)). Qed.
Lemma lem6960134 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term8 A B a op s f.
Proof. exact (EQ_MP (@lem6960133 A B a op s f) (@lem6960132 A B s f a op h1)). Qed.
Lemma lem6960135 {A : Type'} (a : A) (s : A -> Prop) (h1 : term9 A a s) : term9 A a s.
Proof. exact (h1). Qed.
Lemma lem6960136 {A B : Type'} (f : A -> B) (op : type1400 B) (a : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term9 A a s) : (term10 A B op s a f) = (@iterate B A op s f).
Proof. exact (@lem6960134 A B a s f op h1 (@lem6960135 A a s h2)). Qed.
Lemma lem6960137 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term8 A B a op s f.
Proof. exact (fun h0 : term9 A a s => @lem6960136 A B f op a s h1 h0). Qed.
Lemma lem6960138 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term11 A B a op s f.
Proof. exact (fun h0 : @monoidal B op => @lem6960137 A B a s f op h0). Qed.
Lemma lem6960140 (p : Prop) (q : Prop) (r : Prop) : (term12 p q r) = (term13 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6960145 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term11 A B a op s f) = (term14 A B a op s f).
Proof. exact (@lem6960140 (@monoidal B op) (term9 A a s) ((term10 A B op s a f) = (@iterate B A op s f))). Qed.
Lemma lem6960182 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6960183 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem6960182 p q p' q'). Qed.
Lemma lem6960184 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem6960183 p q p'). Qed.
Lemma lem6960185 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) : term18 _127419 a s f.
Proof. exact (@lem6960184 (term9 _127419 a s) ((term19 _127419 s a f) = (@nsum _127419 s f))). Qed.
Lemma lem6960186 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) (p' : Prop) : term20 _127419 a s f p'.
Proof. exact (@lem6960185 _127419 a s f p'). Qed.
Lemma lem6960187 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) (p' : Prop) : (term20 _127419 a s f p') = (term21 _127419 a s f p').
Proof. exact (eq_refl (term20 _127419 a s f p')). Qed.
Lemma lem6960188 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) (p' : Prop) : term21 _127419 a s f p'.
Proof. exact (EQ_MP (@lem6960187 _127419 a s f p') (@lem6960186 _127419 a s f p')). Qed.
Lemma lem6960189 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) (p' : Prop) (q' : Prop) : term22 _127419 a s f p' q'.
Proof. exact (@lem6960188 _127419 a s f p' q'). Qed.
Lemma lem6960190 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) (p' : Prop) (q' : Prop) : (term22 _127419 a s f p' q') = (term23 _127419 a s f p' q').
Proof. exact (eq_refl (term22 _127419 a s f p' q')). Qed.
Lemma lem6960191 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) (p' : Prop) (q' : Prop) : term23 _127419 a s f p' q'.
Proof. exact (EQ_MP (@lem6960190 _127419 a s f p' q') (@lem6960189 _127419 a s f p' q')). Qed.
Lemma lem6960216 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) : (term9 _127419 a s) = (term9 _127419 a s).
Proof. exact (eq_refl (term9 _127419 a s)). Qed.
Lemma lem6960217 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) (q' : Prop) : term24 _127419 f a s q'.
Proof. exact (@lem6960191 _127419 a s f (term9 _127419 a s) q'). Qed.
Lemma lem6960218 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) (q' : Prop) : term25 _127419 f a s q'.
Proof. exact (@lem6960217 _127419 f a s q' (@lem6960216 _127419 a s)). Qed.
Lemma lem6960219 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : term9 _127419 a s.
Proof. exact (h1). Qed.
Lemma lem6960220 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : @IN _127419 a s.
Proof. exact (proj2 (@lem6960219 _127419 a s h1)). Qed.
Lemma lem6960221 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) : (@IN _127419 a s) = ((@IN _127419 a s) = True).
Proof. exact (@lem7 (@IN _127419 a s)). Qed.
Lemma lem6960223 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : @FINITE _127419 s.
Proof. exact (proj1 (@lem6960219 _127419 a s h1)). Qed.
Lemma lem6960224 {_127419 : Type'} (s : _127419 -> Prop) : (@FINITE _127419 s) = ((@FINITE _127419 s) = True).
Proof. exact (@lem7 (@FINITE _127419 s)). Qed.
Lemma lem6960251 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6960252 {_127419 : Type'} : (@nsum _127419) = (@iterate nat _127419 Nat.add).
Proof. exact (@lem6960251 _127419). Qed.
Lemma lem6960269 {_127419 : Type'} (s : _127419 -> Prop) (a : _127419) : (@DELETE _127419 s a) = (@DELETE _127419 s a).
Proof. exact (eq_refl (@DELETE _127419 s a)). Qed.
Lemma lem6960270 {_127419 : Type'} (s : _127419 -> Prop) (a : _127419) : (term26 _127419 s a) = (term27 _127419 s a).
Proof. exact (MK_COMB (@lem6960252 _127419) (@lem6960269 _127419 s a)). Qed.
Lemma lem6960291 {_127419 : Type'} (f : _127419 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6960292 {_127419 : Type'} (s : _127419 -> Prop) (a : _127419) (f : _127419 -> nat) : (term28 _127419 s a f) = (term29 _127419 s a f).
Proof. exact (MK_COMB (@lem6960270 _127419 s a) (@lem6960291 _127419 f)). Qed.
Lemma lem6960315 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) : (term30 _127419 f a) = (term30 _127419 f a).
Proof. exact (eq_refl (term30 _127419 f a)). Qed.
Lemma lem6960316 {_127419 : Type'} (s : _127419 -> Prop) (a : _127419) (f : _127419 -> nat) : (term19 _127419 s a f) = (term31 _127419 s a f).
Proof. exact (MK_COMB (@lem6960315 _127419 f a) (@lem6960292 _127419 s a f)). Qed.
Lemma lem6960318 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term14 A B a op s f.
Proof. exact (EQ_MP (@lem6960145 A B a op s f) (@lem6960138 A B a op s f)). Qed.
Lemma lem6960319 {_127419 : Type'} (a : _127419) (op : type1606) (s : _127419 -> Prop) (f : _127419 -> nat) : term32 _127419 a op s f.
Proof. exact (@lem6960318 _127419 nat a op s f). Qed.
Lemma lem6960320 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) : term33 _127419 a s f.
Proof. exact (@lem6960319 _127419 a Nat.add s f). Qed.
Lemma lem6960330 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6960119) (@lem6924403)). Qed.
Lemma lem6960333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6960334 : term34 = (and True).
Proof. exact (MK_COMB (@lem6960333) (@lem6960330)). Qed.
Lemma lem6960350 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (@FINITE _127419 s) = True.
Proof. exact (EQ_MP (@lem6960224 _127419 s) (@lem6960223 _127419 a s h1)). Qed.
Lemma lem6960353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6960354 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (term35 _127419 s) = (and True).
Proof. exact (MK_COMB (@lem6960353) (@lem6960350 _127419 a s h1)). Qed.
Lemma lem6960362 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (@IN _127419 a s) = True.
Proof. exact (EQ_MP (@lem6960221 _127419 a s) (@lem6960220 _127419 a s h1)). Qed.
Lemma lem6960365 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (term9 _127419 a s) = (True /\ True).
Proof. exact (MK_COMB (@lem6960354 _127419 a s h1) (@lem6960362 _127419 a s h1)). Qed.
Lemma lem6960367 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6960368 : (True /\ True) = True.
Proof. exact (@lem6960367 True). Qed.
Lemma lem6960371 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (term9 _127419 a s) = True.
Proof. exact (TRANS (@lem6960365 _127419 a s h1) (@lem6960368)). Qed.
Lemma lem6960372 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (term36 _127419 a s) = (True /\ True).
Proof. exact (MK_COMB (@lem6960334) (@lem6960371 _127419 a s h1)). Qed.
Lemma lem6960374 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6960375 : (True /\ True) = True.
Proof. exact (@lem6960374 True). Qed.
Lemma lem6960378 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (term36 _127419 a s) = True.
Proof. exact (TRANS (@lem6960372 _127419 a s h1) (@lem6960375)). Qed.
Lemma lem6960379 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : True = (term36 _127419 a s).
Proof. exact (SYM (@lem6960378 _127419 a s h1)). Qed.
Lemma lem6960380 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : term36 _127419 a s.
Proof. exact (EQ_MP (@lem6960379 _127419 a s h1) (@lem0)). Qed.
Lemma lem6960381 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (term31 _127419 s a f) = (@iterate nat _127419 Nat.add s f).
Proof. exact (@lem6960320 _127419 a s f (@lem6960380 _127419 a s h1)). Qed.
Lemma lem6960396 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (term19 _127419 s a f) = (@iterate nat _127419 Nat.add s f).
Proof. exact (TRANS (@lem6960316 _127419 s a f) (@lem6960381 _127419 f a s h1)). Qed.
Lemma lem6960397 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6960398 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : (term37 _127419 s a f) = (term38 _127419 s f).
Proof. exact (MK_COMB (@lem6960397) (@lem6960396 _127419 f a s h1)). Qed.
Lemma lem6960422 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6960423 {_127419 : Type'} : (@nsum _127419) = (@iterate nat _127419 Nat.add).
Proof. exact (@lem6960422 _127419). Qed.
Lemma lem6960432 {_127419 : Type'} (s : _127419 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6960433 {_127419 : Type'} (s : _127419 -> Prop) : (@nsum _127419 s) = (@iterate nat _127419 Nat.add s).
Proof. exact (MK_COMB (@lem6960423 _127419) (@lem6960432 _127419 s)). Qed.
Lemma lem6960446 {_127419 : Type'} (f : _127419 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6960447 {_127419 : Type'} (s : _127419 -> Prop) (f : _127419 -> nat) : (@nsum _127419 s f) = (@iterate nat _127419 Nat.add s f).
Proof. exact (MK_COMB (@lem6960433 _127419 s) (@lem6960446 _127419 f)). Qed.
Lemma lem6960462 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : ((term19 _127419 s a f) = (@nsum _127419 s f)) = ((@iterate nat _127419 Nat.add s f) = (@iterate nat _127419 Nat.add s f)).
Proof. exact (MK_COMB (@lem6960398 _127419 f a s h1) (@lem6960447 _127419 s f)). Qed.
Lemma lem6960464 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6960465 (x : nat) : (x = x) = True.
Proof. exact (@lem6960464 nat x). Qed.
Lemma lem6960466 {_127419 : Type'} (s : _127419 -> Prop) (f : _127419 -> nat) : ((@iterate nat _127419 Nat.add s f) = (@iterate nat _127419 Nat.add s f)) = True.
Proof. exact (@lem6960465 (@iterate nat _127419 Nat.add s f)). Qed.
Lemma lem6960469 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) (h1 : term9 _127419 a s) : ((term19 _127419 s a f) = (@nsum _127419 s f)) = True.
Proof. exact (TRANS (@lem6960462 _127419 f a s h1) (@lem6960466 _127419 s f)). Qed.
Lemma lem6960470 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) : term39 _127419 a s f.
Proof. exact (fun h0 : term9 _127419 a s => @lem6960469 _127419 f a s h0). Qed.
Lemma lem6960471 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) : term40 _127419 f a s.
Proof. exact (@lem6960218 _127419 f a s True). Qed.
Lemma lem6960472 {_127419 : Type'} (f : _127419 -> nat) (a : _127419) (s : _127419 -> Prop) : (term41 _127419 a s f) = (term42 _127419 a s).
Proof. exact (@lem6960471 _127419 f a s (@lem6960470 _127419 a s f)). Qed.
Lemma lem6960474 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6960475 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) : (term42 _127419 a s) = True.
Proof. exact (@lem6960474 (term9 _127419 a s)). Qed.
Lemma lem6960478 {_127419 : Type'} (a : _127419) (s : _127419 -> Prop) (f : _127419 -> nat) : (term41 _127419 a s f) = True.
Proof. exact (TRANS (@lem6960472 _127419 f a s) (@lem6960475 _127419 a s)). Qed.
Lemma lem6960479 {_127419 : Type'} (s : _127419 -> Prop) (f : _127419 -> nat) : (term43 _127419 s f) = (term44 _127419).
Proof. exact (fun_ext (fun a : _127419 => @lem6960478 _127419 a s f)). Qed.
Lemma lem6960484 {_127419 : Type'} : (@all _127419) = (@all _127419).
Proof. exact (eq_refl (@all _127419)). Qed.
Lemma lem6960485 {_127419 : Type'} (s : _127419 -> Prop) (f : _127419 -> nat) : (term45 _127419 s f) = (term46 _127419).
Proof. exact (MK_COMB (@lem6960484 _127419) (@lem6960479 _127419 s f)). Qed.
Lemma lem6960487 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6960488 {_127419 : Type'} (t : Prop) : (term47 _127419 t) = t.
Proof. exact (@lem6960487 _127419 t). Qed.
Lemma lem6960489 {_127419 : Type'} : (term46 _127419) = True.
Proof. exact (@lem6960488 _127419 True). Qed.
Lemma lem6960492 {_127419 : Type'} (s : _127419 -> Prop) (f : _127419 -> nat) : (term45 _127419 s f) = True.
Proof. exact (TRANS (@lem6960485 _127419 s f) (@lem6960489 _127419)). Qed.
Lemma lem6960493 {_127419 : Type'} (f : _127419 -> nat) : (term48 _127419 f) = (term49 _127419).
Proof. exact (fun_ext (fun s : _127419 -> Prop => @lem6960492 _127419 s f)). Qed.
Lemma lem6960498 {_127419 : Type'} : (@all (_127419 -> Prop)) = (@all (_127419 -> Prop)).
Proof. exact (eq_refl (@all (_127419 -> Prop))). Qed.
Lemma lem6960499 {_127419 : Type'} (f : _127419 -> nat) : (term50 _127419 f) = (term51 _127419).
Proof. exact (MK_COMB (@lem6960498 _127419) (@lem6960493 _127419 f)). Qed.
Lemma lem6960501 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6960502 {_127419 : Type'} (t : Prop) : (term52 _127419 t) = t.
Proof. exact (@lem6960501 (_127419 -> Prop) t). Qed.
Lemma lem6960503 {_127419 : Type'} : (term51 _127419) = True.
Proof. exact (@lem6960502 _127419 True). Qed.
Lemma lem6960506 {_127419 : Type'} (f : _127419 -> nat) : (term50 _127419 f) = True.
Proof. exact (TRANS (@lem6960499 _127419 f) (@lem6960503 _127419)). Qed.
Lemma lem6960507 {_127419 : Type'} : (term53 _127419) = (term54 _127419).
Proof. exact (fun_ext (fun f : _127419 -> nat => @lem6960506 _127419 f)). Qed.
Lemma lem6960512 {_127419 : Type'} : (@all (_127419 -> nat)) = (@all (_127419 -> nat)).
Proof. exact (eq_refl (@all (_127419 -> nat))). Qed.
Lemma lem6960513 {_127419 : Type'} : (term55 _127419) = (term56 _127419).
Proof. exact (MK_COMB (@lem6960512 _127419) (@lem6960507 _127419)). Qed.
Lemma lem6960515 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6960516 {_127419 : Type'} (t : Prop) : (term57 _127419 t) = t.
Proof. exact (@lem6960515 (_127419 -> nat) t). Qed.
Lemma lem6960517 {_127419 : Type'} : (term56 _127419) = True.
Proof. exact (@lem6960516 _127419 True). Qed.
Lemma lem6960520 {_127419 : Type'} : (term55 _127419) = True.
Proof. exact (TRANS (@lem6960513 _127419) (@lem6960517 _127419)). Qed.
Lemma lem6960521 {_127419 : Type'} : True = (term55 _127419).
Proof. exact (SYM (@lem6960520 _127419)). Qed.
Lemma lem6960522 {_127419 : Type'} : term55 _127419.
Proof. exact (EQ_MP (@lem6960521 _127419) (@lem0)). Qed.
