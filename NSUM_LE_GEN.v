Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_LE_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_SUBSET_spec.
Require Import IN_DIFF_spec.
Require Import LE_spec.
Require Import LE_TRANS_spec.
Require Import NSUM_LE_spec.
Require Import NSUM_SUBSET_spec.
Require Import NSUM_SUPPORT_spec.
Require Import SUBSET_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Require Import thm7_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7010400 {_127006 : Type'} (h1 : term0 _127006) : term0 _127006.
Proof. exact (h1). Qed.
Lemma lem7010401 {_127006 : Type'} (f : _127006 -> nat) (h1 : term0 _127006) : term1 _127006 f.
Proof. exact (@lem7010400 _127006 h1 f). Qed.
Lemma lem7010402 {_127006 : Type'} (f : _127006 -> nat) : (term1 _127006 f) = (term2 _127006 f).
Proof. exact (eq_refl (term1 _127006 f)). Qed.
Lemma lem7010403 {_127006 : Type'} (f : _127006 -> nat) (h1 : term0 _127006) : term2 _127006 f.
Proof. exact (EQ_MP (@lem7010402 _127006 f) (@lem7010401 _127006 f h1)). Qed.
Lemma lem7010404 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term0 _127006) : term3 _127006 f g.
Proof. exact (@lem7010403 _127006 f h1 g). Qed.
Lemma lem7010405 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term3 _127006 f g) = (term4 _127006 f g).
Proof. exact (eq_refl (term3 _127006 f g)). Qed.
Lemma lem7010406 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term0 _127006) : term4 _127006 f g.
Proof. exact (EQ_MP (@lem7010405 _127006 f g) (@lem7010404 _127006 f g h1)). Qed.
Lemma lem7010407 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (s : _127006 -> Prop) (h1 : term0 _127006) : term5 _127006 f g s.
Proof. exact (@lem7010406 _127006 f g h1 s). Qed.
Lemma lem7010408 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term5 _127006 f g s) = (term6 _127006 f s g).
Proof. exact (eq_refl (term5 _127006 f g s)). Qed.
Lemma lem7010409 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) (h1 : term0 _127006) : term6 _127006 f s g.
Proof. exact (EQ_MP (@lem7010408 _127006 f s g) (@lem7010407 _127006 f g s h1)). Qed.
Lemma lem7010410 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term7 _127006 s f g) : term7 _127006 s f g.
Proof. exact (h1). Qed.
Lemma lem7010411 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term0 _127006) (h2 : term7 _127006 s f g) : term8 _127006 f s g.
Proof. exact (@lem7010409 _127006 f s g h1 (@lem7010410 _127006 s f g h2)). Qed.
Lemma lem7010412 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term7 _127006 s f g) : term9 _127006 f s g.
Proof. exact (fun h0 : term0 _127006 => @lem7010411 _127006 s f g h0 h1). Qed.
Lemma lem7010413 {_127006 : Type'} (h1 : term0 _127006) : term0 _127006.
Proof. exact (h1). Qed.
Lemma lem7010414 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term0 _127006) (h2 : term7 _127006 s f g) : term8 _127006 f s g.
Proof. exact (@lem7010412 _127006 s f g h2 (@lem7010413 _127006 h1)). Qed.
Lemma lem7010415 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) (h1 : term0 _127006) : term6 _127006 f s g.
Proof. exact (fun h0 : term7 _127006 s f g => @lem7010414 _127006 s f g h1 h0). Qed.
Lemma lem7010416 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (h1 : term0 _127006) : term10 _127006 f s.
Proof. exact (fun g : _127006 -> nat => @lem7010415 _127006 f s g h1). Qed.
Lemma lem7010417 {_127006 : Type'} (f : _127006 -> nat) (h1 : term0 _127006) : term11 _127006 f.
Proof. exact (fun s : _127006 -> Prop => @lem7010416 _127006 f s h1). Qed.
Lemma lem7010418 {_127006 : Type'} (h1 : term0 _127006) : term12 _127006.
Proof. exact (fun f : _127006 -> nat => @lem7010417 _127006 f h1). Qed.
Lemma lem7010419 {_127006 : Type'} : term13 _127006.
Proof. exact (fun h0 : term0 _127006 => @lem7010418 _127006 h0). Qed.
Lemma lem7010420 {_127006 : Type'} : term12 _127006.
Proof. exact (@lem7010419 _127006 (@lem6933015 _127006)). Qed.
Lemma lem7010421 {_127006 : Type'} (f : _127006 -> nat) : term14 _127006 f.
Proof. exact (@lem7010420 _127006 f). Qed.
Lemma lem7010422 {_127006 : Type'} (f : _127006 -> nat) : (term14 _127006 f) = (term11 _127006 f).
Proof. exact (eq_refl (term14 _127006 f)). Qed.
Lemma lem7010423 {_127006 : Type'} (f : _127006 -> nat) : term11 _127006 f.
Proof. exact (EQ_MP (@lem7010422 _127006 f) (@lem7010421 _127006 f)). Qed.
Lemma lem7010424 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) : term15 _127006 f s.
Proof. exact (@lem7010423 _127006 f s). Qed.
Lemma lem7010425 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) : (term15 _127006 f s) = (term10 _127006 f s).
Proof. exact (eq_refl (term15 _127006 f s)). Qed.
Lemma lem7010426 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) : term10 _127006 f s.
Proof. exact (EQ_MP (@lem7010425 _127006 f s) (@lem7010424 _127006 f s)). Qed.
Lemma lem7010427 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term16 _127006 f s g.
Proof. exact (@lem7010426 _127006 f s g). Qed.
Lemma lem7010428 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term16 _127006 f s g) = (term6 _127006 f s g).
Proof. exact (eq_refl (term16 _127006 f s g)). Qed.
Lemma lem7010464 {_83095 : Type'} : term17 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem7010465 {_83095 : Type'} (p : _83095 -> Prop) : term18 _83095 p.
Proof. exact (@lem7010464 _83095 p). Qed.
Lemma lem7010466 {_83095 : Type'} (p : _83095 -> Prop) : (term18 _83095 p) = (term19 _83095 p).
Proof. exact (eq_refl (term18 _83095 p)). Qed.
Lemma lem7010467 {_83095 : Type'} (p : _83095 -> Prop) : term19 _83095 p.
Proof. exact (EQ_MP (@lem7010466 _83095 p) (@lem7010465 _83095 p)). Qed.
Lemma lem7010468 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term20 _83095 p x.
Proof. exact (@lem7010467 _83095 p x). Qed.
Lemma lem7010469 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 p x) = ((term21 _83095 x p) = (p x)).
Proof. exact (eq_refl (term20 _83095 p x)). Qed.
Lemma lem7010478 {A : Type'} (s : A -> Prop) : term22 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem7010479 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (eq_refl (term22 A s)). Qed.
Lemma lem7010480 {A : Type'} (s : A -> Prop) : term23 A s.
Proof. exact (EQ_MP (@lem7010479 A s) (@lem7010478 A s)). Qed.
Lemma lem7010481 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term24 A s t.
Proof. exact (@lem7010480 A s t). Qed.
Lemma lem7010482 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term24 A s t) = ((@SUBSET A s t) = (term25 A s t)).
Proof. exact (eq_refl (term24 A s t)). Qed.
Lemma lem7010493 (p : Prop) (q : Prop) (r : Prop) : (term26 p q r) = (term27 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7010494 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term28 A t s) = (term29 A t s).
Proof. exact (@lem7010493 (@FINITE A t) (@SUBSET A s t) (@FINITE A s)). Qed.
Lemma lem7010499 {A : Type'} (s : A -> Prop) : (term30 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7010494 A t s)). Qed.
Lemma lem7010500 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7010501 {A : Type'} (s : A -> Prop) : (term32 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem7010500 A) (@lem7010499 A s)). Qed.
Lemma lem7010506 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7010501 A s)). Qed.
Lemma lem7010507 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7010508 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem7010507 A) (@lem7010506 A)). Qed.
Lemma lem7010513 {A : Type'} : term37 A.
Proof. exact (EQ_MP (@lem7010508 A) (@lem3599924 A)). Qed.
Lemma lem7010514 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (h1). Qed.
Lemma lem7010515 {A : Type'} (s : A -> Prop) (h1 : term37 A) : term38 A s.
Proof. exact (@lem7010514 A h1 s). Qed.
Lemma lem7010516 {A : Type'} (s : A -> Prop) : (term38 A s) = (term33 A s).
Proof. exact (eq_refl (term38 A s)). Qed.
Lemma lem7010517 {A : Type'} (s : A -> Prop) (h1 : term37 A) : term33 A s.
Proof. exact (EQ_MP (@lem7010516 A s) (@lem7010515 A s h1)). Qed.
Lemma lem7010518 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term37 A) : term39 A s t.
Proof. exact (@lem7010517 A s h1 t). Qed.
Lemma lem7010519 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term39 A s t) = (term29 A t s).
Proof. exact (eq_refl (term39 A s t)). Qed.
Lemma lem7010520 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term37 A) : term29 A t s.
Proof. exact (EQ_MP (@lem7010519 A t s) (@lem7010518 A s t h1)). Qed.
Lemma lem7010521 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem7010522 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term37 A) (h2 : @FINITE A t) : term40 A t s.
Proof. exact (@lem7010520 A t s h1 (@lem7010521 A t h2)). Qed.
Lemma lem7010523 {A : Type'} (t : A -> Prop) (h1 : term37 A) (h2 : @FINITE A t) : term41 A t.
Proof. exact (fun s : A -> Prop => @lem7010522 A s t h1 h2). Qed.
Lemma lem7010524 {A : Type'} (t : A -> Prop) (h1 : term37 A) : term42 A t.
Proof. exact (fun h0 : @FINITE A t => @lem7010523 A t h1 h0). Qed.
Lemma lem7010525 {A : Type'} (h1 : term37 A) : term43 A.
Proof. exact (fun t : A -> Prop => @lem7010524 A t h1). Qed.
Lemma lem7010526 {A : Type'} : term44 A.
Proof. exact (fun h0 : term37 A => @lem7010525 A h0). Qed.
Lemma lem7010527 {A : Type'} : term43 A.
Proof. exact (@lem7010526 A (@lem7010513 A)). Qed.
Lemma lem7010528 {A : Type'} (t : A -> Prop) : term45 A t.
Proof. exact (@lem7010527 A t). Qed.
Lemma lem7010529 {A : Type'} (t : A -> Prop) : (term45 A t) = (term42 A t).
Proof. exact (eq_refl (term45 A t)). Qed.
Lemma lem7010541 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem7010542 {A : Type'} (u : A -> Prop) (h1 : term46 A) : term47 A u.
Proof. exact (@lem7010541 A h1 u). Qed.
Lemma lem7010543 {A : Type'} (u : A -> Prop) : (term47 A u) = (term48 A u).
Proof. exact (eq_refl (term47 A u)). Qed.
Lemma lem7010544 {A : Type'} (u : A -> Prop) (h1 : term46 A) : term48 A u.
Proof. exact (EQ_MP (@lem7010543 A u) (@lem7010542 A u h1)). Qed.
Lemma lem7010545 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term46 A) : term49 A u v.
Proof. exact (@lem7010544 A u h1 v). Qed.
Lemma lem7010546 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term49 A u v) = (term50 A u v).
Proof. exact (eq_refl (term49 A u v)). Qed.
Lemma lem7010547 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term46 A) : term50 A u v.
Proof. exact (EQ_MP (@lem7010546 A u v) (@lem7010545 A u v h1)). Qed.
Lemma lem7010548 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term46 A) : term51 A u v f.
Proof. exact (@lem7010547 A u v h1 f). Qed.
Lemma lem7010549 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term51 A u v f) = (term52 A u v f).
Proof. exact (eq_refl (term51 A u v f)). Qed.
Lemma lem7010550 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term46 A) : term52 A u v f.
Proof. exact (EQ_MP (@lem7010549 A u v f) (@lem7010548 A u v f h1)). Qed.
Lemma lem7010551 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term53 A u v f) : term53 A u v f.
Proof. exact (h1). Qed.
Lemma lem7010552 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term46 A) (h2 : term53 A u v f) : term54 A u v f.
Proof. exact (@lem7010550 A u v f h1 (@lem7010551 A u v f h2)). Qed.
Lemma lem7010553 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term53 A u v f) : term55 A u v f.
Proof. exact (fun h0 : term46 A => @lem7010552 A u v f h0 h1). Qed.
Lemma lem7010554 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem7010555 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term46 A) (h2 : term53 A u v f) : term54 A u v f.
Proof. exact (@lem7010553 A u v f h2 (@lem7010554 A h1)). Qed.
Lemma lem7010556 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) (h1 : term46 A) : term52 A u v f.
Proof. exact (fun h0 : term53 A u v f => @lem7010555 A u v f h1 h0). Qed.
Lemma lem7010557 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term46 A) : term50 A u v.
Proof. exact (fun f : A -> nat => @lem7010556 A u v f h1). Qed.
Lemma lem7010558 {A : Type'} (u : A -> Prop) (h1 : term46 A) : term48 A u.
Proof. exact (fun v : A -> Prop => @lem7010557 A u v h1). Qed.
Lemma lem7010559 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (fun u : A -> Prop => @lem7010558 A u h1). Qed.
Lemma lem7010560 {A : Type'} : term56 A.
Proof. exact (fun h0 : term46 A => @lem7010559 A h0). Qed.
Lemma lem7010561 {A : Type'} : term46 A.
Proof. exact (@lem7010560 A (@lem7006898 A)). Qed.
Lemma lem7010562 {A : Type'} (u : A -> Prop) : term47 A u.
Proof. exact (@lem7010561 A u). Qed.
Lemma lem7010563 {A : Type'} (u : A -> Prop) : (term47 A u) = (term48 A u).
Proof. exact (eq_refl (term47 A u)). Qed.
Lemma lem7010564 {A : Type'} (u : A -> Prop) : term48 A u.
Proof. exact (EQ_MP (@lem7010563 A u) (@lem7010562 A u)). Qed.
Lemma lem7010565 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term49 A u v.
Proof. exact (@lem7010564 A u v). Qed.
Lemma lem7010566 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term49 A u v) = (term50 A u v).
Proof. exact (eq_refl (term49 A u v)). Qed.
Lemma lem7010567 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term50 A u v.
Proof. exact (EQ_MP (@lem7010566 A u v) (@lem7010565 A u v)). Qed.
Lemma lem7010568 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term51 A u v f.
Proof. exact (@lem7010567 A u v f). Qed.
Lemma lem7010569 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : (term51 A u v f) = (term52 A u v f).
Proof. exact (eq_refl (term51 A u v f)). Qed.
Lemma lem7010571 {A B : Type'} (s : A -> Prop) : term57 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem7010572 {A B : Type'} (s : A -> Prop) : (term57 A B s) = (term58 A B s).
Proof. exact (eq_refl (term57 A B s)). Qed.
Lemma lem7010573 {A B : Type'} (s : A -> Prop) : term58 A B s.
Proof. exact (EQ_MP (@lem7010572 A B s) (@lem7010571 A B s)). Qed.
Lemma lem7010574 {A B : Type'} (s : A -> Prop) (f : A -> B) : term59 A B s f.
Proof. exact (@lem7010573 A B s f). Qed.
Lemma lem7010575 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term59 A B s f) = (term60 A B s f).
Proof. exact (eq_refl (term59 A B s f)). Qed.
Lemma lem7010576 {A B : Type'} (s : A -> Prop) (f : A -> B) : term60 A B s f.
Proof. exact (EQ_MP (@lem7010575 A B s f) (@lem7010574 A B s f)). Qed.
Lemma lem7010577 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term61 A B s f op.
Proof. exact (@lem7010576 A B s f op). Qed.
Lemma lem7010578 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term61 A B s f op) = ((@support A B op f s) = (term62 A B s f op)).
Proof. exact (eq_refl (term61 A B s f op)). Qed.
Lemma lem7010582 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) (h1 : (term63 _126695 s f) = (@nsum _126695 s f)) : (term63 _126695 s f) = (@nsum _126695 s f).
Proof. exact (h1). Qed.
Lemma lem7010583 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) (h1 : (term63 _126695 s f) = (@nsum _126695 s f)) : (@nsum _126695 s f) = (term63 _126695 s f).
Proof. exact (SYM (@lem7010582 _126695 s f h1)). Qed.
Lemma lem7010584 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) (h1 : (@nsum _126695 s f) = (term63 _126695 s f)) : (@nsum _126695 s f) = (term63 _126695 s f).
Proof. exact (h1). Qed.
Lemma lem7010585 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) (h1 : (@nsum _126695 s f) = (term63 _126695 s f)) : (term63 _126695 s f) = (@nsum _126695 s f).
Proof. exact (SYM (@lem7010584 _126695 s f h1)). Qed.
Lemma lem7010586 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : ((term63 _126695 s f) = (@nsum _126695 s f)) = ((@nsum _126695 s f) = (term63 _126695 s f)).
Proof. exact (prop_ext (fun h1 : (term63 _126695 s f) = (@nsum _126695 s f) => @lem7010583 _126695 s f h1) (fun h1 : (@nsum _126695 s f) = (term63 _126695 s f) => @lem7010585 _126695 s f h1)). Qed.
Lemma lem7010587 {_126695 : Type'} (f : _126695 -> nat) : (term64 _126695 f) = (term65 _126695 f).
Proof. exact (fun_ext (fun s : _126695 -> Prop => @lem7010586 _126695 s f)). Qed.
Lemma lem7010588 {_126695 : Type'} : (@all (_126695 -> Prop)) = (@all (_126695 -> Prop)).
Proof. exact (eq_refl (@all (_126695 -> Prop))). Qed.
Lemma lem7010589 {_126695 : Type'} (f : _126695 -> nat) : (term66 _126695 f) = (term67 _126695 f).
Proof. exact (MK_COMB (@lem7010588 _126695) (@lem7010587 _126695 f)). Qed.
Lemma lem7010590 {_126695 : Type'} : (term68 _126695) = (term69 _126695).
Proof. exact (fun_ext (fun f : _126695 -> nat => @lem7010589 _126695 f)). Qed.
Lemma lem7010591 {_126695 : Type'} : (@all (_126695 -> nat)) = (@all (_126695 -> nat)).
Proof. exact (eq_refl (@all (_126695 -> nat))). Qed.
Lemma lem7010592 {_126695 : Type'} : (term70 _126695) = (term71 _126695).
Proof. exact (MK_COMB (@lem7010591 _126695) (@lem7010590 _126695)). Qed.
Lemma lem7010593 {_126695 : Type'} : term71 _126695.
Proof. exact (EQ_MP (@lem7010592 _126695) (@lem6930330 _126695)). Qed.
Lemma lem7010594 {_126695 : Type'} (f : _126695 -> nat) : term72 _126695 f.
Proof. exact (@lem7010593 _126695 f). Qed.
Lemma lem7010595 {_126695 : Type'} (f : _126695 -> nat) : (term72 _126695 f) = (term67 _126695 f).
Proof. exact (eq_refl (term72 _126695 f)). Qed.
Lemma lem7010596 {_126695 : Type'} (f : _126695 -> nat) : term67 _126695 f.
Proof. exact (EQ_MP (@lem7010595 _126695 f) (@lem7010594 _126695 f)). Qed.
Lemma lem7010597 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : term73 _126695 f s.
Proof. exact (@lem7010596 _126695 f s). Qed.
Lemma lem7010598 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : (term73 _126695 f s) = ((@nsum _126695 s f) = (term63 _126695 s f)).
Proof. exact (eq_refl (term73 _126695 f s)). Qed.
Lemma lem7010600 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term74 A f s g) : term74 A f s g.
Proof. exact (h1). Qed.
Lemma lem7010601 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : term75 A s g.
Proof. exact (h1). Qed.
Lemma lem7010602 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term76 A s f g.
Proof. exact (h1). Qed.
Lemma lem7010604 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : (@nsum _126695 s f) = (term63 _126695 s f).
Proof. exact (EQ_MP (@lem7010598 _126695 s f) (@lem7010597 _126695 f s)). Qed.
Lemma lem7010605 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term63 A s f).
Proof. exact (@lem7010604 A s f). Qed.
Lemma lem7010606 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7010607 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term77 A s f) = (term78 A s f).
Proof. exact (MK_COMB (@lem7010606) (@lem7010605 A s f)). Qed.
Lemma lem7010609 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : (@nsum _126695 s f) = (term63 _126695 s f).
Proof. exact (EQ_MP (@lem7010598 _126695 s f) (@lem7010597 _126695 f s)). Qed.
Lemma lem7010610 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (term63 A s f).
Proof. exact (@lem7010609 A s f). Qed.
Lemma lem7010611 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (term63 A s g).
Proof. exact (@lem7010610 A s g). Qed.
Lemma lem7010612 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term8 A f s g) = (term79 A f s g).
Proof. exact (MK_COMB (@lem7010607 A s f) (@lem7010611 A s g)). Qed.
Lemma lem7010613 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term79 A f s g) = (term8 A f s g).
Proof. exact (SYM (@lem7010612 A f s g)). Qed.
Lemma lem7010615 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term62 A B s f op).
Proof. exact (EQ_MP (@lem7010578 A B s f op) (@lem7010577 A B s f op)). Qed.
Lemma lem7010616 {A : Type'} (s : A -> Prop) (f : A -> nat) (op : type1606) : (@support A nat op f s) = (term80 A s f op).
Proof. exact (@lem7010615 A nat s f op). Qed.
Lemma lem7010617 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@support A nat Nat.add f s) = (term81 A s f).
Proof. exact (@lem7010616 A s f Nat.add). Qed.
Lemma lem7010627 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7010628 {A : Type'} (f : A -> nat) (x : A) : (term82 A f x) = (term82 A f x).
Proof. exact (eq_refl (term82 A f x)). Qed.
Lemma lem7010629 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (@neutral nat Nat.add)) = ((f x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7010628 A f x) (@lem7010627)). Qed.
Lemma lem7010632 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7010633 {A : Type'} (f : A -> nat) (x : A) : (term83 A f x) = (term84 A f x).
Proof. exact (MK_COMB (@lem7010632) (@lem7010629 A f x)). Qed.
Lemma lem7010634 {A : Type'} (x : A) (s : A -> Prop) : (term85 A x s) = (term85 A x s).
Proof. exact (eq_refl (term85 A x s)). Qed.
Lemma lem7010635 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term86 A s f x) = (term87 A s f x).
Proof. exact (MK_COMB (@lem7010634 A x s) (@lem7010633 A f x)). Qed.
Lemma lem7010638 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7010639 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term88 A GEN_PVAR_237 s f x) = (term89 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7010638 A GEN_PVAR_237) (@lem7010635 A s f x)). Qed.
Lemma lem7010640 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7010641 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term90 A GEN_PVAR_237 s f x) = (term91 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7010639 A GEN_PVAR_237 s f x) (@lem7010640 A x)). Qed.
Lemma lem7010642 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term92 A GEN_PVAR_237 s f) = (term93 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem7010641 A GEN_PVAR_237 s f x)). Qed.
Lemma lem7010643 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7010644 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term94 A GEN_PVAR_237 s f) = (term95 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7010643 A) (@lem7010642 A GEN_PVAR_237 s f)). Qed.
Lemma lem7010649 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term96 A s f) = (term97 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7010644 A GEN_PVAR_237 s f)). Qed.
Lemma lem7010650 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7010651 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term81 A s f) = (term98 A s f).
Proof. exact (MK_COMB (@lem7010650 A) (@lem7010649 A s f)). Qed.
Lemma lem7010652 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@support A nat Nat.add f s) = (term98 A s f).
Proof. exact (TRANS (@lem7010617 A s f) (@lem7010651 A s f)). Qed.
Lemma lem7010653 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem7010654 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term99 A f s) = (term100 A s f).
Proof. exact (MK_COMB (@lem7010653 A) (@lem7010652 A s f)). Qed.
Lemma lem7010655 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7010656 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term63 A s f) = (term101 A s f).
Proof. exact (MK_COMB (@lem7010654 A s f) (@lem7010655 A f)). Qed.
Lemma lem7010657 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7010658 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term78 A s f) = (term102 A s f).
Proof. exact (MK_COMB (@lem7010657) (@lem7010656 A s f)). Qed.
Lemma lem7010660 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term62 A B s f op).
Proof. exact (EQ_MP (@lem7010578 A B s f op) (@lem7010577 A B s f op)). Qed.
Lemma lem7010661 {A : Type'} (s : A -> Prop) (f : A -> nat) (op : type1606) : (@support A nat op f s) = (term80 A s f op).
Proof. exact (@lem7010660 A nat s f op). Qed.
Lemma lem7010662 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@support A nat Nat.add g s) = (term81 A s g).
Proof. exact (@lem7010661 A s g Nat.add). Qed.
Lemma lem7010672 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7010673 {A : Type'} (g : A -> nat) (x : A) : (term82 A g x) = (term82 A g x).
Proof. exact (eq_refl (term82 A g x)). Qed.
Lemma lem7010674 {A : Type'} (g : A -> nat) (x : A) : ((g x) = (@neutral nat Nat.add)) = ((g x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7010673 A g x) (@lem7010672)). Qed.
Lemma lem7010677 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7010678 {A : Type'} (g : A -> nat) (x : A) : (term83 A g x) = (term84 A g x).
Proof. exact (MK_COMB (@lem7010677) (@lem7010674 A g x)). Qed.
Lemma lem7010679 {A : Type'} (x : A) (s : A -> Prop) : (term85 A x s) = (term85 A x s).
Proof. exact (eq_refl (term85 A x s)). Qed.
Lemma lem7010680 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term86 A s g x) = (term87 A s g x).
Proof. exact (MK_COMB (@lem7010679 A x s) (@lem7010678 A g x)). Qed.
Lemma lem7010683 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7010684 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term88 A GEN_PVAR_237 s g x) = (term89 A GEN_PVAR_237 s g x).
Proof. exact (MK_COMB (@lem7010683 A GEN_PVAR_237) (@lem7010680 A s g x)). Qed.
Lemma lem7010685 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7010686 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term90 A GEN_PVAR_237 s g x) = (term91 A GEN_PVAR_237 s g x).
Proof. exact (MK_COMB (@lem7010684 A GEN_PVAR_237 s g x) (@lem7010685 A x)). Qed.
Lemma lem7010687 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> nat) : (term92 A GEN_PVAR_237 s g) = (term93 A GEN_PVAR_237 s g).
Proof. exact (fun_ext (fun x : A => @lem7010686 A GEN_PVAR_237 s g x)). Qed.
Lemma lem7010688 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7010689 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (g : A -> nat) : (term94 A GEN_PVAR_237 s g) = (term95 A GEN_PVAR_237 s g).
Proof. exact (MK_COMB (@lem7010688 A) (@lem7010687 A GEN_PVAR_237 s g)). Qed.
Lemma lem7010694 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term96 A s g) = (term97 A s g).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7010689 A GEN_PVAR_237 s g)). Qed.
Lemma lem7010695 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7010696 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term81 A s g) = (term98 A s g).
Proof. exact (MK_COMB (@lem7010695 A) (@lem7010694 A s g)). Qed.
Lemma lem7010697 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@support A nat Nat.add g s) = (term98 A s g).
Proof. exact (TRANS (@lem7010662 A s g) (@lem7010696 A s g)). Qed.
Lemma lem7010698 {A : Type'} : (@nsum A) = (@nsum A).
Proof. exact (eq_refl (@nsum A)). Qed.
Lemma lem7010699 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term99 A g s) = (term100 A s g).
Proof. exact (MK_COMB (@lem7010698 A) (@lem7010697 A s g)). Qed.
Lemma lem7010700 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7010701 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term63 A s g) = (term101 A s g).
Proof. exact (MK_COMB (@lem7010699 A s g) (@lem7010700 A g)). Qed.
Lemma lem7010702 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term79 A f s g) = (term103 A f s g).
Proof. exact (MK_COMB (@lem7010658 A s f) (@lem7010701 A s g)). Qed.
Lemma lem7010703 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term103 A f s g) = (term79 A f s g).
Proof. exact (SYM (@lem7010702 A f s g)). Qed.
Lemma lem7010704 (h1 : term104) : term104.
Proof. exact (h1). Qed.
Lemma lem7010705 (m : nat) (h1 : term104) : term105 m.
Proof. exact (@lem7010704 h1 m). Qed.
Lemma lem7010706 (m : nat) : (term105 m) = (term106 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem7010707 (m : nat) (h1 : term104) : term106 m.
Proof. exact (EQ_MP (@lem7010706 m) (@lem7010705 m h1)). Qed.
Lemma lem7010708 (m : nat) (n : nat) (h1 : term104) : term107 m n.
Proof. exact (@lem7010707 m h1 n). Qed.
Lemma lem7010709 (n : nat) (m : nat) : (term107 m n) = (term108 n m).
Proof. exact (eq_refl (term107 m n)). Qed.
Lemma lem7010710 (n : nat) (m : nat) (h1 : term104) : term108 n m.
Proof. exact (EQ_MP (@lem7010709 n m) (@lem7010708 m n h1)). Qed.
Lemma lem7010711 (n : nat) (m : nat) (p : nat) (h1 : term104) : term109 n m p.
Proof. exact (@lem7010710 n m h1 p). Qed.
Lemma lem7010712 (n : nat) (m : nat) (p : nat) : (term109 n m p) = (term110 n m p).
Proof. exact (eq_refl (term109 n m p)). Qed.
Lemma lem7010713 (n : nat) (m : nat) (p : nat) (h1 : term104) : term110 n m p.
Proof. exact (EQ_MP (@lem7010712 n m p) (@lem7010711 n m p h1)). Qed.
Lemma lem7010714 (m : nat) (n : nat) (p : nat) (h1 : term111 m n p) : term111 m n p.
Proof. exact (h1). Qed.
Lemma lem7010715 (m : nat) (n : nat) (p : nat) (h1 : term104) (h2 : term111 m n p) : Peano.le m p.
Proof. exact (@lem7010713 n m p h1 (@lem7010714 m n p h2)). Qed.
Lemma lem7010716 (m : nat) (n : nat) (p : nat) (h1 : term111 m n p) : term112 m p.
Proof. exact (fun h0 : term104 => @lem7010715 m n p h0 h1). Qed.
Lemma lem7010717 (m : nat) (p : nat) (h1 : term113 m p) : term113 m p.
Proof. exact (h1). Qed.
Lemma lem7010718 (m : nat) (p : nat) (h1 : term113 m p) : term112 m p.
Proof. exact (ex_elim (@lem7010717 m p h1) (fun n : nat => fun h0 : term114 m p n => @lem7010716 m n p h0)). Qed.
Lemma lem7010719 (h1 : term104) : term104.
Proof. exact (h1). Qed.
Lemma lem7010720 (m : nat) (p : nat) (h1 : term104) (h2 : term113 m p) : Peano.le m p.
Proof. exact (@lem7010718 m p h2 (@lem7010719 h1)). Qed.
Lemma lem7010721 (m : nat) (p : nat) (h1 : term104) : term115 m p.
Proof. exact (fun h0 : term113 m p => @lem7010720 m p h1 h0). Qed.
Lemma lem7010722 (m : nat) (h1 : term104) : term116 m.
Proof. exact (fun p : nat => @lem7010721 m p h1). Qed.
Lemma lem7010723 (h1 : term104) : term117.
Proof. exact (fun m : nat => @lem7010722 m h1). Qed.
Lemma lem7010724 : term118.
Proof. exact (fun h0 : term104 => @lem7010723 h0). Qed.
Lemma lem7010725 : term117.
Proof. exact (@lem7010724 (@lem93743)). Qed.
Lemma lem7010726 (m : nat) : term119 m.
Proof. exact (@lem7010725 m). Qed.
Lemma lem7010727 (m : nat) : (term119 m) = (term116 m).
Proof. exact (eq_refl (term119 m)). Qed.
Lemma lem7010728 (m : nat) : term116 m.
Proof. exact (EQ_MP (@lem7010727 m) (@lem7010726 m)). Qed.
Lemma lem7010729 (m : nat) (p : nat) : term120 m p.
Proof. exact (@lem7010728 m p). Qed.
Lemma lem7010730 (m : nat) (p : nat) : (term120 m p) = (term115 m p).
Proof. exact (eq_refl (term120 m p)). Qed.
Lemma lem7010733 (m : nat) (p : nat) : term115 m p.
Proof. exact (EQ_MP (@lem7010730 m p) (@lem7010729 m p)). Qed.
Lemma lem7010734 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term121 A f s g.
Proof. exact (@lem7010733 (term101 A s f) (term101 A s g)). Qed.
Lemma lem7010736 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term52 A u v f.
Proof. exact (EQ_MP (@lem7010569 A u v f) (@lem7010568 A u v f)). Qed.
Lemma lem7010737 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> nat) : term52 A u v f.
Proof. exact (@lem7010736 A u v f). Qed.
Lemma lem7010738 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : term122 A s g f.
Proof. exact (@lem7010737 A (term98 A s f) (term98 A s g) f). Qed.
Lemma lem7010739 {A : Type'} (s : A -> Prop) : term123 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem7010740 {A : Type'} (s : A -> Prop) : (term123 A s) = (term124 A s).
Proof. exact (eq_refl (term123 A s)). Qed.
Lemma lem7010741 {A : Type'} (s : A -> Prop) : term124 A s.
Proof. exact (EQ_MP (@lem7010740 A s) (@lem7010739 A s)). Qed.
Lemma lem7010742 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term125 A s t.
Proof. exact (@lem7010741 A s t). Qed.
Lemma lem7010743 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term126 A s t).
Proof. exact (eq_refl (term125 A s t)). Qed.
Lemma lem7010744 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term126 A s t.
Proof. exact (EQ_MP (@lem7010743 A s t) (@lem7010742 A s t)). Qed.
Lemma lem7010745 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term127 A s t x.
Proof. exact (@lem7010744 A s t x). Qed.
Lemma lem7010746 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term127 A s t x) = ((term128 A x s t) = (term129 A s x t)).
Proof. exact (eq_refl (term127 A s t x)). Qed.
Lemma lem7010772 {_83095 : Type'} : term17 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem7010773 {_83095 : Type'} (p : _83095 -> Prop) : term18 _83095 p.
Proof. exact (@lem7010772 _83095 p). Qed.
Lemma lem7010774 {_83095 : Type'} (p : _83095 -> Prop) : (term18 _83095 p) = (term19 _83095 p).
Proof. exact (eq_refl (term18 _83095 p)). Qed.
Lemma lem7010775 {_83095 : Type'} (p : _83095 -> Prop) : term19 _83095 p.
Proof. exact (EQ_MP (@lem7010774 _83095 p) (@lem7010773 _83095 p)). Qed.
Lemma lem7010776 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term20 _83095 p x.
Proof. exact (@lem7010775 _83095 p x). Qed.
Lemma lem7010777 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 p x) = ((term21 _83095 x p) = (p x)).
Proof. exact (eq_refl (term20 _83095 p x)). Qed.
Lemma lem7010791 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term75 A s g) = ((term75 A s g) = True).
Proof. exact (@lem7 (term75 A s g)). Qed.
Lemma lem7010806 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term75 A s g) = True.
Proof. exact (EQ_MP (@lem7010791 A s g) (@lem7010601 A s g h1)). Qed.
Lemma lem7010807 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term75 A s g) = True.
Proof. exact (@lem7010806 A s g h1). Qed.
Lemma lem7010808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7010809 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term130 A s g) = (and True).
Proof. exact (MK_COMB (@lem7010808) (@lem7010807 A s g h1)). Qed.
Lemma lem7010817 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term128 A x s t) = (term129 A s x t).
Proof. exact (EQ_MP (@lem7010746 A s x t) (@lem7010745 A s t x)). Qed.
Lemma lem7010818 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term128 A x s t) = (term129 A s x t).
Proof. exact (@lem7010817 A s x t). Qed.
Lemma lem7010819 {A : Type'} (f : A -> nat) (x : A) (s : A -> Prop) (g : A -> nat) : (term131 A x f s g) = (term132 A f x s g).
Proof. exact (@lem7010818 A (term98 A s f) x (term98 A s g)). Qed.
Lemma lem7010823 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7010777 _83095 p x) (@lem7010776 _83095 p x)). Qed.
Lemma lem7010824 {A : Type'} (p : A -> Prop) (x : A) : (term21 A x p) = (p x).
Proof. exact (@lem7010823 A p x). Qed.
Lemma lem7010825 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term133 A x s f) = (term134 A s f x).
Proof. exact (@lem7010824 A (term135 A s f) x). Qed.
Lemma lem7010826 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term134 A s f x) = (term87 A s f x).
Proof. exact (eq_refl (term134 A s f x)). Qed.
Lemma lem7010827 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7010828 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term136 A GEN_PVAR_237 s f x) = (term89 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7010827 A GEN_PVAR_237) (@lem7010826 A s f x)). Qed.
Lemma lem7010829 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7010830 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term137 A GEN_PVAR_237 s f x) = (term91 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7010828 A GEN_PVAR_237 s f x) (@lem7010829 A x)). Qed.
Lemma lem7010831 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term138 A GEN_PVAR_237 s f) = (term93 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem7010830 A GEN_PVAR_237 s f x)). Qed.
Lemma lem7010832 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7010833 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term139 A GEN_PVAR_237 s f) = (term95 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7010832 A) (@lem7010831 A GEN_PVAR_237 s f)). Qed.
Lemma lem7010834 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term140 A s f) = (term97 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7010833 A GEN_PVAR_237 s f)). Qed.
Lemma lem7010835 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7010836 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term141 A s f) = (term98 A s f).
Proof. exact (MK_COMB (@lem7010835 A) (@lem7010834 A s f)). Qed.
Lemma lem7010837 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7010838 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term133 A x s f) = (term142 A x s f).
Proof. exact (MK_COMB (@lem7010837 A x) (@lem7010836 A s f)). Qed.
Lemma lem7010839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7010840 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term143 A x s f) = (term144 A x s f).
Proof. exact (MK_COMB (@lem7010839) (@lem7010838 A x s f)). Qed.
Lemma lem7010841 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term134 A s f x) = (term87 A s f x).
Proof. exact (eq_refl (term134 A s f x)). Qed.
Lemma lem7010842 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : ((term133 A x s f) = (term134 A s f x)) = ((term142 A x s f) = (term87 A s f x)).
Proof. exact (MK_COMB (@lem7010840 A x s f) (@lem7010841 A s f x)). Qed.
Lemma lem7010843 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term142 A x s f) = (term87 A s f x).
Proof. exact (EQ_MP (@lem7010842 A s f x) (@lem7010825 A s f x)). Qed.
Lemma lem7010848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7010849 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term145 A x s f) = (term146 A s f x).
Proof. exact (MK_COMB (@lem7010848) (@lem7010843 A s f x)). Qed.
Lemma lem7010851 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7010777 _83095 p x) (@lem7010776 _83095 p x)). Qed.
Lemma lem7010852 {A : Type'} (p : A -> Prop) (x : A) : (term21 A x p) = (p x).
Proof. exact (@lem7010851 A p x). Qed.
Lemma lem7010853 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term133 A x s g) = (term134 A s g x).
Proof. exact (@lem7010852 A (term135 A s g) x). Qed.
Lemma lem7010854 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term134 A s g x) = (term87 A s g x).
Proof. exact (eq_refl (term134 A s g x)). Qed.
Lemma lem7010855 {A : Type'} (GEN_PVAR_298 : A) : (@SETSPEC A GEN_PVAR_298) = (@SETSPEC A GEN_PVAR_298).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_298)). Qed.
Lemma lem7010856 {A : Type'} (GEN_PVAR_298 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term136 A GEN_PVAR_298 s g x) = (term89 A GEN_PVAR_298 s g x).
Proof. exact (MK_COMB (@lem7010855 A GEN_PVAR_298) (@lem7010854 A s g x)). Qed.
Lemma lem7010857 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7010858 {A : Type'} (GEN_PVAR_298 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term137 A GEN_PVAR_298 s g x) = (term91 A GEN_PVAR_298 s g x).
Proof. exact (MK_COMB (@lem7010856 A GEN_PVAR_298 s g x) (@lem7010857 A x)). Qed.
Lemma lem7010859 {A : Type'} (GEN_PVAR_298 : A) (s : A -> Prop) (g : A -> nat) : (term138 A GEN_PVAR_298 s g) = (term93 A GEN_PVAR_298 s g).
Proof. exact (fun_ext (fun x : A => @lem7010858 A GEN_PVAR_298 s g x)). Qed.
Lemma lem7010860 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7010861 {A : Type'} (GEN_PVAR_298 : A) (s : A -> Prop) (g : A -> nat) : (term139 A GEN_PVAR_298 s g) = (term95 A GEN_PVAR_298 s g).
Proof. exact (MK_COMB (@lem7010860 A) (@lem7010859 A GEN_PVAR_298 s g)). Qed.
Lemma lem7010862 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term140 A s g) = (term97 A s g).
Proof. exact (fun_ext (fun GEN_PVAR_298 : A => @lem7010861 A GEN_PVAR_298 s g)). Qed.
Lemma lem7010863 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7010864 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term141 A s g) = (term98 A s g).
Proof. exact (MK_COMB (@lem7010863 A) (@lem7010862 A s g)). Qed.
Lemma lem7010865 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7010866 {A : Type'} (x : A) (s : A -> Prop) (g : A -> nat) : (term133 A x s g) = (term142 A x s g).
Proof. exact (MK_COMB (@lem7010865 A x) (@lem7010864 A s g)). Qed.
Lemma lem7010867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7010868 {A : Type'} (x : A) (s : A -> Prop) (g : A -> nat) : (term143 A x s g) = (term144 A x s g).
Proof. exact (MK_COMB (@lem7010867) (@lem7010866 A x s g)). Qed.
Lemma lem7010869 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term134 A s g x) = (term87 A s g x).
Proof. exact (eq_refl (term134 A s g x)). Qed.
Lemma lem7010870 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : ((term133 A x s g) = (term134 A s g x)) = ((term142 A x s g) = (term87 A s g x)).
Proof. exact (MK_COMB (@lem7010868 A x s g) (@lem7010869 A s g x)). Qed.
Lemma lem7010871 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term142 A x s g) = (term87 A s g x).
Proof. exact (EQ_MP (@lem7010870 A s g x) (@lem7010853 A s g x)). Qed.
Lemma lem7010876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7010877 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term147 A x s g) = (term148 A s g x).
Proof. exact (MK_COMB (@lem7010876) (@lem7010871 A s g x)). Qed.
Lemma lem7010878 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term132 A f x s g) = (term149 A f s g x).
Proof. exact (MK_COMB (@lem7010849 A s f x) (@lem7010877 A s g x)). Qed.
Lemma lem7010881 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term131 A x f s g) = (term149 A f s g x).
Proof. exact (TRANS (@lem7010819 A f x s g) (@lem7010878 A f s g x)). Qed.
Lemma lem7010882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7010883 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term150 A x f s g) = (term151 A f s g x).
Proof. exact (MK_COMB (@lem7010882) (@lem7010881 A f s g x)). Qed.
Lemma lem7010886 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((f x) = (NUMERAL 0)).
Proof. exact (eq_refl ((f x) = (NUMERAL 0))). Qed.
Lemma lem7010887 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term152 A s g f x) = (term153 A s g f x).
Proof. exact (MK_COMB (@lem7010883 A f s g x) (@lem7010886 A f x)). Qed.
Lemma lem7010890 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term154 A s g f) = (term155 A s g f).
Proof. exact (fun_ext (fun x : A => @lem7010887 A s g f x)). Qed.
Lemma lem7010891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7010892 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term156 A s g f) = (term157 A s g f).
Proof. exact (MK_COMB (@lem7010891 A) (@lem7010890 A s g f)). Qed.
Lemma lem7010897 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term158 A s g f) = (term159 A s g f).
Proof. exact (MK_COMB (@lem7010809 A s g h1) (@lem7010892 A s g f)). Qed.
Lemma lem7010899 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7010900 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term159 A s g f) = (term157 A s g f).
Proof. exact (@lem7010899 (term157 A s g f)). Qed.
Lemma lem7010919 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term158 A s g f) = (term157 A s g f).
Proof. exact (TRANS (@lem7010897 A f s g h1) (@lem7010900 A s g f)). Qed.
Lemma lem7010920 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term130 A s f) = (term130 A s f).
Proof. exact (eq_refl (term130 A s f)). Qed.
Lemma lem7010921 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term160 A s g f) = (term161 A s g f).
Proof. exact (MK_COMB (@lem7010920 A s f) (@lem7010919 A f s g h1)). Qed.
Lemma lem7010924 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term161 A s g f) = (term160 A s g f).
Proof. exact (SYM (@lem7010921 A f s g h1)). Qed.
Lemma lem7010926 (p : Prop) : p = (term162 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7010927 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term157 A s g f) = (term163 A s g f).
Proof. exact (@lem7010926 (term157 A s g f)). Qed.
Lemma lem7010928 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term163 A s g f) = (term157 A s g f).
Proof. exact (SYM (@lem7010927 A s g f)). Qed.
Lemma lem7010929 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term164 A s g f) : term164 A s g f.
Proof. exact (h1). Qed.
Lemma lem7010932 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term165 A s g f) : term165 A s g f.
Proof. exact (h1). Qed.
Lemma lem7010933 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : term166 A s g f.
Proof. exact (fun h0 : term165 A s g f => @lem7010932 A s g f h0). Qed.
Lemma lem7010934 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term166 A s g f) : term166 A s g f.
Proof. exact (h1). Qed.
Lemma lem7010935 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term165 A s g f) : term165 A s g f.
Proof. exact (h1). Qed.
Lemma lem7010936 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term165 A s g f) (h2 : term166 A s g f) : term165 A s g f.
Proof. exact (@lem7010934 A s g f h2 (@lem7010935 A s g f h1)). Qed.
Lemma lem7010937 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term165 A s g f) : term167 A s g f.
Proof. exact (fun h0 : term166 A s g f => @lem7010936 A s g f h1 h0). Qed.
Lemma lem7010938 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term166 A s g f) : term166 A s g f.
Proof. exact (h1). Qed.
Lemma lem7010939 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term165 A s g f) (h2 : term166 A s g f) : term165 A s g f.
Proof. exact (@lem7010937 A s g f h1 (@lem7010938 A s g f h2)). Qed.
Lemma lem7010940 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term166 A s g f) : term166 A s g f.
Proof. exact (fun h0 : term165 A s g f => @lem7010939 A s g f h0 h1). Qed.
Lemma lem7010941 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : term168 A s g f.
Proof. exact (fun h0 : term166 A s g f => @lem7010940 A s g f h0). Qed.
Lemma lem7010944 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : term166 A s g f.
Proof. exact (@lem7010941 A s g f (@lem7010933 A s g f)). Qed.
Lemma lem7010945 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : term166 A s g f.
Proof. exact (@lem7010944 A s g f). Qed.
Lemma lem7010989 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7010990 : term169 = term170.
Proof. exact (@lem7010989 term171). Qed.
Lemma lem7011007 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term172 A s g f) = (term172 A s g f).
Proof. exact (eq_refl (term172 A s g f)). Qed.
Lemma lem7011008 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term173 A s g f) = (term174 A s g f).
Proof. exact (MK_COMB (@lem7011007 A s g f) (@lem7010990)). Qed.
Lemma lem7011011 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term175 A s g) = (term175 A s g).
Proof. exact (eq_refl (term175 A s g)). Qed.
Lemma lem7011012 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term176 A s g f) = (term177 A s g f).
Proof. exact (MK_COMB (@lem7011011 A s g) (@lem7011008 A s g f)). Qed.
Lemma lem7011015 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term178 A s f g) = (term178 A s f g).
Proof. exact (eq_refl (term178 A s f g)). Qed.
Lemma lem7011016 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term165 A s g f) = (term179 A s g f).
Proof. exact (MK_COMB (@lem7011015 A s f g) (@lem7011012 A s g f)). Qed.
Lemma lem7011019 {A : Type'} (g : A -> nat) (f : A -> nat) : (term180 A g f) = (term181 A g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011016 A s g f)). Qed.
Lemma lem7011020 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011021 {A : Type'} (g : A -> nat) (f : A -> nat) : (term182 A g f) = (term183 A g f).
Proof. exact (MK_COMB (@lem7011020 A) (@lem7011019 A g f)). Qed.
Lemma lem7011026 {A : Type'} (f : A -> nat) : (term184 A f) = (term185 A f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011021 A g f)). Qed.
Lemma lem7011027 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011028 {A : Type'} (f : A -> nat) : (term186 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem7011027 A) (@lem7011026 A f)). Qed.
Lemma lem7011033 {A : Type'} : (term188 A) = (term189 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7011028 A f)). Qed.
Lemma lem7011034 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011041 {A : Type'} : (term190 A) = (term191 A).
Proof. exact (MK_COMB (@lem7011034 A) (@lem7011033 A)). Qed.
Lemma lem7011042 {A : Type'} (_93554 : type641 A) (h1 : _93554 = (term192 A)) : _93554 = (term192 A).
Proof. exact (h1). Qed.
Lemma lem7011043 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7011044 {A : Type'} (s : A -> Prop) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (_93554 s) = (term193 A s).
Proof. exact (MK_COMB (@lem7011042 A _93554 h1) (@lem7011043 A s)). Qed.
Lemma lem7011045 {A : Type'} (s : A -> Prop) : (term193 A s) = (term194 A s).
Proof. exact (eq_refl (term193 A s)). Qed.
Lemma lem7011046 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term195 A _93554 s) = (term195 A _93554 s).
Proof. exact (eq_refl (term195 A _93554 s)). Qed.
Lemma lem7011047 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : ((_93554 s) = (term193 A s)) = ((_93554 s) = (term194 A s)).
Proof. exact (MK_COMB (@lem7011046 A _93554 s) (@lem7011045 A s)). Qed.
Lemma lem7011048 {A : Type'} (s : A -> Prop) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (_93554 s) = (term194 A s).
Proof. exact (EQ_MP (@lem7011047 A _93554 s) (@lem7011044 A s _93554 h1)). Qed.
Lemma lem7011049 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7011050 {A : Type'} (s : A -> Prop) (g : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (_93554 s g) = (term196 A s g).
Proof. exact (MK_COMB (@lem7011048 A s _93554 h1) (@lem7011049 A g)). Qed.
Lemma lem7011051 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term196 A s g) = (term97 A s g).
Proof. exact (eq_refl (term196 A s g)). Qed.
Lemma lem7011052 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term197 A _93554 s g) = (term197 A _93554 s g).
Proof. exact (eq_refl (term197 A _93554 s g)). Qed.
Lemma lem7011053 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g) = (term196 A s g)) = ((_93554 s g) = (term97 A s g)).
Proof. exact (MK_COMB (@lem7011052 A _93554 s g) (@lem7011051 A s g)). Qed.
Lemma lem7011054 {A : Type'} (s : A -> Prop) (g : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (_93554 s g) = (term97 A s g).
Proof. exact (EQ_MP (@lem7011053 A _93554 s g) (@lem7011050 A s g _93554 h1)). Qed.
Lemma lem7011080 (m : nat) (n : nat) : ((term198 m n) = (term199 m n)) = ((term198 m n) = (term199 m n)).
Proof. exact (eq_refl ((term198 m n) = (term199 m n))). Qed.
Lemma lem7011081 (m : nat) : (term200 m) = (term200 m).
Proof. exact (fun_ext (fun n : nat => @lem7011080 m n)). Qed.
Lemma lem7011082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7011083 (m : nat) : (term201 m) = (term201 m).
Proof. exact (MK_COMB (@lem7011082) (@lem7011081 m)). Qed.
Lemma lem7011084 : term202 = term202.
Proof. exact (fun_ext (fun m : nat => @lem7011083 m)). Qed.
Lemma lem7011085 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7011086 : term203 = term203.
Proof. exact (MK_COMB (@lem7011085) (@lem7011084)). Qed.
Lemma lem7011103 (m : nat) : ((term204 m) = (m = (NUMERAL 0))) = ((term204 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl ((term204 m) = (m = (NUMERAL 0)))). Qed.
Lemma lem7011104 : term205 = term205.
Proof. exact (fun_ext (fun m : nat => @lem7011103 m)). Qed.
Lemma lem7011105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7011106 : term206 = term206.
Proof. exact (MK_COMB (@lem7011105) (@lem7011104)). Qed.
Lemma lem7011107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011108 : term207 = term207.
Proof. exact (MK_COMB (@lem7011107) (@lem7011106)). Qed.
Lemma lem7011109 : term171 = term171.
Proof. exact (MK_COMB (@lem7011108) (@lem7011086)). Qed.
Lemma lem7011110 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7011111 : term170 = term170.
Proof. exact (MK_COMB (@lem7011110) (@lem7011109)). Qed.
Lemma lem7011166 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term153 A s g f x) = (term153 A s g f x).
Proof. exact (eq_refl (term153 A s g f x)). Qed.
Lemma lem7011167 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term155 A s g f) = (term155 A s g f).
Proof. exact (fun_ext (fun x : A => @lem7011166 A s g f x)). Qed.
Lemma lem7011168 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011169 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term157 A s g f) = (term157 A s g f).
Proof. exact (MK_COMB (@lem7011168 A) (@lem7011167 A s g f)). Qed.
Lemma lem7011170 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7011171 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term164 A s g f) = (term164 A s g f).
Proof. exact (MK_COMB (@lem7011170) (@lem7011169 A s g f)). Qed.
Lemma lem7011172 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7011173 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term172 A s g f) = (term172 A s g f).
Proof. exact (MK_COMB (@lem7011172) (@lem7011171 A s g f)). Qed.
Lemma lem7011174 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term174 A s g f) = (term174 A s g f).
Proof. exact (MK_COMB (@lem7011173 A s g f) (@lem7011111)). Qed.
Lemma lem7011176 {A : Type'} (s : A -> Prop) (g : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term97 A s g) = (_93554 s g).
Proof. exact (SYM (@lem7011054 A s g _93554 h1)). Qed.
Lemma lem7011177 {A : Type'} (s : A -> Prop) (g : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term97 A s g) = (_93554 s g).
Proof. exact (@lem7011176 A s g _93554 h1). Qed.
Lemma lem7011178 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7011179 {A : Type'} (s : A -> Prop) (g : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term98 A s g) = (term208 A _93554 s g).
Proof. exact (MK_COMB (@lem7011178 A) (@lem7011177 A s g _93554 h1)). Qed.
Lemma lem7011180 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem7011181 {A : Type'} (s : A -> Prop) (g : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term75 A s g) = (term209 A _93554 s g).
Proof. exact (MK_COMB (@lem7011180 A) (@lem7011179 A s g _93554 h1)). Qed.
Lemma lem7011182 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7011183 {A : Type'} (s : A -> Prop) (g : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term175 A s g) = (term210 A _93554 s g).
Proof. exact (MK_COMB (@lem7011182) (@lem7011181 A s g _93554 h1)). Qed.
Lemma lem7011184 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term177 A s g f) = (term211 A _93554 s g f).
Proof. exact (MK_COMB (@lem7011183 A s g _93554 h1) (@lem7011174 A s g f)). Qed.
Lemma lem7011201 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term212 A s f g x) = (term212 A s f g x).
Proof. exact (eq_refl (term212 A s f g x)). Qed.
Lemma lem7011202 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term213 A s f g) = (term213 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7011201 A s f g x)). Qed.
Lemma lem7011203 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011204 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term76 A s f g) = (term76 A s f g).
Proof. exact (MK_COMB (@lem7011203 A) (@lem7011202 A s f g)). Qed.
Lemma lem7011205 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7011206 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term178 A s f g) = (term178 A s f g).
Proof. exact (MK_COMB (@lem7011205) (@lem7011204 A s f g)). Qed.
Lemma lem7011207 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term179 A s g f) = (term214 A _93554 s g f).
Proof. exact (MK_COMB (@lem7011206 A s f g) (@lem7011184 A s g f _93554 h1)). Qed.
Lemma lem7011208 {A : Type'} (g : A -> nat) (f : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term181 A g f) = (term215 A _93554 g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011207 A s g f _93554 h1)). Qed.
Lemma lem7011209 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011210 {A : Type'} (g : A -> nat) (f : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term183 A g f) = (term216 A _93554 g f).
Proof. exact (MK_COMB (@lem7011209 A) (@lem7011208 A g f _93554 h1)). Qed.
Lemma lem7011211 {A : Type'} (f : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term185 A f) = (term217 A _93554 f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011210 A g f _93554 h1)). Qed.
Lemma lem7011212 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011213 {A : Type'} (f : A -> nat) (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term187 A f) = (term218 A _93554 f).
Proof. exact (MK_COMB (@lem7011212 A) (@lem7011211 A f _93554 h1)). Qed.
Lemma lem7011214 {A : Type'} (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term189 A) = (term219 A _93554).
Proof. exact (fun_ext (fun f : A -> nat => @lem7011213 A f _93554 h1)). Qed.
Lemma lem7011215 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011216 {A : Type'} (_93554 : type641 A) (h1 : _93554 = (term192 A)) : (term191 A) = (term220 A _93554).
Proof. exact (MK_COMB (@lem7011215 A) (@lem7011214 A _93554 h1)). Qed.
Lemma lem7011217 {A : Type'} (_93554 : type641 A) : term221 A _93554.
Proof. exact (fun h0 : _93554 = (term192 A) => @lem7011216 A _93554 h0). Qed.
Lemma lem7011218 {A : Type'} : term222 A.
Proof. exact (fun _93554 : type641 A => @lem7011217 A _93554). Qed.
Lemma lem7011220 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term223 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem7011221 {A : Type'} (P : Prop) (c : type641 A) (Q : type143 A) : term224 A P c Q.
Proof. exact (@lem7011220 (type641 A) P c Q). Qed.
Lemma lem7011222 {A : Type'} : term225 A.
Proof. exact (@lem7011221 A (term191 A) (term192 A) (term226 A)). Qed.
Lemma lem7011223 {A : Type'} (_93554 : type641 A) : (term227 A _93554) = (term220 A _93554).
Proof. exact (eq_refl (term227 A _93554)). Qed.
Lemma lem7011224 {A : Type'} : (term228 A) = (term228 A).
Proof. exact (eq_refl (term228 A)). Qed.
Lemma lem7011225 {A : Type'} (_93554 : type641 A) : ((term191 A) = (term227 A _93554)) = ((term191 A) = (term220 A _93554)).
Proof. exact (MK_COMB (@lem7011224 A) (@lem7011223 A _93554)). Qed.
Lemma lem7011226 {A : Type'} (_93554 : type641 A) : (term229 A _93554) = (term229 A _93554).
Proof. exact (eq_refl (term229 A _93554)). Qed.
Lemma lem7011227 {A : Type'} (_93554 : type641 A) : (term230 A _93554) = (term221 A _93554).
Proof. exact (MK_COMB (@lem7011226 A _93554) (@lem7011225 A _93554)). Qed.
Lemma lem7011228 {A : Type'} : (term231 A) = (term232 A).
Proof. exact (fun_ext (fun _93554 : type641 A => @lem7011227 A _93554)). Qed.
Lemma lem7011229 {A : Type'} : (@all ((A -> Prop) -> (A -> nat) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> nat) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> nat) -> A -> Prop))). Qed.
Lemma lem7011230 {A : Type'} : (term233 A) = (term222 A).
Proof. exact (MK_COMB (@lem7011229 A) (@lem7011228 A)). Qed.
Lemma lem7011231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7011232 {A : Type'} : (term234 A) = (term235 A).
Proof. exact (MK_COMB (@lem7011231) (@lem7011230 A)). Qed.
Lemma lem7011233 {A : Type'} (_93554 : type641 A) : (term227 A _93554) = (term220 A _93554).
Proof. exact (eq_refl (term227 A _93554)). Qed.
Lemma lem7011234 {A : Type'} (_93554 : type641 A) : (term229 A _93554) = (term229 A _93554).
Proof. exact (eq_refl (term229 A _93554)). Qed.
Lemma lem7011235 {A : Type'} (_93554 : type641 A) : (term236 A _93554) = (term237 A _93554).
Proof. exact (MK_COMB (@lem7011234 A _93554) (@lem7011233 A _93554)). Qed.
Lemma lem7011236 {A : Type'} : (term238 A) = (term239 A).
Proof. exact (fun_ext (fun _93554 : type641 A => @lem7011235 A _93554)). Qed.
Lemma lem7011237 {A : Type'} : (@all ((A -> Prop) -> (A -> nat) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> nat) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> nat) -> A -> Prop))). Qed.
Lemma lem7011238 {A : Type'} : (term240 A) = (term241 A).
Proof. exact (MK_COMB (@lem7011237 A) (@lem7011236 A)). Qed.
Lemma lem7011239 {A : Type'} : (term228 A) = (term228 A).
Proof. exact (eq_refl (term228 A)). Qed.
Lemma lem7011240 {A : Type'} : ((term191 A) = (term240 A)) = ((term191 A) = (term241 A)).
Proof. exact (MK_COMB (@lem7011239 A) (@lem7011238 A)). Qed.
Lemma lem7011241 {A : Type'} : (term225 A) = (term242 A).
Proof. exact (MK_COMB (@lem7011232 A) (@lem7011240 A)). Qed.
Lemma lem7011242 {A : Type'} : term242 A.
Proof. exact (EQ_MP (@lem7011241 A) (@lem7011222 A)). Qed.
Lemma lem7011243 {A : Type'} : (term191 A) = (term241 A).
Proof. exact (@lem7011242 A (@lem7011218 A)). Qed.
Lemma lem7011245 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term243 _3571 _3575 t)) = (term244 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7011246 {A : Type'} (s : type641 A) (t : type641 A) : (s = (term245 A t)) = (term246 A s t).
Proof. exact (@lem7011245 (type699 A) (A -> Prop) s t). Qed.
Lemma lem7011247 {A : Type'} (_93554 : type641 A) : (_93554 = (term247 A)) = (term248 A _93554).
Proof. exact (@lem7011246 A _93554 (term192 A)). Qed.
Lemma lem7011248 {A : Type'} (s : A -> Prop) : (term193 A s) = (term194 A s).
Proof. exact (eq_refl (term193 A s)). Qed.
Lemma lem7011249 {A : Type'} : (term247 A) = (term192 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011248 A s)). Qed.
Lemma lem7011250 {A : Type'} (_93554 : type641 A) : (@eq ((A -> Prop) -> (A -> nat) -> A -> Prop) _93554) = (@eq ((A -> Prop) -> (A -> nat) -> A -> Prop) _93554).
Proof. exact (eq_refl (@eq ((A -> Prop) -> (A -> nat) -> A -> Prop) _93554)). Qed.
Lemma lem7011251 {A : Type'} (_93554 : type641 A) : (_93554 = (term247 A)) = (_93554 = (term192 A)).
Proof. exact (MK_COMB (@lem7011250 A _93554) (@lem7011249 A)). Qed.
Lemma lem7011252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7011253 {A : Type'} (_93554 : type641 A) : (term249 A _93554) = (term250 A _93554).
Proof. exact (MK_COMB (@lem7011252) (@lem7011251 A _93554)). Qed.
Lemma lem7011254 {A : Type'} (s : A -> Prop) : (term193 A s) = (term194 A s).
Proof. exact (eq_refl (term193 A s)). Qed.
Lemma lem7011255 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term195 A _93554 s) = (term195 A _93554 s).
Proof. exact (eq_refl (term195 A _93554 s)). Qed.
Lemma lem7011256 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : ((_93554 s) = (term193 A s)) = ((_93554 s) = (term194 A s)).
Proof. exact (MK_COMB (@lem7011255 A _93554 s) (@lem7011254 A s)). Qed.
Lemma lem7011257 {A : Type'} (_93554 : type641 A) : (term251 A _93554) = (term252 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011256 A _93554 s)). Qed.
Lemma lem7011258 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011259 {A : Type'} (_93554 : type641 A) : (term248 A _93554) = (term253 A _93554).
Proof. exact (MK_COMB (@lem7011258 A) (@lem7011257 A _93554)). Qed.
Lemma lem7011260 {A : Type'} (_93554 : type641 A) : ((_93554 = (term247 A)) = (term248 A _93554)) = ((_93554 = (term192 A)) = (term253 A _93554)).
Proof. exact (MK_COMB (@lem7011253 A _93554) (@lem7011259 A _93554)). Qed.
Lemma lem7011261 {A : Type'} (_93554 : type641 A) : (_93554 = (term192 A)) = (term253 A _93554).
Proof. exact (EQ_MP (@lem7011260 A _93554) (@lem7011247 A _93554)). Qed.
Lemma lem7011263 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term243 _3571 _3575 t)) = (term244 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7011264 {A : Type'} (s : type699 A) (t : type699 A) : (s = (term254 A t)) = (term255 A s t).
Proof. exact (@lem7011263 (A -> Prop) (A -> nat) s t). Qed.
Lemma lem7011265 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : ((_93554 s) = (term256 A s)) = (term257 A _93554 s).
Proof. exact (@lem7011264 A (_93554 s) (term194 A s)). Qed.
Lemma lem7011266 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term196 A s g) = (term97 A s g).
Proof. exact (eq_refl (term196 A s g)). Qed.
Lemma lem7011267 {A : Type'} (s : A -> Prop) : (term256 A s) = (term194 A s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011266 A s g)). Qed.
Lemma lem7011268 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term195 A _93554 s) = (term195 A _93554 s).
Proof. exact (eq_refl (term195 A _93554 s)). Qed.
Lemma lem7011269 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : ((_93554 s) = (term256 A s)) = ((_93554 s) = (term194 A s)).
Proof. exact (MK_COMB (@lem7011268 A _93554 s) (@lem7011267 A s)). Qed.
Lemma lem7011270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7011271 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term258 A _93554 s) = (term259 A _93554 s).
Proof. exact (MK_COMB (@lem7011270) (@lem7011269 A _93554 s)). Qed.
Lemma lem7011272 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term196 A s g) = (term97 A s g).
Proof. exact (eq_refl (term196 A s g)). Qed.
Lemma lem7011273 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term197 A _93554 s g) = (term197 A _93554 s g).
Proof. exact (eq_refl (term197 A _93554 s g)). Qed.
Lemma lem7011274 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g) = (term196 A s g)) = ((_93554 s g) = (term97 A s g)).
Proof. exact (MK_COMB (@lem7011273 A _93554 s g) (@lem7011272 A s g)). Qed.
Lemma lem7011275 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term260 A _93554 s) = (term261 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011274 A _93554 s g)). Qed.
Lemma lem7011276 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011277 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term257 A _93554 s) = (term262 A _93554 s).
Proof. exact (MK_COMB (@lem7011276 A) (@lem7011275 A _93554 s)). Qed.
Lemma lem7011278 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (((_93554 s) = (term256 A s)) = (term257 A _93554 s)) = (((_93554 s) = (term194 A s)) = (term262 A _93554 s)).
Proof. exact (MK_COMB (@lem7011271 A _93554 s) (@lem7011277 A _93554 s)). Qed.
Lemma lem7011279 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : ((_93554 s) = (term194 A s)) = (term262 A _93554 s).
Proof. exact (EQ_MP (@lem7011278 A _93554 s) (@lem7011265 A _93554 s)). Qed.
Lemma lem7011281 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term243 _3571 _3575 t)) = (term244 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem7011282 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = (term263 A t)) = (term264 A s t).
Proof. exact (@lem7011281 Prop A s t). Qed.
Lemma lem7011283 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g) = (term265 A s g)) = (term266 A _93554 s g).
Proof. exact (@lem7011282 A (_93554 s g) (term97 A s g)). Qed.
Lemma lem7011284 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term267 A s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g).
Proof. exact (eq_refl (term267 A s g GEN_PVAR_299)). Qed.
Lemma lem7011285 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term265 A s g) = (term97 A s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7011284 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011286 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term197 A _93554 s g) = (term197 A _93554 s g).
Proof. exact (eq_refl (term197 A _93554 s g)). Qed.
Lemma lem7011287 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g) = (term265 A s g)) = ((_93554 s g) = (term97 A s g)).
Proof. exact (MK_COMB (@lem7011286 A _93554 s g) (@lem7011285 A s g)). Qed.
Lemma lem7011288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7011289 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term268 A _93554 s g) = (term269 A _93554 s g).
Proof. exact (MK_COMB (@lem7011288) (@lem7011287 A _93554 s g)). Qed.
Lemma lem7011290 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term267 A s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g).
Proof. exact (eq_refl (term267 A s g GEN_PVAR_299)). Qed.
Lemma lem7011291 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (GEN_PVAR_299 : A) : (term270 A _93554 s g GEN_PVAR_299) = (term270 A _93554 s g GEN_PVAR_299).
Proof. exact (eq_refl (term270 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7011292 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g GEN_PVAR_299) = (term267 A s g GEN_PVAR_299)) = ((_93554 s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g)).
Proof. exact (MK_COMB (@lem7011291 A _93554 s g GEN_PVAR_299) (@lem7011290 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011293 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term271 A _93554 s g) = (term272 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7011292 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011294 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011295 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term266 A _93554 s g) = (term273 A _93554 s g).
Proof. exact (MK_COMB (@lem7011294 A) (@lem7011293 A _93554 s g)). Qed.
Lemma lem7011296 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (((_93554 s g) = (term265 A s g)) = (term266 A _93554 s g)) = (((_93554 s g) = (term97 A s g)) = (term273 A _93554 s g)).
Proof. exact (MK_COMB (@lem7011289 A _93554 s g) (@lem7011295 A _93554 s g)). Qed.
Lemma lem7011297 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g) = (term97 A s g)) = (term273 A _93554 s g).
Proof. exact (EQ_MP (@lem7011296 A _93554 s g) (@lem7011283 A _93554 s g)). Qed.
Lemma lem7011298 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g)) = ((_93554 s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g)).
Proof. exact (eq_refl ((_93554 s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g))). Qed.
Lemma lem7011299 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term272 A _93554 s g) = (term272 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7011298 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011300 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011301 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term273 A _93554 s g) = (term273 A _93554 s g).
Proof. exact (MK_COMB (@lem7011300 A) (@lem7011299 A _93554 s g)). Qed.
Lemma lem7011302 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g) = (term97 A s g)) = (term273 A _93554 s g).
Proof. exact (TRANS (@lem7011297 A _93554 s g) (@lem7011301 A _93554 s g)). Qed.
Lemma lem7011303 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term261 A _93554 s) = (term274 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011302 A _93554 s g)). Qed.
Lemma lem7011304 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011305 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term262 A _93554 s) = (term275 A _93554 s).
Proof. exact (MK_COMB (@lem7011304 A) (@lem7011303 A _93554 s)). Qed.
Lemma lem7011306 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : ((_93554 s) = (term194 A s)) = (term275 A _93554 s).
Proof. exact (TRANS (@lem7011279 A _93554 s) (@lem7011305 A _93554 s)). Qed.
Lemma lem7011307 {A : Type'} (_93554 : type641 A) : (term252 A _93554) = (term276 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011306 A _93554 s)). Qed.
Lemma lem7011308 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011309 {A : Type'} (_93554 : type641 A) : (term253 A _93554) = (term277 A _93554).
Proof. exact (MK_COMB (@lem7011308 A) (@lem7011307 A _93554)). Qed.
Lemma lem7011310 {A : Type'} (_93554 : type641 A) : (_93554 = (term192 A)) = (term277 A _93554).
Proof. exact (TRANS (@lem7011261 A _93554) (@lem7011309 A _93554)). Qed.
Lemma lem7011311 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7011312 {A : Type'} (_93554 : type641 A) : (term229 A _93554) = (term278 A _93554).
Proof. exact (MK_COMB (@lem7011311) (@lem7011310 A _93554)). Qed.
Lemma lem7011313 {A : Type'} (_93554 : type641 A) : (term220 A _93554) = (term220 A _93554).
Proof. exact (eq_refl (term220 A _93554)). Qed.
Lemma lem7011314 {A : Type'} (_93554 : type641 A) : (term237 A _93554) = (term279 A _93554).
Proof. exact (MK_COMB (@lem7011312 A _93554) (@lem7011313 A _93554)). Qed.
Lemma lem7011315 {A : Type'} : (term239 A) = (term280 A).
Proof. exact (fun_ext (fun _93554 : type641 A => @lem7011314 A _93554)). Qed.
Lemma lem7011316 {A : Type'} : (@all ((A -> Prop) -> (A -> nat) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> nat) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> nat) -> A -> Prop))). Qed.
Lemma lem7011317 {A : Type'} : (term241 A) = (term281 A).
Proof. exact (MK_COMB (@lem7011316 A) (@lem7011315 A)). Qed.
Lemma lem7011318 {A : Type'} : (term228 A) = (term228 A).
Proof. exact (eq_refl (term228 A)). Qed.
Lemma lem7011319 {A : Type'} : ((term191 A) = (term241 A)) = ((term191 A) = (term281 A)).
Proof. exact (MK_COMB (@lem7011318 A) (@lem7011317 A)). Qed.
Lemma lem7011322 {A : Type'} : (term191 A) = (term281 A).
Proof. exact (EQ_MP (@lem7011319 A) (@lem7011243 A)). Qed.
Lemma lem7011323 {A : Type'} : (term190 A) = (term281 A).
Proof. exact (TRANS (@lem7011041 A) (@lem7011322 A)). Qed.
Lemma lem7011332 (m : nat) (n : nat) : ((term198 m n) = (term199 m n)) = ((term198 m n) = (term199 m n)).
Proof. exact (eq_refl ((term198 m n) = (term199 m n))). Qed.
Lemma lem7011333 (m : nat) : (term200 m) = (term200 m).
Proof. exact (fun_ext (fun n : nat => @lem7011332 m n)). Qed.
Lemma lem7011334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7011335 (m : nat) : (term201 m) = (term201 m).
Proof. exact (MK_COMB (@lem7011334) (@lem7011333 m)). Qed.
Lemma lem7011336 : term202 = term202.
Proof. exact (fun_ext (fun m : nat => @lem7011335 m)). Qed.
Lemma lem7011337 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7011338 : term203 = term203.
Proof. exact (MK_COMB (@lem7011337) (@lem7011336)). Qed.
Lemma lem7011343 (m : nat) : ((term204 m) = (m = (NUMERAL 0))) = ((term204 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl ((term204 m) = (m = (NUMERAL 0)))). Qed.
Lemma lem7011344 : term205 = term205.
Proof. exact (fun_ext (fun m : nat => @lem7011343 m)). Qed.
Lemma lem7011345 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7011346 : term206 = term206.
Proof. exact (MK_COMB (@lem7011345) (@lem7011344)). Qed.
Lemma lem7011347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011348 : term207 = term207.
Proof. exact (MK_COMB (@lem7011347) (@lem7011346)). Qed.
Lemma lem7011349 : term171 = term171.
Proof. exact (MK_COMB (@lem7011348) (@lem7011338)). Qed.
Lemma lem7011350 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7011351 : term170 = term170.
Proof. exact (MK_COMB (@lem7011350) (@lem7011349)). Qed.
Lemma lem7011374 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term153 A s g f x) = (term153 A s g f x).
Proof. exact (eq_refl (term153 A s g f x)). Qed.
Lemma lem7011375 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term155 A s g f) = (term155 A s g f).
Proof. exact (fun_ext (fun x : A => @lem7011374 A s g f x)). Qed.
Lemma lem7011376 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011377 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term157 A s g f) = (term157 A s g f).
Proof. exact (MK_COMB (@lem7011376 A) (@lem7011375 A s g f)). Qed.
Lemma lem7011378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7011379 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term164 A s g f) = (term164 A s g f).
Proof. exact (MK_COMB (@lem7011378) (@lem7011377 A s g f)). Qed.
Lemma lem7011380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7011381 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term172 A s g f) = (term172 A s g f).
Proof. exact (MK_COMB (@lem7011380) (@lem7011379 A s g f)). Qed.
Lemma lem7011382 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term174 A s g f) = (term174 A s g f).
Proof. exact (MK_COMB (@lem7011381 A s g f) (@lem7011351)). Qed.
Lemma lem7011385 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term210 A _93554 s g) = (term210 A _93554 s g).
Proof. exact (eq_refl (term210 A _93554 s g)). Qed.
Lemma lem7011386 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term211 A _93554 s g f) = (term211 A _93554 s g f).
Proof. exact (MK_COMB (@lem7011385 A _93554 s g) (@lem7011382 A s g f)). Qed.
Lemma lem7011391 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term212 A s f g x) = (term212 A s f g x).
Proof. exact (eq_refl (term212 A s f g x)). Qed.
Lemma lem7011392 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term213 A s f g) = (term213 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7011391 A s f g x)). Qed.
Lemma lem7011393 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011394 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term76 A s f g) = (term76 A s f g).
Proof. exact (MK_COMB (@lem7011393 A) (@lem7011392 A s f g)). Qed.
Lemma lem7011395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7011396 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term178 A s f g) = (term178 A s f g).
Proof. exact (MK_COMB (@lem7011395) (@lem7011394 A s f g)). Qed.
Lemma lem7011397 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term214 A _93554 s g f) = (term214 A _93554 s g f).
Proof. exact (MK_COMB (@lem7011396 A s f g) (@lem7011386 A _93554 s g f)). Qed.
Lemma lem7011398 {A : Type'} (_93554 : type641 A) (g : A -> nat) (f : A -> nat) : (term215 A _93554 g f) = (term215 A _93554 g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011397 A _93554 s g f)). Qed.
Lemma lem7011399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011400 {A : Type'} (_93554 : type641 A) (g : A -> nat) (f : A -> nat) : (term216 A _93554 g f) = (term216 A _93554 g f).
Proof. exact (MK_COMB (@lem7011399 A) (@lem7011398 A _93554 g f)). Qed.
Lemma lem7011401 {A : Type'} (_93554 : type641 A) (f : A -> nat) : (term217 A _93554 f) = (term217 A _93554 f).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011400 A _93554 g f)). Qed.
Lemma lem7011402 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011403 {A : Type'} (_93554 : type641 A) (f : A -> nat) : (term218 A _93554 f) = (term218 A _93554 f).
Proof. exact (MK_COMB (@lem7011402 A) (@lem7011401 A _93554 f)). Qed.
Lemma lem7011404 {A : Type'} (_93554 : type641 A) : (term219 A _93554) = (term219 A _93554).
Proof. exact (fun_ext (fun f : A -> nat => @lem7011403 A _93554 f)). Qed.
Lemma lem7011405 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011406 {A : Type'} (_93554 : type641 A) : (term220 A _93554) = (term220 A _93554).
Proof. exact (MK_COMB (@lem7011405 A) (@lem7011404 A _93554)). Qed.
Lemma lem7011407 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term91 A GEN_PVAR_299 s g x) = (term91 A GEN_PVAR_299 s g x).
Proof. exact (eq_refl (term91 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7011408 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term93 A GEN_PVAR_299 s g) = (term93 A GEN_PVAR_299 s g).
Proof. exact (fun_ext (fun x : A => @lem7011407 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7011409 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7011410 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term95 A GEN_PVAR_299 s g) = (term95 A GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011409 A) (@lem7011408 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011413 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (GEN_PVAR_299 : A) : (term270 A _93554 s g GEN_PVAR_299) = (term270 A _93554 s g GEN_PVAR_299).
Proof. exact (eq_refl (term270 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7011414 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g)) = ((_93554 s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g)).
Proof. exact (MK_COMB (@lem7011413 A _93554 s g GEN_PVAR_299) (@lem7011410 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011415 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term272 A _93554 s g) = (term272 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7011414 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011416 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011417 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term273 A _93554 s g) = (term273 A _93554 s g).
Proof. exact (MK_COMB (@lem7011416 A) (@lem7011415 A _93554 s g)). Qed.
Lemma lem7011418 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term274 A _93554 s) = (term274 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011417 A _93554 s g)). Qed.
Lemma lem7011419 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011420 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term275 A _93554 s) = (term275 A _93554 s).
Proof. exact (MK_COMB (@lem7011419 A) (@lem7011418 A _93554 s)). Qed.
Lemma lem7011421 {A : Type'} (_93554 : type641 A) : (term276 A _93554) = (term276 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011420 A _93554 s)). Qed.
Lemma lem7011422 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011423 {A : Type'} (_93554 : type641 A) : (term277 A _93554) = (term277 A _93554).
Proof. exact (MK_COMB (@lem7011422 A) (@lem7011421 A _93554)). Qed.
Lemma lem7011424 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7011425 {A : Type'} (_93554 : type641 A) : (term278 A _93554) = (term278 A _93554).
Proof. exact (MK_COMB (@lem7011424) (@lem7011423 A _93554)). Qed.
Lemma lem7011426 {A : Type'} (_93554 : type641 A) : (term279 A _93554) = (term279 A _93554).
Proof. exact (MK_COMB (@lem7011425 A _93554) (@lem7011406 A _93554)). Qed.
Lemma lem7011427 {A : Type'} : (term280 A) = (term280 A).
Proof. exact (fun_ext (fun _93554 : type641 A => @lem7011426 A _93554)). Qed.
Lemma lem7011428 {A : Type'} : (@all ((A -> Prop) -> (A -> nat) -> A -> Prop)) = (@all ((A -> Prop) -> (A -> nat) -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> nat) -> A -> Prop))). Qed.
Lemma lem7011429 {A : Type'} : (term281 A) = (term281 A).
Proof. exact (MK_COMB (@lem7011428 A) (@lem7011427 A)). Qed.
Lemma lem7011534 {A : Type'} : (term190 A) = (term281 A).
Proof. exact (TRANS (@lem7011323 A) (@lem7011429 A)). Qed.
Lemma lem7011535 {A : Type'} : (term281 A) = (term190 A).
Proof. exact (SYM (@lem7011534 A)). Qed.
Lemma lem7011536 {A : Type'} (_93554 : type641 A) (h1 : term277 A _93554) : term277 A _93554.
Proof. exact (h1). Qed.
Lemma lem7011537 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term76 A s f g.
Proof. exact (h1). Qed.
Lemma lem7011539 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term164 A s g f) : term164 A s g f.
Proof. exact (h1). Qed.
Lemma lem7011540 (h1 : term171) : term171.
Proof. exact (h1). Qed.
Lemma lem7011544 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term91 A GEN_PVAR_299 s g x) = (term91 A GEN_PVAR_299 s g x).
Proof. exact (eq_refl (term91 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7011545 {A : Type'} (P : A -> Prop) : (term282 A P) = (term283 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7011546 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term284 A GEN_PVAR_299 s g) = (term285 A GEN_PVAR_299 s g).
Proof. exact (@lem7011545 A (term93 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011547 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term286 A GEN_PVAR_299 s g x) = (term91 A GEN_PVAR_299 s g x).
Proof. exact (eq_refl (term286 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7011548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7011550 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term287 A GEN_PVAR_299 s g x) = (term288 A GEN_PVAR_299 s g x).
Proof. exact (MK_COMB (@lem7011548) (@lem7011547 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7011551 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term289 A GEN_PVAR_299 s g) = (term290 A GEN_PVAR_299 s g).
Proof. exact (fun_ext (fun x : A => @lem7011550 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7011552 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011553 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term285 A GEN_PVAR_299 s g) = (term291 A GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011552 A) (@lem7011551 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011554 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term284 A GEN_PVAR_299 s g) = (term291 A GEN_PVAR_299 s g).
Proof. exact (TRANS (@lem7011546 A GEN_PVAR_299 s g) (@lem7011553 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011555 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term93 A GEN_PVAR_299 s g) = (term93 A GEN_PVAR_299 s g).
Proof. exact (fun_ext (fun x : A => @lem7011544 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7011556 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7011557 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term95 A GEN_PVAR_299 s g) = (term95 A GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011556 A) (@lem7011555 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011559 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (GEN_PVAR_299 : A) : (term292 A _93554 s g GEN_PVAR_299) = (term292 A _93554 s g GEN_PVAR_299).
Proof. exact (eq_refl (term292 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7011560 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term293 A _93554 GEN_PVAR_299 s g) = (term293 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011559 A _93554 s g GEN_PVAR_299) (@lem7011557 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011562 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (GEN_PVAR_299 : A) : (term294 A _93554 s g GEN_PVAR_299) = (term294 A _93554 s g GEN_PVAR_299).
Proof. exact (eq_refl (term294 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7011563 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term295 A _93554 GEN_PVAR_299 s g) = (term296 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011562 A _93554 s g GEN_PVAR_299) (@lem7011554 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011565 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term297 A _93554 GEN_PVAR_299 s g) = (term298 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011564) (@lem7011563 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011566 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term299 A _93554 GEN_PVAR_299 s g) = (term300 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011565 A _93554 GEN_PVAR_299 s g) (@lem7011560 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011567 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g)) = (term299 A _93554 GEN_PVAR_299 s g).
Proof. exact (@lem17784 (_93554 s g GEN_PVAR_299) (term95 A GEN_PVAR_299 s g)). Qed.
Lemma lem7011568 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : ((_93554 s g GEN_PVAR_299) = (term95 A GEN_PVAR_299 s g)) = (term300 A _93554 GEN_PVAR_299 s g).
Proof. exact (TRANS (@lem7011567 A _93554 GEN_PVAR_299 s g) (@lem7011566 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011569 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term272 A _93554 s g) = (term301 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7011568 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011570 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011571 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term273 A _93554 s g) = (term302 A _93554 s g).
Proof. exact (MK_COMB (@lem7011570 A) (@lem7011569 A _93554 s g)). Qed.
Lemma lem7011572 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term274 A _93554 s) = (term303 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011571 A _93554 s g)). Qed.
Lemma lem7011573 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011574 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term275 A _93554 s) = (term304 A _93554 s).
Proof. exact (MK_COMB (@lem7011573 A) (@lem7011572 A _93554 s)). Qed.
Lemma lem7011575 {A : Type'} (_93554 : type641 A) : (term276 A _93554) = (term305 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011574 A _93554 s)). Qed.
Lemma lem7011576 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011577 {A : Type'} (_93554 : type641 A) : (term277 A _93554) = (term306 A _93554).
Proof. exact (MK_COMB (@lem7011576 A) (@lem7011575 A _93554)). Qed.
Lemma lem7011587 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7011588 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (@lem7011587 A P Q). Qed.
Lemma lem7011589 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term309 A _93554 s g) = (term310 A _93554 s g).
Proof. exact (@lem7011588 A (term311 A _93554 s g) (term312 A _93554 s g)). Qed.
Lemma lem7011590 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term313 A _93554 s g GEN_PVAR_299) = (term296 A _93554 GEN_PVAR_299 s g).
Proof. exact (eq_refl (term313 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7011591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011592 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term314 A _93554 s g GEN_PVAR_299) = (term298 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011591) (@lem7011590 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011593 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term315 A _93554 s g GEN_PVAR_299) = (term293 A _93554 GEN_PVAR_299 s g).
Proof. exact (eq_refl (term315 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7011594 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term316 A _93554 s g GEN_PVAR_299) = (term300 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7011592 A _93554 GEN_PVAR_299 s g) (@lem7011593 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011595 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term317 A _93554 s g) = (term301 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7011594 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011596 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011597 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term309 A _93554 s g) = (term302 A _93554 s g).
Proof. exact (MK_COMB (@lem7011596 A) (@lem7011595 A _93554 s g)). Qed.
Lemma lem7011598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7011599 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term318 A _93554 s g) = (term319 A _93554 s g).
Proof. exact (MK_COMB (@lem7011598) (@lem7011597 A _93554 s g)). Qed.
Lemma lem7011600 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term313 A _93554 s g GEN_PVAR_299) = (term296 A _93554 GEN_PVAR_299 s g).
Proof. exact (eq_refl (term313 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7011601 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term320 A _93554 s g) = (term311 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7011600 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011602 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011603 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term321 A _93554 s g) = (term322 A _93554 s g).
Proof. exact (MK_COMB (@lem7011602 A) (@lem7011601 A _93554 s g)). Qed.
Lemma lem7011604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011605 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term323 A _93554 s g) = (term324 A _93554 s g).
Proof. exact (MK_COMB (@lem7011604) (@lem7011603 A _93554 s g)). Qed.
Lemma lem7011606 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term315 A _93554 s g GEN_PVAR_299) = (term293 A _93554 GEN_PVAR_299 s g).
Proof. exact (eq_refl (term315 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7011607 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term325 A _93554 s g) = (term312 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7011606 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7011608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7011609 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term326 A _93554 s g) = (term327 A _93554 s g).
Proof. exact (MK_COMB (@lem7011608 A) (@lem7011607 A _93554 s g)). Qed.
Lemma lem7011610 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term310 A _93554 s g) = (term328 A _93554 s g).
Proof. exact (MK_COMB (@lem7011605 A _93554 s g) (@lem7011609 A _93554 s g)). Qed.
Lemma lem7011611 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : ((term309 A _93554 s g) = (term310 A _93554 s g)) = ((term302 A _93554 s g) = (term328 A _93554 s g)).
Proof. exact (MK_COMB (@lem7011599 A _93554 s g) (@lem7011610 A _93554 s g)). Qed.
Lemma lem7011612 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term302 A _93554 s g) = (term328 A _93554 s g).
Proof. exact (EQ_MP (@lem7011611 A _93554 s g) (@lem7011589 A _93554 s g)). Qed.
Lemma lem7011717 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term303 A _93554 s) = (term329 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011612 A _93554 s g)). Qed.
Lemma lem7011718 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011719 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term304 A _93554 s) = (term330 A _93554 s).
Proof. exact (MK_COMB (@lem7011718 A) (@lem7011717 A _93554 s)). Qed.
Lemma lem7011721 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7011722 {A : Type'} (P : type704 A) (Q : type704 A) : (term331 A P Q) = (term332 A P Q).
Proof. exact (@lem7011721 (A -> nat) P Q). Qed.
Lemma lem7011723 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term333 A _93554 s) = (term334 A _93554 s).
Proof. exact (@lem7011722 A (term335 A _93554 s) (term336 A _93554 s)). Qed.
Lemma lem7011724 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term337 A _93554 s g) = (term322 A _93554 s g).
Proof. exact (eq_refl (term337 A _93554 s g)). Qed.
Lemma lem7011725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011726 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term338 A _93554 s g) = (term324 A _93554 s g).
Proof. exact (MK_COMB (@lem7011725) (@lem7011724 A _93554 s g)). Qed.
Lemma lem7011727 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term339 A _93554 s g) = (term327 A _93554 s g).
Proof. exact (eq_refl (term339 A _93554 s g)). Qed.
Lemma lem7011728 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term340 A _93554 s g) = (term328 A _93554 s g).
Proof. exact (MK_COMB (@lem7011726 A _93554 s g) (@lem7011727 A _93554 s g)). Qed.
Lemma lem7011729 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term341 A _93554 s) = (term329 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011728 A _93554 s g)). Qed.
Lemma lem7011730 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011731 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term333 A _93554 s) = (term330 A _93554 s).
Proof. exact (MK_COMB (@lem7011730 A) (@lem7011729 A _93554 s)). Qed.
Lemma lem7011732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7011733 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term342 A _93554 s) = (term343 A _93554 s).
Proof. exact (MK_COMB (@lem7011732) (@lem7011731 A _93554 s)). Qed.
Lemma lem7011734 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term337 A _93554 s g) = (term322 A _93554 s g).
Proof. exact (eq_refl (term337 A _93554 s g)). Qed.
Lemma lem7011735 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term344 A _93554 s) = (term335 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011734 A _93554 s g)). Qed.
Lemma lem7011736 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011737 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term345 A _93554 s) = (term346 A _93554 s).
Proof. exact (MK_COMB (@lem7011736 A) (@lem7011735 A _93554 s)). Qed.
Lemma lem7011738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011739 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term347 A _93554 s) = (term348 A _93554 s).
Proof. exact (MK_COMB (@lem7011738) (@lem7011737 A _93554 s)). Qed.
Lemma lem7011740 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term339 A _93554 s g) = (term327 A _93554 s g).
Proof. exact (eq_refl (term339 A _93554 s g)). Qed.
Lemma lem7011741 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term349 A _93554 s) = (term336 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7011740 A _93554 s g)). Qed.
Lemma lem7011742 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7011743 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term350 A _93554 s) = (term351 A _93554 s).
Proof. exact (MK_COMB (@lem7011742 A) (@lem7011741 A _93554 s)). Qed.
Lemma lem7011744 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term334 A _93554 s) = (term352 A _93554 s).
Proof. exact (MK_COMB (@lem7011739 A _93554 s) (@lem7011743 A _93554 s)). Qed.
Lemma lem7011745 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : ((term333 A _93554 s) = (term334 A _93554 s)) = ((term330 A _93554 s) = (term352 A _93554 s)).
Proof. exact (MK_COMB (@lem7011733 A _93554 s) (@lem7011744 A _93554 s)). Qed.
Lemma lem7011746 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term330 A _93554 s) = (term352 A _93554 s).
Proof. exact (EQ_MP (@lem7011745 A _93554 s) (@lem7011723 A _93554 s)). Qed.
Lemma lem7011859 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term304 A _93554 s) = (term352 A _93554 s).
Proof. exact (TRANS (@lem7011719 A _93554 s) (@lem7011746 A _93554 s)). Qed.
Lemma lem7011860 {A : Type'} (_93554 : type641 A) : (term305 A _93554) = (term353 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011859 A _93554 s)). Qed.
Lemma lem7011861 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011862 {A : Type'} (_93554 : type641 A) : (term306 A _93554) = (term354 A _93554).
Proof. exact (MK_COMB (@lem7011861 A) (@lem7011860 A _93554)). Qed.
Lemma lem7011864 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7011865 {A : Type'} (P : type686 A) (Q : type686 A) : (term355 A P Q) = (term356 A P Q).
Proof. exact (@lem7011864 (A -> Prop) P Q). Qed.
Lemma lem7011866 {A : Type'} (_93554 : type641 A) : (term357 A _93554) = (term358 A _93554).
Proof. exact (@lem7011865 A (term359 A _93554) (term360 A _93554)). Qed.
Lemma lem7011867 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term361 A _93554 s) = (term346 A _93554 s).
Proof. exact (eq_refl (term361 A _93554 s)). Qed.
Lemma lem7011868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011869 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term362 A _93554 s) = (term348 A _93554 s).
Proof. exact (MK_COMB (@lem7011868) (@lem7011867 A _93554 s)). Qed.
Lemma lem7011870 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term363 A _93554 s) = (term351 A _93554 s).
Proof. exact (eq_refl (term363 A _93554 s)). Qed.
Lemma lem7011871 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term364 A _93554 s) = (term352 A _93554 s).
Proof. exact (MK_COMB (@lem7011869 A _93554 s) (@lem7011870 A _93554 s)). Qed.
Lemma lem7011872 {A : Type'} (_93554 : type641 A) : (term365 A _93554) = (term353 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011871 A _93554 s)). Qed.
Lemma lem7011873 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011874 {A : Type'} (_93554 : type641 A) : (term357 A _93554) = (term354 A _93554).
Proof. exact (MK_COMB (@lem7011873 A) (@lem7011872 A _93554)). Qed.
Lemma lem7011875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7011876 {A : Type'} (_93554 : type641 A) : (term366 A _93554) = (term367 A _93554).
Proof. exact (MK_COMB (@lem7011875) (@lem7011874 A _93554)). Qed.
Lemma lem7011877 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term361 A _93554 s) = (term346 A _93554 s).
Proof. exact (eq_refl (term361 A _93554 s)). Qed.
Lemma lem7011878 {A : Type'} (_93554 : type641 A) : (term368 A _93554) = (term359 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011877 A _93554 s)). Qed.
Lemma lem7011879 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011880 {A : Type'} (_93554 : type641 A) : (term369 A _93554) = (term370 A _93554).
Proof. exact (MK_COMB (@lem7011879 A) (@lem7011878 A _93554)). Qed.
Lemma lem7011881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7011882 {A : Type'} (_93554 : type641 A) : (term371 A _93554) = (term372 A _93554).
Proof. exact (MK_COMB (@lem7011881) (@lem7011880 A _93554)). Qed.
Lemma lem7011883 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term363 A _93554 s) = (term351 A _93554 s).
Proof. exact (eq_refl (term363 A _93554 s)). Qed.
Lemma lem7011884 {A : Type'} (_93554 : type641 A) : (term373 A _93554) = (term360 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7011883 A _93554 s)). Qed.
Lemma lem7011885 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7011886 {A : Type'} (_93554 : type641 A) : (term374 A _93554) = (term375 A _93554).
Proof. exact (MK_COMB (@lem7011885 A) (@lem7011884 A _93554)). Qed.
Lemma lem7011887 {A : Type'} (_93554 : type641 A) : (term358 A _93554) = (term376 A _93554).
Proof. exact (MK_COMB (@lem7011882 A _93554) (@lem7011886 A _93554)). Qed.
Lemma lem7011888 {A : Type'} (_93554 : type641 A) : ((term357 A _93554) = (term358 A _93554)) = ((term354 A _93554) = (term376 A _93554)).
Proof. exact (MK_COMB (@lem7011876 A _93554) (@lem7011887 A _93554)). Qed.
Lemma lem7011889 {A : Type'} (_93554 : type641 A) : (term354 A _93554) = (term376 A _93554).
Proof. exact (EQ_MP (@lem7011888 A _93554) (@lem7011866 A _93554)). Qed.
Lemma lem7012010 {A : Type'} (_93554 : type641 A) : (term306 A _93554) = (term376 A _93554).
Proof. exact (TRANS (@lem7011862 A _93554) (@lem7011889 A _93554)). Qed.
Lemma lem7012012 {A : Type'} (P : Prop) (Q : A -> Prop) : (term377 A P Q) = (term378 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7012013 {A : Type'} (P : Prop) (Q : A -> Prop) : (term377 A P Q) = (term378 A P Q).
Proof. exact (@lem7012012 A P Q). Qed.
Lemma lem7012014 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term379 A _93554 GEN_PVAR_299 s g) = (term380 A _93554 GEN_PVAR_299 s g).
Proof. exact (@lem7012013 A (term381 A _93554 s g GEN_PVAR_299) (term93 A GEN_PVAR_299 s g)). Qed.
Lemma lem7012015 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term286 A GEN_PVAR_299 s g x) = (term91 A GEN_PVAR_299 s g x).
Proof. exact (eq_refl (term286 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7012016 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term382 A GEN_PVAR_299 s g) = (term93 A GEN_PVAR_299 s g).
Proof. exact (fun_ext (fun x : A => @lem7012015 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7012017 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7012018 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term383 A GEN_PVAR_299 s g) = (term95 A GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7012017 A) (@lem7012016 A GEN_PVAR_299 s g)). Qed.
Lemma lem7012019 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (GEN_PVAR_299 : A) : (term292 A _93554 s g GEN_PVAR_299) = (term292 A _93554 s g GEN_PVAR_299).
Proof. exact (eq_refl (term292 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7012020 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term379 A _93554 GEN_PVAR_299 s g) = (term293 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7012019 A _93554 s g GEN_PVAR_299) (@lem7012018 A GEN_PVAR_299 s g)). Qed.
Lemma lem7012021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7012022 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term384 A _93554 GEN_PVAR_299 s g) = (term385 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7012021) (@lem7012020 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7012023 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term286 A GEN_PVAR_299 s g x) = (term91 A GEN_PVAR_299 s g x).
Proof. exact (eq_refl (term286 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7012024 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (GEN_PVAR_299 : A) : (term292 A _93554 s g GEN_PVAR_299) = (term292 A _93554 s g GEN_PVAR_299).
Proof. exact (eq_refl (term292 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7012025 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term386 A _93554 GEN_PVAR_299 s g x) = (term387 A _93554 GEN_PVAR_299 s g x).
Proof. exact (MK_COMB (@lem7012024 A _93554 s g GEN_PVAR_299) (@lem7012023 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7012026 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term388 A _93554 GEN_PVAR_299 s g) = (term389 A _93554 GEN_PVAR_299 s g).
Proof. exact (fun_ext (fun x : A => @lem7012025 A _93554 GEN_PVAR_299 s g x)). Qed.
Lemma lem7012027 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7012028 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term380 A _93554 GEN_PVAR_299 s g) = (term390 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7012027 A) (@lem7012026 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7012029 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : ((term379 A _93554 GEN_PVAR_299 s g) = (term380 A _93554 GEN_PVAR_299 s g)) = ((term293 A _93554 GEN_PVAR_299 s g) = (term390 A _93554 GEN_PVAR_299 s g)).
Proof. exact (MK_COMB (@lem7012022 A _93554 GEN_PVAR_299 s g) (@lem7012028 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7012030 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term293 A _93554 GEN_PVAR_299 s g) = (term390 A _93554 GEN_PVAR_299 s g).
Proof. exact (EQ_MP (@lem7012029 A _93554 GEN_PVAR_299 s g) (@lem7012014 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7012031 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term312 A _93554 s g) = (term391 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7012030 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7012032 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7012033 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term327 A _93554 s g) = (term392 A _93554 s g).
Proof. exact (MK_COMB (@lem7012032 A) (@lem7012031 A _93554 s g)). Qed.
Lemma lem7012035 {A B : Type'} (P : type1413 A B) : (term393 A B P) = (term394 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7012036 {A : Type'} (P : type1402 A) : (term395 A P) = (term396 A P).
Proof. exact (@lem7012035 A A P). Qed.
Lemma lem7012037 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term397 A _93554 s g) = (term398 A _93554 s g).
Proof. exact (@lem7012036 A (term399 A _93554 s g)). Qed.
Lemma lem7012038 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term400 A _93554 s g GEN_PVAR_299) = (term389 A _93554 GEN_PVAR_299 s g).
Proof. exact (eq_refl (term400 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7012039 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7012040 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term401 A _93554 s g GEN_PVAR_299 x) = (term402 A _93554 GEN_PVAR_299 s g x).
Proof. exact (MK_COMB (@lem7012038 A _93554 GEN_PVAR_299 s g) (@lem7012039 A x)). Qed.
Lemma lem7012041 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term402 A _93554 GEN_PVAR_299 s g x) = (term387 A _93554 GEN_PVAR_299 s g x).
Proof. exact (eq_refl (term402 A _93554 GEN_PVAR_299 s g x)). Qed.
Lemma lem7012042 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term401 A _93554 s g GEN_PVAR_299 x) = (term387 A _93554 GEN_PVAR_299 s g x).
Proof. exact (TRANS (@lem7012040 A _93554 GEN_PVAR_299 s g x) (@lem7012041 A _93554 GEN_PVAR_299 s g x)). Qed.
Lemma lem7012043 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term403 A _93554 s g GEN_PVAR_299) = (term389 A _93554 GEN_PVAR_299 s g).
Proof. exact (fun_ext (fun x : A => @lem7012042 A _93554 GEN_PVAR_299 s g x)). Qed.
Lemma lem7012044 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7012045 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term404 A _93554 s g GEN_PVAR_299) = (term390 A _93554 GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7012044 A) (@lem7012043 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7012046 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term405 A _93554 s g) = (term391 A _93554 s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7012045 A _93554 GEN_PVAR_299 s g)). Qed.
Lemma lem7012047 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7012048 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term397 A _93554 s g) = (term392 A _93554 s g).
Proof. exact (MK_COMB (@lem7012047 A) (@lem7012046 A _93554 s g)). Qed.
Lemma lem7012049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7012050 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term406 A _93554 s g) = (term407 A _93554 s g).
Proof. exact (MK_COMB (@lem7012049) (@lem7012048 A _93554 s g)). Qed.
Lemma lem7012051 {A : Type'} (_93554 : type641 A) (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term400 A _93554 s g GEN_PVAR_299) = (term389 A _93554 GEN_PVAR_299 s g).
Proof. exact (eq_refl (term400 A _93554 s g GEN_PVAR_299)). Qed.
Lemma lem7012052 {A : Type'} (x : A -> A) (GEN_PVAR_299 : A) : (x GEN_PVAR_299) = (x GEN_PVAR_299).
Proof. exact (eq_refl (x GEN_PVAR_299)). Qed.
Lemma lem7012053 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (x : A -> A) (GEN_PVAR_299 : A) : (term408 A _93554 s g x GEN_PVAR_299) = (term409 A _93554 s g x GEN_PVAR_299).
Proof. exact (MK_COMB (@lem7012051 A _93554 GEN_PVAR_299 s g) (@lem7012052 A x GEN_PVAR_299)). Qed.
Lemma lem7012054 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (x : A -> A) (GEN_PVAR_299 : A) : (term409 A _93554 s g x GEN_PVAR_299) = (term410 A _93554 s g x GEN_PVAR_299).
Proof. exact (eq_refl (term409 A _93554 s g x GEN_PVAR_299)). Qed.
Lemma lem7012055 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (x : A -> A) (GEN_PVAR_299 : A) : (term408 A _93554 s g x GEN_PVAR_299) = (term410 A _93554 s g x GEN_PVAR_299).
Proof. exact (TRANS (@lem7012053 A _93554 s g x GEN_PVAR_299) (@lem7012054 A _93554 s g x GEN_PVAR_299)). Qed.
Lemma lem7012056 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (x : A -> A) : (term411 A _93554 s g x) = (term412 A _93554 s g x).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7012055 A _93554 s g x GEN_PVAR_299)). Qed.
Lemma lem7012057 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7012058 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (x : A -> A) : (term413 A _93554 s g x) = (term414 A _93554 s g x).
Proof. exact (MK_COMB (@lem7012057 A) (@lem7012056 A _93554 s g x)). Qed.
Lemma lem7012059 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term415 A _93554 s g) = (term416 A _93554 s g).
Proof. exact (fun_ext (fun x : A -> A => @lem7012058 A _93554 s g x)). Qed.
Lemma lem7012060 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem7012061 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term398 A _93554 s g) = (term417 A _93554 s g).
Proof. exact (MK_COMB (@lem7012060 A) (@lem7012059 A _93554 s g)). Qed.
Lemma lem7012062 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : ((term397 A _93554 s g) = (term398 A _93554 s g)) = ((term392 A _93554 s g) = (term417 A _93554 s g)).
Proof. exact (MK_COMB (@lem7012050 A _93554 s g) (@lem7012061 A _93554 s g)). Qed.
Lemma lem7012063 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term392 A _93554 s g) = (term417 A _93554 s g).
Proof. exact (EQ_MP (@lem7012062 A _93554 s g) (@lem7012037 A _93554 s g)). Qed.
Lemma lem7012064 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term327 A _93554 s g) = (term417 A _93554 s g).
Proof. exact (TRANS (@lem7012033 A _93554 s g) (@lem7012063 A _93554 s g)). Qed.
Lemma lem7012065 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term336 A _93554 s) = (term418 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7012064 A _93554 s g)). Qed.
Lemma lem7012066 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7012067 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term351 A _93554 s) = (term419 A _93554 s).
Proof. exact (MK_COMB (@lem7012066 A) (@lem7012065 A _93554 s)). Qed.
Lemma lem7012069 {A B : Type'} (P : type1413 A B) : (term393 A B P) = (term394 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7012070 {A : Type'} (P : type692 A) : (term420 A P) = (term421 A P).
Proof. exact (@lem7012069 (A -> nat) (A -> A) P). Qed.
Lemma lem7012071 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term422 A _93554 s) = (term423 A _93554 s).
Proof. exact (@lem7012070 A (term424 A _93554 s)). Qed.
Lemma lem7012072 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term425 A _93554 s g) = (term416 A _93554 s g).
Proof. exact (eq_refl (term425 A _93554 s g)). Qed.
Lemma lem7012073 {A : Type'} (x : A -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7012074 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (x : A -> A) : (term426 A _93554 s g x) = (term427 A _93554 s g x).
Proof. exact (MK_COMB (@lem7012072 A _93554 s g) (@lem7012073 A x)). Qed.
Lemma lem7012075 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (x : A -> A) : (term427 A _93554 s g x) = (term414 A _93554 s g x).
Proof. exact (eq_refl (term427 A _93554 s g x)). Qed.
Lemma lem7012076 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (x : A -> A) : (term426 A _93554 s g x) = (term414 A _93554 s g x).
Proof. exact (TRANS (@lem7012074 A _93554 s g x) (@lem7012075 A _93554 s g x)). Qed.
Lemma lem7012077 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term428 A _93554 s g) = (term416 A _93554 s g).
Proof. exact (fun_ext (fun x : A -> A => @lem7012076 A _93554 s g x)). Qed.
Lemma lem7012078 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem7012079 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term429 A _93554 s g) = (term417 A _93554 s g).
Proof. exact (MK_COMB (@lem7012078 A) (@lem7012077 A _93554 s g)). Qed.
Lemma lem7012080 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term430 A _93554 s) = (term418 A _93554 s).
Proof. exact (fun_ext (fun g : A -> nat => @lem7012079 A _93554 s g)). Qed.
Lemma lem7012081 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7012082 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term422 A _93554 s) = (term419 A _93554 s).
Proof. exact (MK_COMB (@lem7012081 A) (@lem7012080 A _93554 s)). Qed.
Lemma lem7012083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7012084 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term431 A _93554 s) = (term432 A _93554 s).
Proof. exact (MK_COMB (@lem7012083) (@lem7012082 A _93554 s)). Qed.
Lemma lem7012085 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) : (term425 A _93554 s g) = (term416 A _93554 s g).
Proof. exact (eq_refl (term425 A _93554 s g)). Qed.
Lemma lem7012086 {A : Type'} (x : type698 A) (g : A -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7012087 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (x : type698 A) (g : A -> nat) : (term433 A _93554 s x g) = (term434 A _93554 s x g).
Proof. exact (MK_COMB (@lem7012085 A _93554 s g) (@lem7012086 A x g)). Qed.
Lemma lem7012088 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (x : type698 A) (g : A -> nat) : (term434 A _93554 s x g) = (term435 A _93554 s x g).
Proof. exact (eq_refl (term434 A _93554 s x g)). Qed.
Lemma lem7012089 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (x : type698 A) (g : A -> nat) : (term433 A _93554 s x g) = (term435 A _93554 s x g).
Proof. exact (TRANS (@lem7012087 A _93554 s x g) (@lem7012088 A _93554 s x g)). Qed.
Lemma lem7012090 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (x : type698 A) : (term436 A _93554 s x) = (term437 A _93554 s x).
Proof. exact (fun_ext (fun g : A -> nat => @lem7012089 A _93554 s x g)). Qed.
Lemma lem7012091 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7012092 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (x : type698 A) : (term438 A _93554 s x) = (term439 A _93554 s x).
Proof. exact (MK_COMB (@lem7012091 A) (@lem7012090 A _93554 s x)). Qed.
Lemma lem7012093 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term440 A _93554 s) = (term441 A _93554 s).
Proof. exact (fun_ext (fun x : type698 A => @lem7012092 A _93554 s x)). Qed.
Lemma lem7012094 {A : Type'} : (@ex ((A -> nat) -> A -> A)) = (@ex ((A -> nat) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> A -> A))). Qed.
Lemma lem7012095 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term423 A _93554 s) = (term442 A _93554 s).
Proof. exact (MK_COMB (@lem7012094 A) (@lem7012093 A _93554 s)). Qed.
Lemma lem7012096 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : ((term422 A _93554 s) = (term423 A _93554 s)) = ((term419 A _93554 s) = (term442 A _93554 s)).
Proof. exact (MK_COMB (@lem7012084 A _93554 s) (@lem7012095 A _93554 s)). Qed.
Lemma lem7012097 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term419 A _93554 s) = (term442 A _93554 s).
Proof. exact (EQ_MP (@lem7012096 A _93554 s) (@lem7012071 A _93554 s)). Qed.
Lemma lem7012098 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term351 A _93554 s) = (term442 A _93554 s).
Proof. exact (TRANS (@lem7012067 A _93554 s) (@lem7012097 A _93554 s)). Qed.
Lemma lem7012099 {A : Type'} (_93554 : type641 A) : (term360 A _93554) = (term443 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7012098 A _93554 s)). Qed.
Lemma lem7012100 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7012101 {A : Type'} (_93554 : type641 A) : (term375 A _93554) = (term444 A _93554).
Proof. exact (MK_COMB (@lem7012100 A) (@lem7012099 A _93554)). Qed.
Lemma lem7012103 {A B : Type'} (P : type1413 A B) : (term393 A B P) = (term394 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7012104 {A : Type'} (P : type600 A) : (term445 A P) = (term446 A P).
Proof. exact (@lem7012103 (A -> Prop) (type698 A) P). Qed.
Lemma lem7012105 {A : Type'} (_93554 : type641 A) : (term447 A _93554) = (term448 A _93554).
Proof. exact (@lem7012104 A (term449 A _93554)). Qed.
Lemma lem7012106 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term450 A _93554 s) = (term441 A _93554 s).
Proof. exact (eq_refl (term450 A _93554 s)). Qed.
Lemma lem7012107 {A : Type'} (x : type698 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7012108 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (x : type698 A) : (term451 A _93554 s x) = (term452 A _93554 s x).
Proof. exact (MK_COMB (@lem7012106 A _93554 s) (@lem7012107 A x)). Qed.
Lemma lem7012109 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (x : type698 A) : (term452 A _93554 s x) = (term439 A _93554 s x).
Proof. exact (eq_refl (term452 A _93554 s x)). Qed.
Lemma lem7012110 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (x : type698 A) : (term451 A _93554 s x) = (term439 A _93554 s x).
Proof. exact (TRANS (@lem7012108 A _93554 s x) (@lem7012109 A _93554 s x)). Qed.
Lemma lem7012111 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term453 A _93554 s) = (term441 A _93554 s).
Proof. exact (fun_ext (fun x : type698 A => @lem7012110 A _93554 s x)). Qed.
Lemma lem7012112 {A : Type'} : (@ex ((A -> nat) -> A -> A)) = (@ex ((A -> nat) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> A -> A))). Qed.
Lemma lem7012113 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term454 A _93554 s) = (term442 A _93554 s).
Proof. exact (MK_COMB (@lem7012112 A) (@lem7012111 A _93554 s)). Qed.
Lemma lem7012114 {A : Type'} (_93554 : type641 A) : (term455 A _93554) = (term443 A _93554).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7012113 A _93554 s)). Qed.
Lemma lem7012115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7012116 {A : Type'} (_93554 : type641 A) : (term447 A _93554) = (term444 A _93554).
Proof. exact (MK_COMB (@lem7012115 A) (@lem7012114 A _93554)). Qed.
Lemma lem7012117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7012118 {A : Type'} (_93554 : type641 A) : (term456 A _93554) = (term457 A _93554).
Proof. exact (MK_COMB (@lem7012117) (@lem7012116 A _93554)). Qed.
Lemma lem7012119 {A : Type'} (_93554 : type641 A) (s : A -> Prop) : (term450 A _93554 s) = (term441 A _93554 s).
Proof. exact (eq_refl (term450 A _93554 s)). Qed.
Lemma lem7012120 {A : Type'} (x : type640 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7012121 {A : Type'} (_93554 : type641 A) (x : type640 A) (s : A -> Prop) : (term458 A _93554 x s) = (term459 A _93554 x s).
Proof. exact (MK_COMB (@lem7012119 A _93554 s) (@lem7012120 A x s)). Qed.
Lemma lem7012122 {A : Type'} (_93554 : type641 A) (x : type640 A) (s : A -> Prop) : (term459 A _93554 x s) = (term460 A _93554 x s).
Proof. exact (eq_refl (term459 A _93554 x s)). Qed.
Lemma lem7012123 {A : Type'} (_93554 : type641 A) (x : type640 A) (s : A -> Prop) : (term458 A _93554 x s) = (term460 A _93554 x s).
Proof. exact (TRANS (@lem7012121 A _93554 x s) (@lem7012122 A _93554 x s)). Qed.
Lemma lem7012124 {A : Type'} (_93554 : type641 A) (x : type640 A) : (term461 A _93554 x) = (term462 A _93554 x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7012123 A _93554 x s)). Qed.
Lemma lem7012125 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7012126 {A : Type'} (_93554 : type641 A) (x : type640 A) : (term463 A _93554 x) = (term464 A _93554 x).
Proof. exact (MK_COMB (@lem7012125 A) (@lem7012124 A _93554 x)). Qed.
Lemma lem7012127 {A : Type'} (_93554 : type641 A) : (term465 A _93554) = (term466 A _93554).
Proof. exact (fun_ext (fun x : type640 A => @lem7012126 A _93554 x)). Qed.
Lemma lem7012128 {A : Type'} : (@ex ((A -> Prop) -> (A -> nat) -> A -> A)) = (@ex ((A -> Prop) -> (A -> nat) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> nat) -> A -> A))). Qed.
Lemma lem7012129 {A : Type'} (_93554 : type641 A) : (term448 A _93554) = (term467 A _93554).
Proof. exact (MK_COMB (@lem7012128 A) (@lem7012127 A _93554)). Qed.
Lemma lem7012130 {A : Type'} (_93554 : type641 A) : ((term447 A _93554) = (term448 A _93554)) = ((term444 A _93554) = (term467 A _93554)).
Proof. exact (MK_COMB (@lem7012118 A _93554) (@lem7012129 A _93554)). Qed.
Lemma lem7012131 {A : Type'} (_93554 : type641 A) : (term444 A _93554) = (term467 A _93554).
Proof. exact (EQ_MP (@lem7012130 A _93554) (@lem7012105 A _93554)). Qed.
Lemma lem7012132 {A : Type'} (_93554 : type641 A) : (term375 A _93554) = (term467 A _93554).
Proof. exact (TRANS (@lem7012101 A _93554) (@lem7012131 A _93554)). Qed.
Lemma lem7012133 {A : Type'} (_93554 : type641 A) : (term372 A _93554) = (term372 A _93554).
Proof. exact (eq_refl (term372 A _93554)). Qed.
Lemma lem7012134 {A : Type'} (_93554 : type641 A) : (term376 A _93554) = (term468 A _93554).
Proof. exact (MK_COMB (@lem7012133 A _93554) (@lem7012132 A _93554)). Qed.
Lemma lem7012136 {A : Type'} (P : Prop) (Q : A -> Prop) : (term469 A P Q) = (term470 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7012137 {A : Type'} (P : Prop) (Q : type142 A) : (term471 A P Q) = (term472 A P Q).
Proof. exact (@lem7012136 (type640 A) P Q). Qed.
Lemma lem7012138 {A : Type'} (_93554 : type641 A) : (term473 A _93554) = (term474 A _93554).
Proof. exact (@lem7012137 A (term370 A _93554) (term466 A _93554)). Qed.
Lemma lem7012139 {A : Type'} (_93554 : type641 A) (x : type640 A) : (term475 A _93554 x) = (term464 A _93554 x).
Proof. exact (eq_refl (term475 A _93554 x)). Qed.
Lemma lem7012140 {A : Type'} (_93554 : type641 A) : (term476 A _93554) = (term466 A _93554).
Proof. exact (fun_ext (fun x : type640 A => @lem7012139 A _93554 x)). Qed.
Lemma lem7012141 {A : Type'} : (@ex ((A -> Prop) -> (A -> nat) -> A -> A)) = (@ex ((A -> Prop) -> (A -> nat) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> nat) -> A -> A))). Qed.
Lemma lem7012142 {A : Type'} (_93554 : type641 A) : (term477 A _93554) = (term467 A _93554).
Proof. exact (MK_COMB (@lem7012141 A) (@lem7012140 A _93554)). Qed.
Lemma lem7012143 {A : Type'} (_93554 : type641 A) : (term372 A _93554) = (term372 A _93554).
Proof. exact (eq_refl (term372 A _93554)). Qed.
Lemma lem7012144 {A : Type'} (_93554 : type641 A) : (term473 A _93554) = (term468 A _93554).
Proof. exact (MK_COMB (@lem7012143 A _93554) (@lem7012142 A _93554)). Qed.
Lemma lem7012145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7012146 {A : Type'} (_93554 : type641 A) : (term478 A _93554) = (term479 A _93554).
Proof. exact (MK_COMB (@lem7012145) (@lem7012144 A _93554)). Qed.
Lemma lem7012147 {A : Type'} (_93554 : type641 A) (x : type640 A) : (term475 A _93554 x) = (term464 A _93554 x).
Proof. exact (eq_refl (term475 A _93554 x)). Qed.
Lemma lem7012148 {A : Type'} (_93554 : type641 A) : (term372 A _93554) = (term372 A _93554).
Proof. exact (eq_refl (term372 A _93554)). Qed.
Lemma lem7012149 {A : Type'} (_93554 : type641 A) (x : type640 A) : (term480 A _93554 x) = (term481 A _93554 x).
Proof. exact (MK_COMB (@lem7012148 A _93554) (@lem7012147 A _93554 x)). Qed.
Lemma lem7012150 {A : Type'} (_93554 : type641 A) : (term482 A _93554) = (term483 A _93554).
Proof. exact (fun_ext (fun x : type640 A => @lem7012149 A _93554 x)). Qed.
Lemma lem7012151 {A : Type'} : (@ex ((A -> Prop) -> (A -> nat) -> A -> A)) = (@ex ((A -> Prop) -> (A -> nat) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> nat) -> A -> A))). Qed.
Lemma lem7012152 {A : Type'} (_93554 : type641 A) : (term474 A _93554) = (term484 A _93554).
Proof. exact (MK_COMB (@lem7012151 A) (@lem7012150 A _93554)). Qed.
Lemma lem7012153 {A : Type'} (_93554 : type641 A) : ((term473 A _93554) = (term474 A _93554)) = ((term468 A _93554) = (term484 A _93554)).
Proof. exact (MK_COMB (@lem7012146 A _93554) (@lem7012152 A _93554)). Qed.
Lemma lem7012154 {A : Type'} (_93554 : type641 A) : (term468 A _93554) = (term484 A _93554).
Proof. exact (EQ_MP (@lem7012153 A _93554) (@lem7012138 A _93554)). Qed.
Lemma lem7012155 {A : Type'} (_93554 : type641 A) : (term376 A _93554) = (term484 A _93554).
Proof. exact (TRANS (@lem7012134 A _93554) (@lem7012154 A _93554)). Qed.
Lemma lem7012156 {A : Type'} (_93554 : type641 A) : (term306 A _93554) = (term484 A _93554).
Proof. exact (TRANS (@lem7012010 A _93554) (@lem7012155 A _93554)). Qed.
Lemma lem7012157 {A : Type'} (_93554 : type641 A) : (term277 A _93554) = (term484 A _93554).
Proof. exact (TRANS (@lem7011577 A _93554) (@lem7012156 A _93554)). Qed.
Lemma lem7012158 {A : Type'} (_93554 : type641 A) (h1 : term277 A _93554) : term484 A _93554.
Proof. exact (EQ_MP (@lem7012157 A _93554) (@lem7011536 A _93554 h1)). Qed.
Lemma lem7012165 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term212 A s f g x) = (term485 A s f g x).
Proof. exact (@lem17265 (@IN A x s) (term486 A f g x)). Qed.
Lemma lem7012166 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term213 A s f g) = (term487 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7012165 A s f g x)). Qed.
Lemma lem7012167 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7012220 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term76 A s f g) = (term488 A s f g).
Proof. exact (MK_COMB (@lem7012167 A) (@lem7012166 A s f g)). Qed.
Lemma lem7012221 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term488 A s f g.
Proof. exact (EQ_MP (@lem7012220 A s f g) (@lem7011537 A s f g h1)). Qed.
Lemma lem7012236 {A : Type'} (g : A -> nat) (x : A) : (term489 A g x) = ((g x) = (NUMERAL 0)).
Proof. exact (@lem16933 ((g x) = (NUMERAL 0))). Qed.
Lemma lem7012238 {A : Type'} (x : A) (s : A -> Prop) : (term490 A x s) = (term490 A x s).
Proof. exact (eq_refl (term490 A x s)). Qed.
Lemma lem7012239 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term491 A s g x) = (term492 A s g x).
Proof. exact (MK_COMB (@lem7012238 A x s) (@lem7012236 A g x)). Qed.
Lemma lem7012240 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term148 A s g x) = (term491 A s g x).
Proof. exact (@lem17045 (@IN A x s) (term84 A g x)). Qed.
Lemma lem7012241 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term148 A s g x) = (term492 A s g x).
Proof. exact (TRANS (@lem7012240 A s g x) (@lem7012239 A s g x)). Qed.
Lemma lem7012243 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term146 A s f x) = (term146 A s f x).
Proof. exact (eq_refl (term146 A s f x)). Qed.
Lemma lem7012244 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term149 A f s g x) = (term493 A f s g x).
Proof. exact (MK_COMB (@lem7012243 A s f x) (@lem7012241 A s g x)). Qed.
Lemma lem7012245 {A : Type'} (f : A -> nat) (x : A) : (term84 A f x) = (term84 A f x).
Proof. exact (eq_refl (term84 A f x)). Qed.
Lemma lem7012246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012247 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term494 A f s g x) = (term495 A f s g x).
Proof. exact (MK_COMB (@lem7012246) (@lem7012244 A f s g x)). Qed.
Lemma lem7012248 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term496 A s g f x) = (term497 A s g f x).
Proof. exact (MK_COMB (@lem7012247 A f s g x) (@lem7012245 A f x)). Qed.
Lemma lem7012249 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term498 A s g f x) = (term496 A s g f x).
Proof. exact (@lem17362 (term149 A f s g x) ((f x) = (NUMERAL 0))). Qed.
Lemma lem7012250 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term498 A s g f x) = (term497 A s g f x).
Proof. exact (TRANS (@lem7012249 A s g f x) (@lem7012248 A s g f x)). Qed.
Lemma lem7012251 {A : Type'} (P : A -> Prop) : (term499 A P) = (term500 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7012252 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term164 A s g f) = (term501 A s g f).
Proof. exact (@lem7012251 A (term155 A s g f)). Qed.
Lemma lem7012253 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term502 A s g f x) = (term153 A s g f x).
Proof. exact (eq_refl (term502 A s g f x)). Qed.
Lemma lem7012254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7012255 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term503 A s g f x) = (term498 A s g f x).
Proof. exact (MK_COMB (@lem7012254) (@lem7012253 A s g f x)). Qed.
Lemma lem7012256 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term503 A s g f x) = (term497 A s g f x).
Proof. exact (TRANS (@lem7012255 A s g f x) (@lem7012250 A s g f x)). Qed.
Lemma lem7012257 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term504 A s g f) = (term505 A s g f).
Proof. exact (fun_ext (fun x : A => @lem7012256 A s g f x)). Qed.
Lemma lem7012258 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7012259 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term501 A s g f) = (term506 A s g f).
Proof. exact (MK_COMB (@lem7012258 A) (@lem7012257 A s g f)). Qed.
Lemma lem7012312 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term164 A s g f) = (term506 A s g f).
Proof. exact (TRANS (@lem7012252 A s g f) (@lem7012259 A s g f)). Qed.
Lemma lem7012313 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term164 A s g f) : term506 A s g f.
Proof. exact (EQ_MP (@lem7012312 A s g f) (@lem7011539 A s g f h1)). Qed.
Lemma lem7012328 (m : nat) : ((term204 m) = (m = (NUMERAL 0))) = (term507 m).
Proof. exact (@lem17784 (term204 m) (m = (NUMERAL 0))). Qed.
Lemma lem7012329 : term205 = term508.
Proof. exact (fun_ext (fun m : nat => @lem7012328 m)). Qed.
Lemma lem7012330 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012331 : term206 = term509.
Proof. exact (MK_COMB (@lem7012330) (@lem7012329)). Qed.
Lemma lem7012342 (m : nat) (n : nat) : (term510 m n) = (term511 m n).
Proof. exact (@lem17160 (m = (S n)) (Peano.le m n)). Qed.
Lemma lem7012348 (m : nat) (n : nat) : (term512 m n) = (term512 m n).
Proof. exact (eq_refl (term512 m n)). Qed.
Lemma lem7012350 (m : nat) (n : nat) : (term513 m n) = (term513 m n).
Proof. exact (eq_refl (term513 m n)). Qed.
Lemma lem7012351 (m : nat) (n : nat) : (term514 m n) = (term515 m n).
Proof. exact (MK_COMB (@lem7012350 m n) (@lem7012342 m n)). Qed.
Lemma lem7012352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012353 (m : nat) (n : nat) : (term516 m n) = (term517 m n).
Proof. exact (MK_COMB (@lem7012352) (@lem7012351 m n)). Qed.
Lemma lem7012354 (m : nat) (n : nat) : (term518 m n) = (term519 m n).
Proof. exact (MK_COMB (@lem7012353 m n) (@lem7012348 m n)). Qed.
Lemma lem7012355 (m : nat) (n : nat) : ((term198 m n) = (term199 m n)) = (term518 m n).
Proof. exact (@lem17784 (term198 m n) (term199 m n)). Qed.
Lemma lem7012356 (m : nat) (n : nat) : ((term198 m n) = (term199 m n)) = (term519 m n).
Proof. exact (TRANS (@lem7012355 m n) (@lem7012354 m n)). Qed.
Lemma lem7012357 (m : nat) : (term200 m) = (term520 m).
Proof. exact (fun_ext (fun n : nat => @lem7012356 m n)). Qed.
Lemma lem7012358 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012359 (m : nat) : (term201 m) = (term521 m).
Proof. exact (MK_COMB (@lem7012358) (@lem7012357 m)). Qed.
Lemma lem7012360 : term202 = term522.
Proof. exact (fun_ext (fun m : nat => @lem7012359 m)). Qed.
Lemma lem7012361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012362 : term203 = term523.
Proof. exact (MK_COMB (@lem7012361) (@lem7012360)). Qed.
Lemma lem7012363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012364 : term207 = term524.
Proof. exact (MK_COMB (@lem7012363) (@lem7012331)). Qed.
Lemma lem7012365 : term171 = term525.
Proof. exact (MK_COMB (@lem7012364) (@lem7012362)). Qed.
Lemma lem7012367 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7012368 (P : nat -> Prop) (Q : nat -> Prop) : (term526 P Q) = (term527 P Q).
Proof. exact (@lem7012367 nat P Q). Qed.
Lemma lem7012369 : term528 = term529.
Proof. exact (@lem7012368 term530 term531). Qed.
Lemma lem7012370 (m : nat) : (term532 m) = (term533 m).
Proof. exact (eq_refl (term532 m)). Qed.
Lemma lem7012371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012372 (m : nat) : (term534 m) = (term535 m).
Proof. exact (MK_COMB (@lem7012371) (@lem7012370 m)). Qed.
Lemma lem7012373 (m : nat) : (term536 m) = (term537 m).
Proof. exact (eq_refl (term536 m)). Qed.
Lemma lem7012374 (m : nat) : (term538 m) = (term507 m).
Proof. exact (MK_COMB (@lem7012372 m) (@lem7012373 m)). Qed.
Lemma lem7012375 : term539 = term508.
Proof. exact (fun_ext (fun m : nat => @lem7012374 m)). Qed.
Lemma lem7012376 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012377 : term528 = term509.
Proof. exact (MK_COMB (@lem7012376) (@lem7012375)). Qed.
Lemma lem7012378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7012379 : term540 = term541.
Proof. exact (MK_COMB (@lem7012378) (@lem7012377)). Qed.
Lemma lem7012380 (m : nat) : (term532 m) = (term533 m).
Proof. exact (eq_refl (term532 m)). Qed.
Lemma lem7012381 : term542 = term530.
Proof. exact (fun_ext (fun m : nat => @lem7012380 m)). Qed.
Lemma lem7012382 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012383 : term543 = term544.
Proof. exact (MK_COMB (@lem7012382) (@lem7012381)). Qed.
Lemma lem7012384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012385 : term545 = term546.
Proof. exact (MK_COMB (@lem7012384) (@lem7012383)). Qed.
Lemma lem7012386 (m : nat) : (term536 m) = (term537 m).
Proof. exact (eq_refl (term536 m)). Qed.
Lemma lem7012387 : term547 = term531.
Proof. exact (fun_ext (fun m : nat => @lem7012386 m)). Qed.
Lemma lem7012388 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012389 : term548 = term549.
Proof. exact (MK_COMB (@lem7012388) (@lem7012387)). Qed.
Lemma lem7012390 : term529 = term550.
Proof. exact (MK_COMB (@lem7012385) (@lem7012389)). Qed.
Lemma lem7012391 : (term528 = term529) = (term509 = term550).
Proof. exact (MK_COMB (@lem7012379) (@lem7012390)). Qed.
Lemma lem7012392 : term509 = term550.
Proof. exact (EQ_MP (@lem7012391) (@lem7012369)). Qed.
Lemma lem7012489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012490 : term524 = term551.
Proof. exact (MK_COMB (@lem7012489) (@lem7012392)). Qed.
Lemma lem7012496 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7012497 (P : nat -> Prop) (Q : nat -> Prop) : (term526 P Q) = (term527 P Q).
Proof. exact (@lem7012496 nat P Q). Qed.
Lemma lem7012498 (m : nat) : (term552 m) = (term553 m).
Proof. exact (@lem7012497 (term554 m) (term555 m)). Qed.
Lemma lem7012499 (m : nat) (n : nat) : (term556 m n) = (term515 m n).
Proof. exact (eq_refl (term556 m n)). Qed.
Lemma lem7012500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012501 (m : nat) (n : nat) : (term557 m n) = (term517 m n).
Proof. exact (MK_COMB (@lem7012500) (@lem7012499 m n)). Qed.
Lemma lem7012502 (m : nat) (n : nat) : (term558 m n) = (term512 m n).
Proof. exact (eq_refl (term558 m n)). Qed.
Lemma lem7012503 (m : nat) (n : nat) : (term559 m n) = (term519 m n).
Proof. exact (MK_COMB (@lem7012501 m n) (@lem7012502 m n)). Qed.
Lemma lem7012504 (m : nat) : (term560 m) = (term520 m).
Proof. exact (fun_ext (fun n : nat => @lem7012503 m n)). Qed.
Lemma lem7012505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012506 (m : nat) : (term552 m) = (term521 m).
Proof. exact (MK_COMB (@lem7012505) (@lem7012504 m)). Qed.
Lemma lem7012507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7012508 (m : nat) : (term561 m) = (term562 m).
Proof. exact (MK_COMB (@lem7012507) (@lem7012506 m)). Qed.
Lemma lem7012509 (m : nat) (n : nat) : (term556 m n) = (term515 m n).
Proof. exact (eq_refl (term556 m n)). Qed.
Lemma lem7012510 (m : nat) : (term563 m) = (term554 m).
Proof. exact (fun_ext (fun n : nat => @lem7012509 m n)). Qed.
Lemma lem7012511 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012512 (m : nat) : (term564 m) = (term565 m).
Proof. exact (MK_COMB (@lem7012511) (@lem7012510 m)). Qed.
Lemma lem7012513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012514 (m : nat) : (term566 m) = (term567 m).
Proof. exact (MK_COMB (@lem7012513) (@lem7012512 m)). Qed.
Lemma lem7012515 (m : nat) (n : nat) : (term558 m n) = (term512 m n).
Proof. exact (eq_refl (term558 m n)). Qed.
Lemma lem7012516 (m : nat) : (term568 m) = (term555 m).
Proof. exact (fun_ext (fun n : nat => @lem7012515 m n)). Qed.
Lemma lem7012517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012518 (m : nat) : (term569 m) = (term570 m).
Proof. exact (MK_COMB (@lem7012517) (@lem7012516 m)). Qed.
Lemma lem7012519 (m : nat) : (term553 m) = (term571 m).
Proof. exact (MK_COMB (@lem7012514 m) (@lem7012518 m)). Qed.
Lemma lem7012520 (m : nat) : ((term552 m) = (term553 m)) = ((term521 m) = (term571 m)).
Proof. exact (MK_COMB (@lem7012508 m) (@lem7012519 m)). Qed.
Lemma lem7012521 (m : nat) : (term521 m) = (term571 m).
Proof. exact (EQ_MP (@lem7012520 m) (@lem7012498 m)). Qed.
Lemma lem7012618 : term522 = term572.
Proof. exact (fun_ext (fun m : nat => @lem7012521 m)). Qed.
Lemma lem7012619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012620 : term523 = term573.
Proof. exact (MK_COMB (@lem7012619) (@lem7012618)). Qed.
Lemma lem7012622 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7012623 (P : nat -> Prop) (Q : nat -> Prop) : (term526 P Q) = (term527 P Q).
Proof. exact (@lem7012622 nat P Q). Qed.
Lemma lem7012624 : term574 = term575.
Proof. exact (@lem7012623 term576 term577). Qed.
Lemma lem7012625 (m : nat) : (term578 m) = (term565 m).
Proof. exact (eq_refl (term578 m)). Qed.
Lemma lem7012626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012627 (m : nat) : (term579 m) = (term567 m).
Proof. exact (MK_COMB (@lem7012626) (@lem7012625 m)). Qed.
Lemma lem7012628 (m : nat) : (term580 m) = (term570 m).
Proof. exact (eq_refl (term580 m)). Qed.
Lemma lem7012629 (m : nat) : (term581 m) = (term571 m).
Proof. exact (MK_COMB (@lem7012627 m) (@lem7012628 m)). Qed.
Lemma lem7012630 : term582 = term572.
Proof. exact (fun_ext (fun m : nat => @lem7012629 m)). Qed.
Lemma lem7012631 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012632 : term574 = term573.
Proof. exact (MK_COMB (@lem7012631) (@lem7012630)). Qed.
Lemma lem7012633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7012634 : term583 = term584.
Proof. exact (MK_COMB (@lem7012633) (@lem7012632)). Qed.
Lemma lem7012635 (m : nat) : (term578 m) = (term565 m).
Proof. exact (eq_refl (term578 m)). Qed.
Lemma lem7012636 : term585 = term576.
Proof. exact (fun_ext (fun m : nat => @lem7012635 m)). Qed.
Lemma lem7012637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012638 : term586 = term587.
Proof. exact (MK_COMB (@lem7012637) (@lem7012636)). Qed.
Lemma lem7012639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012640 : term588 = term589.
Proof. exact (MK_COMB (@lem7012639) (@lem7012638)). Qed.
Lemma lem7012641 (m : nat) : (term580 m) = (term570 m).
Proof. exact (eq_refl (term580 m)). Qed.
Lemma lem7012642 : term590 = term577.
Proof. exact (fun_ext (fun m : nat => @lem7012641 m)). Qed.
Lemma lem7012643 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012644 : term591 = term592.
Proof. exact (MK_COMB (@lem7012643) (@lem7012642)). Qed.
Lemma lem7012645 : term575 = term593.
Proof. exact (MK_COMB (@lem7012640) (@lem7012644)). Qed.
Lemma lem7012646 : (term574 = term575) = (term573 = term593).
Proof. exact (MK_COMB (@lem7012634) (@lem7012645)). Qed.
Lemma lem7012647 : term573 = term593.
Proof. exact (EQ_MP (@lem7012646) (@lem7012624)). Qed.
Lemma lem7012752 : term523 = term593.
Proof. exact (TRANS (@lem7012620) (@lem7012647)). Qed.
Lemma lem7012755 : term525 = term594.
Proof. exact (MK_COMB (@lem7012490) (@lem7012752)). Qed.
Lemma lem7012756 : term171 = term594.
Proof. exact (TRANS (@lem7012365) (@lem7012755)). Qed.
Lemma lem7012757 (h1 : term171) : term594.
Proof. exact (EQ_MP (@lem7012756) (@lem7011540 h1)). Qed.
Lemma lem7012758 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term497 A s g f x.
Proof. exact (h1). Qed.
Lemma lem7012760 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7012765 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012767 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7012765 A nat f x). Qed.
Lemma lem7012772 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012773 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7012772 A nat f x). Qed.
Lemma lem7012775 {A : Type'} (g : A -> nat) (x : A) : (g x) = (@I (A -> nat) g x).
Proof. exact (@lem7012773 A g x). Qed.
Lemma lem7012776 {A : Type'} (f : A -> nat) (x : A) : (term595 A f x) = (term596 A f x).
Proof. exact (MK_COMB (@lem7012760) (@lem7012767 A f x)). Qed.
Lemma lem7012777 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term486 A f g x) = (term597 A f g x).
Proof. exact (MK_COMB (@lem7012776 A f x) (@lem7012775 A g x)). Qed.
Lemma lem7012779 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012780 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7012779 nat (nat -> Prop) f x). Qed.
Lemma lem7012781 {A : Type'} (f : A -> nat) (x : A) : (term596 A f x) = (term598 A f x).
Proof. exact (@lem7012780 Peano.le (@I (A -> nat) f x)). Qed.
Lemma lem7012782 {A : Type'} (g : A -> nat) (x : A) : (@I (A -> nat) g x) = (@I (A -> nat) g x).
Proof. exact (eq_refl (@I (A -> nat) g x)). Qed.
Lemma lem7012783 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term597 A f g x) = (term599 A f g x).
Proof. exact (MK_COMB (@lem7012781 A f x) (@lem7012782 A g x)). Qed.
Lemma lem7012785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012786 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7012785 nat Prop f x). Qed.
Lemma lem7012787 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term599 A f g x) = (term600 A f g x).
Proof. exact (@lem7012786 (term598 A f x) (@I (A -> nat) g x)). Qed.
Lemma lem7012788 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term597 A f g x) = (term600 A f g x).
Proof. exact (TRANS (@lem7012783 A f g x) (@lem7012787 A f g x)). Qed.
Lemma lem7012789 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term486 A f g x) = (term600 A f g x).
Proof. exact (TRANS (@lem7012777 A f g x) (@lem7012788 A f g x)). Qed.
Lemma lem7012790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7012797 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012798 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7012797 A (type686 A) f x). Qed.
Lemma lem7012799 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7012798 A (@IN A) x). Qed.
Lemma lem7012800 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7012801 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7012799 A x) (@lem7012800 A s)). Qed.
Lemma lem7012803 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012804 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7012803 (A -> Prop) Prop f x). Qed.
Lemma lem7012805 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term601 A x s).
Proof. exact (@lem7012804 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7012807 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term601 A x s).
Proof. exact (TRANS (@lem7012801 A x s) (@lem7012805 A x s)). Qed.
Lemma lem7012808 {A : Type'} (x : A) (s : A -> Prop) : (term602 A x s) = (term603 A x s).
Proof. exact (MK_COMB (@lem7012790) (@lem7012807 A x s)). Qed.
Lemma lem7012809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7012810 {A : Type'} (x : A) (s : A -> Prop) : (term490 A x s) = (term604 A x s).
Proof. exact (MK_COMB (@lem7012809) (@lem7012808 A x s)). Qed.
Lemma lem7012811 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term485 A s f g x) = (term605 A s f g x).
Proof. exact (MK_COMB (@lem7012810 A x s) (@lem7012789 A f g x)). Qed.
Lemma lem7012812 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term487 A s f g) = (term606 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7012811 A s f g x)). Qed.
Lemma lem7012813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7012814 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term488 A s f g) = (term607 A s f g).
Proof. exact (MK_COMB (@lem7012813 A) (@lem7012812 A s f g)). Qed.
Lemma lem7012815 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term607 A s f g.
Proof. exact (EQ_MP (@lem7012814 A s f g) (@lem7012221 A s f g h1)). Qed.
Lemma lem7012854 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012855 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7012854 nat (nat -> Prop) f x). Qed.
Lemma lem7012856 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7012855 Peano.le m). Qed.
Lemma lem7012857 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7012858 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem7012856 m) (@lem7012857 n)). Qed.
Lemma lem7012860 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012861 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7012860 nat Prop f x). Qed.
Lemma lem7012862 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term608 m n).
Proof. exact (@lem7012861 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem7012864 (m : nat) (n : nat) : (Peano.le m n) = (term608 m n).
Proof. exact (TRANS (@lem7012858 m n) (@lem7012862 m n)). Qed.
Lemma lem7012871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012872 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7012871 nat nat f x). Qed.
Lemma lem7012874 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem7012872 S n). Qed.
Lemma lem7012875 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem7012876 (m : nat) (n : nat) : (m = (S n)) = (m = (@I (nat -> nat) S n)).
Proof. exact (MK_COMB (@lem7012875 m) (@lem7012874 n)). Qed.
Lemma lem7012877 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7012878 (m : nat) (n : nat) : (term609 m n) = (term610 m n).
Proof. exact (MK_COMB (@lem7012877) (@lem7012876 m n)). Qed.
Lemma lem7012879 (m : nat) (n : nat) : (term199 m n) = (term611 m n).
Proof. exact (MK_COMB (@lem7012878 m n) (@lem7012864 m n)). Qed.
Lemma lem7012880 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7012887 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012888 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7012887 nat nat f x). Qed.
Lemma lem7012890 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem7012888 S n). Qed.
Lemma lem7012891 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem7012892 (m : nat) (n : nat) : (term198 m n) = (term612 m n).
Proof. exact (MK_COMB (@lem7012891 m) (@lem7012890 n)). Qed.
Lemma lem7012894 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012895 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7012894 nat (nat -> Prop) f x). Qed.
Lemma lem7012896 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7012895 Peano.le m). Qed.
Lemma lem7012897 (n : nat) : (@I (nat -> nat) S n) = (@I (nat -> nat) S n).
Proof. exact (eq_refl (@I (nat -> nat) S n)). Qed.
Lemma lem7012898 (m : nat) (n : nat) : (term612 m n) = (term613 m n).
Proof. exact (MK_COMB (@lem7012896 m) (@lem7012897 n)). Qed.
Lemma lem7012900 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012901 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7012900 nat Prop f x). Qed.
Lemma lem7012902 (m : nat) (n : nat) : (term613 m n) = (term614 m n).
Proof. exact (@lem7012901 (@I (nat -> nat -> Prop) Peano.le m) (@I (nat -> nat) S n)). Qed.
Lemma lem7012903 (m : nat) (n : nat) : (term612 m n) = (term614 m n).
Proof. exact (TRANS (@lem7012898 m n) (@lem7012902 m n)). Qed.
Lemma lem7012904 (m : nat) (n : nat) : (term198 m n) = (term614 m n).
Proof. exact (TRANS (@lem7012892 m n) (@lem7012903 m n)). Qed.
Lemma lem7012905 (m : nat) (n : nat) : (term615 m n) = (term616 m n).
Proof. exact (MK_COMB (@lem7012880) (@lem7012904 m n)). Qed.
Lemma lem7012906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7012907 (m : nat) (n : nat) : (term617 m n) = (term618 m n).
Proof. exact (MK_COMB (@lem7012906) (@lem7012905 m n)). Qed.
Lemma lem7012908 (m : nat) (n : nat) : (term512 m n) = (term619 m n).
Proof. exact (MK_COMB (@lem7012907 m n) (@lem7012879 m n)). Qed.
Lemma lem7012909 (m : nat) : (term555 m) = (term620 m).
Proof. exact (fun_ext (fun n : nat => @lem7012908 m n)). Qed.
Lemma lem7012910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012911 (m : nat) : (term570 m) = (term621 m).
Proof. exact (MK_COMB (@lem7012910) (@lem7012909 m)). Qed.
Lemma lem7012912 : term577 = term622.
Proof. exact (fun_ext (fun m : nat => @lem7012911 m)). Qed.
Lemma lem7012913 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012914 : term592 = term623.
Proof. exact (MK_COMB (@lem7012913) (@lem7012912)). Qed.
Lemma lem7012915 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7012922 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012923 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7012922 nat (nat -> Prop) f x). Qed.
Lemma lem7012924 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7012923 Peano.le m). Qed.
Lemma lem7012925 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7012926 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem7012924 m) (@lem7012925 n)). Qed.
Lemma lem7012928 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012929 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7012928 nat Prop f x). Qed.
Lemma lem7012930 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term608 m n).
Proof. exact (@lem7012929 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem7012932 (m : nat) (n : nat) : (Peano.le m n) = (term608 m n).
Proof. exact (TRANS (@lem7012926 m n) (@lem7012930 m n)). Qed.
Lemma lem7012933 (m : nat) (n : nat) : (term624 m n) = (term625 m n).
Proof. exact (MK_COMB (@lem7012915) (@lem7012932 m n)). Qed.
Lemma lem7012934 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7012941 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012942 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7012941 nat nat f x). Qed.
Lemma lem7012944 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem7012942 S n). Qed.
Lemma lem7012945 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem7012946 (m : nat) (n : nat) : (m = (S n)) = (m = (@I (nat -> nat) S n)).
Proof. exact (MK_COMB (@lem7012945 m) (@lem7012944 n)). Qed.
Lemma lem7012947 (m : nat) (n : nat) : (term626 m n) = (term627 m n).
Proof. exact (MK_COMB (@lem7012934) (@lem7012946 m n)). Qed.
Lemma lem7012948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012949 (m : nat) (n : nat) : (term628 m n) = (term629 m n).
Proof. exact (MK_COMB (@lem7012948) (@lem7012947 m n)). Qed.
Lemma lem7012950 (m : nat) (n : nat) : (term511 m n) = (term630 m n).
Proof. exact (MK_COMB (@lem7012949 m n) (@lem7012933 m n)). Qed.
Lemma lem7012957 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012958 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7012957 nat nat f x). Qed.
Lemma lem7012960 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem7012958 S n). Qed.
Lemma lem7012961 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem7012962 (m : nat) (n : nat) : (term198 m n) = (term612 m n).
Proof. exact (MK_COMB (@lem7012961 m) (@lem7012960 n)). Qed.
Lemma lem7012964 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012965 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7012964 nat (nat -> Prop) f x). Qed.
Lemma lem7012966 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7012965 Peano.le m). Qed.
Lemma lem7012967 (n : nat) : (@I (nat -> nat) S n) = (@I (nat -> nat) S n).
Proof. exact (eq_refl (@I (nat -> nat) S n)). Qed.
Lemma lem7012968 (m : nat) (n : nat) : (term612 m n) = (term613 m n).
Proof. exact (MK_COMB (@lem7012966 m) (@lem7012967 n)). Qed.
Lemma lem7012970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012971 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7012970 nat Prop f x). Qed.
Lemma lem7012972 (m : nat) (n : nat) : (term613 m n) = (term614 m n).
Proof. exact (@lem7012971 (@I (nat -> nat -> Prop) Peano.le m) (@I (nat -> nat) S n)). Qed.
Lemma lem7012973 (m : nat) (n : nat) : (term612 m n) = (term614 m n).
Proof. exact (TRANS (@lem7012968 m n) (@lem7012972 m n)). Qed.
Lemma lem7012974 (m : nat) (n : nat) : (term198 m n) = (term614 m n).
Proof. exact (TRANS (@lem7012962 m n) (@lem7012973 m n)). Qed.
Lemma lem7012975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7012976 (m : nat) (n : nat) : (term513 m n) = (term631 m n).
Proof. exact (MK_COMB (@lem7012975) (@lem7012974 m n)). Qed.
Lemma lem7012977 (m : nat) (n : nat) : (term515 m n) = (term632 m n).
Proof. exact (MK_COMB (@lem7012976 m n) (@lem7012950 m n)). Qed.
Lemma lem7012978 (m : nat) : (term554 m) = (term633 m).
Proof. exact (fun_ext (fun n : nat => @lem7012977 m n)). Qed.
Lemma lem7012979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012980 (m : nat) : (term565 m) = (term634 m).
Proof. exact (MK_COMB (@lem7012979) (@lem7012978 m)). Qed.
Lemma lem7012981 : term576 = term635.
Proof. exact (fun_ext (fun m : nat => @lem7012980 m)). Qed.
Lemma lem7012982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7012983 : term587 = term636.
Proof. exact (MK_COMB (@lem7012982) (@lem7012981)). Qed.
Lemma lem7012984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7012985 : term589 = term637.
Proof. exact (MK_COMB (@lem7012984) (@lem7012983)). Qed.
Lemma lem7012986 : term593 = term638.
Proof. exact (MK_COMB (@lem7012985) (@lem7012914)). Qed.
Lemma lem7012993 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7012994 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7012993 nat nat f x). Qed.
Lemma lem7012996 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7012994 NUMERAL 0). Qed.
Lemma lem7012997 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem7012998 (m : nat) : (m = (NUMERAL 0)) = (m = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem7012997 m) (@lem7012996)). Qed.
Lemma lem7012999 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7013006 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013007 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7013006 nat nat f x). Qed.
Lemma lem7013009 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7013007 NUMERAL 0). Qed.
Lemma lem7013010 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem7013011 (m : nat) : (term204 m) = (term639 m).
Proof. exact (MK_COMB (@lem7013010 m) (@lem7013009)). Qed.
Lemma lem7013013 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013014 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7013013 nat (nat -> Prop) f x). Qed.
Lemma lem7013015 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7013014 Peano.le m). Qed.
Lemma lem7013016 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7013017 (m : nat) : (term639 m) = (term640 m).
Proof. exact (MK_COMB (@lem7013015 m) (@lem7013016)). Qed.
Lemma lem7013019 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013020 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7013019 nat Prop f x). Qed.
Lemma lem7013021 (m : nat) : (term640 m) = (term641 m).
Proof. exact (@lem7013020 (@I (nat -> nat -> Prop) Peano.le m) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7013022 (m : nat) : (term639 m) = (term641 m).
Proof. exact (TRANS (@lem7013017 m) (@lem7013021 m)). Qed.
Lemma lem7013023 (m : nat) : (term204 m) = (term641 m).
Proof. exact (TRANS (@lem7013011 m) (@lem7013022 m)). Qed.
Lemma lem7013024 (m : nat) : (term642 m) = (term643 m).
Proof. exact (MK_COMB (@lem7012999) (@lem7013023 m)). Qed.
Lemma lem7013025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7013026 (m : nat) : (term644 m) = (term645 m).
Proof. exact (MK_COMB (@lem7013025) (@lem7013024 m)). Qed.
Lemma lem7013027 (m : nat) : (term537 m) = (term646 m).
Proof. exact (MK_COMB (@lem7013026 m) (@lem7012998 m)). Qed.
Lemma lem7013028 : term531 = term647.
Proof. exact (fun_ext (fun m : nat => @lem7013027 m)). Qed.
Lemma lem7013029 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7013030 : term549 = term648.
Proof. exact (MK_COMB (@lem7013029) (@lem7013028)). Qed.
Lemma lem7013031 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7013038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013039 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7013038 nat nat f x). Qed.
Lemma lem7013041 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7013039 NUMERAL 0). Qed.
Lemma lem7013042 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem7013043 (m : nat) : (m = (NUMERAL 0)) = (m = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem7013042 m) (@lem7013041)). Qed.
Lemma lem7013044 (m : nat) : (term649 m) = (term650 m).
Proof. exact (MK_COMB (@lem7013031) (@lem7013043 m)). Qed.
Lemma lem7013051 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013052 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7013051 nat nat f x). Qed.
Lemma lem7013054 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7013052 NUMERAL 0). Qed.
Lemma lem7013055 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem7013056 (m : nat) : (term204 m) = (term639 m).
Proof. exact (MK_COMB (@lem7013055 m) (@lem7013054)). Qed.
Lemma lem7013058 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013059 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7013058 nat (nat -> Prop) f x). Qed.
Lemma lem7013060 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7013059 Peano.le m). Qed.
Lemma lem7013061 : (@I (nat -> nat) NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (eq_refl (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7013062 (m : nat) : (term639 m) = (term640 m).
Proof. exact (MK_COMB (@lem7013060 m) (@lem7013061)). Qed.
Lemma lem7013064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013065 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7013064 nat Prop f x). Qed.
Lemma lem7013066 (m : nat) : (term640 m) = (term641 m).
Proof. exact (@lem7013065 (@I (nat -> nat -> Prop) Peano.le m) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7013067 (m : nat) : (term639 m) = (term641 m).
Proof. exact (TRANS (@lem7013062 m) (@lem7013066 m)). Qed.
Lemma lem7013068 (m : nat) : (term204 m) = (term641 m).
Proof. exact (TRANS (@lem7013056 m) (@lem7013067 m)). Qed.
Lemma lem7013069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7013070 (m : nat) : (term651 m) = (term652 m).
Proof. exact (MK_COMB (@lem7013069) (@lem7013068 m)). Qed.
Lemma lem7013071 (m : nat) : (term533 m) = (term653 m).
Proof. exact (MK_COMB (@lem7013070 m) (@lem7013044 m)). Qed.
Lemma lem7013072 : term530 = term654.
Proof. exact (fun_ext (fun m : nat => @lem7013071 m)). Qed.
Lemma lem7013073 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7013074 : term544 = term655.
Proof. exact (MK_COMB (@lem7013073) (@lem7013072)). Qed.
Lemma lem7013075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7013076 : term546 = term656.
Proof. exact (MK_COMB (@lem7013075) (@lem7013074)). Qed.
Lemma lem7013077 : term550 = term657.
Proof. exact (MK_COMB (@lem7013076) (@lem7013030)). Qed.
Lemma lem7013078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7013079 : term551 = term658.
Proof. exact (MK_COMB (@lem7013078) (@lem7013077)). Qed.
Lemma lem7013080 : term594 = term659.
Proof. exact (MK_COMB (@lem7013079) (@lem7012986)). Qed.
Lemma lem7013081 (h1 : term171) : term659.
Proof. exact (EQ_MP (@lem7013080) (@lem7012757 h1)). Qed.
Lemma lem7013082 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7013083 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7013088 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013090 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7013088 A nat f x). Qed.
Lemma lem7013095 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013096 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7013095 nat nat f x). Qed.
Lemma lem7013098 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7013096 NUMERAL 0). Qed.
Lemma lem7013099 {A : Type'} (f : A -> nat) (x : A) : (term82 A f x) = (term660 A f x).
Proof. exact (MK_COMB (@lem7013083) (@lem7013090 A f x)). Qed.
Lemma lem7013100 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem7013099 A f x) (@lem7013098)). Qed.
Lemma lem7013101 {A : Type'} (f : A -> nat) (x : A) : (term84 A f x) = (term661 A f x).
Proof. exact (MK_COMB (@lem7013082) (@lem7013100 A f x)). Qed.
Lemma lem7013102 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7013107 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013108 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7013107 A nat f x). Qed.
Lemma lem7013110 {A : Type'} (g : A -> nat) (x : A) : (g x) = (@I (A -> nat) g x).
Proof. exact (@lem7013108 A g x). Qed.
Lemma lem7013115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013116 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7013115 nat nat f x). Qed.
Lemma lem7013118 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7013116 NUMERAL 0). Qed.
Lemma lem7013119 {A : Type'} (g : A -> nat) (x : A) : (term82 A g x) = (term660 A g x).
Proof. exact (MK_COMB (@lem7013102) (@lem7013110 A g x)). Qed.
Lemma lem7013120 {A : Type'} (g : A -> nat) (x : A) : ((g x) = (NUMERAL 0)) = ((@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem7013119 A g x) (@lem7013118)). Qed.
Lemma lem7013121 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7013128 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013129 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7013128 A (type686 A) f x). Qed.
Lemma lem7013130 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7013129 A (@IN A) x). Qed.
Lemma lem7013131 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7013132 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7013130 A x) (@lem7013131 A s)). Qed.
Lemma lem7013134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013135 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7013134 (A -> Prop) Prop f x). Qed.
Lemma lem7013136 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term601 A x s).
Proof. exact (@lem7013135 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7013138 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term601 A x s).
Proof. exact (TRANS (@lem7013132 A x s) (@lem7013136 A x s)). Qed.
Lemma lem7013139 {A : Type'} (x : A) (s : A -> Prop) : (term602 A x s) = (term603 A x s).
Proof. exact (MK_COMB (@lem7013121) (@lem7013138 A x s)). Qed.
Lemma lem7013140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7013141 {A : Type'} (x : A) (s : A -> Prop) : (term490 A x s) = (term604 A x s).
Proof. exact (MK_COMB (@lem7013140) (@lem7013139 A x s)). Qed.
Lemma lem7013142 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term492 A s g x) = (term662 A s g x).
Proof. exact (MK_COMB (@lem7013141 A x s) (@lem7013120 A g x)). Qed.
Lemma lem7013143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7013144 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7013149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013151 {A : Type'} (f : A -> nat) (x : A) : (f x) = (@I (A -> nat) f x).
Proof. exact (@lem7013149 A nat f x). Qed.
Lemma lem7013156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013157 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7013156 nat nat f x). Qed.
Lemma lem7013159 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7013157 NUMERAL 0). Qed.
Lemma lem7013160 {A : Type'} (f : A -> nat) (x : A) : (term82 A f x) = (term660 A f x).
Proof. exact (MK_COMB (@lem7013144) (@lem7013151 A f x)). Qed.
Lemma lem7013161 {A : Type'} (f : A -> nat) (x : A) : ((f x) = (NUMERAL 0)) = ((@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem7013160 A f x) (@lem7013159)). Qed.
Lemma lem7013162 {A : Type'} (f : A -> nat) (x : A) : (term84 A f x) = (term661 A f x).
Proof. exact (MK_COMB (@lem7013143) (@lem7013161 A f x)). Qed.
Lemma lem7013169 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013170 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7013169 A (type686 A) f x). Qed.
Lemma lem7013171 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7013170 A (@IN A) x). Qed.
Lemma lem7013172 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7013173 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7013171 A x) (@lem7013172 A s)). Qed.
Lemma lem7013175 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7013176 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7013175 (A -> Prop) Prop f x). Qed.
Lemma lem7013177 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term601 A x s).
Proof. exact (@lem7013176 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7013179 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term601 A x s).
Proof. exact (TRANS (@lem7013173 A x s) (@lem7013177 A x s)). Qed.
Lemma lem7013180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7013181 {A : Type'} (x : A) (s : A -> Prop) : (term85 A x s) = (term663 A x s).
Proof. exact (MK_COMB (@lem7013180) (@lem7013179 A x s)). Qed.
Lemma lem7013182 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term87 A s f x) = (term664 A s f x).
Proof. exact (MK_COMB (@lem7013181 A x s) (@lem7013162 A f x)). Qed.
Lemma lem7013183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7013184 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term146 A s f x) = (term665 A s f x).
Proof. exact (MK_COMB (@lem7013183) (@lem7013182 A s f x)). Qed.
Lemma lem7013185 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term493 A f s g x) = (term666 A f s g x).
Proof. exact (MK_COMB (@lem7013184 A s f x) (@lem7013142 A s g x)). Qed.
Lemma lem7013186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7013187 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term495 A f s g x) = (term667 A f s g x).
Proof. exact (MK_COMB (@lem7013186) (@lem7013185 A f s g x)). Qed.
Lemma lem7013188 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) : (term497 A s g f x) = (term668 A s g f x).
Proof. exact (MK_COMB (@lem7013187 A f s g x) (@lem7013101 A f x)). Qed.
Lemma lem7013189 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term668 A s g f x.
Proof. exact (EQ_MP (@lem7013188 A s g f x) (@lem7012758 A s g f x h1)). Qed.
Lemma lem7013487 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term666 A f s g x.
Proof. exact (proj1 (@lem7013189 A s g f x h1)). Qed.
Lemma lem7013488 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term662 A s g x.
Proof. exact (proj2 (@lem7013487 A s g f x h1)). Qed.
Lemma lem7013489 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term664 A s f x.
Proof. exact (proj1 (@lem7013487 A s g f x h1)). Qed.
Lemma lem7013493 (h1 : term171) : term657.
Proof. exact (proj1 (@lem7013081 h1)). Qed.
Lemma lem7013496 (h1 : term171) : term648.
Proof. exact (proj2 (@lem7013493 h1)). Qed.
Lemma lem7013675 {A : Type'} (x : A) (s : A -> Prop) (h1 : term603 A x s) : term603 A x s.
Proof. exact (h1). Qed.
Lemma lem7013683 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term605 A s f g x) = (term605 A s f g x).
Proof. exact (eq_refl (term605 A s f g x)). Qed.
Lemma lem7013684 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term606 A s f g) = (term606 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7013683 A s f g x)). Qed.
Lemma lem7013685 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7013687 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term607 A s f g) = (term607 A s f g).
Proof. exact (MK_COMB (@lem7013685 A) (@lem7013684 A s f g)). Qed.
Lemma lem7013688 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term607 A s f g.
Proof. exact (EQ_MP (@lem7013687 A s f g) (@lem7012815 A s f g h1)). Qed.
Lemma lem7013842 (m : nat) : (term646 m) = (term646 m).
Proof. exact (eq_refl (term646 m)). Qed.
Lemma lem7013843 : term647 = term647.
Proof. exact (fun_ext (fun m : nat => @lem7013842 m)). Qed.
Lemma lem7013844 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7013846 : term648 = term648.
Proof. exact (MK_COMB (@lem7013844) (@lem7013843)). Qed.
Lemma lem7013847 (h1 : term171) : term648.
Proof. exact (EQ_MP (@lem7013846) (@lem7013496 h1)). Qed.
Lemma lem7013851 {A : Type'} (g : A -> nat) (x : A) (h1 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7013894 {A : Type'} (_93569 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term669 A s f g _93569.
Proof. exact (@lem7013688 A s f g h1 _93569). Qed.
Lemma lem7013895 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93569 : A) : (term669 A s f g _93569) = (term605 A s f g _93569).
Proof. exact (eq_refl (term669 A s f g _93569)). Qed.
Lemma lem7013933 (_93582 : nat) (h1 : term171) : term670 _93582.
Proof. exact (@lem7013847 h1 _93582). Qed.
Lemma lem7013934 (_93582 : nat) : (term670 _93582) = (term646 _93582).
Proof. exact (eq_refl (term670 _93582)). Qed.
Lemma lem7013989 {A : Type'} (x : A) (s : A -> Prop) (h1 : term603 A x s) : term603 A x s.
Proof. exact (h1). Qed.
Lemma lem7014007 {A : Type'} (_93569 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term605 A s f g _93569.
Proof. exact (EQ_MP (@lem7013895 A s f g _93569) (@lem7013894 A _93569 s f g h1)). Qed.
Lemma lem7014023 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term661 A f x.
Proof. exact (proj2 (@lem7013189 A s g f x h1)). Qed.
Lemma lem7014049 (_93582 : nat) (h1 : term171) : term646 _93582.
Proof. exact (EQ_MP (@lem7013934 _93582) (@lem7013933 _93582 h1)). Qed.
Lemma lem7014051 {A : Type'} (g : A -> nat) (x : A) (h1 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7014389 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term601 A x s.
Proof. exact (proj1 (@lem7013489 A s g f x h1)). Qed.
Lemma lem7014390 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term671 A x s.
Proof. exact (fun h0 : term603 A x s => @lem7014389 A s g f x h1). Qed.
Lemma lem7014392 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7014393 {A : Type'} (x : A) (s : A -> Prop) : (term671 A x s) = (term601 A x s).
Proof. exact (@lem7014392 (term601 A x s)). Qed.
Lemma lem7014394 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term601 A x s.
Proof. exact (EQ_MP (@lem7014393 A x s) (@lem7014390 A s g f x h1)). Qed.
Lemma lem7014397 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7014399 {A : Type'} (x : A) (s : A -> Prop) : (term603 A x s) = (term673 A x s).
Proof. exact (@lem7014397 (term601 A x s)). Qed.
Lemma lem7014402 {A : Type'} (x : A) (s : A -> Prop) (h1 : term603 A x s) : term673 A x s.
Proof. exact (EQ_MP (@lem7014399 A x s) (@lem7013989 A x s h1)). Qed.
Lemma lem7014405 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : False.
Proof. exact (@lem7014402 A x s h1 (@lem7014394 A s g f x h2)). Qed.
Lemma lem7014406 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : term674.
Proof. exact (fun h0 : ~ False => @lem7014405 A s g f x h1 h2). Qed.
Lemma lem7014408 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7014409 : term674 = False.
Proof. exact (@lem7014408 False). Qed.
Lemma lem7014410 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : False.
Proof. exact (EQ_MP (@lem7014409) (@lem7014406 A s g f x h1 h2)). Qed.
Lemma lem7014449 : (@I (nat -> Prop)) = (@I (nat -> Prop)).
Proof. exact (eq_refl (@I (nat -> Prop))). Qed.
Lemma lem7014450 (_93665 : nat -> Prop) (_93667 : nat -> Prop) (h1 : _93665 = _93667) : _93665 = _93667.
Proof. exact (h1). Qed.
Lemma lem7014451 (_93666 : nat) (_93668 : nat) (h1 : _93666 = _93668) : _93666 = _93668.
Proof. exact (h1). Qed.
Lemma lem7014452 (_93665 : nat -> Prop) (_93667 : nat -> Prop) (h1 : _93665 = _93667) : (@I (nat -> Prop) _93665) = (@I (nat -> Prop) _93667).
Proof. exact (MK_COMB (@lem7014449) (@lem7014450 _93665 _93667 h1)). Qed.
Lemma lem7014453 (_93665 : nat -> Prop) (_93667 : nat -> Prop) (_93666 : nat) (_93668 : nat) (h1 : _93665 = _93667) (h2 : _93666 = _93668) : (@I (nat -> Prop) _93665 _93666) = (@I (nat -> Prop) _93667 _93668).
Proof. exact (MK_COMB (@lem7014452 _93665 _93667 h1) (@lem7014451 _93666 _93668 h2)). Qed.
Lemma lem7014455 (b : Prop) (a : Prop) : term675 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7014456 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : term676 _93667 _93668 _93665 _93666.
Proof. exact (@lem7014455 (@I (nat -> Prop) _93667 _93668) (@I (nat -> Prop) _93665 _93666)). Qed.
Lemma lem7014457 (_93665 : nat -> Prop) (_93667 : nat -> Prop) (_93666 : nat) (_93668 : nat) (h1 : _93665 = _93667) (h2 : _93666 = _93668) : term677 _93667 _93668 _93665 _93666.
Proof. exact (@lem7014456 _93667 _93668 _93665 _93666 (@lem7014453 _93665 _93667 _93666 _93668 h1 h2)). Qed.
Lemma lem7014458 (_93668 : nat) (_93666 : nat) (_93665 : nat -> Prop) (_93667 : nat -> Prop) (h1 : _93665 = _93667) : term678 _93667 _93668 _93665 _93666.
Proof. exact (fun h0 : _93666 = _93668 => @lem7014457 _93665 _93667 _93666 _93668 h1 h0). Qed.
Lemma lem7014460 (a : Prop) (b : Prop) : (a -> b) = (term679 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7014461 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term678 _93667 _93668 _93665 _93666) = (term680 _93667 _93668 _93665 _93666).
Proof. exact (@lem7014460 (_93666 = _93668) (term677 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014462 (_93668 : nat) (_93666 : nat) (_93665 : nat -> Prop) (_93667 : nat -> Prop) (h1 : _93665 = _93667) : term680 _93667 _93668 _93665 _93666.
Proof. exact (EQ_MP (@lem7014461 _93667 _93668 _93665 _93666) (@lem7014458 _93668 _93666 _93665 _93667 h1)). Qed.
Lemma lem7014463 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : term681 _93667 _93668 _93665 _93666.
Proof. exact (fun h0 : _93665 = _93667 => @lem7014462 _93668 _93666 _93665 _93667 h0). Qed.
Lemma lem7014465 (a : Prop) (b : Prop) : (a -> b) = (term679 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7014466 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term681 _93667 _93668 _93665 _93666) = (term682 _93667 _93668 _93665 _93666).
Proof. exact (@lem7014465 (_93665 = _93667) (term680 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014467 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : term682 _93667 _93668 _93665 _93666.
Proof. exact (EQ_MP (@lem7014466 _93667 _93668 _93665 _93666) (@lem7014463 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014736 (x : nat -> Prop) : x = x.
Proof. exact (@lem21386 (nat -> Prop) x). Qed.
Lemma lem7014737 {A : Type'} (f : A -> nat) (x : A) : (term598 A f x) = (term598 A f x).
Proof. exact (@lem7014736 (term598 A f x)). Qed.
Lemma lem7014738 {A : Type'} (f : A -> nat) (x : A) : term683 A f x.
Proof. exact (fun h0 : term684 A f x => @lem7014737 A f x). Qed.
Lemma lem7014740 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7014741 {A : Type'} (f : A -> nat) (x : A) : (term683 A f x) = ((term598 A f x) = (term598 A f x)).
Proof. exact (@lem7014740 ((term598 A f x) = (term598 A f x))). Qed.
Lemma lem7014742 {A : Type'} (f : A -> nat) (x : A) : (term598 A f x) = (term598 A f x).
Proof. exact (EQ_MP (@lem7014741 A f x) (@lem7014738 A f x)). Qed.
Lemma lem7014744 {A : Type'} (g : A -> nat) (x : A) (h1 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7014745 {A : Type'} (g : A -> nat) (x : A) (h1 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : term685 A g x.
Proof. exact (fun h0 : term661 A g x => @lem7014744 A g x h1). Qed.
Lemma lem7014747 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7014748 {A : Type'} (g : A -> nat) (x : A) : (term685 A g x) = ((@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (@lem7014747 ((@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7014749 {A : Type'} (g : A -> nat) (x : A) (h1 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (EQ_MP (@lem7014748 A g x) (@lem7014745 A g x h1)). Qed.
Lemma lem7014751 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term601 A x s.
Proof. exact (proj1 (@lem7013489 A s g f x h1)). Qed.
Lemma lem7014752 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term671 A x s.
Proof. exact (fun h0 : term603 A x s => @lem7014751 A s g f x h1). Qed.
Lemma lem7014754 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7014755 {A : Type'} (x : A) (s : A -> Prop) : (term671 A x s) = (term601 A x s).
Proof. exact (@lem7014754 (term601 A x s)). Qed.
Lemma lem7014756 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term601 A x s.
Proof. exact (EQ_MP (@lem7014755 A x s) (@lem7014752 A s g f x h1)). Qed.
Lemma lem7014762 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7014763 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) (s : A -> Prop) : (term605 A s f g _93569) = (term686 A f g _93569 s).
Proof. exact (@lem7014762 (term600 A f g _93569) (term603 A _93569 s)). Qed.
Lemma lem7014769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7014770 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) (s : A -> Prop) : (term687 A s f g _93569) = (term688 A f g _93569 s).
Proof. exact (MK_COMB (@lem7014769) (@lem7014763 A f g _93569 s)). Qed.
Lemma lem7014776 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) (s : A -> Prop) : (term686 A f g _93569 s) = (term686 A f g _93569 s).
Proof. exact (eq_refl (term686 A f g _93569 s)). Qed.
Lemma lem7014777 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) (s : A -> Prop) : ((term605 A s f g _93569) = (term686 A f g _93569 s)) = ((term686 A f g _93569 s) = (term686 A f g _93569 s)).
Proof. exact (MK_COMB (@lem7014770 A f g _93569 s) (@lem7014776 A f g _93569 s)). Qed.
Lemma lem7014779 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7014780 (x : Prop) : (x = x) = True.
Proof. exact (@lem7014779 Prop x). Qed.
Lemma lem7014781 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) (s : A -> Prop) : ((term686 A f g _93569 s) = (term686 A f g _93569 s)) = True.
Proof. exact (@lem7014780 (term686 A f g _93569 s)). Qed.
Lemma lem7014782 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) (s : A -> Prop) : ((term605 A s f g _93569) = (term686 A f g _93569 s)) = True.
Proof. exact (TRANS (@lem7014777 A f g _93569 s) (@lem7014781 A f g _93569 s)). Qed.
Lemma lem7014783 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) (s : A -> Prop) : True = ((term605 A s f g _93569) = (term686 A f g _93569 s)).
Proof. exact (SYM (@lem7014782 A f g _93569 s)). Qed.
Lemma lem7014784 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) (s : A -> Prop) : (term605 A s f g _93569) = (term686 A f g _93569 s).
Proof. exact (EQ_MP (@lem7014783 A f g _93569 s) (@lem0)). Qed.
Lemma lem7014785 {A : Type'} (_93569 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term686 A f g _93569 s.
Proof. exact (EQ_MP (@lem7014784 A f g _93569 s) (@lem7014007 A _93569 s f g h1)). Qed.
Lemma lem7014787 (b : Prop) (a : Prop) : (a \/ b) = (term689 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7014788 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93569 : A) : (term686 A f g _93569 s) = (term690 A s f g _93569).
Proof. exact (@lem7014787 (term603 A _93569 s) (term600 A f g _93569)). Qed.
Lemma lem7014790 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7014791 {A : Type'} (_93569 : A) (s : A -> Prop) : (term692 A _93569 s) = (term601 A _93569 s).
Proof. exact (@lem7014790 (term601 A _93569 s)). Qed.
Lemma lem7014792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7014793 {A : Type'} (_93569 : A) (s : A -> Prop) : (term693 A _93569 s) = (term694 A _93569 s).
Proof. exact (MK_COMB (@lem7014792) (@lem7014791 A _93569 s)). Qed.
Lemma lem7014794 {A : Type'} (f : A -> nat) (g : A -> nat) (_93569 : A) : (term600 A f g _93569) = (term600 A f g _93569).
Proof. exact (eq_refl (term600 A f g _93569)). Qed.
Lemma lem7014795 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93569 : A) : (term690 A s f g _93569) = (term695 A s f g _93569).
Proof. exact (MK_COMB (@lem7014793 A _93569 s) (@lem7014794 A f g _93569)). Qed.
Lemma lem7014796 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93569 : A) : (term686 A f g _93569 s) = (term695 A s f g _93569).
Proof. exact (TRANS (@lem7014788 A s f g _93569) (@lem7014795 A s f g _93569)). Qed.
Lemma lem7014799 {A : Type'} (_93569 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term695 A s f g _93569.
Proof. exact (EQ_MP (@lem7014796 A s f g _93569) (@lem7014785 A _93569 s f g h1)). Qed.
Lemma lem7014800 {A : Type'} (_93569 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term695 A s f g _93569.
Proof. exact (@lem7014799 A _93569 s f g h1). Qed.
Lemma lem7014801 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term695 A s f g x.
Proof. exact (@lem7014800 A x s f g h1). Qed.
Lemma lem7014804 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term497 A s g f x) : term600 A f g x.
Proof. exact (@lem7014801 A x s f g h1 (@lem7014756 A s g f x h2)). Qed.
Lemma lem7014805 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term497 A s g f x) : term696 A f g x.
Proof. exact (fun h0 : term697 A f g x => @lem7014804 A s g f x h1 h2). Qed.
Lemma lem7014807 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7014808 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term696 A f g x) = (term600 A f g x).
Proof. exact (@lem7014807 (term600 A f g x)). Qed.
Lemma lem7014809 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term497 A s g f x) : term600 A f g x.
Proof. exact (EQ_MP (@lem7014808 A f g x) (@lem7014805 A s g f x h1 h2)). Qed.
Lemma lem7014827 (q : Prop) (p : Prop) (r : Prop) : (term698 p q r) = (term698 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7014828 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term680 _93667 _93668 _93665 _93666) = (term699 _93667 _93668 _93665 _93666).
Proof. exact (@lem7014827 (@I (nat -> Prop) _93667 _93668) (term700 _93666 _93668) (term701 _93665 _93666)). Qed.
Lemma lem7014846 (_93665 : nat -> Prop) (_93667 : nat -> Prop) : (term702 _93665 _93667) = (term702 _93665 _93667).
Proof. exact (eq_refl (term702 _93665 _93667)). Qed.
Lemma lem7014847 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term682 _93667 _93668 _93665 _93666) = (term703 _93667 _93668 _93665 _93666).
Proof. exact (MK_COMB (@lem7014846 _93665 _93667) (@lem7014828 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014851 (q : Prop) (p : Prop) (r : Prop) : (term698 p q r) = (term698 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7014852 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term703 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666).
Proof. exact (@lem7014851 (@I (nat -> Prop) _93667 _93668) (term705 _93665 _93667) (term706 _93668 _93665 _93666)). Qed.
Lemma lem7014882 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term682 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666).
Proof. exact (TRANS (@lem7014847 _93667 _93668 _93665 _93666) (@lem7014852 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7014884 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term707 _93667 _93668 _93665 _93666) = (term708 _93667 _93668 _93665 _93666).
Proof. exact (MK_COMB (@lem7014883) (@lem7014882 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014914 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term704 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666).
Proof. exact (eq_refl (term704 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014915 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : ((term682 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666)) = ((term704 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666)).
Proof. exact (MK_COMB (@lem7014884 _93667 _93668 _93665 _93666) (@lem7014914 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014917 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7014918 (x : Prop) : (x = x) = True.
Proof. exact (@lem7014917 Prop x). Qed.
Lemma lem7014919 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : ((term704 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666)) = True.
Proof. exact (@lem7014918 (term704 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014920 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : ((term682 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666)) = True.
Proof. exact (TRANS (@lem7014915 _93667 _93668 _93665 _93666) (@lem7014919 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014921 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : True = ((term682 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666)).
Proof. exact (SYM (@lem7014920 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014922 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term682 _93667 _93668 _93665 _93666) = (term704 _93667 _93668 _93665 _93666).
Proof. exact (EQ_MP (@lem7014921 _93667 _93668 _93665 _93666) (@lem0)). Qed.
Lemma lem7014923 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : term704 _93667 _93668 _93665 _93666.
Proof. exact (EQ_MP (@lem7014922 _93667 _93668 _93665 _93666) (@lem7014467 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014925 (b : Prop) (a : Prop) : (a \/ b) = (term689 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7014926 (_93665 : nat -> Prop) (_93666 : nat) (_93667 : nat -> Prop) (_93668 : nat) : (term704 _93667 _93668 _93665 _93666) = (term709 _93665 _93666 _93667 _93668).
Proof. exact (@lem7014925 (term710 _93667 _93668 _93665 _93666) (@I (nat -> Prop) _93667 _93668)). Qed.
Lemma lem7014928 (a : Prop) (b : Prop) : (term711 a b) = (term712 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7014929 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term713 _93667 _93668 _93665 _93666) = (term714 _93667 _93668 _93665 _93666).
Proof. exact (@lem7014928 (term705 _93665 _93667) (term706 _93668 _93665 _93666)). Qed.
Lemma lem7014931 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7014932 (_93665 : nat -> Prop) (_93667 : nat -> Prop) : (term715 _93665 _93667) = (_93665 = _93667).
Proof. exact (@lem7014931 (_93665 = _93667)). Qed.
Lemma lem7014933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7014934 (_93665 : nat -> Prop) (_93667 : nat -> Prop) : (term716 _93665 _93667) = (term717 _93665 _93667).
Proof. exact (MK_COMB (@lem7014933) (@lem7014932 _93665 _93667)). Qed.
Lemma lem7014936 (a : Prop) (b : Prop) : (term711 a b) = (term712 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7014937 (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term718 _93668 _93665 _93666) = (term719 _93668 _93665 _93666).
Proof. exact (@lem7014936 (term700 _93666 _93668) (term701 _93665 _93666)). Qed.
Lemma lem7014939 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7014940 (_93666 : nat) (_93668 : nat) : (term720 _93666 _93668) = (_93666 = _93668).
Proof. exact (@lem7014939 (_93666 = _93668)). Qed.
Lemma lem7014941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7014942 (_93666 : nat) (_93668 : nat) : (term721 _93666 _93668) = (term722 _93666 _93668).
Proof. exact (MK_COMB (@lem7014941) (@lem7014940 _93666 _93668)). Qed.
Lemma lem7014944 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7014945 (_93665 : nat -> Prop) (_93666 : nat) : (term723 _93665 _93666) = (@I (nat -> Prop) _93665 _93666).
Proof. exact (@lem7014944 (@I (nat -> Prop) _93665 _93666)). Qed.
Lemma lem7014946 (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term719 _93668 _93665 _93666) = (term724 _93668 _93665 _93666).
Proof. exact (MK_COMB (@lem7014942 _93666 _93668) (@lem7014945 _93665 _93666)). Qed.
Lemma lem7014947 (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term718 _93668 _93665 _93666) = (term724 _93668 _93665 _93666).
Proof. exact (TRANS (@lem7014937 _93668 _93665 _93666) (@lem7014946 _93668 _93665 _93666)). Qed.
Lemma lem7014948 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term714 _93667 _93668 _93665 _93666) = (term725 _93667 _93668 _93665 _93666).
Proof. exact (MK_COMB (@lem7014934 _93665 _93667) (@lem7014947 _93668 _93665 _93666)). Qed.
Lemma lem7014949 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term713 _93667 _93668 _93665 _93666) = (term725 _93667 _93668 _93665 _93666).
Proof. exact (TRANS (@lem7014929 _93667 _93668 _93665 _93666) (@lem7014948 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7014951 (_93667 : nat -> Prop) (_93668 : nat) (_93665 : nat -> Prop) (_93666 : nat) : (term726 _93667 _93668 _93665 _93666) = (term727 _93667 _93668 _93665 _93666).
Proof. exact (MK_COMB (@lem7014950) (@lem7014949 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014952 (_93667 : nat -> Prop) (_93668 : nat) : (@I (nat -> Prop) _93667 _93668) = (@I (nat -> Prop) _93667 _93668).
Proof. exact (eq_refl (@I (nat -> Prop) _93667 _93668)). Qed.
Lemma lem7014953 (_93665 : nat -> Prop) (_93666 : nat) (_93667 : nat -> Prop) (_93668 : nat) : (term709 _93665 _93666 _93667 _93668) = (term728 _93665 _93666 _93667 _93668).
Proof. exact (MK_COMB (@lem7014951 _93667 _93668 _93665 _93666) (@lem7014952 _93667 _93668)). Qed.
Lemma lem7014954 (_93665 : nat -> Prop) (_93666 : nat) (_93667 : nat -> Prop) (_93668 : nat) : (term704 _93667 _93668 _93665 _93666) = (term728 _93665 _93666 _93667 _93668).
Proof. exact (TRANS (@lem7014926 _93665 _93666 _93667 _93668) (@lem7014953 _93665 _93666 _93667 _93668)). Qed.
Lemma lem7014956 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term497 A s g f x) (h3 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : term729 A f g x.
Proof. exact (conj (@lem7014749 A g x h3) (@lem7014809 A s g f x h1 h2)). Qed.
Lemma lem7014957 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term497 A s g f x) (h3 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : term730 A f g x.
Proof. exact (conj (@lem7014742 A f x) (@lem7014956 A s f g x h1 h2 h3)). Qed.
Lemma lem7014959 (_93665 : nat -> Prop) (_93666 : nat) (_93667 : nat -> Prop) (_93668 : nat) : term728 _93665 _93666 _93667 _93668.
Proof. exact (EQ_MP (@lem7014954 _93665 _93666 _93667 _93668) (@lem7014923 _93667 _93668 _93665 _93666)). Qed.
Lemma lem7014960 {A : Type'} (g : A -> nat) (f : A -> nat) (x : A) : term731 A g f x.
Proof. exact (@lem7014959 (term598 A f x) (@I (A -> nat) g x) (term598 A f x) (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7014963 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term497 A s g f x) (h3 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : term732 A f x.
Proof. exact (@lem7014960 A g f x (@lem7014957 A s f g x h1 h2 h3)). Qed.
Lemma lem7014964 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term497 A s g f x) (h3 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : term733 A f x.
Proof. exact (fun h0 : term734 A f x => @lem7014963 A s f g x h1 h2 h3). Qed.
Lemma lem7014966 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7014967 {A : Type'} (f : A -> nat) (x : A) : (term733 A f x) = (term732 A f x).
Proof. exact (@lem7014966 (term732 A f x)). Qed.
Lemma lem7014968 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term497 A s g f x) (h3 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : term732 A f x.
Proof. exact (EQ_MP (@lem7014967 A f x) (@lem7014964 A s f g x h1 h2 h3)). Qed.
Lemma lem7014974 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7014975 (_93582 : nat) : (term646 _93582) = (term735 _93582).
Proof. exact (@lem7014974 (_93582 = (@I (nat -> nat) NUMERAL 0)) (term643 _93582)). Qed.
Lemma lem7014983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7014984 (_93582 : nat) : (term736 _93582) = (term737 _93582).
Proof. exact (MK_COMB (@lem7014983) (@lem7014975 _93582)). Qed.
Lemma lem7014992 (_93582 : nat) : (term735 _93582) = (term735 _93582).
Proof. exact (eq_refl (term735 _93582)). Qed.
Lemma lem7014993 (_93582 : nat) : ((term646 _93582) = (term735 _93582)) = ((term735 _93582) = (term735 _93582)).
Proof. exact (MK_COMB (@lem7014984 _93582) (@lem7014992 _93582)). Qed.
Lemma lem7014995 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7014996 (x : Prop) : (x = x) = True.
Proof. exact (@lem7014995 Prop x). Qed.
Lemma lem7014997 (_93582 : nat) : ((term735 _93582) = (term735 _93582)) = True.
Proof. exact (@lem7014996 (term735 _93582)). Qed.
Lemma lem7014998 (_93582 : nat) : ((term646 _93582) = (term735 _93582)) = True.
Proof. exact (TRANS (@lem7014993 _93582) (@lem7014997 _93582)). Qed.
Lemma lem7014999 (_93582 : nat) : True = ((term646 _93582) = (term735 _93582)).
Proof. exact (SYM (@lem7014998 _93582)). Qed.
Lemma lem7015000 (_93582 : nat) : (term646 _93582) = (term735 _93582).
Proof. exact (EQ_MP (@lem7014999 _93582) (@lem0)). Qed.
Lemma lem7015001 (_93582 : nat) (h1 : term171) : term735 _93582.
Proof. exact (EQ_MP (@lem7015000 _93582) (@lem7014049 _93582 h1)). Qed.
Lemma lem7015003 (b : Prop) (a : Prop) : (a \/ b) = (term689 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7015004 (_93582 : nat) : (term735 _93582) = (term738 _93582).
Proof. exact (@lem7015003 (term643 _93582) (_93582 = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7015006 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7015007 (_93582 : nat) : (term739 _93582) = (term641 _93582).
Proof. exact (@lem7015006 (term641 _93582)). Qed.
Lemma lem7015008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7015009 (_93582 : nat) : (term740 _93582) = (term741 _93582).
Proof. exact (MK_COMB (@lem7015008) (@lem7015007 _93582)). Qed.
Lemma lem7015010 (_93582 : nat) : (_93582 = (@I (nat -> nat) NUMERAL 0)) = (_93582 = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (eq_refl (_93582 = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7015011 (_93582 : nat) : (term738 _93582) = (term742 _93582).
Proof. exact (MK_COMB (@lem7015009 _93582) (@lem7015010 _93582)). Qed.
Lemma lem7015012 (_93582 : nat) : (term735 _93582) = (term742 _93582).
Proof. exact (TRANS (@lem7015004 _93582) (@lem7015011 _93582)). Qed.
Lemma lem7015015 (_93582 : nat) (h1 : term171) : term742 _93582.
Proof. exact (EQ_MP (@lem7015012 _93582) (@lem7015001 _93582 h1)). Qed.
Lemma lem7015016 {A : Type'} (f : A -> nat) (x : A) (h1 : term171) : term743 A f x.
Proof. exact (@lem7015015 (@I (A -> nat) f x) h1). Qed.
Lemma lem7015019 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : (@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7015016 A f x h2 (@lem7014968 A s f g x h1 h3 h4)). Qed.
Lemma lem7015020 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : term685 A f x.
Proof. exact (fun h0 : term661 A f x => @lem7015019 A s f g x h1 h2 h3 h4). Qed.
Lemma lem7015022 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7015023 {A : Type'} (f : A -> nat) (x : A) : (term685 A f x) = ((@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (@lem7015022 ((@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7015024 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : (@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (EQ_MP (@lem7015023 A f x) (@lem7015020 A s f g x h1 h2 h3 h4)). Qed.
Lemma lem7015027 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7015029 {A : Type'} (f : A -> nat) (x : A) : (term661 A f x) = (term744 A f x).
Proof. exact (@lem7015027 ((@I (A -> nat) f x) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7015032 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term497 A s g f x) : term744 A f x.
Proof. exact (EQ_MP (@lem7015029 A f x) (@lem7014023 A s g f x h1)). Qed.
Lemma lem7015035 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : False.
Proof. exact (@lem7015032 A s g f x h3 (@lem7015024 A s f g x h1 h2 h3 h4)). Qed.
Lemma lem7015036 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : term674.
Proof. exact (fun h0 : ~ False => @lem7015035 A s f g x h1 h2 h3 h4). Qed.
Lemma lem7015038 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7015039 : term674 = False.
Proof. exact (@lem7015038 False). Qed.
Lemma lem7015040 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem7015039) (@lem7015036 A s f g x h1 h2 h3 h4)). Qed.
Lemma lem7015041 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : ((@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0) => @lem7015040 A s f g x h1 h2 h3 h4) (fun h5 : False => @lem7014051 A g x h4)). Qed.
Lemma lem7015042 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem7015041 A s f g x h1 h2 h3 h4) (@lem7014051 A g x h4)). Qed.
Lemma lem7015043 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : (term603 A x s) = False.
Proof. exact (prop_ext (fun h3 : term603 A x s => @lem7014410 A s g f x h1 h2) (fun h3 : False => @lem7013989 A x s h1)). Qed.
Lemma lem7015044 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : False.
Proof. exact (EQ_MP (@lem7015043 A s g f x h1 h2) (@lem7013989 A x s h1)). Qed.
Lemma lem7015045 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : ((@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0) => @lem7015042 A s f g x h1 h2 h3 h4) (fun h5 : False => @lem7013851 A g x h4)). Qed.
Lemma lem7015046 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem7015045 A s f g x h1 h2 h3 h4) (@lem7013851 A g x h4)). Qed.
Lemma lem7015047 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : (term603 A x s) = False.
Proof. exact (prop_ext (fun h3 : term603 A x s => @lem7015044 A s g f x h1 h2) (fun h3 : False => @lem7013675 A x s h1)). Qed.
Lemma lem7015048 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : False.
Proof. exact (EQ_MP (@lem7015047 A s g f x h1 h2) (@lem7013675 A x s h1)). Qed.
Lemma lem7015049 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : ((@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0) => @lem7015046 A s f g x h1 h2 h3 h4) (fun h5 : False => @lem7013851 A g x h4)). Qed.
Lemma lem7015050 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) (h4 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem7015049 A s f g x h1 h2 h3 h4) (@lem7013851 A g x h4)). Qed.
Lemma lem7015051 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : (term603 A x s) = False.
Proof. exact (prop_ext (fun h3 : term603 A x s => @lem7015048 A s g f x h1 h2) (fun h3 : False => @lem7013675 A x s h1)). Qed.
Lemma lem7015052 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term603 A x s) (h2 : term497 A s g f x) : False.
Proof. exact (EQ_MP (@lem7015051 A s g f x h1 h2) (@lem7013675 A x s h1)). Qed.
Lemma lem7015053 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term497 A s g f x) : False.
Proof. exact (or_elim (@lem7013488 A s g f x h3) (fun h0 : term603 A x s => @lem7015052 A s g f x h0 h3) (fun h0 : (@I (A -> nat) g x) = (@I (nat -> nat) NUMERAL 0) => @lem7015050 A s f g x h1 h2 h3 h0)). Qed.
Lemma lem7015054 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (f : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term277 A _93554) (h3 : term171) (h4 : term497 A s g f x) : False.
Proof. exact (ex_elim (@lem7012158 A _93554 h2) (fun x' : type640 A => fun h0 : term483 A _93554 x' => @lem7015053 A s g f x h1 h3 h4)). Qed.
Lemma lem7015055 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term76 A s f g) (h2 : term277 A _93554) (h3 : term164 A s g f) (h4 : term171) : False.
Proof. exact (ex_elim (@lem7012313 A s g f h3) (fun x : A => fun h0 : term505 A s g f x => @lem7015054 A _93554 s g f x h1 h2 h4 h0)). Qed.
Lemma lem7015056 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term76 A s f g) (h2 : term277 A _93554) (h3 : term164 A s g f) : term169.
Proof. exact (fun h0 : term171 => @lem7015055 A _93554 s g f h1 h2 h3 h0). Qed.
Lemma lem7015057 : term169 = term170.
Proof. exact (@lem69 term171). Qed.
Lemma lem7015058 {A : Type'} (_93554 : type641 A) (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term76 A s f g) (h2 : term277 A _93554) (h3 : term164 A s g f) : term170.
Proof. exact (EQ_MP (@lem7015057) (@lem7015056 A _93554 s g f h1 h2 h3)). Qed.
Lemma lem7015059 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93554 : type641 A) (h1 : term76 A s f g) (h2 : term277 A _93554) : term174 A s g f.
Proof. exact (fun h0 : term164 A s g f => @lem7015058 A _93554 s g f h1 h2 h0). Qed.
Lemma lem7015060 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93554 : type641 A) (h1 : term76 A s f g) (h2 : term277 A _93554) : term211 A _93554 s g f.
Proof. exact (fun h0 : term209 A _93554 s g => @lem7015059 A s f g _93554 h1 h2). Qed.
Lemma lem7015061 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (_93554 : type641 A) (h1 : term277 A _93554) : term214 A _93554 s g f.
Proof. exact (fun h0 : term76 A s f g => @lem7015060 A s f g _93554 h0 h1). Qed.
Lemma lem7015066 {A : Type'} (g : A -> nat) (f : A -> nat) (_93554 : type641 A) (h1 : term277 A _93554) : term216 A _93554 g f.
Proof. exact (fun s : A -> Prop => @lem7015061 A s g f _93554 h1). Qed.
Lemma lem7015071 {A : Type'} (f : A -> nat) (_93554 : type641 A) (h1 : term277 A _93554) : term218 A _93554 f.
Proof. exact (fun g : A -> nat => @lem7015066 A g f _93554 h1). Qed.
Lemma lem7015076 {A : Type'} (_93554 : type641 A) (h1 : term277 A _93554) : term220 A _93554.
Proof. exact (fun f : A -> nat => @lem7015071 A f _93554 h1). Qed.
Lemma lem7015077 {A : Type'} (_93554 : type641 A) : term279 A _93554.
Proof. exact (fun h0 : term277 A _93554 => @lem7015076 A _93554 h0). Qed.
Lemma lem7015082 {A : Type'} : term281 A.
Proof. exact (fun _93554 : type641 A => @lem7015077 A _93554). Qed.
Lemma lem7015083 {A : Type'} : term190 A.
Proof. exact (EQ_MP (@lem7011535 A) (@lem7015082 A)). Qed.
Lemma lem7015084 {A : Type'} (f : A -> nat) : term745 A f.
Proof. exact (@lem7015083 A f). Qed.
Lemma lem7015085 {A : Type'} (f : A -> nat) : (term745 A f) = (term186 A f).
Proof. exact (eq_refl (term745 A f)). Qed.
Lemma lem7015086 {A : Type'} (f : A -> nat) : term186 A f.
Proof. exact (EQ_MP (@lem7015085 A f) (@lem7015084 A f)). Qed.
Lemma lem7015087 {A : Type'} (f : A -> nat) (g : A -> nat) : term746 A f g.
Proof. exact (@lem7015086 A f g). Qed.
Lemma lem7015088 {A : Type'} (g : A -> nat) (f : A -> nat) : (term746 A f g) = (term182 A g f).
Proof. exact (eq_refl (term746 A f g)). Qed.
Lemma lem7015089 {A : Type'} (g : A -> nat) (f : A -> nat) : term182 A g f.
Proof. exact (EQ_MP (@lem7015088 A g f) (@lem7015087 A f g)). Qed.
Lemma lem7015090 {A : Type'} (g : A -> nat) (f : A -> nat) (s : A -> Prop) : term747 A g f s.
Proof. exact (@lem7015089 A g f s). Qed.
Lemma lem7015091 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : (term747 A g f s) = (term165 A s g f).
Proof. exact (eq_refl (term747 A g f s)). Qed.
Lemma lem7015092 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : term165 A s g f.
Proof. exact (EQ_MP (@lem7015091 A s g f) (@lem7015090 A g f s)). Qed.
Lemma lem7015094 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : term165 A s g f.
Proof. exact (@lem7010945 A s g f (@lem7015092 A s g f)). Qed.
Lemma lem7015095 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term176 A s g f.
Proof. exact (@lem7015094 A s g f (@lem7010602 A s f g h1)). Qed.
Lemma lem7015096 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term173 A s g f.
Proof. exact (@lem7015095 A s f g h1 (@lem7010601 A s g h2)). Qed.
Lemma lem7015097 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) (h3 : term164 A s g f) : term169.
Proof. exact (@lem7015096 A f s g h1 h2 (@lem7010929 A s g f h3)). Qed.
Lemma lem7015098 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) (h3 : term164 A s g f) : False.
Proof. exact (@lem7015097 A s g f h1 h2 h3 (@lem89501)). Qed.
Lemma lem7015099 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) (h3 : term164 A s g f) : (term164 A s g f) = False.
Proof. exact (prop_ext (fun h4 : term164 A s g f => @lem7015098 A s g f h1 h2 h3) (fun h4 : False => @lem7010929 A s g f h3)). Qed.
Lemma lem7015100 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) (h3 : term164 A s g f) : False.
Proof. exact (EQ_MP (@lem7015099 A s g f h1 h2 h3) (@lem7010929 A s g f h3)). Qed.
Lemma lem7015101 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term163 A s g f.
Proof. exact (fun h0 : term164 A s g f => @lem7015100 A s g f h1 h2 h0). Qed.
Lemma lem7015102 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term157 A s g f.
Proof. exact (EQ_MP (@lem7010928 A s g f) (@lem7015101 A f s g h1 h2)). Qed.
Lemma lem7015104 {A : Type'} (t : A -> Prop) : term42 A t.
Proof. exact (EQ_MP (@lem7010529 A t) (@lem7010528 A t)). Qed.
Lemma lem7015105 {A : Type'} (t : A -> Prop) : term42 A t.
Proof. exact (@lem7015104 A t). Qed.
Lemma lem7015106 {A : Type'} (s : A -> Prop) (g : A -> nat) : term748 A s g.
Proof. exact (@lem7015105 A (term98 A s g)). Qed.
Lemma lem7015107 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : term749 A s g.
Proof. exact (@lem7015106 A s g (@lem7010601 A s g h1)). Qed.
Lemma lem7015108 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term749 A s g) : term749 A s g.
Proof. exact (h1). Qed.
Lemma lem7015109 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term749 A s g) : term750 A s g s'.
Proof. exact (@lem7015108 A s g h1 s'). Qed.
Lemma lem7015110 {A : Type'} (s : A -> Prop) (g : A -> nat) (s' : A -> Prop) : (term750 A s g s') = (term751 A s g s').
Proof. exact (eq_refl (term750 A s g s')). Qed.
Lemma lem7015111 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term749 A s g) : term751 A s g s'.
Proof. exact (EQ_MP (@lem7015110 A s g s') (@lem7015109 A s' s g h1)). Qed.
Lemma lem7015112 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term752 A s' s g) : term752 A s' s g.
Proof. exact (h1). Qed.
Lemma lem7015113 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term749 A s g) (h2 : term752 A s' s g) : @FINITE A s'.
Proof. exact (@lem7015111 A s' s g h1 (@lem7015112 A s' s g h2)). Qed.
Lemma lem7015114 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term752 A s' s g) : term753 A s g s'.
Proof. exact (fun h0 : term749 A s g => @lem7015113 A s' s g h0 h1). Qed.
Lemma lem7015115 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term749 A s g) : term749 A s g.
Proof. exact (h1). Qed.
Lemma lem7015116 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term749 A s g) (h2 : term752 A s' s g) : @FINITE A s'.
Proof. exact (@lem7015114 A s' s g h2 (@lem7015115 A s g h1)). Qed.
Lemma lem7015117 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term749 A s g) : term751 A s g s'.
Proof. exact (fun h0 : term752 A s' s g => @lem7015116 A s' s g h1 h0). Qed.
Lemma lem7015118 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term749 A s g) : term749 A s g.
Proof. exact (fun s' : A -> Prop => @lem7015117 A s' s g h1). Qed.
Lemma lem7015119 {A : Type'} (s : A -> Prop) (g : A -> nat) : term754 A s g.
Proof. exact (fun h0 : term749 A s g => @lem7015118 A s g h0). Qed.
Lemma lem7015120 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : term749 A s g.
Proof. exact (@lem7015119 A s g (@lem7015107 A s g h1)). Qed.
Lemma lem7015121 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : term750 A s g s'.
Proof. exact (@lem7015120 A s g h1 s'). Qed.
Lemma lem7015122 {A : Type'} (s : A -> Prop) (g : A -> nat) (s' : A -> Prop) : (term750 A s g s') = (term751 A s g s').
Proof. exact (eq_refl (term750 A s g s')). Qed.
Lemma lem7015125 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : term751 A s g s'.
Proof. exact (EQ_MP (@lem7015122 A s g s') (@lem7015121 A s' s g h1)). Qed.
Lemma lem7015126 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : term751 A s g s'.
Proof. exact (@lem7015125 A s' s g h1). Qed.
Lemma lem7015127 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : term755 A g s f.
Proof. exact (@lem7015126 A (term98 A s f) s g h1). Qed.
Lemma lem7015129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term25 A s t).
Proof. exact (EQ_MP (@lem7010482 A s t) (@lem7010481 A s t)). Qed.
Lemma lem7015130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term25 A s t).
Proof. exact (@lem7015129 A s t). Qed.
Lemma lem7015131 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term756 A f s g) = (term757 A f s g).
Proof. exact (@lem7015130 A (term98 A s f) (term98 A s g)). Qed.
Lemma lem7015139 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7010469 _83095 p x) (@lem7010468 _83095 p x)). Qed.
Lemma lem7015140 {A : Type'} (p : A -> Prop) (x : A) : (term21 A x p) = (p x).
Proof. exact (@lem7015139 A p x). Qed.
Lemma lem7015141 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term133 A x s f) = (term134 A s f x).
Proof. exact (@lem7015140 A (term135 A s f) x). Qed.
Lemma lem7015142 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term134 A s f x) = (term87 A s f x).
Proof. exact (eq_refl (term134 A s f x)). Qed.
Lemma lem7015143 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7015144 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term136 A GEN_PVAR_237 s f x) = (term89 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7015143 A GEN_PVAR_237) (@lem7015142 A s f x)). Qed.
Lemma lem7015145 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7015146 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) (x : A) : (term137 A GEN_PVAR_237 s f x) = (term91 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7015144 A GEN_PVAR_237 s f x) (@lem7015145 A x)). Qed.
Lemma lem7015147 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term138 A GEN_PVAR_237 s f) = (term93 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem7015146 A GEN_PVAR_237 s f x)). Qed.
Lemma lem7015148 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7015149 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> nat) : (term139 A GEN_PVAR_237 s f) = (term95 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7015148 A) (@lem7015147 A GEN_PVAR_237 s f)). Qed.
Lemma lem7015150 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term140 A s f) = (term97 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7015149 A GEN_PVAR_237 s f)). Qed.
Lemma lem7015151 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7015152 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term141 A s f) = (term98 A s f).
Proof. exact (MK_COMB (@lem7015151 A) (@lem7015150 A s f)). Qed.
Lemma lem7015153 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7015154 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term133 A x s f) = (term142 A x s f).
Proof. exact (MK_COMB (@lem7015153 A x) (@lem7015152 A s f)). Qed.
Lemma lem7015155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7015156 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : (term143 A x s f) = (term144 A x s f).
Proof. exact (MK_COMB (@lem7015155) (@lem7015154 A x s f)). Qed.
Lemma lem7015157 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term134 A s f x) = (term87 A s f x).
Proof. exact (eq_refl (term134 A s f x)). Qed.
Lemma lem7015158 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : ((term133 A x s f) = (term134 A s f x)) = ((term142 A x s f) = (term87 A s f x)).
Proof. exact (MK_COMB (@lem7015156 A x s f) (@lem7015157 A s f x)). Qed.
Lemma lem7015159 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term142 A x s f) = (term87 A s f x).
Proof. exact (EQ_MP (@lem7015158 A s f x) (@lem7015141 A s f x)). Qed.
Lemma lem7015164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7015165 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term758 A x s f) = (term759 A s f x).
Proof. exact (MK_COMB (@lem7015164) (@lem7015159 A s f x)). Qed.
Lemma lem7015167 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7010469 _83095 p x) (@lem7010468 _83095 p x)). Qed.
Lemma lem7015168 {A : Type'} (p : A -> Prop) (x : A) : (term21 A x p) = (p x).
Proof. exact (@lem7015167 A p x). Qed.
Lemma lem7015169 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term133 A x s g) = (term134 A s g x).
Proof. exact (@lem7015168 A (term135 A s g) x). Qed.
Lemma lem7015170 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term134 A s g x) = (term87 A s g x).
Proof. exact (eq_refl (term134 A s g x)). Qed.
Lemma lem7015171 {A : Type'} (GEN_PVAR_299 : A) : (@SETSPEC A GEN_PVAR_299) = (@SETSPEC A GEN_PVAR_299).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_299)). Qed.
Lemma lem7015172 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term136 A GEN_PVAR_299 s g x) = (term89 A GEN_PVAR_299 s g x).
Proof. exact (MK_COMB (@lem7015171 A GEN_PVAR_299) (@lem7015170 A s g x)). Qed.
Lemma lem7015173 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7015174 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term137 A GEN_PVAR_299 s g x) = (term91 A GEN_PVAR_299 s g x).
Proof. exact (MK_COMB (@lem7015172 A GEN_PVAR_299 s g x) (@lem7015173 A x)). Qed.
Lemma lem7015175 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term138 A GEN_PVAR_299 s g) = (term93 A GEN_PVAR_299 s g).
Proof. exact (fun_ext (fun x : A => @lem7015174 A GEN_PVAR_299 s g x)). Qed.
Lemma lem7015176 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7015177 {A : Type'} (GEN_PVAR_299 : A) (s : A -> Prop) (g : A -> nat) : (term139 A GEN_PVAR_299 s g) = (term95 A GEN_PVAR_299 s g).
Proof. exact (MK_COMB (@lem7015176 A) (@lem7015175 A GEN_PVAR_299 s g)). Qed.
Lemma lem7015178 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term140 A s g) = (term97 A s g).
Proof. exact (fun_ext (fun GEN_PVAR_299 : A => @lem7015177 A GEN_PVAR_299 s g)). Qed.
Lemma lem7015179 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7015180 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term141 A s g) = (term98 A s g).
Proof. exact (MK_COMB (@lem7015179 A) (@lem7015178 A s g)). Qed.
Lemma lem7015181 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7015182 {A : Type'} (x : A) (s : A -> Prop) (g : A -> nat) : (term133 A x s g) = (term142 A x s g).
Proof. exact (MK_COMB (@lem7015181 A x) (@lem7015180 A s g)). Qed.
Lemma lem7015183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7015184 {A : Type'} (x : A) (s : A -> Prop) (g : A -> nat) : (term143 A x s g) = (term144 A x s g).
Proof. exact (MK_COMB (@lem7015183) (@lem7015182 A x s g)). Qed.
Lemma lem7015185 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term134 A s g x) = (term87 A s g x).
Proof. exact (eq_refl (term134 A s g x)). Qed.
Lemma lem7015186 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : ((term133 A x s g) = (term134 A s g x)) = ((term142 A x s g) = (term87 A s g x)).
Proof. exact (MK_COMB (@lem7015184 A x s g) (@lem7015185 A s g x)). Qed.
Lemma lem7015187 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term142 A x s g) = (term87 A s g x).
Proof. exact (EQ_MP (@lem7015186 A s g x) (@lem7015169 A s g x)). Qed.
Lemma lem7015192 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term760 A f x s g) = (term761 A f s g x).
Proof. exact (MK_COMB (@lem7015165 A s f x) (@lem7015187 A s g x)). Qed.
Lemma lem7015195 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term762 A f s g) = (term763 A f s g).
Proof. exact (fun_ext (fun x : A => @lem7015192 A f s g x)). Qed.
Lemma lem7015196 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7015197 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term757 A f s g) = (term764 A f s g).
Proof. exact (MK_COMB (@lem7015196 A) (@lem7015195 A f s g)). Qed.
Lemma lem7015202 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term756 A f s g) = (term764 A f s g).
Proof. exact (TRANS (@lem7015131 A f s g) (@lem7015197 A f s g)). Qed.
Lemma lem7015203 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term764 A f s g) = (term756 A f s g).
Proof. exact (SYM (@lem7015202 A f s g)). Qed.
Lemma lem7015205 (p : Prop) : p = (term162 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7015206 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term764 A f s g) = (term765 A f s g).
Proof. exact (@lem7015205 (term764 A f s g)). Qed.
Lemma lem7015207 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term765 A f s g) = (term764 A f s g).
Proof. exact (SYM (@lem7015206 A f s g)). Qed.
Lemma lem7015208 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term766 A f s g) : term766 A f s g.
Proof. exact (h1). Qed.
Lemma lem7015211 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term767 A f s g) : term767 A f s g.
Proof. exact (h1). Qed.
Lemma lem7015212 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term768 A f s g.
Proof. exact (fun h0 : term767 A f s g => @lem7015211 A f s g h0). Qed.
Lemma lem7015213 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term768 A f s g) : term768 A f s g.
Proof. exact (h1). Qed.
Lemma lem7015214 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term767 A f s g) : term767 A f s g.
Proof. exact (h1). Qed.
Lemma lem7015215 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term767 A f s g) (h2 : term768 A f s g) : term767 A f s g.
Proof. exact (@lem7015213 A f s g h2 (@lem7015214 A f s g h1)). Qed.
Lemma lem7015216 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term767 A f s g) : term769 A f s g.
Proof. exact (fun h0 : term768 A f s g => @lem7015215 A f s g h1 h0). Qed.
Lemma lem7015217 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term768 A f s g) : term768 A f s g.
Proof. exact (h1). Qed.
Lemma lem7015218 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term767 A f s g) (h2 : term768 A f s g) : term767 A f s g.
Proof. exact (@lem7015216 A f s g h1 (@lem7015217 A f s g h2)). Qed.
Lemma lem7015219 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term768 A f s g) : term768 A f s g.
Proof. exact (fun h0 : term767 A f s g => @lem7015218 A f s g h0 h1). Qed.
Lemma lem7015220 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term770 A f s g.
Proof. exact (fun h0 : term768 A f s g => @lem7015219 A f s g h0). Qed.
Lemma lem7015223 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term768 A f s g.
Proof. exact (@lem7015220 A f s g (@lem7015212 A f s g)). Qed.
Lemma lem7015224 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term768 A f s g.
Proof. exact (@lem7015223 A f s g). Qed.
Lemma lem7015258 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7015259 : term169 = term170.
Proof. exact (@lem7015258 term171). Qed.
Lemma lem7015276 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term771 A f s g) = (term771 A f s g).
Proof. exact (eq_refl (term771 A f s g)). Qed.
Lemma lem7015277 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term772 A f s g) = (term773 A f s g).
Proof. exact (MK_COMB (@lem7015276 A f s g) (@lem7015259)). Qed.
Lemma lem7015280 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term178 A s f g) = (term178 A s f g).
Proof. exact (eq_refl (term178 A s f g)). Qed.
Lemma lem7015281 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term767 A f s g) = (term774 A f s g).
Proof. exact (MK_COMB (@lem7015280 A s f g) (@lem7015277 A f s g)). Qed.
Lemma lem7015284 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term775 A s g) = (term776 A s g).
Proof. exact (fun_ext (fun f : A -> nat => @lem7015281 A f s g)). Qed.
Lemma lem7015285 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7015286 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term777 A s g) = (term778 A s g).
Proof. exact (MK_COMB (@lem7015285 A) (@lem7015284 A s g)). Qed.
Lemma lem7015291 {A : Type'} (g : A -> nat) : (term779 A g) = (term780 A g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7015286 A s g)). Qed.
Lemma lem7015292 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7015293 {A : Type'} (g : A -> nat) : (term781 A g) = (term782 A g).
Proof. exact (MK_COMB (@lem7015292 A) (@lem7015291 A g)). Qed.
Lemma lem7015298 {A : Type'} : (term783 A) = (term784 A).
Proof. exact (fun_ext (fun g : A -> nat => @lem7015293 A g)). Qed.
Lemma lem7015299 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7015308 {A : Type'} : (term785 A) = (term786 A).
Proof. exact (MK_COMB (@lem7015299 A) (@lem7015298 A)). Qed.
Lemma lem7015317 (m : nat) (n : nat) : ((term198 m n) = (term199 m n)) = ((term198 m n) = (term199 m n)).
Proof. exact (eq_refl ((term198 m n) = (term199 m n))). Qed.
Lemma lem7015318 (m : nat) : (term200 m) = (term200 m).
Proof. exact (fun_ext (fun n : nat => @lem7015317 m n)). Qed.
Lemma lem7015319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015320 (m : nat) : (term201 m) = (term201 m).
Proof. exact (MK_COMB (@lem7015319) (@lem7015318 m)). Qed.
Lemma lem7015321 : term202 = term202.
Proof. exact (fun_ext (fun m : nat => @lem7015320 m)). Qed.
Lemma lem7015322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015323 : term203 = term203.
Proof. exact (MK_COMB (@lem7015322) (@lem7015321)). Qed.
Lemma lem7015328 (m : nat) : ((term204 m) = (m = (NUMERAL 0))) = ((term204 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl ((term204 m) = (m = (NUMERAL 0)))). Qed.
Lemma lem7015329 : term205 = term205.
Proof. exact (fun_ext (fun m : nat => @lem7015328 m)). Qed.
Lemma lem7015330 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015331 : term206 = term206.
Proof. exact (MK_COMB (@lem7015330) (@lem7015329)). Qed.
Lemma lem7015332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015333 : term207 = term207.
Proof. exact (MK_COMB (@lem7015332) (@lem7015331)). Qed.
Lemma lem7015334 : term171 = term171.
Proof. exact (MK_COMB (@lem7015333) (@lem7015323)). Qed.
Lemma lem7015335 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7015336 : term170 = term170.
Proof. exact (MK_COMB (@lem7015335) (@lem7015334)). Qed.
Lemma lem7015353 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term761 A f s g x) = (term761 A f s g x).
Proof. exact (eq_refl (term761 A f s g x)). Qed.
Lemma lem7015354 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term763 A f s g) = (term763 A f s g).
Proof. exact (fun_ext (fun x : A => @lem7015353 A f s g x)). Qed.
Lemma lem7015355 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7015356 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term764 A f s g) = (term764 A f s g).
Proof. exact (MK_COMB (@lem7015355 A) (@lem7015354 A f s g)). Qed.
Lemma lem7015357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7015358 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term766 A f s g) = (term766 A f s g).
Proof. exact (MK_COMB (@lem7015357) (@lem7015356 A f s g)). Qed.
Lemma lem7015359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7015360 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term771 A f s g) = (term771 A f s g).
Proof. exact (MK_COMB (@lem7015359) (@lem7015358 A f s g)). Qed.
Lemma lem7015361 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term773 A f s g) = (term773 A f s g).
Proof. exact (MK_COMB (@lem7015360 A f s g) (@lem7015336)). Qed.
Lemma lem7015366 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term212 A s f g x) = (term212 A s f g x).
Proof. exact (eq_refl (term212 A s f g x)). Qed.
Lemma lem7015367 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term213 A s f g) = (term213 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7015366 A s f g x)). Qed.
Lemma lem7015368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7015369 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term76 A s f g) = (term76 A s f g).
Proof. exact (MK_COMB (@lem7015368 A) (@lem7015367 A s f g)). Qed.
Lemma lem7015370 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7015371 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term178 A s f g) = (term178 A s f g).
Proof. exact (MK_COMB (@lem7015370) (@lem7015369 A s f g)). Qed.
Lemma lem7015372 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term774 A f s g) = (term774 A f s g).
Proof. exact (MK_COMB (@lem7015371 A s f g) (@lem7015361 A f s g)). Qed.
Lemma lem7015373 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term776 A s g) = (term776 A s g).
Proof. exact (fun_ext (fun f : A -> nat => @lem7015372 A f s g)). Qed.
Lemma lem7015374 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7015375 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term778 A s g) = (term778 A s g).
Proof. exact (MK_COMB (@lem7015374 A) (@lem7015373 A s g)). Qed.
Lemma lem7015376 {A : Type'} (g : A -> nat) : (term780 A g) = (term780 A g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7015375 A s g)). Qed.
Lemma lem7015377 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7015378 {A : Type'} (g : A -> nat) : (term782 A g) = (term782 A g).
Proof. exact (MK_COMB (@lem7015377 A) (@lem7015376 A g)). Qed.
Lemma lem7015379 {A : Type'} : (term784 A) = (term784 A).
Proof. exact (fun_ext (fun g : A -> nat => @lem7015378 A g)). Qed.
Lemma lem7015380 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7015381 {A : Type'} : (term786 A) = (term786 A).
Proof. exact (MK_COMB (@lem7015380 A) (@lem7015379 A)). Qed.
Lemma lem7015448 {A : Type'} : (term785 A) = (term786 A).
Proof. exact (TRANS (@lem7015308 A) (@lem7015381 A)). Qed.
Lemma lem7015449 {A : Type'} : (term786 A) = (term785 A).
Proof. exact (SYM (@lem7015448 A)). Qed.
Lemma lem7015450 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term76 A s f g.
Proof. exact (h1). Qed.
Lemma lem7015451 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term766 A f s g) : term766 A f s g.
Proof. exact (h1). Qed.
Lemma lem7015452 (h1 : term171) : term171.
Proof. exact (h1). Qed.
Lemma lem7015459 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term212 A s f g x) = (term485 A s f g x).
Proof. exact (@lem17265 (@IN A x s) (term486 A f g x)). Qed.
Lemma lem7015460 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term213 A s f g) = (term487 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7015459 A s f g x)). Qed.
Lemma lem7015461 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7015514 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term76 A s f g) = (term488 A s f g).
Proof. exact (MK_COMB (@lem7015461 A) (@lem7015460 A s f g)). Qed.
Lemma lem7015515 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term488 A s f g.
Proof. exact (EQ_MP (@lem7015514 A s f g) (@lem7015450 A s f g h1)). Qed.
Lemma lem7015524 {A : Type'} (g : A -> nat) (x : A) : (term489 A g x) = ((g x) = (NUMERAL 0)).
Proof. exact (@lem16933 ((g x) = (NUMERAL 0))). Qed.
Lemma lem7015526 {A : Type'} (x : A) (s : A -> Prop) : (term490 A x s) = (term490 A x s).
Proof. exact (eq_refl (term490 A x s)). Qed.
Lemma lem7015527 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term491 A s g x) = (term492 A s g x).
Proof. exact (MK_COMB (@lem7015526 A x s) (@lem7015524 A g x)). Qed.
Lemma lem7015528 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term148 A s g x) = (term491 A s g x).
Proof. exact (@lem17045 (@IN A x s) (term84 A g x)). Qed.
Lemma lem7015529 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term148 A s g x) = (term492 A s g x).
Proof. exact (TRANS (@lem7015528 A s g x) (@lem7015527 A s g x)). Qed.
Lemma lem7015531 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term146 A s f x) = (term146 A s f x).
Proof. exact (eq_refl (term146 A s f x)). Qed.
Lemma lem7015532 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term149 A f s g x) = (term493 A f s g x).
Proof. exact (MK_COMB (@lem7015531 A s f x) (@lem7015529 A s g x)). Qed.
Lemma lem7015533 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term787 A f s g x) = (term149 A f s g x).
Proof. exact (@lem17362 (term87 A s f x) (term87 A s g x)). Qed.
Lemma lem7015534 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term787 A f s g x) = (term493 A f s g x).
Proof. exact (TRANS (@lem7015533 A f s g x) (@lem7015532 A f s g x)). Qed.
Lemma lem7015535 {A : Type'} (P : A -> Prop) : (term499 A P) = (term500 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7015536 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term766 A f s g) = (term788 A f s g).
Proof. exact (@lem7015535 A (term763 A f s g)). Qed.
Lemma lem7015537 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term789 A f s g x) = (term761 A f s g x).
Proof. exact (eq_refl (term789 A f s g x)). Qed.
Lemma lem7015538 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7015539 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term790 A f s g x) = (term787 A f s g x).
Proof. exact (MK_COMB (@lem7015538) (@lem7015537 A f s g x)). Qed.
Lemma lem7015540 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : (term790 A f s g x) = (term493 A f s g x).
Proof. exact (TRANS (@lem7015539 A f s g x) (@lem7015534 A f s g x)). Qed.
Lemma lem7015541 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term791 A f s g) = (term792 A f s g).
Proof. exact (fun_ext (fun x : A => @lem7015540 A f s g x)). Qed.
Lemma lem7015542 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7015543 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term788 A f s g) = (term793 A f s g).
Proof. exact (MK_COMB (@lem7015542 A) (@lem7015541 A f s g)). Qed.
Lemma lem7015596 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term766 A f s g) = (term793 A f s g).
Proof. exact (TRANS (@lem7015536 A f s g) (@lem7015543 A f s g)). Qed.
Lemma lem7015597 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term766 A f s g) : term793 A f s g.
Proof. exact (EQ_MP (@lem7015596 A f s g) (@lem7015451 A f s g h1)). Qed.
Lemma lem7015612 (m : nat) : ((term204 m) = (m = (NUMERAL 0))) = (term507 m).
Proof. exact (@lem17784 (term204 m) (m = (NUMERAL 0))). Qed.
Lemma lem7015613 : term205 = term508.
Proof. exact (fun_ext (fun m : nat => @lem7015612 m)). Qed.
Lemma lem7015614 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015615 : term206 = term509.
Proof. exact (MK_COMB (@lem7015614) (@lem7015613)). Qed.
Lemma lem7015626 (m : nat) (n : nat) : (term510 m n) = (term511 m n).
Proof. exact (@lem17160 (m = (S n)) (Peano.le m n)). Qed.
Lemma lem7015632 (m : nat) (n : nat) : (term512 m n) = (term512 m n).
Proof. exact (eq_refl (term512 m n)). Qed.
Lemma lem7015634 (m : nat) (n : nat) : (term513 m n) = (term513 m n).
Proof. exact (eq_refl (term513 m n)). Qed.
Lemma lem7015635 (m : nat) (n : nat) : (term514 m n) = (term515 m n).
Proof. exact (MK_COMB (@lem7015634 m n) (@lem7015626 m n)). Qed.
Lemma lem7015636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015637 (m : nat) (n : nat) : (term516 m n) = (term517 m n).
Proof. exact (MK_COMB (@lem7015636) (@lem7015635 m n)). Qed.
Lemma lem7015638 (m : nat) (n : nat) : (term518 m n) = (term519 m n).
Proof. exact (MK_COMB (@lem7015637 m n) (@lem7015632 m n)). Qed.
Lemma lem7015639 (m : nat) (n : nat) : ((term198 m n) = (term199 m n)) = (term518 m n).
Proof. exact (@lem17784 (term198 m n) (term199 m n)). Qed.
Lemma lem7015640 (m : nat) (n : nat) : ((term198 m n) = (term199 m n)) = (term519 m n).
Proof. exact (TRANS (@lem7015639 m n) (@lem7015638 m n)). Qed.
Lemma lem7015641 (m : nat) : (term200 m) = (term520 m).
Proof. exact (fun_ext (fun n : nat => @lem7015640 m n)). Qed.
Lemma lem7015642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015643 (m : nat) : (term201 m) = (term521 m).
Proof. exact (MK_COMB (@lem7015642) (@lem7015641 m)). Qed.
Lemma lem7015644 : term202 = term522.
Proof. exact (fun_ext (fun m : nat => @lem7015643 m)). Qed.
Lemma lem7015645 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015646 : term203 = term523.
Proof. exact (MK_COMB (@lem7015645) (@lem7015644)). Qed.
Lemma lem7015647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015648 : term207 = term524.
Proof. exact (MK_COMB (@lem7015647) (@lem7015615)). Qed.
Lemma lem7015649 : term171 = term525.
Proof. exact (MK_COMB (@lem7015648) (@lem7015646)). Qed.
Lemma lem7015651 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7015652 (P : nat -> Prop) (Q : nat -> Prop) : (term526 P Q) = (term527 P Q).
Proof. exact (@lem7015651 nat P Q). Qed.
Lemma lem7015653 : term528 = term529.
Proof. exact (@lem7015652 term530 term531). Qed.
Lemma lem7015654 (m : nat) : (term532 m) = (term533 m).
Proof. exact (eq_refl (term532 m)). Qed.
Lemma lem7015655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015656 (m : nat) : (term534 m) = (term535 m).
Proof. exact (MK_COMB (@lem7015655) (@lem7015654 m)). Qed.
Lemma lem7015657 (m : nat) : (term536 m) = (term537 m).
Proof. exact (eq_refl (term536 m)). Qed.
Lemma lem7015658 (m : nat) : (term538 m) = (term507 m).
Proof. exact (MK_COMB (@lem7015656 m) (@lem7015657 m)). Qed.
Lemma lem7015659 : term539 = term508.
Proof. exact (fun_ext (fun m : nat => @lem7015658 m)). Qed.
Lemma lem7015660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015661 : term528 = term509.
Proof. exact (MK_COMB (@lem7015660) (@lem7015659)). Qed.
Lemma lem7015662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7015663 : term540 = term541.
Proof. exact (MK_COMB (@lem7015662) (@lem7015661)). Qed.
Lemma lem7015664 (m : nat) : (term532 m) = (term533 m).
Proof. exact (eq_refl (term532 m)). Qed.
Lemma lem7015665 : term542 = term530.
Proof. exact (fun_ext (fun m : nat => @lem7015664 m)). Qed.
Lemma lem7015666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015667 : term543 = term544.
Proof. exact (MK_COMB (@lem7015666) (@lem7015665)). Qed.
Lemma lem7015668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015669 : term545 = term546.
Proof. exact (MK_COMB (@lem7015668) (@lem7015667)). Qed.
Lemma lem7015670 (m : nat) : (term536 m) = (term537 m).
Proof. exact (eq_refl (term536 m)). Qed.
Lemma lem7015671 : term547 = term531.
Proof. exact (fun_ext (fun m : nat => @lem7015670 m)). Qed.
Lemma lem7015672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015673 : term548 = term549.
Proof. exact (MK_COMB (@lem7015672) (@lem7015671)). Qed.
Lemma lem7015674 : term529 = term550.
Proof. exact (MK_COMB (@lem7015669) (@lem7015673)). Qed.
Lemma lem7015675 : (term528 = term529) = (term509 = term550).
Proof. exact (MK_COMB (@lem7015663) (@lem7015674)). Qed.
Lemma lem7015676 : term509 = term550.
Proof. exact (EQ_MP (@lem7015675) (@lem7015653)). Qed.
Lemma lem7015773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015774 : term524 = term551.
Proof. exact (MK_COMB (@lem7015773) (@lem7015676)). Qed.
Lemma lem7015780 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7015781 (P : nat -> Prop) (Q : nat -> Prop) : (term526 P Q) = (term527 P Q).
Proof. exact (@lem7015780 nat P Q). Qed.
Lemma lem7015782 (m : nat) : (term552 m) = (term553 m).
Proof. exact (@lem7015781 (term554 m) (term555 m)). Qed.
Lemma lem7015783 (m : nat) (n : nat) : (term556 m n) = (term515 m n).
Proof. exact (eq_refl (term556 m n)). Qed.
Lemma lem7015784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015785 (m : nat) (n : nat) : (term557 m n) = (term517 m n).
Proof. exact (MK_COMB (@lem7015784) (@lem7015783 m n)). Qed.
Lemma lem7015786 (m : nat) (n : nat) : (term558 m n) = (term512 m n).
Proof. exact (eq_refl (term558 m n)). Qed.
Lemma lem7015787 (m : nat) (n : nat) : (term559 m n) = (term519 m n).
Proof. exact (MK_COMB (@lem7015785 m n) (@lem7015786 m n)). Qed.
Lemma lem7015788 (m : nat) : (term560 m) = (term520 m).
Proof. exact (fun_ext (fun n : nat => @lem7015787 m n)). Qed.
Lemma lem7015789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015790 (m : nat) : (term552 m) = (term521 m).
Proof. exact (MK_COMB (@lem7015789) (@lem7015788 m)). Qed.
Lemma lem7015791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7015792 (m : nat) : (term561 m) = (term562 m).
Proof. exact (MK_COMB (@lem7015791) (@lem7015790 m)). Qed.
Lemma lem7015793 (m : nat) (n : nat) : (term556 m n) = (term515 m n).
Proof. exact (eq_refl (term556 m n)). Qed.
Lemma lem7015794 (m : nat) : (term563 m) = (term554 m).
Proof. exact (fun_ext (fun n : nat => @lem7015793 m n)). Qed.
Lemma lem7015795 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015796 (m : nat) : (term564 m) = (term565 m).
Proof. exact (MK_COMB (@lem7015795) (@lem7015794 m)). Qed.
Lemma lem7015797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015798 (m : nat) : (term566 m) = (term567 m).
Proof. exact (MK_COMB (@lem7015797) (@lem7015796 m)). Qed.
Lemma lem7015799 (m : nat) (n : nat) : (term558 m n) = (term512 m n).
Proof. exact (eq_refl (term558 m n)). Qed.
Lemma lem7015800 (m : nat) : (term568 m) = (term555 m).
Proof. exact (fun_ext (fun n : nat => @lem7015799 m n)). Qed.
Lemma lem7015801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015802 (m : nat) : (term569 m) = (term570 m).
Proof. exact (MK_COMB (@lem7015801) (@lem7015800 m)). Qed.
Lemma lem7015803 (m : nat) : (term553 m) = (term571 m).
Proof. exact (MK_COMB (@lem7015798 m) (@lem7015802 m)). Qed.
Lemma lem7015804 (m : nat) : ((term552 m) = (term553 m)) = ((term521 m) = (term571 m)).
Proof. exact (MK_COMB (@lem7015792 m) (@lem7015803 m)). Qed.
Lemma lem7015805 (m : nat) : (term521 m) = (term571 m).
Proof. exact (EQ_MP (@lem7015804 m) (@lem7015782 m)). Qed.
Lemma lem7015902 : term522 = term572.
Proof. exact (fun_ext (fun m : nat => @lem7015805 m)). Qed.
Lemma lem7015903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015904 : term523 = term573.
Proof. exact (MK_COMB (@lem7015903) (@lem7015902)). Qed.
Lemma lem7015906 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term307 A P Q) = (term308 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7015907 (P : nat -> Prop) (Q : nat -> Prop) : (term526 P Q) = (term527 P Q).
Proof. exact (@lem7015906 nat P Q). Qed.
Lemma lem7015908 : term574 = term575.
Proof. exact (@lem7015907 term576 term577). Qed.
Lemma lem7015909 (m : nat) : (term578 m) = (term565 m).
Proof. exact (eq_refl (term578 m)). Qed.
Lemma lem7015910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015911 (m : nat) : (term579 m) = (term567 m).
Proof. exact (MK_COMB (@lem7015910) (@lem7015909 m)). Qed.
Lemma lem7015912 (m : nat) : (term580 m) = (term570 m).
Proof. exact (eq_refl (term580 m)). Qed.
Lemma lem7015913 (m : nat) : (term581 m) = (term571 m).
Proof. exact (MK_COMB (@lem7015911 m) (@lem7015912 m)). Qed.
Lemma lem7015914 : term582 = term572.
Proof. exact (fun_ext (fun m : nat => @lem7015913 m)). Qed.
Lemma lem7015915 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015916 : term574 = term573.
Proof. exact (MK_COMB (@lem7015915) (@lem7015914)). Qed.
Lemma lem7015917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7015918 : term583 = term584.
Proof. exact (MK_COMB (@lem7015917) (@lem7015916)). Qed.
Lemma lem7015919 (m : nat) : (term578 m) = (term565 m).
Proof. exact (eq_refl (term578 m)). Qed.
Lemma lem7015920 : term585 = term576.
Proof. exact (fun_ext (fun m : nat => @lem7015919 m)). Qed.
Lemma lem7015921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015922 : term586 = term587.
Proof. exact (MK_COMB (@lem7015921) (@lem7015920)). Qed.
Lemma lem7015923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7015924 : term588 = term589.
Proof. exact (MK_COMB (@lem7015923) (@lem7015922)). Qed.
Lemma lem7015925 (m : nat) : (term580 m) = (term570 m).
Proof. exact (eq_refl (term580 m)). Qed.
Lemma lem7015926 : term590 = term577.
Proof. exact (fun_ext (fun m : nat => @lem7015925 m)). Qed.
Lemma lem7015927 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7015928 : term591 = term592.
Proof. exact (MK_COMB (@lem7015927) (@lem7015926)). Qed.
Lemma lem7015929 : term575 = term593.
Proof. exact (MK_COMB (@lem7015924) (@lem7015928)). Qed.
Lemma lem7015930 : (term574 = term575) = (term573 = term593).
Proof. exact (MK_COMB (@lem7015918) (@lem7015929)). Qed.
Lemma lem7015931 : term573 = term593.
Proof. exact (EQ_MP (@lem7015930) (@lem7015908)). Qed.
Lemma lem7016036 : term523 = term593.
Proof. exact (TRANS (@lem7015904) (@lem7015931)). Qed.
Lemma lem7016039 : term525 = term594.
Proof. exact (MK_COMB (@lem7015774) (@lem7016036)). Qed.
Lemma lem7016040 : term171 = term594.
Proof. exact (TRANS (@lem7015649) (@lem7016039)). Qed.
Lemma lem7016041 (h1 : term171) : term594.
Proof. exact (EQ_MP (@lem7016040) (@lem7015452 h1)). Qed.
Lemma lem7016061 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term485 A s f g x) = (term485 A s f g x).
Proof. exact (eq_refl (term485 A s f g x)). Qed.
Lemma lem7016062 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term487 A s f g) = (term487 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7016061 A s f g x)). Qed.
Lemma lem7016063 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7016064 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term488 A s f g) = (term488 A s f g).
Proof. exact (MK_COMB (@lem7016063 A) (@lem7016062 A s f g)). Qed.
Lemma lem7016065 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term488 A s f g.
Proof. exact (EQ_MP (@lem7016064 A s f g) (@lem7015515 A s f g h1)). Qed.
Lemma lem7016092 (m : nat) (n : nat) : (term512 m n) = (term512 m n).
Proof. exact (eq_refl (term512 m n)). Qed.
Lemma lem7016093 (m : nat) : (term555 m) = (term555 m).
Proof. exact (fun_ext (fun n : nat => @lem7016092 m n)). Qed.
Lemma lem7016094 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7016095 (m : nat) : (term570 m) = (term570 m).
Proof. exact (MK_COMB (@lem7016094) (@lem7016093 m)). Qed.
Lemma lem7016096 : term577 = term577.
Proof. exact (fun_ext (fun m : nat => @lem7016095 m)). Qed.
Lemma lem7016097 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7016098 : term592 = term592.
Proof. exact (MK_COMB (@lem7016097) (@lem7016096)). Qed.
Lemma lem7016127 (m : nat) (n : nat) : (term515 m n) = (term515 m n).
Proof. exact (eq_refl (term515 m n)). Qed.
Lemma lem7016128 (m : nat) : (term554 m) = (term554 m).
Proof. exact (fun_ext (fun n : nat => @lem7016127 m n)). Qed.
Lemma lem7016129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7016130 (m : nat) : (term565 m) = (term565 m).
Proof. exact (MK_COMB (@lem7016129) (@lem7016128 m)). Qed.
Lemma lem7016131 : term576 = term576.
Proof. exact (fun_ext (fun m : nat => @lem7016130 m)). Qed.
Lemma lem7016132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7016133 : term587 = term587.
Proof. exact (MK_COMB (@lem7016132) (@lem7016131)). Qed.
Lemma lem7016134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7016135 : term589 = term589.
Proof. exact (MK_COMB (@lem7016134) (@lem7016133)). Qed.
Lemma lem7016136 : term593 = term593.
Proof. exact (MK_COMB (@lem7016135) (@lem7016098)). Qed.
Lemma lem7016155 (m : nat) : (term537 m) = (term537 m).
Proof. exact (eq_refl (term537 m)). Qed.
Lemma lem7016156 : term531 = term531.
Proof. exact (fun_ext (fun m : nat => @lem7016155 m)). Qed.
Lemma lem7016157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7016158 : term549 = term549.
Proof. exact (MK_COMB (@lem7016157) (@lem7016156)). Qed.
Lemma lem7016177 (m : nat) : (term533 m) = (term533 m).
Proof. exact (eq_refl (term533 m)). Qed.
Lemma lem7016178 : term530 = term530.
Proof. exact (fun_ext (fun m : nat => @lem7016177 m)). Qed.
Lemma lem7016179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7016180 : term544 = term544.
Proof. exact (MK_COMB (@lem7016179) (@lem7016178)). Qed.
Lemma lem7016181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7016182 : term546 = term546.
Proof. exact (MK_COMB (@lem7016181) (@lem7016180)). Qed.
Lemma lem7016183 : term550 = term550.
Proof. exact (MK_COMB (@lem7016182) (@lem7016158)). Qed.
Lemma lem7016184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7016185 : term551 = term551.
Proof. exact (MK_COMB (@lem7016184) (@lem7016183)). Qed.
Lemma lem7016186 : term594 = term594.
Proof. exact (MK_COMB (@lem7016185) (@lem7016136)). Qed.
Lemma lem7016187 (h1 : term171) : term594.
Proof. exact (EQ_MP (@lem7016186) (@lem7016041 h1)). Qed.
Lemma lem7016229 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : term493 A f s g x.
Proof. exact (h1). Qed.
Lemma lem7016230 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : term492 A s g x.
Proof. exact (proj2 (@lem7016229 A f s g x h1)). Qed.
Lemma lem7016231 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : term87 A s f x.
Proof. exact (proj1 (@lem7016229 A f s g x h1)). Qed.
Lemma lem7016235 (h1 : term171) : term550.
Proof. exact (proj1 (@lem7016187 h1)). Qed.
Lemma lem7016238 (h1 : term171) : term549.
Proof. exact (proj2 (@lem7016235 h1)). Qed.
Lemma lem7016340 {A : Type'} (x : A) (s : A -> Prop) (h1 : term602 A x s) : term602 A x s.
Proof. exact (h1). Qed.
Lemma lem7016348 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term485 A s f g x) = (term485 A s f g x).
Proof. exact (eq_refl (term485 A s f g x)). Qed.
Lemma lem7016349 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term487 A s f g) = (term487 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7016348 A s f g x)). Qed.
Lemma lem7016350 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7016352 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) : (term488 A s f g) = (term488 A s f g).
Proof. exact (MK_COMB (@lem7016350 A) (@lem7016349 A s f g)). Qed.
Lemma lem7016353 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term488 A s f g.
Proof. exact (EQ_MP (@lem7016352 A s f g) (@lem7016065 A s f g h1)). Qed.
Lemma lem7016430 (m : nat) : (term537 m) = (term537 m).
Proof. exact (eq_refl (term537 m)). Qed.
Lemma lem7016431 : term531 = term531.
Proof. exact (fun_ext (fun m : nat => @lem7016430 m)). Qed.
Lemma lem7016432 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7016434 : term549 = term549.
Proof. exact (MK_COMB (@lem7016432) (@lem7016431)). Qed.
Lemma lem7016435 (h1 : term171) : term549.
Proof. exact (EQ_MP (@lem7016434) (@lem7016238 h1)). Qed.
Lemma lem7016439 {A : Type'} (g : A -> nat) (x : A) (h1 : (g x) = (NUMERAL 0)) : (g x) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7016461 {A : Type'} (_93738 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term794 A s f g _93738.
Proof. exact (@lem7016353 A s f g h1 _93738). Qed.
Lemma lem7016462 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93738 : A) : (term794 A s f g _93738) = (term485 A s f g _93738).
Proof. exact (eq_refl (term794 A s f g _93738)). Qed.
Lemma lem7016479 (_93744 : nat) (h1 : term171) : term536 _93744.
Proof. exact (@lem7016435 h1 _93744). Qed.
Lemma lem7016480 (_93744 : nat) : (term536 _93744) = (term537 _93744).
Proof. exact (eq_refl (term536 _93744)). Qed.
Lemma lem7016519 {A : Type'} (x : A) (s : A -> Prop) (h1 : term602 A x s) : term602 A x s.
Proof. exact (h1). Qed.
Lemma lem7016537 {A : Type'} (_93738 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term485 A s f g _93738.
Proof. exact (EQ_MP (@lem7016462 A s f g _93738) (@lem7016461 A _93738 s f g h1)). Qed.
Lemma lem7016541 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : term84 A f x.
Proof. exact (proj2 (@lem7016231 A f s g x h1)). Qed.
Lemma lem7016563 (_93744 : nat) (h1 : term171) : term537 _93744.
Proof. exact (EQ_MP (@lem7016480 _93744) (@lem7016479 _93744 h1)). Qed.
Lemma lem7016565 {A : Type'} (g : A -> nat) (x : A) (h1 : (g x) = (NUMERAL 0)) : (g x) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7016655 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : @IN A x s.
Proof. exact (proj1 (@lem7016231 A f s g x h1)). Qed.
Lemma lem7016656 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : term795 A x s.
Proof. exact (fun h0 : term602 A x s => @lem7016655 A f s g x h1). Qed.
Lemma lem7016658 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7016659 {A : Type'} (x : A) (s : A -> Prop) : (term795 A x s) = (@IN A x s).
Proof. exact (@lem7016658 (@IN A x s)). Qed.
Lemma lem7016660 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : @IN A x s.
Proof. exact (EQ_MP (@lem7016659 A x s) (@lem7016656 A f s g x h1)). Qed.
Lemma lem7016663 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7016665 {A : Type'} (x : A) (s : A -> Prop) : (term602 A x s) = (term796 A x s).
Proof. exact (@lem7016663 (@IN A x s)). Qed.
Lemma lem7016668 {A : Type'} (x : A) (s : A -> Prop) (h1 : term602 A x s) : term796 A x s.
Proof. exact (EQ_MP (@lem7016665 A x s) (@lem7016519 A x s h1)). Qed.
Lemma lem7016671 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : False.
Proof. exact (@lem7016668 A x s h1 (@lem7016660 A f s g x h2)). Qed.
Lemma lem7016672 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : term674.
Proof. exact (fun h0 : ~ False => @lem7016671 A f s g x h1 h2). Qed.
Lemma lem7016674 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7016675 : term674 = False.
Proof. exact (@lem7016674 False). Qed.
Lemma lem7016676 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : False.
Proof. exact (EQ_MP (@lem7016675) (@lem7016672 A f s g x h1 h2)). Qed.
Lemma lem7016696 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7016697 (_93765 : nat) (_93767 : nat) (h1 : _93765 = _93767) : _93765 = _93767.
Proof. exact (h1). Qed.
Lemma lem7016698 (_93766 : nat) (_93768 : nat) (h1 : _93766 = _93768) : _93766 = _93768.
Proof. exact (h1). Qed.
Lemma lem7016699 (_93765 : nat) (_93767 : nat) (h1 : _93765 = _93767) : (Peano.le _93765) = (Peano.le _93767).
Proof. exact (MK_COMB (@lem7016696) (@lem7016697 _93765 _93767 h1)). Qed.
Lemma lem7016700 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) (h1 : _93765 = _93767) (h2 : _93766 = _93768) : (Peano.le _93765 _93766) = (Peano.le _93767 _93768).
Proof. exact (MK_COMB (@lem7016699 _93765 _93767 h1) (@lem7016698 _93766 _93768 h2)). Qed.
Lemma lem7016702 (b : Prop) (a : Prop) : term675 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7016703 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : term797 _93767 _93768 _93765 _93766.
Proof. exact (@lem7016702 (Peano.le _93767 _93768) (Peano.le _93765 _93766)). Qed.
Lemma lem7016704 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) (h1 : _93765 = _93767) (h2 : _93766 = _93768) : term798 _93767 _93768 _93765 _93766.
Proof. exact (@lem7016703 _93767 _93768 _93765 _93766 (@lem7016700 _93765 _93767 _93766 _93768 h1 h2)). Qed.
Lemma lem7016705 (_93768 : nat) (_93766 : nat) (_93765 : nat) (_93767 : nat) (h1 : _93765 = _93767) : term799 _93767 _93768 _93765 _93766.
Proof. exact (fun h0 : _93766 = _93768 => @lem7016704 _93765 _93767 _93766 _93768 h1 h0). Qed.
Lemma lem7016707 (a : Prop) (b : Prop) : (a -> b) = (term679 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7016708 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term799 _93767 _93768 _93765 _93766) = (term800 _93767 _93768 _93765 _93766).
Proof. exact (@lem7016707 (_93766 = _93768) (term798 _93767 _93768 _93765 _93766)). Qed.
Lemma lem7016709 (_93768 : nat) (_93766 : nat) (_93765 : nat) (_93767 : nat) (h1 : _93765 = _93767) : term800 _93767 _93768 _93765 _93766.
Proof. exact (EQ_MP (@lem7016708 _93767 _93768 _93765 _93766) (@lem7016705 _93768 _93766 _93765 _93767 h1)). Qed.
Lemma lem7016710 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : term801 _93767 _93768 _93765 _93766.
Proof. exact (fun h0 : _93765 = _93767 => @lem7016709 _93768 _93766 _93765 _93767 h0). Qed.
Lemma lem7016712 (a : Prop) (b : Prop) : (a -> b) = (term679 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7016713 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term801 _93767 _93768 _93765 _93766) = (term802 _93767 _93768 _93765 _93766).
Proof. exact (@lem7016712 (_93765 = _93767) (term800 _93767 _93768 _93765 _93766)). Qed.
Lemma lem7016714 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : term802 _93767 _93768 _93765 _93766.
Proof. exact (EQ_MP (@lem7016713 _93767 _93768 _93765 _93766) (@lem7016710 _93767 _93768 _93765 _93766)). Qed.
Lemma lem7016754 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem7016755 {A : Type'} (f : A -> nat) (x : A) : (f x) = (f x).
Proof. exact (@lem7016754 (f x)). Qed.
Lemma lem7016756 {A : Type'} (f : A -> nat) (x : A) : term803 A f x.
Proof. exact (fun h0 : term804 A f x => @lem7016755 A f x). Qed.
Lemma lem7016758 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7016759 {A : Type'} (f : A -> nat) (x : A) : (term803 A f x) = ((f x) = (f x)).
Proof. exact (@lem7016758 ((f x) = (f x))). Qed.
Lemma lem7016760 {A : Type'} (f : A -> nat) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem7016759 A f x) (@lem7016756 A f x)). Qed.
Lemma lem7016762 {A : Type'} (g : A -> nat) (x : A) (h1 : (g x) = (NUMERAL 0)) : (g x) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7016763 {A : Type'} (g : A -> nat) (x : A) (h1 : (g x) = (NUMERAL 0)) : term805 A g x.
Proof. exact (fun h0 : term84 A g x => @lem7016762 A g x h1). Qed.
Lemma lem7016765 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7016766 {A : Type'} (g : A -> nat) (x : A) : (term805 A g x) = ((g x) = (NUMERAL 0)).
Proof. exact (@lem7016765 ((g x) = (NUMERAL 0))). Qed.
Lemma lem7016767 {A : Type'} (g : A -> nat) (x : A) (h1 : (g x) = (NUMERAL 0)) : (g x) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7016766 A g x) (@lem7016763 A g x h1)). Qed.
Lemma lem7016769 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : @IN A x s.
Proof. exact (proj1 (@lem7016231 A f s g x h1)). Qed.
Lemma lem7016770 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : term795 A x s.
Proof. exact (fun h0 : term602 A x s => @lem7016769 A f s g x h1). Qed.
Lemma lem7016772 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7016773 {A : Type'} (x : A) (s : A -> Prop) : (term795 A x s) = (@IN A x s).
Proof. exact (@lem7016772 (@IN A x s)). Qed.
Lemma lem7016774 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : @IN A x s.
Proof. exact (EQ_MP (@lem7016773 A x s) (@lem7016770 A f s g x h1)). Qed.
Lemma lem7016780 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7016781 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) (s : A -> Prop) : (term485 A s f g _93738) = (term806 A f g _93738 s).
Proof. exact (@lem7016780 (term486 A f g _93738) (term602 A _93738 s)). Qed.
Lemma lem7016787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7016788 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) (s : A -> Prop) : (term807 A s f g _93738) = (term808 A f g _93738 s).
Proof. exact (MK_COMB (@lem7016787) (@lem7016781 A f g _93738 s)). Qed.
Lemma lem7016794 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) (s : A -> Prop) : (term806 A f g _93738 s) = (term806 A f g _93738 s).
Proof. exact (eq_refl (term806 A f g _93738 s)). Qed.
Lemma lem7016795 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) (s : A -> Prop) : ((term485 A s f g _93738) = (term806 A f g _93738 s)) = ((term806 A f g _93738 s) = (term806 A f g _93738 s)).
Proof. exact (MK_COMB (@lem7016788 A f g _93738 s) (@lem7016794 A f g _93738 s)). Qed.
Lemma lem7016797 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7016798 (x : Prop) : (x = x) = True.
Proof. exact (@lem7016797 Prop x). Qed.
Lemma lem7016799 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) (s : A -> Prop) : ((term806 A f g _93738 s) = (term806 A f g _93738 s)) = True.
Proof. exact (@lem7016798 (term806 A f g _93738 s)). Qed.
Lemma lem7016800 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) (s : A -> Prop) : ((term485 A s f g _93738) = (term806 A f g _93738 s)) = True.
Proof. exact (TRANS (@lem7016795 A f g _93738 s) (@lem7016799 A f g _93738 s)). Qed.
Lemma lem7016801 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) (s : A -> Prop) : True = ((term485 A s f g _93738) = (term806 A f g _93738 s)).
Proof. exact (SYM (@lem7016800 A f g _93738 s)). Qed.
Lemma lem7016802 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) (s : A -> Prop) : (term485 A s f g _93738) = (term806 A f g _93738 s).
Proof. exact (EQ_MP (@lem7016801 A f g _93738 s) (@lem0)). Qed.
Lemma lem7016803 {A : Type'} (_93738 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term806 A f g _93738 s.
Proof. exact (EQ_MP (@lem7016802 A f g _93738 s) (@lem7016537 A _93738 s f g h1)). Qed.
Lemma lem7016805 (b : Prop) (a : Prop) : (a \/ b) = (term689 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7016806 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93738 : A) : (term806 A f g _93738 s) = (term809 A s f g _93738).
Proof. exact (@lem7016805 (term602 A _93738 s) (term486 A f g _93738)). Qed.
Lemma lem7016808 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7016809 {A : Type'} (_93738 : A) (s : A -> Prop) : (term810 A _93738 s) = (@IN A _93738 s).
Proof. exact (@lem7016808 (@IN A _93738 s)). Qed.
Lemma lem7016810 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7016811 {A : Type'} (_93738 : A) (s : A -> Prop) : (term811 A _93738 s) = (term812 A _93738 s).
Proof. exact (MK_COMB (@lem7016810) (@lem7016809 A _93738 s)). Qed.
Lemma lem7016812 {A : Type'} (f : A -> nat) (g : A -> nat) (_93738 : A) : (term486 A f g _93738) = (term486 A f g _93738).
Proof. exact (eq_refl (term486 A f g _93738)). Qed.
Lemma lem7016813 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93738 : A) : (term809 A s f g _93738) = (term212 A s f g _93738).
Proof. exact (MK_COMB (@lem7016811 A _93738 s) (@lem7016812 A f g _93738)). Qed.
Lemma lem7016814 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (_93738 : A) : (term806 A f g _93738 s) = (term212 A s f g _93738).
Proof. exact (TRANS (@lem7016806 A s f g _93738) (@lem7016813 A s f g _93738)). Qed.
Lemma lem7016817 {A : Type'} (_93738 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term212 A s f g _93738.
Proof. exact (EQ_MP (@lem7016814 A s f g _93738) (@lem7016803 A _93738 s f g h1)). Qed.
Lemma lem7016818 {A : Type'} (_93738 : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term212 A s f g _93738.
Proof. exact (@lem7016817 A _93738 s f g h1). Qed.
Lemma lem7016819 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term212 A s f g x.
Proof. exact (@lem7016818 A x s f g h1). Qed.
Lemma lem7016822 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term493 A f s g x) : term486 A f g x.
Proof. exact (@lem7016819 A x s f g h1 (@lem7016774 A f s g x h2)). Qed.
Lemma lem7016823 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term493 A f s g x) : term813 A f g x.
Proof. exact (fun h0 : term814 A f g x => @lem7016822 A f s g x h1 h2). Qed.
Lemma lem7016825 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7016826 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term813 A f g x) = (term486 A f g x).
Proof. exact (@lem7016825 (term486 A f g x)). Qed.
Lemma lem7016827 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term493 A f s g x) : term486 A f g x.
Proof. exact (EQ_MP (@lem7016826 A f g x) (@lem7016823 A f s g x h1 h2)). Qed.
Lemma lem7016845 (q : Prop) (p : Prop) (r : Prop) : (term698 p q r) = (term698 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7016846 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term800 _93767 _93768 _93765 _93766) = (term815 _93767 _93768 _93765 _93766).
Proof. exact (@lem7016845 (Peano.le _93767 _93768) (term700 _93766 _93768) (term624 _93765 _93766)). Qed.
Lemma lem7016860 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7016861 (_93765 : nat) (_93766 : nat) (_93768 : nat) : (term816 _93768 _93765 _93766) = (term817 _93765 _93766 _93768).
Proof. exact (@lem7016860 (term624 _93765 _93766) (term700 _93766 _93768)). Qed.
Lemma lem7016869 (_93767 : nat) (_93768 : nat) : (term818 _93767 _93768) = (term818 _93767 _93768).
Proof. exact (eq_refl (term818 _93767 _93768)). Qed.
Lemma lem7016870 (_93767 : nat) (_93765 : nat) (_93766 : nat) (_93768 : nat) : (term815 _93767 _93768 _93765 _93766) = (term819 _93767 _93765 _93766 _93768).
Proof. exact (MK_COMB (@lem7016869 _93767 _93768) (@lem7016861 _93765 _93766 _93768)). Qed.
Lemma lem7016881 (_93767 : nat) (_93765 : nat) (_93766 : nat) (_93768 : nat) : (term800 _93767 _93768 _93765 _93766) = (term819 _93767 _93765 _93766 _93768).
Proof. exact (TRANS (@lem7016846 _93767 _93768 _93765 _93766) (@lem7016870 _93767 _93765 _93766 _93768)). Qed.
Lemma lem7016882 (_93765 : nat) (_93767 : nat) : (term820 _93765 _93767) = (term820 _93765 _93767).
Proof. exact (eq_refl (term820 _93765 _93767)). Qed.
Lemma lem7016883 (_93767 : nat) (_93765 : nat) (_93766 : nat) (_93768 : nat) : (term802 _93767 _93768 _93765 _93766) = (term821 _93767 _93765 _93766 _93768).
Proof. exact (MK_COMB (@lem7016882 _93765 _93767) (@lem7016881 _93767 _93765 _93766 _93768)). Qed.
Lemma lem7016887 (q : Prop) (p : Prop) (r : Prop) : (term698 p q r) = (term698 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7016888 (_93767 : nat) (_93765 : nat) (_93766 : nat) (_93768 : nat) : (term821 _93767 _93765 _93766 _93768) = (term822 _93767 _93765 _93766 _93768).
Proof. exact (@lem7016887 (Peano.le _93767 _93768) (term700 _93765 _93767) (term817 _93765 _93766 _93768)). Qed.
Lemma lem7016902 (q : Prop) (p : Prop) (r : Prop) : (term698 p q r) = (term698 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7016903 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : (term823 _93767 _93765 _93766 _93768) = (term824 _93765 _93767 _93766 _93768).
Proof. exact (@lem7016902 (term624 _93765 _93766) (term700 _93765 _93767) (term700 _93766 _93768)). Qed.
Lemma lem7016923 (_93767 : nat) (_93768 : nat) : (term818 _93767 _93768) = (term818 _93767 _93768).
Proof. exact (eq_refl (term818 _93767 _93768)). Qed.
Lemma lem7016924 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : (term822 _93767 _93765 _93766 _93768) = (term825 _93765 _93767 _93766 _93768).
Proof. exact (MK_COMB (@lem7016923 _93767 _93768) (@lem7016903 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7016935 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : (term821 _93767 _93765 _93766 _93768) = (term825 _93765 _93767 _93766 _93768).
Proof. exact (TRANS (@lem7016888 _93767 _93765 _93766 _93768) (@lem7016924 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7016936 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : (term802 _93767 _93768 _93765 _93766) = (term825 _93765 _93767 _93766 _93768).
Proof. exact (TRANS (@lem7016883 _93767 _93765 _93766 _93768) (@lem7016935 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7016937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7016938 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : (term826 _93767 _93768 _93765 _93766) = (term827 _93765 _93767 _93766 _93768).
Proof. exact (MK_COMB (@lem7016937) (@lem7016936 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7016964 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7016965 (_93765 : nat) (_93766 : nat) (_93768 : nat) : (term816 _93768 _93765 _93766) = (term817 _93765 _93766 _93768).
Proof. exact (@lem7016964 (term624 _93765 _93766) (term700 _93766 _93768)). Qed.
Lemma lem7016973 (_93765 : nat) (_93767 : nat) : (term820 _93765 _93767) = (term820 _93765 _93767).
Proof. exact (eq_refl (term820 _93765 _93767)). Qed.
Lemma lem7016974 (_93767 : nat) (_93765 : nat) (_93766 : nat) (_93768 : nat) : (term828 _93767 _93768 _93765 _93766) = (term823 _93767 _93765 _93766 _93768).
Proof. exact (MK_COMB (@lem7016973 _93765 _93767) (@lem7016965 _93765 _93766 _93768)). Qed.
Lemma lem7016978 (q : Prop) (p : Prop) (r : Prop) : (term698 p q r) = (term698 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7016979 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : (term823 _93767 _93765 _93766 _93768) = (term824 _93765 _93767 _93766 _93768).
Proof. exact (@lem7016978 (term624 _93765 _93766) (term700 _93765 _93767) (term700 _93766 _93768)). Qed.
Lemma lem7016999 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : (term828 _93767 _93768 _93765 _93766) = (term824 _93765 _93767 _93766 _93768).
Proof. exact (TRANS (@lem7016974 _93767 _93765 _93766 _93768) (@lem7016979 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7017000 (_93767 : nat) (_93768 : nat) : (term818 _93767 _93768) = (term818 _93767 _93768).
Proof. exact (eq_refl (term818 _93767 _93768)). Qed.
Lemma lem7017001 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : (term829 _93767 _93768 _93765 _93766) = (term825 _93765 _93767 _93766 _93768).
Proof. exact (MK_COMB (@lem7017000 _93767 _93768) (@lem7016999 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7017012 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : ((term802 _93767 _93768 _93765 _93766) = (term829 _93767 _93768 _93765 _93766)) = ((term825 _93765 _93767 _93766 _93768) = (term825 _93765 _93767 _93766 _93768)).
Proof. exact (MK_COMB (@lem7016938 _93765 _93767 _93766 _93768) (@lem7017001 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7017014 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7017015 (x : Prop) : (x = x) = True.
Proof. exact (@lem7017014 Prop x). Qed.
Lemma lem7017016 (_93765 : nat) (_93767 : nat) (_93766 : nat) (_93768 : nat) : ((term825 _93765 _93767 _93766 _93768) = (term825 _93765 _93767 _93766 _93768)) = True.
Proof. exact (@lem7017015 (term825 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7017017 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : ((term802 _93767 _93768 _93765 _93766) = (term829 _93767 _93768 _93765 _93766)) = True.
Proof. exact (TRANS (@lem7017012 _93765 _93767 _93766 _93768) (@lem7017016 _93765 _93767 _93766 _93768)). Qed.
Lemma lem7017018 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : True = ((term802 _93767 _93768 _93765 _93766) = (term829 _93767 _93768 _93765 _93766)).
Proof. exact (SYM (@lem7017017 _93767 _93768 _93765 _93766)). Qed.
Lemma lem7017019 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term802 _93767 _93768 _93765 _93766) = (term829 _93767 _93768 _93765 _93766).
Proof. exact (EQ_MP (@lem7017018 _93767 _93768 _93765 _93766) (@lem0)). Qed.
Lemma lem7017020 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : term829 _93767 _93768 _93765 _93766.
Proof. exact (EQ_MP (@lem7017019 _93767 _93768 _93765 _93766) (@lem7016714 _93767 _93768 _93765 _93766)). Qed.
Lemma lem7017022 (b : Prop) (a : Prop) : (a \/ b) = (term689 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7017023 (_93765 : nat) (_93766 : nat) (_93767 : nat) (_93768 : nat) : (term829 _93767 _93768 _93765 _93766) = (term830 _93765 _93766 _93767 _93768).
Proof. exact (@lem7017022 (term828 _93767 _93768 _93765 _93766) (Peano.le _93767 _93768)). Qed.
Lemma lem7017025 (a : Prop) (b : Prop) : (term711 a b) = (term712 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7017026 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term831 _93767 _93768 _93765 _93766) = (term832 _93767 _93768 _93765 _93766).
Proof. exact (@lem7017025 (term700 _93765 _93767) (term816 _93768 _93765 _93766)). Qed.
Lemma lem7017028 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7017029 (_93765 : nat) (_93767 : nat) : (term720 _93765 _93767) = (_93765 = _93767).
Proof. exact (@lem7017028 (_93765 = _93767)). Qed.
Lemma lem7017030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7017031 (_93765 : nat) (_93767 : nat) : (term721 _93765 _93767) = (term722 _93765 _93767).
Proof. exact (MK_COMB (@lem7017030) (@lem7017029 _93765 _93767)). Qed.
Lemma lem7017033 (a : Prop) (b : Prop) : (term711 a b) = (term712 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7017034 (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term833 _93768 _93765 _93766) = (term834 _93768 _93765 _93766).
Proof. exact (@lem7017033 (term700 _93766 _93768) (term624 _93765 _93766)). Qed.
Lemma lem7017036 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7017037 (_93766 : nat) (_93768 : nat) : (term720 _93766 _93768) = (_93766 = _93768).
Proof. exact (@lem7017036 (_93766 = _93768)). Qed.
Lemma lem7017038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7017039 (_93766 : nat) (_93768 : nat) : (term721 _93766 _93768) = (term722 _93766 _93768).
Proof. exact (MK_COMB (@lem7017038) (@lem7017037 _93766 _93768)). Qed.
Lemma lem7017041 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7017042 (_93765 : nat) (_93766 : nat) : (term835 _93765 _93766) = (Peano.le _93765 _93766).
Proof. exact (@lem7017041 (Peano.le _93765 _93766)). Qed.
Lemma lem7017043 (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term834 _93768 _93765 _93766) = (term836 _93768 _93765 _93766).
Proof. exact (MK_COMB (@lem7017039 _93766 _93768) (@lem7017042 _93765 _93766)). Qed.
Lemma lem7017044 (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term833 _93768 _93765 _93766) = (term836 _93768 _93765 _93766).
Proof. exact (TRANS (@lem7017034 _93768 _93765 _93766) (@lem7017043 _93768 _93765 _93766)). Qed.
Lemma lem7017045 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term832 _93767 _93768 _93765 _93766) = (term837 _93767 _93768 _93765 _93766).
Proof. exact (MK_COMB (@lem7017031 _93765 _93767) (@lem7017044 _93768 _93765 _93766)). Qed.
Lemma lem7017046 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term831 _93767 _93768 _93765 _93766) = (term837 _93767 _93768 _93765 _93766).
Proof. exact (TRANS (@lem7017026 _93767 _93768 _93765 _93766) (@lem7017045 _93767 _93768 _93765 _93766)). Qed.
Lemma lem7017047 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7017048 (_93767 : nat) (_93768 : nat) (_93765 : nat) (_93766 : nat) : (term838 _93767 _93768 _93765 _93766) = (term839 _93767 _93768 _93765 _93766).
Proof. exact (MK_COMB (@lem7017047) (@lem7017046 _93767 _93768 _93765 _93766)). Qed.
Lemma lem7017049 (_93767 : nat) (_93768 : nat) : (Peano.le _93767 _93768) = (Peano.le _93767 _93768).
Proof. exact (eq_refl (Peano.le _93767 _93768)). Qed.
Lemma lem7017050 (_93765 : nat) (_93766 : nat) (_93767 : nat) (_93768 : nat) : (term830 _93765 _93766 _93767 _93768) = (term840 _93765 _93766 _93767 _93768).
Proof. exact (MK_COMB (@lem7017048 _93767 _93768 _93765 _93766) (@lem7017049 _93767 _93768)). Qed.
Lemma lem7017051 (_93765 : nat) (_93766 : nat) (_93767 : nat) (_93768 : nat) : (term829 _93767 _93768 _93765 _93766) = (term840 _93765 _93766 _93767 _93768).
Proof. exact (TRANS (@lem7017023 _93765 _93766 _93767 _93768) (@lem7017050 _93765 _93766 _93767 _93768)). Qed.
Lemma lem7017053 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term493 A f s g x) (h3 : (g x) = (NUMERAL 0)) : term841 A f g x.
Proof. exact (conj (@lem7016767 A g x h3) (@lem7016827 A f s g x h1 h2)). Qed.
Lemma lem7017054 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term493 A f s g x) (h3 : (g x) = (NUMERAL 0)) : term842 A f g x.
Proof. exact (conj (@lem7016760 A f x) (@lem7017053 A f s g x h1 h2 h3)). Qed.
Lemma lem7017056 (_93765 : nat) (_93766 : nat) (_93767 : nat) (_93768 : nat) : term840 _93765 _93766 _93767 _93768.
Proof. exact (EQ_MP (@lem7017051 _93765 _93766 _93767 _93768) (@lem7017020 _93767 _93768 _93765 _93766)). Qed.
Lemma lem7017057 {A : Type'} (g : A -> nat) (f : A -> nat) (x : A) : term843 A g f x.
Proof. exact (@lem7017056 (f x) (g x) (f x) (NUMERAL 0)). Qed.
Lemma lem7017060 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term493 A f s g x) (h3 : (g x) = (NUMERAL 0)) : term844 A f x.
Proof. exact (@lem7017057 A g f x (@lem7017054 A f s g x h1 h2 h3)). Qed.
Lemma lem7017061 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term493 A f s g x) (h3 : (g x) = (NUMERAL 0)) : term845 A f x.
Proof. exact (fun h0 : term846 A f x => @lem7017060 A f s g x h1 h2 h3). Qed.
Lemma lem7017063 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7017064 {A : Type'} (f : A -> nat) (x : A) : (term845 A f x) = (term844 A f x).
Proof. exact (@lem7017063 (term844 A f x)). Qed.
Lemma lem7017065 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term493 A f s g x) (h3 : (g x) = (NUMERAL 0)) : term844 A f x.
Proof. exact (EQ_MP (@lem7017064 A f x) (@lem7017061 A f s g x h1 h2 h3)). Qed.
Lemma lem7017071 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7017072 (_93744 : nat) : (term537 _93744) = (term847 _93744).
Proof. exact (@lem7017071 (_93744 = (NUMERAL 0)) (term642 _93744)). Qed.
Lemma lem7017080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7017081 (_93744 : nat) : (term848 _93744) = (term849 _93744).
Proof. exact (MK_COMB (@lem7017080) (@lem7017072 _93744)). Qed.
Lemma lem7017089 (_93744 : nat) : (term847 _93744) = (term847 _93744).
Proof. exact (eq_refl (term847 _93744)). Qed.
Lemma lem7017090 (_93744 : nat) : ((term537 _93744) = (term847 _93744)) = ((term847 _93744) = (term847 _93744)).
Proof. exact (MK_COMB (@lem7017081 _93744) (@lem7017089 _93744)). Qed.
Lemma lem7017092 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7017093 (x : Prop) : (x = x) = True.
Proof. exact (@lem7017092 Prop x). Qed.
Lemma lem7017094 (_93744 : nat) : ((term847 _93744) = (term847 _93744)) = True.
Proof. exact (@lem7017093 (term847 _93744)). Qed.
Lemma lem7017095 (_93744 : nat) : ((term537 _93744) = (term847 _93744)) = True.
Proof. exact (TRANS (@lem7017090 _93744) (@lem7017094 _93744)). Qed.
Lemma lem7017096 (_93744 : nat) : True = ((term537 _93744) = (term847 _93744)).
Proof. exact (SYM (@lem7017095 _93744)). Qed.
Lemma lem7017097 (_93744 : nat) : (term537 _93744) = (term847 _93744).
Proof. exact (EQ_MP (@lem7017096 _93744) (@lem0)). Qed.
Lemma lem7017098 (_93744 : nat) (h1 : term171) : term847 _93744.
Proof. exact (EQ_MP (@lem7017097 _93744) (@lem7016563 _93744 h1)). Qed.
Lemma lem7017100 (b : Prop) (a : Prop) : (a \/ b) = (term689 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7017101 (_93744 : nat) : (term847 _93744) = (term850 _93744).
Proof. exact (@lem7017100 (term642 _93744) (_93744 = (NUMERAL 0))). Qed.
Lemma lem7017103 (a : Prop) : (term691 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7017104 (_93744 : nat) : (term851 _93744) = (term204 _93744).
Proof. exact (@lem7017103 (term204 _93744)). Qed.
Lemma lem7017105 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7017106 (_93744 : nat) : (term852 _93744) = (term853 _93744).
Proof. exact (MK_COMB (@lem7017105) (@lem7017104 _93744)). Qed.
Lemma lem7017107 (_93744 : nat) : (_93744 = (NUMERAL 0)) = (_93744 = (NUMERAL 0)).
Proof. exact (eq_refl (_93744 = (NUMERAL 0))). Qed.
Lemma lem7017108 (_93744 : nat) : (term850 _93744) = (term854 _93744).
Proof. exact (MK_COMB (@lem7017106 _93744) (@lem7017107 _93744)). Qed.
Lemma lem7017109 (_93744 : nat) : (term847 _93744) = (term854 _93744).
Proof. exact (TRANS (@lem7017101 _93744) (@lem7017108 _93744)). Qed.
Lemma lem7017112 (_93744 : nat) (h1 : term171) : term854 _93744.
Proof. exact (EQ_MP (@lem7017109 _93744) (@lem7017098 _93744 h1)). Qed.
Lemma lem7017113 {A : Type'} (f : A -> nat) (x : A) (h1 : term171) : term855 A f x.
Proof. exact (@lem7017112 (f x) h1). Qed.
Lemma lem7017116 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : (f x) = (NUMERAL 0).
Proof. exact (@lem7017113 A f x h2 (@lem7017065 A f s g x h1 h3 h4)). Qed.
Lemma lem7017117 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : term805 A f x.
Proof. exact (fun h0 : term84 A f x => @lem7017116 A f s g x h1 h2 h3 h4). Qed.
Lemma lem7017119 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7017120 {A : Type'} (f : A -> nat) (x : A) : (term805 A f x) = ((f x) = (NUMERAL 0)).
Proof. exact (@lem7017119 ((f x) = (NUMERAL 0))). Qed.
Lemma lem7017121 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : (f x) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7017120 A f x) (@lem7017117 A f s g x h1 h2 h3 h4)). Qed.
Lemma lem7017124 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7017126 {A : Type'} (f : A -> nat) (x : A) : (term84 A f x) = (term856 A f x).
Proof. exact (@lem7017124 ((f x) = (NUMERAL 0))). Qed.
Lemma lem7017129 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term493 A f s g x) : term856 A f x.
Proof. exact (EQ_MP (@lem7017126 A f x) (@lem7016541 A f s g x h1)). Qed.
Lemma lem7017132 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : False.
Proof. exact (@lem7017129 A f s g x h3 (@lem7017121 A f s g x h1 h2 h3 h4)). Qed.
Lemma lem7017133 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : term674.
Proof. exact (fun h0 : ~ False => @lem7017132 A f s g x h1 h2 h3 h4). Qed.
Lemma lem7017135 (p : Prop) : (term672 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7017136 : term674 = False.
Proof. exact (@lem7017135 False). Qed.
Lemma lem7017137 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem7017136) (@lem7017133 A f s g x h1 h2 h3 h4)). Qed.
Lemma lem7017138 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : ((g x) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : (g x) = (NUMERAL 0) => @lem7017137 A f s g x h1 h2 h3 h4) (fun h5 : False => @lem7016565 A g x h4)). Qed.
Lemma lem7017139 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem7017138 A f s g x h1 h2 h3 h4) (@lem7016565 A g x h4)). Qed.
Lemma lem7017140 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : (term602 A x s) = False.
Proof. exact (prop_ext (fun h3 : term602 A x s => @lem7016676 A f s g x h1 h2) (fun h3 : False => @lem7016519 A x s h1)). Qed.
Lemma lem7017141 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : False.
Proof. exact (EQ_MP (@lem7017140 A f s g x h1 h2) (@lem7016519 A x s h1)). Qed.
Lemma lem7017142 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : ((g x) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : (g x) = (NUMERAL 0) => @lem7017139 A f s g x h1 h2 h3 h4) (fun h5 : False => @lem7016439 A g x h4)). Qed.
Lemma lem7017143 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem7017142 A f s g x h1 h2 h3 h4) (@lem7016439 A g x h4)). Qed.
Lemma lem7017144 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : (term602 A x s) = False.
Proof. exact (prop_ext (fun h3 : term602 A x s => @lem7017141 A f s g x h1 h2) (fun h3 : False => @lem7016340 A x s h1)). Qed.
Lemma lem7017145 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : False.
Proof. exact (EQ_MP (@lem7017144 A f s g x h1 h2) (@lem7016340 A x s h1)). Qed.
Lemma lem7017146 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : ((g x) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h5 : (g x) = (NUMERAL 0) => @lem7017143 A f s g x h1 h2 h3 h4) (fun h5 : False => @lem7016439 A g x h4)). Qed.
Lemma lem7017147 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) (h4 : (g x) = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem7017146 A f s g x h1 h2 h3 h4) (@lem7016439 A g x h4)). Qed.
Lemma lem7017148 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : (term602 A x s) = False.
Proof. exact (prop_ext (fun h3 : term602 A x s => @lem7017145 A f s g x h1 h2) (fun h3 : False => @lem7016340 A x s h1)). Qed.
Lemma lem7017149 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term602 A x s) (h2 : term493 A f s g x) : False.
Proof. exact (EQ_MP (@lem7017148 A f s g x h1 h2) (@lem7016340 A x s h1)). Qed.
Lemma lem7017150 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) : False.
Proof. exact (or_elim (@lem7016230 A f s g x h3) (fun h0 : term602 A x s => @lem7017149 A f s g x h0 h3) (fun h0 : (g x) = (NUMERAL 0) => @lem7017147 A f s g x h1 h2 h3 h0)). Qed.
Lemma lem7017151 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) : (term493 A f s g x) = False.
Proof. exact (prop_ext (fun h4 : term493 A f s g x => @lem7017150 A f s g x h1 h2 h3) (fun h4 : False => @lem7016229 A f s g x h3)). Qed.
Lemma lem7017152 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term171) (h3 : term493 A f s g x) : False.
Proof. exact (EQ_MP (@lem7017151 A f s g x h1 h2 h3) (@lem7016229 A f s g x h3)). Qed.
Lemma lem7017153 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term766 A f s g) (h3 : term171) : False.
Proof. exact (ex_elim (@lem7015597 A f s g h2) (fun x : A => fun h0 : term792 A f s g x => @lem7017152 A f s g x h1 h3 h0)). Qed.
Lemma lem7017154 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term766 A f s g) : term169.
Proof. exact (fun h0 : term171 => @lem7017153 A f s g h1 h2 h0). Qed.
Lemma lem7017155 : term169 = term170.
Proof. exact (@lem69 term171). Qed.
Lemma lem7017156 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term766 A f s g) : term170.
Proof. exact (EQ_MP (@lem7017155) (@lem7017154 A f s g h1 h2)). Qed.
Lemma lem7017157 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term773 A f s g.
Proof. exact (fun h0 : term766 A f s g => @lem7017156 A f s g h1 h0). Qed.
Lemma lem7017158 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term774 A f s g.
Proof. exact (fun h0 : term76 A s f g => @lem7017157 A s f g h0). Qed.
Lemma lem7017163 {A : Type'} (s : A -> Prop) (g : A -> nat) : term778 A s g.
Proof. exact (fun f : A -> nat => @lem7017158 A f s g). Qed.
Lemma lem7017168 {A : Type'} (g : A -> nat) : term782 A g.
Proof. exact (fun s : A -> Prop => @lem7017163 A s g). Qed.
Lemma lem7017173 {A : Type'} : term786 A.
Proof. exact (fun g : A -> nat => @lem7017168 A g). Qed.
Lemma lem7017174 {A : Type'} : term785 A.
Proof. exact (EQ_MP (@lem7015449 A) (@lem7017173 A)). Qed.
Lemma lem7017175 {A : Type'} (g : A -> nat) : term857 A g.
Proof. exact (@lem7017174 A g). Qed.
Lemma lem7017176 {A : Type'} (g : A -> nat) : (term857 A g) = (term781 A g).
Proof. exact (eq_refl (term857 A g)). Qed.
Lemma lem7017177 {A : Type'} (g : A -> nat) : term781 A g.
Proof. exact (EQ_MP (@lem7017176 A g) (@lem7017175 A g)). Qed.
Lemma lem7017178 {A : Type'} (g : A -> nat) (s : A -> Prop) : term858 A g s.
Proof. exact (@lem7017177 A g s). Qed.
Lemma lem7017179 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term858 A g s) = (term777 A s g).
Proof. exact (eq_refl (term858 A g s)). Qed.
Lemma lem7017180 {A : Type'} (s : A -> Prop) (g : A -> nat) : term777 A s g.
Proof. exact (EQ_MP (@lem7017179 A s g) (@lem7017178 A g s)). Qed.
Lemma lem7017181 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : A -> nat) : term859 A s g f.
Proof. exact (@lem7017180 A s g f). Qed.
Lemma lem7017182 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term859 A s g f) = (term767 A f s g).
Proof. exact (eq_refl (term859 A s g f)). Qed.
Lemma lem7017183 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term767 A f s g.
Proof. exact (EQ_MP (@lem7017182 A f s g) (@lem7017181 A s g f)). Qed.
Lemma lem7017185 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term767 A f s g.
Proof. exact (@lem7015224 A f s g (@lem7017183 A f s g)). Qed.
Lemma lem7017186 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term772 A f s g.
Proof. exact (@lem7017185 A f s g (@lem7010602 A s f g h1)). Qed.
Lemma lem7017187 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term766 A f s g) : term169.
Proof. exact (@lem7017186 A s f g h1 (@lem7015208 A f s g h2)). Qed.
Lemma lem7017188 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term766 A f s g) : False.
Proof. exact (@lem7017187 A f s g h1 h2 (@lem89501)). Qed.
Lemma lem7017189 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term766 A f s g) : (term766 A f s g) = False.
Proof. exact (prop_ext (fun h3 : term766 A f s g => @lem7017188 A f s g h1 h2) (fun h3 : False => @lem7015208 A f s g h2)). Qed.
Lemma lem7017190 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term766 A f s g) : False.
Proof. exact (EQ_MP (@lem7017189 A f s g h1 h2) (@lem7015208 A f s g h2)). Qed.
Lemma lem7017191 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term765 A f s g.
Proof. exact (fun h0 : term766 A f s g => @lem7017190 A f s g h1 h0). Qed.
Lemma lem7017192 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term764 A f s g.
Proof. exact (EQ_MP (@lem7015207 A f s g) (@lem7017191 A s f g h1)). Qed.
Lemma lem7017193 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term756 A f s g.
Proof. exact (EQ_MP (@lem7015203 A f s g) (@lem7017192 A s f g h1)). Qed.
Lemma lem7017194 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term75 A s f.
Proof. exact (@lem7015127 A f s g h2 (@lem7017193 A s f g h1)). Qed.
Lemma lem7017195 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term161 A s g f.
Proof. exact (conj (@lem7017194 A f s g h1 h2) (@lem7015102 A f s g h1 h2)). Qed.
Lemma lem7017196 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term160 A s g f.
Proof. exact (EQ_MP (@lem7010924 A f s g h2) (@lem7017195 A f s g h1 h2)). Qed.
Lemma lem7017197 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term860 A s g f.
Proof. exact (@lem7010738 A s g f (@lem7017196 A f s g h1 h2)). Qed.
Lemma lem7017199 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term6 _127006 f s g.
Proof. exact (EQ_MP (@lem7010428 _127006 f s g) (@lem7010427 _127006 f s g)). Qed.
Lemma lem7017200 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term6 A f s g.
Proof. exact (@lem7017199 A f s g). Qed.
Lemma lem7017201 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term861 A f s g.
Proof. exact (@lem7017200 A f (term98 A s g) g). Qed.
Lemma lem7017204 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term862 A f s g) = (term862 A f s g).
Proof. exact (eq_refl (term862 A f s g)). Qed.
Lemma lem7017205 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term862 A f s g) = (term861 A f s g).
Proof. exact (eq_refl (term862 A f s g)). Qed.
Lemma lem7017206 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term863 A f s g) = (term863 A f s g).
Proof. exact (eq_refl (term863 A f s g)). Qed.
Lemma lem7017207 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((term862 A f s g) = (term862 A f s g)) = ((term862 A f s g) = (term861 A f s g)).
Proof. exact (MK_COMB (@lem7017206 A f s g) (@lem7017205 A f s g)). Qed.
Lemma lem7017208 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term862 A f s g) = (term861 A f s g).
Proof. exact (eq_refl (term862 A f s g)). Qed.
Lemma lem7017209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7017210 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term863 A f s g) = (term864 A f s g).
Proof. exact (MK_COMB (@lem7017209) (@lem7017208 A f s g)). Qed.
Lemma lem7017211 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term861 A f s g) = (term861 A f s g).
Proof. exact (eq_refl (term861 A f s g)). Qed.
Lemma lem7017212 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((term862 A f s g) = (term861 A f s g)) = ((term861 A f s g) = (term861 A f s g)).
Proof. exact (MK_COMB (@lem7017210 A f s g) (@lem7017211 A f s g)). Qed.
Lemma lem7017213 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : ((term862 A f s g) = (term862 A f s g)) = ((term861 A f s g) = (term861 A f s g)).
Proof. exact (TRANS (@lem7017207 A f s g) (@lem7017212 A f s g)). Qed.
Lemma lem7017214 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term861 A f s g) = (term861 A f s g).
Proof. exact (EQ_MP (@lem7017213 A f s g) (@lem7017204 A f s g)). Qed.
Lemma lem7017215 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term861 A f s g.
Proof. exact (EQ_MP (@lem7017214 A f s g) (@lem7017201 A f s g)). Qed.
Lemma lem7017240 {_83095 : Type'} : term17 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem7017241 {_83095 : Type'} (p : _83095 -> Prop) : term18 _83095 p.
Proof. exact (@lem7017240 _83095 p). Qed.
Lemma lem7017242 {_83095 : Type'} (p : _83095 -> Prop) : (term18 _83095 p) = (term19 _83095 p).
Proof. exact (eq_refl (term18 _83095 p)). Qed.
Lemma lem7017243 {_83095 : Type'} (p : _83095 -> Prop) : term19 _83095 p.
Proof. exact (EQ_MP (@lem7017242 _83095 p) (@lem7017241 _83095 p)). Qed.
Lemma lem7017244 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term20 _83095 p x.
Proof. exact (@lem7017243 _83095 p x). Qed.
Lemma lem7017245 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 p x) = ((term21 _83095 x p) = (p x)).
Proof. exact (eq_refl (term20 _83095 p x)). Qed.
Lemma lem7017254 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term865 A s f g x.
Proof. exact (@lem7010602 A s f g h1 x). Qed.
Lemma lem7017255 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term865 A s f g x) = (term212 A s f g x).
Proof. exact (eq_refl (term865 A s f g x)). Qed.
Lemma lem7017256 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term212 A s f g x.
Proof. exact (EQ_MP (@lem7017255 A s f g x) (@lem7017254 A x s f g h1)). Qed.
Lemma lem7017257 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7017258 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) (s : A -> Prop) (h1 : term76 A s f g) (h2 : @IN A x s) : term486 A f g x.
Proof. exact (@lem7017256 A x s f g h1 (@lem7017257 A x s h2)). Qed.
Lemma lem7017259 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term486 A f g x) = ((term486 A f g x) = True).
Proof. exact (@lem7 (term486 A f g x)). Qed.
Lemma lem7017260 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) (s : A -> Prop) (h1 : term76 A s f g) (h2 : @IN A x s) : (term486 A f g x) = True.
Proof. exact (EQ_MP (@lem7017259 A f g x) (@lem7017258 A f g x s h1 h2)). Qed.
Lemma lem7017266 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term75 A s g) = ((term75 A s g) = True).
Proof. exact (@lem7 (term75 A s g)). Qed.
Lemma lem7017271 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term75 A s g) = True.
Proof. exact (EQ_MP (@lem7017266 A s g) (@lem7010601 A s g h1)). Qed.
Lemma lem7017272 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term75 A s g) = True.
Proof. exact (@lem7017271 A s g h1). Qed.
Lemma lem7017273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7017274 {A : Type'} (s : A -> Prop) (g : A -> nat) (h1 : term75 A s g) : (term130 A s g) = (and True).
Proof. exact (MK_COMB (@lem7017273) (@lem7017272 A s g h1)). Qed.
Lemma lem7017282 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term866 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7017283 (p : Prop) (q : Prop) (p' : Prop) : term867 p q p'.
Proof. exact (fun q' : Prop => @lem7017282 p q p' q'). Qed.
Lemma lem7017284 (p : Prop) (q : Prop) : term868 p q.
Proof. exact (fun p' : Prop => @lem7017283 p q p'). Qed.
Lemma lem7017285 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : term869 A s f g x.
Proof. exact (@lem7017284 (term142 A x s g) (term486 A f g x)). Qed.
Lemma lem7017286 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) : term870 A s f g x p'.
Proof. exact (@lem7017285 A s f g x p'). Qed.
Lemma lem7017287 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) : (term870 A s f g x p') = (term871 A s f g x p').
Proof. exact (eq_refl (term870 A s f g x p')). Qed.
Lemma lem7017288 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) : term871 A s f g x p'.
Proof. exact (EQ_MP (@lem7017287 A s f g x p') (@lem7017286 A s f g x p')). Qed.
Lemma lem7017289 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term872 A s f g x p' q'.
Proof. exact (@lem7017288 A s f g x p' q'). Qed.
Lemma lem7017290 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term872 A s f g x p' q') = (term873 A s f g x p' q').
Proof. exact (eq_refl (term872 A s f g x p' q')). Qed.
Lemma lem7017291 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term873 A s f g x p' q'.
Proof. exact (EQ_MP (@lem7017290 A s f g x p' q') (@lem7017289 A s f g x p' q')). Qed.
Lemma lem7017293 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7017245 _83095 p x) (@lem7017244 _83095 p x)). Qed.
Lemma lem7017294 {A : Type'} (p : A -> Prop) (x : A) : (term21 A x p) = (p x).
Proof. exact (@lem7017293 A p x). Qed.
Lemma lem7017295 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term133 A x s g) = (term134 A s g x).
Proof. exact (@lem7017294 A (term135 A s g) x). Qed.
Lemma lem7017296 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term134 A s g x) = (term87 A s g x).
Proof. exact (eq_refl (term134 A s g x)). Qed.
Lemma lem7017297 {A : Type'} (GEN_PVAR_298 : A) : (@SETSPEC A GEN_PVAR_298) = (@SETSPEC A GEN_PVAR_298).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_298)). Qed.
Lemma lem7017298 {A : Type'} (GEN_PVAR_298 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term136 A GEN_PVAR_298 s g x) = (term89 A GEN_PVAR_298 s g x).
Proof. exact (MK_COMB (@lem7017297 A GEN_PVAR_298) (@lem7017296 A s g x)). Qed.
Lemma lem7017299 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7017300 {A : Type'} (GEN_PVAR_298 : A) (s : A -> Prop) (g : A -> nat) (x : A) : (term137 A GEN_PVAR_298 s g x) = (term91 A GEN_PVAR_298 s g x).
Proof. exact (MK_COMB (@lem7017298 A GEN_PVAR_298 s g x) (@lem7017299 A x)). Qed.
Lemma lem7017301 {A : Type'} (GEN_PVAR_298 : A) (s : A -> Prop) (g : A -> nat) : (term138 A GEN_PVAR_298 s g) = (term93 A GEN_PVAR_298 s g).
Proof. exact (fun_ext (fun x : A => @lem7017300 A GEN_PVAR_298 s g x)). Qed.
Lemma lem7017302 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7017303 {A : Type'} (GEN_PVAR_298 : A) (s : A -> Prop) (g : A -> nat) : (term139 A GEN_PVAR_298 s g) = (term95 A GEN_PVAR_298 s g).
Proof. exact (MK_COMB (@lem7017302 A) (@lem7017301 A GEN_PVAR_298 s g)). Qed.
Lemma lem7017304 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term140 A s g) = (term97 A s g).
Proof. exact (fun_ext (fun GEN_PVAR_298 : A => @lem7017303 A GEN_PVAR_298 s g)). Qed.
Lemma lem7017305 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7017306 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term141 A s g) = (term98 A s g).
Proof. exact (MK_COMB (@lem7017305 A) (@lem7017304 A s g)). Qed.
Lemma lem7017307 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7017308 {A : Type'} (x : A) (s : A -> Prop) (g : A -> nat) : (term133 A x s g) = (term142 A x s g).
Proof. exact (MK_COMB (@lem7017307 A x) (@lem7017306 A s g)). Qed.
Lemma lem7017309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7017310 {A : Type'} (x : A) (s : A -> Prop) (g : A -> nat) : (term143 A x s g) = (term144 A x s g).
Proof. exact (MK_COMB (@lem7017309) (@lem7017308 A x s g)). Qed.
Lemma lem7017311 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term134 A s g x) = (term87 A s g x).
Proof. exact (eq_refl (term134 A s g x)). Qed.
Lemma lem7017312 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : ((term133 A x s g) = (term134 A s g x)) = ((term142 A x s g) = (term87 A s g x)).
Proof. exact (MK_COMB (@lem7017310 A x s g) (@lem7017311 A s g x)). Qed.
Lemma lem7017313 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term142 A x s g) = (term87 A s g x).
Proof. exact (EQ_MP (@lem7017312 A s g x) (@lem7017295 A s g x)). Qed.
Lemma lem7017318 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (q' : Prop) : term874 A f s g x q'.
Proof. exact (@lem7017291 A s f g x (term87 A s g x) q'). Qed.
Lemma lem7017319 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (q' : Prop) : term875 A f s g x q'.
Proof. exact (@lem7017318 A f s g x q' (@lem7017313 A s g x)). Qed.
Lemma lem7017320 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term87 A s g x) : term87 A s g x.
Proof. exact (h1). Qed.
Lemma lem7017335 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term87 A s g x) : @IN A x s.
Proof. exact (proj1 (@lem7017320 A s g x h1)). Qed.
Lemma lem7017336 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7017339 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term876 A s f g x.
Proof. exact (fun h0 : @IN A x s => @lem7017260 A f g x s h1 h0). Qed.
Lemma lem7017340 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term876 A s f g x.
Proof. exact (@lem7017339 A x s f g h1). Qed.
Lemma lem7017342 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term87 A s g x) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7017336 A x s) (@lem7017335 A s g x h1)). Qed.
Lemma lem7017343 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term87 A s g x) : True = (@IN A x s).
Proof. exact (SYM (@lem7017342 A s g x h1)). Qed.
Lemma lem7017344 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term87 A s g x) : @IN A x s.
Proof. exact (EQ_MP (@lem7017343 A s g x h1) (@lem0)). Qed.
Lemma lem7017345 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) (h1 : term76 A s f g) (h2 : term87 A s g x) : (term486 A f g x) = True.
Proof. exact (@lem7017340 A x s f g h1 (@lem7017344 A s g x h2)). Qed.
Lemma lem7017346 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : term877 A s f g x.
Proof. exact (fun h0 : term87 A s g x => @lem7017345 A f s g x h1 h0). Qed.
Lemma lem7017347 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (x : A) : term878 A f s g x.
Proof. exact (@lem7017319 A f s g x True). Qed.
Lemma lem7017348 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : (term879 A s f g x) = (term880 A s g x).
Proof. exact (@lem7017347 A f s g x (@lem7017346 A x s f g h1)). Qed.
Lemma lem7017350 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7017351 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term880 A s g x) = True.
Proof. exact (@lem7017350 (term87 A s g x)). Qed.
Lemma lem7017352 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : (term879 A s f g x) = True.
Proof. exact (TRANS (@lem7017348 A x s f g h1) (@lem7017351 A s g x)). Qed.
Lemma lem7017353 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : (term881 A s f g) = (term882 A).
Proof. exact (fun_ext (fun x : A => @lem7017352 A x s f g h1)). Qed.
Lemma lem7017354 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7017355 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : (term883 A s f g) = (term884 A).
Proof. exact (MK_COMB (@lem7017354 A) (@lem7017353 A s f g h1)). Qed.
Lemma lem7017357 {A : Type'} (t : Prop) : (term885 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7017358 {A : Type'} (t : Prop) : (term885 A t) = t.
Proof. exact (@lem7017357 A t). Qed.
Lemma lem7017359 {A : Type'} : (term884 A) = True.
Proof. exact (@lem7017358 A True). Qed.
Lemma lem7017360 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term76 A s f g) : (term883 A s f g) = True.
Proof. exact (TRANS (@lem7017355 A s f g h1) (@lem7017359 A)). Qed.
Lemma lem7017361 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : (term886 A s f g) = (True /\ True).
Proof. exact (MK_COMB (@lem7017274 A s g h2) (@lem7017360 A s f g h1)). Qed.
Lemma lem7017363 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7017364 : (True /\ True) = True.
Proof. exact (@lem7017363 True). Qed.
Lemma lem7017365 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : (term886 A s f g) = True.
Proof. exact (TRANS (@lem7017361 A f s g h1 h2) (@lem7017364)). Qed.
Lemma lem7017366 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : True = (term886 A s f g).
Proof. exact (SYM (@lem7017365 A f s g h1 h2)). Qed.
Lemma lem7017367 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term886 A s f g.
Proof. exact (EQ_MP (@lem7017366 A f s g h1 h2) (@lem0)). Qed.
Lemma lem7017368 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term887 A f s g.
Proof. exact (@lem7017215 A f s g (@lem7017367 A f s g h1 h2)). Qed.
Lemma lem7017369 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term888 A f s g.
Proof. exact (conj (@lem7017197 A f s g h1 h2) (@lem7017368 A f s g h1 h2)). Qed.
Lemma lem7017370 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term889 A f s g.
Proof. exact (ex_intro (term890 A f s g) (term891 A s g f) (@lem7017369 A f s g h1 h2)). Qed.
Lemma lem7017371 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term103 A f s g.
Proof. exact (@lem7010734 A f s g (@lem7017370 A f s g h1 h2)). Qed.
Lemma lem7017372 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term79 A f s g.
Proof. exact (EQ_MP (@lem7010703 A f s g) (@lem7017371 A f s g h1 h2)). Qed.
Lemma lem7017373 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term8 A f s g.
Proof. exact (EQ_MP (@lem7010613 A f s g) (@lem7017372 A f s g h1 h2)). Qed.
Lemma lem7017374 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term74 A f s g) : term75 A s g.
Proof. exact (proj2 (@lem7010600 A f s g h1)). Qed.
Lemma lem7017375 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term74 A f s g) : term76 A s f g.
Proof. exact (proj1 (@lem7010600 A f s g h1)). Qed.
Lemma lem7017376 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : (term75 A s g) = (term8 A f s g).
Proof. exact (prop_ext (fun h3 : term75 A s g => @lem7017373 A f s g h1 h2) (fun h3 : term8 A f s g => @lem7010601 A s g h2)). Qed.
Lemma lem7017377 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term8 A f s g.
Proof. exact (EQ_MP (@lem7017376 A f s g h1 h2) (@lem7010601 A s g h2)). Qed.
Lemma lem7017378 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : (term76 A s f g) = (term8 A f s g).
Proof. exact (prop_ext (fun h3 : term76 A s f g => @lem7017377 A f s g h1 h2) (fun h3 : term8 A f s g => @lem7010602 A s f g h1)). Qed.
Lemma lem7017379 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term75 A s g) : term8 A f s g.
Proof. exact (EQ_MP (@lem7017378 A f s g h1 h2) (@lem7010602 A s f g h1)). Qed.
Lemma lem7017380 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term74 A f s g) : (term75 A s g) = (term8 A f s g).
Proof. exact (prop_ext (fun h3 : term75 A s g => @lem7017379 A f s g h1 h3) (fun h3 : term8 A f s g => @lem7017374 A f s g h2)). Qed.
Lemma lem7017381 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term76 A s f g) (h2 : term74 A f s g) : term8 A f s g.
Proof. exact (EQ_MP (@lem7017380 A f s g h1 h2) (@lem7017374 A f s g h2)). Qed.
Lemma lem7017382 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term74 A f s g) : (term76 A s f g) = (term8 A f s g).
Proof. exact (prop_ext (fun h2 : term76 A s f g => @lem7017381 A f s g h2 h1) (fun h2 : term8 A f s g => @lem7017375 A f s g h1)). Qed.
Lemma lem7017383 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term74 A f s g) : term8 A f s g.
Proof. exact (EQ_MP (@lem7017382 A f s g h1) (@lem7017375 A f s g h1)). Qed.
Lemma lem7017384 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term892 A f s g.
Proof. exact (fun h0 : term74 A f s g => @lem7017383 A f s g h0). Qed.
Lemma lem7017389 {A : Type'} (f : A -> nat) (g : A -> nat) : term893 A f g.
Proof. exact (fun s : A -> Prop => @lem7017384 A f s g). Qed.
Lemma lem7017394 {A : Type'} (f : A -> nat) : term894 A f.
Proof. exact (fun g : A -> nat => @lem7017389 A f g). Qed.
Lemma lem7017399 {A : Type'} : term895 A.
Proof. exact (fun f : A -> nat => @lem7017394 A f). Qed.
