Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SUPERSET_term_abbrevs.
Require Import ITERATE_SUPERSET_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NEUTRAL_REAL_ADD_spec.
Require Import NOT_CLAUSES_WEAK_spec.
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
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Require Import thm82_spec.
Lemma lem7124522 (h1 : (@neutral real real_add) = term0) : (@neutral real real_add) = term0.
Proof. exact (h1). Qed.
Lemma lem7124523 (h1 : (@neutral real real_add) = term0) : term0 = (@neutral real real_add).
Proof. exact (SYM (@lem7124522 h1)). Qed.
Lemma lem7124524 (h1 : term0 = (@neutral real real_add)) : term0 = (@neutral real real_add).
Proof. exact (h1). Qed.
Lemma lem7124525 (h1 : term0 = (@neutral real real_add)) : (@neutral real real_add) = term0.
Proof. exact (SYM (@lem7124524 h1)). Qed.
Lemma lem7124526 : ((@neutral real real_add) = term0) = (term0 = (@neutral real real_add)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_add) = term0 => @lem7124523 h1) (fun h1 : term0 = (@neutral real real_add) => @lem7124525 h1)). Qed.
Lemma lem7124528 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7124530 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem6016892 A B op). Qed.
Lemma lem7124531 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7124532 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7124531 A B op) (@lem7124530 A B op)). Qed.
Lemma lem7124533 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7124534 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7124532 A B op (@lem7124533 B op h1)). Qed.
Lemma lem7124535 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term4 A B op f.
Proof. exact (@lem7124534 A B op h1 f). Qed.
Lemma lem7124536 {A B : Type'} (op : type1400 B) (f : A -> B) : (term4 A B op f) = (term5 A B op f).
Proof. exact (eq_refl (term4 A B op f)). Qed.
Lemma lem7124537 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term5 A B op f.
Proof. exact (EQ_MP (@lem7124536 A B op f) (@lem7124535 A B f op h1)). Qed.
Lemma lem7124538 {A B : Type'} (f : A -> B) (u : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term6 A B op f u.
Proof. exact (@lem7124537 A B f op h1 u). Qed.
Lemma lem7124539 {A B : Type'} (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term6 A B op f u) = (term7 A B op u f).
Proof. exact (eq_refl (term6 A B op f u)). Qed.
Lemma lem7124540 {A B : Type'} (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term7 A B op u f.
Proof. exact (EQ_MP (@lem7124539 A B op u f) (@lem7124538 A B f u op h1)). Qed.
Lemma lem7124541 {A B : Type'} (u : A -> Prop) (f : A -> B) (v : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term8 A B op u f v.
Proof. exact (@lem7124540 A B u f op h1 v). Qed.
Lemma lem7124542 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term8 A B op u f v) = (term9 A B v op u f).
Proof. exact (eq_refl (term8 A B op u f v)). Qed.
Lemma lem7124543 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term9 A B v op u f.
Proof. exact (EQ_MP (@lem7124542 A B v op u f) (@lem7124541 A B u f v op h1)). Qed.
Lemma lem7124544 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term10 A B v u f op) : term10 A B v u f op.
Proof. exact (h1). Qed.
Lemma lem7124545 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) (h2 : term10 A B v u f op) : (@iterate B A op v f) = (@iterate B A op u f).
Proof. exact (@lem7124543 A B v u f op h1 (@lem7124544 A B v u f op h2)). Qed.
Lemma lem7124546 {A B : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term9 A B v op u f.
Proof. exact (fun h0 : term10 A B v u f op => @lem7124545 A B v u f op h1 h0). Qed.
Lemma lem7124547 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : term11 A B v op u f.
Proof. exact (fun h0 : @monoidal B op => @lem7124546 A B v u f op h0). Qed.
Lemma lem7124549 (p : Prop) (q : Prop) (r : Prop) : (term12 p q r) = (term13 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem7124554 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : (term11 A B v op u f) = (term14 A B v op u f).
Proof. exact (@lem7124549 (@monoidal B op) (term10 A B v u f op) ((@iterate B A op v f) = (@iterate B A op u f))). Qed.
Lemma lem7124571 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7124572 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem7124571 p q p' q'). Qed.
Lemma lem7124573 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem7124572 p q p'). Qed.
Lemma lem7124574 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term18 A v u f.
Proof. exact (@lem7124573 (term19 A v u f) ((@sum A v f) = (@sum A u f))). Qed.
Lemma lem7124575 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) : term20 A v u f p'.
Proof. exact (@lem7124574 A v u f p'). Qed.
Lemma lem7124576 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) : (term20 A v u f p') = (term21 A v u f p').
Proof. exact (eq_refl (term20 A v u f p')). Qed.
Lemma lem7124577 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) : term21 A v u f p'.
Proof. exact (EQ_MP (@lem7124576 A v u f p') (@lem7124575 A v u f p')). Qed.
Lemma lem7124578 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term22 A v u f p' q'.
Proof. exact (@lem7124577 A v u f p' q'). Qed.
Lemma lem7124579 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term22 A v u f p' q') = (term23 A v u f p' q').
Proof. exact (eq_refl (term22 A v u f p' q')). Qed.
Lemma lem7124580 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term23 A v u f p' q'.
Proof. exact (EQ_MP (@lem7124579 A v u f p' q') (@lem7124578 A v u f p' q')). Qed.
Lemma lem7124590 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7124591 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem7124590 p q p' q'). Qed.
Lemma lem7124592 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem7124591 p q p'). Qed.
Lemma lem7124593 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : term24 A v u f x.
Proof. exact (@lem7124592 (term25 A v x u) ((f x) = term0)). Qed.
Lemma lem7124594 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term26 A v u f x p'.
Proof. exact (@lem7124593 A v u f x p'). Qed.
Lemma lem7124595 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term26 A v u f x p') = (term27 A v u f x p').
Proof. exact (eq_refl (term26 A v u f x p')). Qed.
Lemma lem7124596 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term27 A v u f x p'.
Proof. exact (EQ_MP (@lem7124595 A v u f x p') (@lem7124594 A v u f x p')). Qed.
Lemma lem7124597 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term28 A v u f x p' q'.
Proof. exact (@lem7124596 A v u f x p' q'). Qed.
Lemma lem7124598 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term28 A v u f x p' q') = (term29 A v u f x p' q').
Proof. exact (eq_refl (term28 A v u f x p' q')). Qed.
Lemma lem7124599 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term29 A v u f x p' q'.
Proof. exact (EQ_MP (@lem7124598 A v u f x p' q') (@lem7124597 A v u f x p' q')). Qed.
Lemma lem7124602 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term25 A v x u) = (term25 A v x u).
Proof. exact (eq_refl (term25 A v x u)). Qed.
Lemma lem7124603 {A : Type'} (f : A -> real) (v : A -> Prop) (x : A) (u : A -> Prop) (q' : Prop) : term30 A f v x u q'.
Proof. exact (@lem7124599 A v u f x (term25 A v x u) q'). Qed.
Lemma lem7124604 {A : Type'} (f : A -> real) (v : A -> Prop) (x : A) (u : A -> Prop) (q' : Prop) : term31 A f v x u q'.
Proof. exact (@lem7124603 A f v x u q' (@lem7124602 A v x u)). Qed.
Lemma lem7124615 : term0 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7124526) (@lem7065438)). Qed.
Lemma lem7124616 {A : Type'} (f : A -> real) (x : A) : (term32 A f x) = (term32 A f x).
Proof. exact (eq_refl (term32 A f x)). Qed.
Lemma lem7124617 {A : Type'} (f : A -> real) (x : A) : ((f x) = term0) = ((f x) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7124616 A f x) (@lem7124615)). Qed.
Lemma lem7124620 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : term33 A v u f x.
Proof. exact (fun h0 : term25 A v x u => @lem7124617 A f x). Qed.
Lemma lem7124621 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : term34 A v u f x.
Proof. exact (@lem7124604 A f v x u ((f x) = (@neutral real real_add))). Qed.
Lemma lem7124622 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term35 A v u f x) = (term36 A v u f x).
Proof. exact (@lem7124621 A v u f x (@lem7124620 A v u f x)). Qed.
Lemma lem7124658 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term37 A v u f) = (term38 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7124622 A v u f x)). Qed.
Lemma lem7124694 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7124695 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term39 A v u f) = (term40 A v u f).
Proof. exact (MK_COMB (@lem7124694 A) (@lem7124658 A v u f)). Qed.
Lemma lem7124735 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term41 A u v) = (term41 A u v).
Proof. exact (eq_refl (term41 A u v)). Qed.
Lemma lem7124736 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term19 A v u f) = (term42 A v u f).
Proof. exact (MK_COMB (@lem7124735 A u v) (@lem7124695 A v u f)). Qed.
Lemma lem7124778 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (q' : Prop) : term43 A v u f q'.
Proof. exact (@lem7124580 A v u f (term42 A v u f) q'). Qed.
Lemma lem7124779 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (q' : Prop) : term44 A v u f q'.
Proof. exact (@lem7124778 A v u f q' (@lem7124736 A v u f)). Qed.
Lemma lem7124780 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : term42 A v u f.
Proof. exact (h1). Qed.
Lemma lem7124781 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : term40 A v u f.
Proof. exact (proj2 (@lem7124780 A v u f h1)). Qed.
Lemma lem7124782 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : term45 A v u f x.
Proof. exact (@lem7124781 A v u f h1 x). Qed.
Lemma lem7124783 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term45 A v u f x) = (term36 A v u f x).
Proof. exact (eq_refl (term45 A v u f x)). Qed.
Lemma lem7124784 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : term36 A v u f x.
Proof. exact (EQ_MP (@lem7124783 A v u f x) (@lem7124782 A x v u f h1)). Qed.
Lemma lem7124785 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : term25 A v x u.
Proof. exact (h1). Qed.
Lemma lem7124786 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term25 A v x u) (h2 : term42 A v u f) : (f x) = (@neutral real real_add).
Proof. exact (@lem7124784 A x v u f h2 (@lem7124785 A v x u h1)). Qed.
Lemma lem7124792 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : @SUBSET A u v.
Proof. exact (proj1 (@lem7124780 A v u f h1)). Qed.
Lemma lem7124793 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@SUBSET A u v) = ((@SUBSET A u v) = True).
Proof. exact (@lem7 (@SUBSET A u v)). Qed.
Lemma lem7124798 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7124799 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7124798 A). Qed.
Lemma lem7124800 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7124801 {A : Type'} (v : A -> Prop) : (@sum A v) = (@iterate real A real_add v).
Proof. exact (MK_COMB (@lem7124799 A) (@lem7124800 A v)). Qed.
Lemma lem7124802 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7124803 {A : Type'} (v : A -> Prop) (f : A -> real) : (@sum A v f) = (@iterate real A real_add v f).
Proof. exact (MK_COMB (@lem7124801 A v) (@lem7124802 A f)). Qed.
Lemma lem7124805 {A B : Type'} (v : A -> Prop) (op : type1400 B) (u : A -> Prop) (f : A -> B) : term14 A B v op u f.
Proof. exact (EQ_MP (@lem7124554 A B v op u f) (@lem7124547 A B v op u f)). Qed.
Lemma lem7124806 {A : Type'} (v : A -> Prop) (op : type1627) (u : A -> Prop) (f : A -> real) : term46 A v op u f.
Proof. exact (@lem7124805 A real v op u f). Qed.
Lemma lem7124807 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term47 A v u f.
Proof. exact (@lem7124806 A v real_add u f). Qed.
Lemma lem7124811 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7124528) (@lem7067132)). Qed.
Lemma lem7124812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7124813 : term48 = (and True).
Proof. exact (MK_COMB (@lem7124812) (@lem7124811)). Qed.
Lemma lem7124817 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (@SUBSET A u v) = True.
Proof. exact (EQ_MP (@lem7124793 A u v) (@lem7124792 A v u f h1)). Qed.
Lemma lem7124818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7124819 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term41 A u v) = (and True).
Proof. exact (MK_COMB (@lem7124818) (@lem7124817 A v u f h1)). Qed.
Lemma lem7124827 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7124828 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem7124827 p q p' q'). Qed.
Lemma lem7124829 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem7124828 p q p'). Qed.
Lemma lem7124830 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : term49 A v u f x.
Proof. exact (@lem7124829 (term25 A v x u) ((f x) = (@neutral real real_add))). Qed.
Lemma lem7124831 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term50 A v u f x p'.
Proof. exact (@lem7124830 A v u f x p'). Qed.
Lemma lem7124832 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term50 A v u f x p') = (term51 A v u f x p').
Proof. exact (eq_refl (term50 A v u f x p')). Qed.
Lemma lem7124833 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term51 A v u f x p'.
Proof. exact (EQ_MP (@lem7124832 A v u f x p') (@lem7124831 A v u f x p')). Qed.
Lemma lem7124834 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term52 A v u f x p' q'.
Proof. exact (@lem7124833 A v u f x p' q'). Qed.
Lemma lem7124835 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term52 A v u f x p' q') = (term53 A v u f x p' q').
Proof. exact (eq_refl (term52 A v u f x p' q')). Qed.
Lemma lem7124836 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term53 A v u f x p' q'.
Proof. exact (EQ_MP (@lem7124835 A v u f x p' q') (@lem7124834 A v u f x p' q')). Qed.
Lemma lem7124839 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term25 A v x u) = (term25 A v x u).
Proof. exact (eq_refl (term25 A v x u)). Qed.
Lemma lem7124840 {A : Type'} (f : A -> real) (v : A -> Prop) (x : A) (u : A -> Prop) (q' : Prop) : term54 A f v x u q'.
Proof. exact (@lem7124836 A v u f x (term25 A v x u) q'). Qed.
Lemma lem7124841 {A : Type'} (f : A -> real) (v : A -> Prop) (x : A) (u : A -> Prop) (q' : Prop) : term55 A f v x u q'.
Proof. exact (@lem7124840 A f v x u q' (@lem7124839 A v x u)). Qed.
Lemma lem7124842 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : term25 A v x u.
Proof. exact (h1). Qed.
Lemma lem7124843 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : term56 A x u.
Proof. exact (proj2 (@lem7124842 A v x u h1)). Qed.
Lemma lem7124844 {A : Type'} (x : A) (u : A -> Prop) : term57 A x u.
Proof. exact (@lem82 (@IN A x u)). Qed.
Lemma lem7124846 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : @IN A x v.
Proof. exact (proj1 (@lem7124842 A v x u h1)). Qed.
Lemma lem7124847 {A : Type'} (x : A) (v : A -> Prop) : (@IN A x v) = ((@IN A x v) = True).
Proof. exact (@lem7 (@IN A x v)). Qed.
Lemma lem7124852 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : term36 A v u f x.
Proof. exact (fun h0 : term25 A v x u => @lem7124786 A x v u f h0 h1). Qed.
Lemma lem7124853 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : term36 A v u f x.
Proof. exact (@lem7124852 A x v u f h1). Qed.
Lemma lem7124857 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : (@IN A x v) = True.
Proof. exact (EQ_MP (@lem7124847 A x v) (@lem7124846 A v x u h1)). Qed.
Lemma lem7124858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7124859 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : (term58 A x v) = (and True).
Proof. exact (MK_COMB (@lem7124858) (@lem7124857 A v x u h1)). Qed.
Lemma lem7124861 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : (@IN A x u) = False.
Proof. exact (@lem7124844 A x u (@lem7124843 A v x u h1)). Qed.
Lemma lem7124862 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7124863 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : (term56 A x u) = (~ False).
Proof. exact (MK_COMB (@lem7124862) (@lem7124861 A v x u h1)). Qed.
Lemma lem7124865 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7124866 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : (term56 A x u) = True.
Proof. exact (TRANS (@lem7124863 A v x u h1) (@lem7124865)). Qed.
Lemma lem7124867 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : (term25 A v x u) = (True /\ True).
Proof. exact (MK_COMB (@lem7124859 A v x u h1) (@lem7124866 A v x u h1)). Qed.
Lemma lem7124869 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7124870 : (True /\ True) = True.
Proof. exact (@lem7124869 True). Qed.
Lemma lem7124871 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : (term25 A v x u) = True.
Proof. exact (TRANS (@lem7124867 A v x u h1) (@lem7124870)). Qed.
Lemma lem7124872 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : True = (term25 A v x u).
Proof. exact (SYM (@lem7124871 A v x u h1)). Qed.
Lemma lem7124873 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) (h1 : term25 A v x u) : term25 A v x u.
Proof. exact (EQ_MP (@lem7124872 A v x u h1) (@lem0)). Qed.
Lemma lem7124874 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term25 A v x u) (h2 : term42 A v u f) : (f x) = (@neutral real real_add).
Proof. exact (@lem7124853 A x v u f h2 (@lem7124873 A v x u h1)). Qed.
Lemma lem7124875 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7124876 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term25 A v x u) (h2 : term42 A v u f) : (term32 A f x) = term59.
Proof. exact (MK_COMB (@lem7124875) (@lem7124874 A x v u f h1 h2)). Qed.
Lemma lem7124877 : (@neutral real real_add) = (@neutral real real_add).
Proof. exact (eq_refl (@neutral real real_add)). Qed.
Lemma lem7124878 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term25 A v x u) (h2 : term42 A v u f) : ((f x) = (@neutral real real_add)) = ((@neutral real real_add) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7124876 A x v u f h1 h2) (@lem7124877)). Qed.
Lemma lem7124880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7124881 (x : real) : (x = x) = True.
Proof. exact (@lem7124880 real x). Qed.
Lemma lem7124882 : ((@neutral real real_add) = (@neutral real real_add)) = True.
Proof. exact (@lem7124881 (@neutral real real_add)). Qed.
Lemma lem7124883 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term25 A v x u) (h2 : term42 A v u f) : ((f x) = (@neutral real real_add)) = True.
Proof. exact (TRANS (@lem7124878 A x v u f h1 h2) (@lem7124882)). Qed.
Lemma lem7124884 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : term60 A v u f x.
Proof. exact (fun h0 : term25 A v x u => @lem7124883 A x v u f h0 h1). Qed.
Lemma lem7124885 {A : Type'} (f : A -> real) (v : A -> Prop) (x : A) (u : A -> Prop) : term61 A f v x u.
Proof. exact (@lem7124841 A f v x u True). Qed.
Lemma lem7124886 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term36 A v u f x) = (term62 A v x u).
Proof. exact (@lem7124885 A f v x u (@lem7124884 A x v u f h1)). Qed.
Lemma lem7124888 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7124889 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term62 A v x u) = True.
Proof. exact (@lem7124888 (term25 A v x u)). Qed.
Lemma lem7124890 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term36 A v u f x) = True.
Proof. exact (TRANS (@lem7124886 A x v u f h1) (@lem7124889 A v x u)). Qed.
Lemma lem7124891 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term38 A v u f) = (term63 A).
Proof. exact (fun_ext (fun x : A => @lem7124890 A x v u f h1)). Qed.
Lemma lem7124892 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7124893 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term40 A v u f) = (term64 A).
Proof. exact (MK_COMB (@lem7124892 A) (@lem7124891 A v u f h1)). Qed.
Lemma lem7124895 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7124896 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (@lem7124895 A t). Qed.
Lemma lem7124897 {A : Type'} : (term64 A) = True.
Proof. exact (@lem7124896 A True). Qed.
Lemma lem7124898 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term40 A v u f) = True.
Proof. exact (TRANS (@lem7124893 A v u f h1) (@lem7124897 A)). Qed.
Lemma lem7124899 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term42 A v u f) = (True /\ True).
Proof. exact (MK_COMB (@lem7124819 A v u f h1) (@lem7124898 A v u f h1)). Qed.
Lemma lem7124901 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7124902 : (True /\ True) = True.
Proof. exact (@lem7124901 True). Qed.
Lemma lem7124903 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term42 A v u f) = True.
Proof. exact (TRANS (@lem7124899 A v u f h1) (@lem7124902)). Qed.
Lemma lem7124904 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term66 A v u f) = (True /\ True).
Proof. exact (MK_COMB (@lem7124813) (@lem7124903 A v u f h1)). Qed.
Lemma lem7124906 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7124907 : (True /\ True) = True.
Proof. exact (@lem7124906 True). Qed.
Lemma lem7124908 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term66 A v u f) = True.
Proof. exact (TRANS (@lem7124904 A v u f h1) (@lem7124907)). Qed.
Lemma lem7124909 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : True = (term66 A v u f).
Proof. exact (SYM (@lem7124908 A v u f h1)). Qed.
Lemma lem7124910 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : term66 A v u f.
Proof. exact (EQ_MP (@lem7124909 A v u f h1) (@lem0)). Qed.
Lemma lem7124911 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (@iterate real A real_add v f) = (@iterate real A real_add u f).
Proof. exact (@lem7124807 A v u f (@lem7124910 A v u f h1)). Qed.
Lemma lem7124916 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (@sum A v f) = (@iterate real A real_add u f).
Proof. exact (TRANS (@lem7124803 A v f) (@lem7124911 A v u f h1)). Qed.
Lemma lem7124917 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7124918 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : (term67 A v f) = (term68 A u f).
Proof. exact (MK_COMB (@lem7124917) (@lem7124916 A v u f h1)). Qed.
Lemma lem7124924 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7124925 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7124924 A). Qed.
Lemma lem7124926 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7124927 {A : Type'} (u : A -> Prop) : (@sum A u) = (@iterate real A real_add u).
Proof. exact (MK_COMB (@lem7124925 A) (@lem7124926 A u)). Qed.
Lemma lem7124928 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7124929 {A : Type'} (u : A -> Prop) (f : A -> real) : (@sum A u f) = (@iterate real A real_add u f).
Proof. exact (MK_COMB (@lem7124927 A u) (@lem7124928 A f)). Qed.
Lemma lem7124934 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : ((@sum A v f) = (@sum A u f)) = ((@iterate real A real_add u f) = (@iterate real A real_add u f)).
Proof. exact (MK_COMB (@lem7124918 A v u f h1) (@lem7124929 A u f)). Qed.
Lemma lem7124936 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7124937 (x : real) : (x = x) = True.
Proof. exact (@lem7124936 real x). Qed.
Lemma lem7124938 {A : Type'} (u : A -> Prop) (f : A -> real) : ((@iterate real A real_add u f) = (@iterate real A real_add u f)) = True.
Proof. exact (@lem7124937 (@iterate real A real_add u f)). Qed.
Lemma lem7124939 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term42 A v u f) : ((@sum A v f) = (@sum A u f)) = True.
Proof. exact (TRANS (@lem7124934 A v u f h1) (@lem7124938 A u f)). Qed.
Lemma lem7124940 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term69 A v u f.
Proof. exact (fun h0 : term42 A v u f => @lem7124939 A v u f h0). Qed.
Lemma lem7124941 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term70 A v u f.
Proof. exact (@lem7124779 A v u f True). Qed.
Lemma lem7124942 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term71 A v u f) = (term72 A v u f).
Proof. exact (@lem7124941 A v u f (@lem7124940 A v u f)). Qed.
Lemma lem7124944 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7124945 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term72 A v u f) = True.
Proof. exact (@lem7124944 (term42 A v u f)). Qed.
Lemma lem7124946 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term71 A v u f) = True.
Proof. exact (TRANS (@lem7124942 A v u f) (@lem7124945 A v u f)). Qed.
Lemma lem7124947 {A : Type'} (u : A -> Prop) (f : A -> real) : (term73 A u f) = (term74 A).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7124946 A v u f)). Qed.
Lemma lem7124948 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7124949 {A : Type'} (u : A -> Prop) (f : A -> real) : (term75 A u f) = (term76 A).
Proof. exact (MK_COMB (@lem7124948 A) (@lem7124947 A u f)). Qed.
Lemma lem7124951 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7124952 {A : Type'} (t : Prop) : (term77 A t) = t.
Proof. exact (@lem7124951 (A -> Prop) t). Qed.
Lemma lem7124953 {A : Type'} : (term76 A) = True.
Proof. exact (@lem7124952 A True). Qed.
Lemma lem7124954 {A : Type'} (u : A -> Prop) (f : A -> real) : (term75 A u f) = True.
Proof. exact (TRANS (@lem7124949 A u f) (@lem7124953 A)). Qed.
Lemma lem7124955 {A : Type'} (f : A -> real) : (term78 A f) = (term74 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7124954 A u f)). Qed.
Lemma lem7124956 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7124957 {A : Type'} (f : A -> real) : (term79 A f) = (term76 A).
Proof. exact (MK_COMB (@lem7124956 A) (@lem7124955 A f)). Qed.
Lemma lem7124959 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7124960 {A : Type'} (t : Prop) : (term77 A t) = t.
Proof. exact (@lem7124959 (A -> Prop) t). Qed.
Lemma lem7124961 {A : Type'} : (term76 A) = True.
Proof. exact (@lem7124960 A True). Qed.
Lemma lem7124962 {A : Type'} (f : A -> real) : (term79 A f) = True.
Proof. exact (TRANS (@lem7124957 A f) (@lem7124961 A)). Qed.
Lemma lem7124963 {A : Type'} : (term80 A) = (term81 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7124962 A f)). Qed.
Lemma lem7124964 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7124965 {A : Type'} : (term82 A) = (term83 A).
Proof. exact (MK_COMB (@lem7124964 A) (@lem7124963 A)). Qed.
Lemma lem7124967 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7124968 {A : Type'} (t : Prop) : (term84 A t) = t.
Proof. exact (@lem7124967 (A -> real) t). Qed.
Lemma lem7124969 {A : Type'} : (term83 A) = True.
Proof. exact (@lem7124968 A True). Qed.
Lemma lem7124970 {A : Type'} : (term82 A) = True.
Proof. exact (TRANS (@lem7124965 A) (@lem7124969 A)). Qed.
Lemma lem7124971 {A : Type'} : True = (term82 A).
Proof. exact (SYM (@lem7124970 A)). Qed.
Lemma lem7124972 {A : Type'} : term82 A.
Proof. exact (EQ_MP (@lem7124971 A) (@lem0)). Qed.
