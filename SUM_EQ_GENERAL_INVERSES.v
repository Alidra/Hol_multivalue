Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_EQ_GENERAL_INVERSES_term_abbrevs.
Require Import ITERATE_EQ_GENERAL_INVERSES_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7178401 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7178403 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7178404 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7178403 A B C h1 op). Qed.
Lemma lem7178405 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7178406 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7178405 A B C op) (@lem7178404 A B C op h1)). Qed.
Lemma lem7178407 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7178408 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7178406 A B C op h1 (@lem7178407 C op h2)). Qed.
Lemma lem7178409 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7178408 A B C op h0 h1). Qed.
Lemma lem7178410 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7178411 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7178409 A B C op h2 (@lem7178410 A B C h1)). Qed.
Lemma lem7178412 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7178411 A B C op h1 h0). Qed.
Lemma lem7178413 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7178412 A B C op h1). Qed.
Lemma lem7178414 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7178413 A B C h0). Qed.
Lemma lem7178415 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7178414 A B C (@lem6000071 A B C)). Qed.
Lemma lem7178416 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7178415 A B C op). Qed.
Lemma lem7178417 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7178474 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178475 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7178474 A). Qed.
Lemma lem7178476 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7178477 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7178475 A) (@lem7178476 A s)). Qed.
Lemma lem7178478 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7178479 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@iterate real A real_add s f).
Proof. exact (MK_COMB (@lem7178477 A s) (@lem7178478 A f)). Qed.
Lemma lem7178480 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7178481 {A : Type'} (s : A -> Prop) (f : A -> real) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7178480) (@lem7178479 A s f)). Qed.
Lemma lem7178483 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178484 {B : Type'} : (@sum B) = (@iterate real B real_add).
Proof. exact (@lem7178483 B). Qed.
Lemma lem7178485 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7178486 {B : Type'} (t : B -> Prop) : (@sum B t) = (@iterate real B real_add t).
Proof. exact (MK_COMB (@lem7178484 B) (@lem7178485 B t)). Qed.
Lemma lem7178487 {B : Type'} (g : B -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7178488 {B : Type'} (t : B -> Prop) (g : B -> real) : (@sum B t g) = (@iterate real B real_add t g).
Proof. exact (MK_COMB (@lem7178486 B t) (@lem7178487 B g)). Qed.
Lemma lem7178489 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : ((@sum A s f) = (@sum B t g)) = ((@iterate real A real_add s f) = (@iterate real B real_add t g)).
Proof. exact (MK_COMB (@lem7178481 A s f) (@lem7178488 B t g)). Qed.
Lemma lem7178492 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> real) (h : A -> B) (f : A -> real) : (term8 A B s t k g h f) = (term8 A B s t k g h f).
Proof. exact (eq_refl (term8 A B s t k g h f)). Qed.
Lemma lem7178493 {A B : Type'} (k : B -> A) (h : A -> B) (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term9 A B k h s f t g) = (term10 A B k h s f t g).
Proof. exact (MK_COMB (@lem7178492 A B s t k g h f) (@lem7178489 A B s f t g)). Qed.
Lemma lem7178496 {A B : Type'} (h : A -> B) (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term11 A B h s f t g) = (term12 A B h s f t g).
Proof. exact (fun_ext (fun k : B -> A => @lem7178493 A B k h s f t g)). Qed.
Lemma lem7178497 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem7178498 {A B : Type'} (h : A -> B) (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term13 A B h s f t g) = (term14 A B h s f t g).
Proof. exact (MK_COMB (@lem7178497 A B) (@lem7178496 A B h s f t g)). Qed.
Lemma lem7178503 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term15 A B s f t g) = (term16 A B s f t g).
Proof. exact (fun_ext (fun h : A -> B => @lem7178498 A B h s f t g)). Qed.
Lemma lem7178504 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7178505 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term17 A B s f t g) = (term18 A B s f t g).
Proof. exact (MK_COMB (@lem7178504 A B) (@lem7178503 A B s f t g)). Qed.
Lemma lem7178510 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) : (term19 A B s f t) = (term20 A B s f t).
Proof. exact (fun_ext (fun g : B -> real => @lem7178505 A B s f t g)). Qed.
Lemma lem7178511 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7178512 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) : (term21 A B s f t) = (term22 A B s f t).
Proof. exact (MK_COMB (@lem7178511 B) (@lem7178510 A B s f t)). Qed.
Lemma lem7178517 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term23 A B s t) = (term24 A B s t).
Proof. exact (fun_ext (fun f : A -> real => @lem7178512 A B s f t)). Qed.
Lemma lem7178518 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7178519 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term25 A B s t) = (term26 A B s t).
Proof. exact (MK_COMB (@lem7178518 A) (@lem7178517 A B s t)). Qed.
Lemma lem7178524 {A B : Type'} (s : A -> Prop) : (term27 A B s) = (term28 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7178519 A B s t)). Qed.
Lemma lem7178525 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7178526 {A B : Type'} (s : A -> Prop) : (term29 A B s) = (term30 A B s).
Proof. exact (MK_COMB (@lem7178525 B) (@lem7178524 A B s)). Qed.
Lemma lem7178531 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7178526 A B s)). Qed.
Lemma lem7178532 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7178533 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7178532 A) (@lem7178531 A B)). Qed.
Lemma lem7178538 {A B : Type'} : (term34 A B) = (term33 A B).
Proof. exact (SYM (@lem7178533 A B)). Qed.
Lemma lem7178540 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7178417 A B C op) (@lem7178416 A B C op)). Qed.
Lemma lem7178541 {A B : Type'} (op : type1627) : term35 A B op.
Proof. exact (@lem7178540 A B real op). Qed.
Lemma lem7178542 {A B : Type'} : term36 A B.
Proof. exact (@lem7178541 A B real_add). Qed.
Lemma lem7178544 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7178401) (@lem7067132)). Qed.
Lemma lem7178545 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7178544)). Qed.
Lemma lem7178546 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7178545) (@lem0)). Qed.
Lemma lem7178547 {A B : Type'} : term34 A B.
Proof. exact (@lem7178542 A B (@lem7178546)). Qed.
Lemma lem7178548 {A B : Type'} : term33 A B.
Proof. exact (EQ_MP (@lem7178538 A B) (@lem7178547 A B)). Qed.
