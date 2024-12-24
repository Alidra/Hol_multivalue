Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_SUM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import SUM_EQ_NUMSEG_spec.
Require Import admissible_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20669_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Lemma lem8220445 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8220446 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8220447 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8220446 t1) (@lem8220445 t1)). Qed.
Lemma lem8220448 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8220447 t1 t2). Qed.
Lemma lem8220449 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8220450 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8220449 t1 t2) (@lem8220448 t1 t2)). Qed.
Lemma lem8220451 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8220450 t1 t2 t3). Qed.
Lemma lem8220452 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8220453 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8220452 t1 t2 t3) (@lem8220451 t1 t2 t3)). Qed.
Lemma lem8220454 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8220453 t1 t2 t3)). Qed.
Lemma lem8220455 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem8220456 (f : nat -> real) (h1 : term7) : term8 f.
Proof. exact (@lem8220455 h1 f). Qed.
Lemma lem8220457 (f : nat -> real) : (term8 f) = (term9 f).
Proof. exact (eq_refl (term8 f)). Qed.
Lemma lem8220458 (f : nat -> real) (h1 : term7) : term9 f.
Proof. exact (EQ_MP (@lem8220457 f) (@lem8220456 f h1)). Qed.
Lemma lem8220459 (f : nat -> real) (g : nat -> real) (h1 : term7) : term10 f g.
Proof. exact (@lem8220458 f h1 g). Qed.
Lemma lem8220460 (f : nat -> real) (g : nat -> real) : (term10 f g) = (term11 f g).
Proof. exact (eq_refl (term10 f g)). Qed.
Lemma lem8220461 (f : nat -> real) (g : nat -> real) (h1 : term7) : term11 f g.
Proof. exact (EQ_MP (@lem8220460 f g) (@lem8220459 f g h1)). Qed.
Lemma lem8220462 (f : nat -> real) (g : nat -> real) (m : nat) (h1 : term7) : term12 f g m.
Proof. exact (@lem8220461 f g h1 m). Qed.
Lemma lem8220463 (f : nat -> real) (m : nat) (g : nat -> real) : (term12 f g m) = (term13 f m g).
Proof. exact (eq_refl (term12 f g m)). Qed.
Lemma lem8220464 (f : nat -> real) (m : nat) (g : nat -> real) (h1 : term7) : term13 f m g.
Proof. exact (EQ_MP (@lem8220463 f m g) (@lem8220462 f g m h1)). Qed.
Lemma lem8220465 (f : nat -> real) (m : nat) (g : nat -> real) (n : nat) (h1 : term7) : term14 f m g n.
Proof. exact (@lem8220464 f m g h1 n). Qed.
Lemma lem8220466 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term14 f m g n) = (term15 f m n g).
Proof. exact (eq_refl (term14 f m g n)). Qed.
Lemma lem8220467 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term7) : term15 f m n g.
Proof. exact (EQ_MP (@lem8220466 f m n g) (@lem8220465 f m g n h1)). Qed.
Lemma lem8220468 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term16 m n f g) : term16 m n f g.
Proof. exact (h1). Qed.
Lemma lem8220469 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term7) (h2 : term16 m n f g) : (term17 m n f) = (term17 m n g).
Proof. exact (@lem8220467 f m n g h1 (@lem8220468 m n f g h2)). Qed.
Lemma lem8220470 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term16 m n f g) : term18 f m n g.
Proof. exact (fun h0 : term7 => @lem8220469 m n f g h0 h1). Qed.
Lemma lem8220471 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem8220472 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) (h1 : term7) (h2 : term16 m n f g) : (term17 m n f) = (term17 m n g).
Proof. exact (@lem8220470 m n f g h2 (@lem8220471 h1)). Qed.
Lemma lem8220473 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) (h1 : term7) : term15 f m n g.
Proof. exact (fun h0 : term16 m n f g => @lem8220472 m n f g h1 h0). Qed.
Lemma lem8220474 (f : nat -> real) (m : nat) (n : nat) (h1 : term7) : term19 f m n.
Proof. exact (fun g : nat -> real => @lem8220473 f m n g h1). Qed.
Lemma lem8220475 (f : nat -> real) (m : nat) (h1 : term7) : term20 f m.
Proof. exact (fun n : nat => @lem8220474 f m n h1). Qed.
Lemma lem8220476 (f : nat -> real) (h1 : term7) : term21 f.
Proof. exact (fun m : nat => @lem8220475 f m h1). Qed.
Lemma lem8220477 (h1 : term7) : term22.
Proof. exact (fun f : nat -> real => @lem8220476 f h1). Qed.
Lemma lem8220478 : term23.
Proof. exact (fun h0 : term7 => @lem8220477 h0). Qed.
Lemma lem8220479 : term22.
Proof. exact (@lem8220478 (@lem7213670)). Qed.
Lemma lem8220480 (f : nat -> real) : term24 f.
Proof. exact (@lem8220479 f). Qed.
Lemma lem8220481 (f : nat -> real) : (term24 f) = (term21 f).
Proof. exact (eq_refl (term24 f)). Qed.
Lemma lem8220482 (f : nat -> real) : term21 f.
Proof. exact (EQ_MP (@lem8220481 f) (@lem8220480 f)). Qed.
Lemma lem8220483 (f : nat -> real) (m : nat) : term25 f m.
Proof. exact (@lem8220482 f m). Qed.
Lemma lem8220484 (f : nat -> real) (m : nat) : (term25 f m) = (term20 f m).
Proof. exact (eq_refl (term25 f m)). Qed.
Lemma lem8220485 (f : nat -> real) (m : nat) : term20 f m.
Proof. exact (EQ_MP (@lem8220484 f m) (@lem8220483 f m)). Qed.
Lemma lem8220486 (f : nat -> real) (m : nat) (n : nat) : term26 f m n.
Proof. exact (@lem8220485 f m n). Qed.
Lemma lem8220487 (f : nat -> real) (m : nat) (n : nat) : (term26 f m n) = (term19 f m n).
Proof. exact (eq_refl (term26 f m n)). Qed.
Lemma lem8220488 (f : nat -> real) (m : nat) (n : nat) : term19 f m n.
Proof. exact (EQ_MP (@lem8220487 f m n) (@lem8220486 f m n)). Qed.
Lemma lem8220489 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : term27 f m n g.
Proof. exact (@lem8220488 f m n g). Qed.
Lemma lem8220490 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term27 f m n g) = (term15 f m n g).
Proof. exact (eq_refl (term27 f m n g)). Qed.
Lemma lem8220492 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term28 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem8220493 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term28 _5106 _5107 P) = ((term29 _5106 _5107 P) = (term30 _5106 _5107 P)).
Proof. exact (eq_refl (term28 _5106 _5107 P)). Qed.
Lemma lem8220495 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term31 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8220496 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term31 _143449 _143452 _143456 _143457 _143462 p) = (term32 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term31 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8220497 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term32 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8220496 _143449 _143452 _143456 _143457 _143462 p) (@lem8220495 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8220498 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term33 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8220497 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8220499 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term33 _143449 _143452 _143456 _143457 _143462 p lt2) = (term34 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term33 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8220500 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term34 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8220499 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8220498 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8220501 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term35 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8220500 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8220502 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term35 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term36 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term35 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8220503 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term36 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8220502 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8220501 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8220504 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term37 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8220503 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8220505 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term37 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term38 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term37 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8220546 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term38 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8220505 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8220504 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8220547 {A B C P : Type'} (p : type542 B C P) (lt2 : type1470 A B) (s : type1313 A P) (t : type544 B C P) : (@admissible A C B real (prod nat P) lt2 p s t) = (term39 A B C P p lt2 s t).
Proof. exact (@lem8220546 A C B real (prod nat P) p lt2 s t). Qed.
Lemma lem8220548 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term40 A B C P lt2 a b p s h) = (term41 A B C P a b p lt2 s h).
Proof. exact (@lem8220547 A B C P (term42 B C P a b p) lt2 (term43 A P s) (term44 B C P h)). Qed.
Lemma lem8220566 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term29 _5106 _5107 P) = (term30 _5106 _5107 P).
Proof. exact (EQ_MP (@lem8220493 _5106 _5107 P) (@lem8220492 _5106 _5107 P)). Qed.
Lemma lem8220567 {P : Type'} (P' : type1310 P) : (term45 P P') = (term46 P P').
Proof. exact (@lem8220566 P nat P'). Qed.
Lemma lem8220568 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term47 A B C P a b p lt2 s f h g) = (term48 A B C P a b p lt2 s f h g).
Proof. exact (@lem8220567 P (term49 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8220569 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : prod nat P) : (term50 A B C P a b p lt2 s f h g a') = (term51 A B C P a b p lt2 s f h g a').
Proof. exact (eq_refl (term50 A B C P a b p lt2 s f h g a')). Qed.
Lemma lem8220570 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term52 A B C P a b p lt2 s f h g) = (term49 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun a' : prod nat P => @lem8220569 A B C P a b p lt2 s f h g a')). Qed.
Lemma lem8220571 {P : Type'} : (@all (prod nat P)) = (@all (prod nat P)).
Proof. exact (eq_refl (@all (prod nat P))). Qed.
Lemma lem8220572 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term47 A B C P a b p lt2 s f h g) = (term53 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8220571 P) (@lem8220570 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8220573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8220574 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term54 A B C P a b p lt2 s f h g) = (term55 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8220573) (@lem8220572 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8220575 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) (p2 : P) : (term56 A B C P a b p lt2 s f h g p1 p2) = (term57 A B C P a b p lt2 s f h g p1 p2).
Proof. exact (eq_refl (term56 A B C P a b p lt2 s f h g p1 p2)). Qed.
Lemma lem8220576 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term58 A B C P a b p lt2 s f h g p1) = (term59 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8220575 A B C P a b p lt2 s f h g p1 p2)). Qed.
Lemma lem8220577 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8220578 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term60 A B C P a b p lt2 s f h g p1) = (term61 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8220577 P) (@lem8220576 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8220579 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term62 A B C P a b p lt2 s f h g) = (term63 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8220578 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8220580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8220581 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term48 A B C P a b p lt2 s f h g) = (term64 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8220580) (@lem8220579 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8220582 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : ((term47 A B C P a b p lt2 s f h g) = (term48 A B C P a b p lt2 s f h g)) = ((term53 A B C P a b p lt2 s f h g) = (term64 A B C P a b p lt2 s f h g)).
Proof. exact (MK_COMB (@lem8220574 A B C P a b p lt2 s f h g) (@lem8220581 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8220583 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term53 A B C P a b p lt2 s f h g) = (term64 A B C P a b p lt2 s f h g).
Proof. exact (EQ_MP (@lem8220582 A B C P a b p lt2 s f h g) (@lem8220568 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8220601 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8220602 {B C P : Type'} (f : type542 B C P) (y : B -> C) : (term66 B C P f y) = (f y).
Proof. exact (@lem8220601 (B -> C) (type1310 P) f y). Qed.
Lemma lem8220603 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term67 B C P a b p f) = (term68 B C P a b p f).
Proof. exact (@lem8220602 B C P (term42 B C P a b p) f). Qed.
Lemma lem8220604 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term68 B C P a b p f) = (term69 B C P a b p f).
Proof. exact (eq_refl (term68 B C P a b p f)). Qed.
Lemma lem8220605 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) : (term70 B C P a b p) = (term42 B C P a b p).
Proof. exact (fun_ext (fun f : B -> C => @lem8220604 B C P a b p f)). Qed.
Lemma lem8220606 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8220607 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term67 B C P a b p f) = (term68 B C P a b p f).
Proof. exact (MK_COMB (@lem8220605 B C P a b p) (@lem8220606 B C f)). Qed.
Lemma lem8220608 {P : Type'} : (@eq ((prod nat P) -> Prop)) = (@eq ((prod nat P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod nat P) -> Prop))). Qed.
Lemma lem8220609 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term71 B C P a b p f) = (term72 B C P a b p f).
Proof. exact (MK_COMB (@lem8220608 P) (@lem8220607 B C P a b p f)). Qed.
Lemma lem8220610 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term68 B C P a b p f) = (term69 B C P a b p f).
Proof. exact (eq_refl (term68 B C P a b p f)). Qed.
Lemma lem8220611 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : ((term67 B C P a b p f) = (term68 B C P a b p f)) = ((term68 B C P a b p f) = (term69 B C P a b p f)).
Proof. exact (MK_COMB (@lem8220609 B C P a b p f) (@lem8220610 B C P a b p f)). Qed.
Lemma lem8220612 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term68 B C P a b p f) = (term69 B C P a b p f).
Proof. exact (EQ_MP (@lem8220611 B C P a b p f) (@lem8220603 B C P a b p f)). Qed.
Lemma lem8220629 {P : Type'} (p1 : nat) (p2 : P) : (@pair nat P p1 p2) = (@pair nat P p1 p2).
Proof. exact (eq_refl (@pair nat P p1 p2)). Qed.
Lemma lem8220630 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p1 : nat) (p2 : P) : (term73 B C P a b p f p1 p2) = (term74 B C P a b p f p1 p2).
Proof. exact (MK_COMB (@lem8220612 B C P a b p f) (@lem8220629 P p1 p2)). Qed.
Lemma lem8220631 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8220632 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8220631 P k x). Qed.
Lemma lem8220633 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8220634 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8220633 P k x). Qed.
Lemma lem8220635 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8220636 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8220637 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8220636) (@lem8220632 P k x)). Qed.
Lemma lem8220638 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8220639 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8220640 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220639 k) (@lem8220638 P k x)). Qed.
Lemma lem8220641 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8220642 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8220643 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8220642) (@lem8220641 k)). Qed.
Lemma lem8220644 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8220645 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220643 k) (@lem8220644 P k x)). Qed.
Lemma lem8220646 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8220640 P k x) (@lem8220645 P k x)). Qed.
Lemma lem8220647 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8220646 P k x) (@lem8220637 P k x)). Qed.
Lemma lem8220648 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8220649 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220648 k) (@lem8220647 P k x)). Qed.
Lemma lem8220650 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8220649 P k x) (@lem8220635 k)). Qed.
Lemma lem8220651 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8220652 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8220653 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8220652 P) (@lem8220634 P k x)). Qed.
Lemma lem8220654 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8220655 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8220656 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220655 P x) (@lem8220654 P k x)). Qed.
Lemma lem8220657 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8220658 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8220659 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8220658 P) (@lem8220657 P x)). Qed.
Lemma lem8220660 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8220661 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220659 P x) (@lem8220660 P k x)). Qed.
Lemma lem8220662 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8220656 P k x) (@lem8220661 P k x)). Qed.
Lemma lem8220663 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8220662 P k x) (@lem8220653 P k x)). Qed.
Lemma lem8220664 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8220665 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220664 P x) (@lem8220663 P k x)). Qed.
Lemma lem8220666 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8220665 P k x) (@lem8220651 P x)). Qed.
Lemma lem8220667 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term85 B C P a b p f) = (term85 B C P a b p f).
Proof. exact (eq_refl (term85 B C P a b p f)). Qed.
Lemma lem8220668 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term86 B C P a b p f k) = (term87 B C P a b p f k x).
Proof. exact (MK_COMB (@lem8220667 B C P a b p f) (@lem8220650 P k x)). Qed.
Lemma lem8220669 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term87 B C P a b p f k x) = (term88 B C P a k x b p f).
Proof. exact (eq_refl (term87 B C P a b p f k x)). Qed.
Lemma lem8220670 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) : (term89 B C P a b p f k) = (term89 B C P a b p f k).
Proof. exact (eq_refl (term89 B C P a b p f k)). Qed.
Lemma lem8220671 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : ((term86 B C P a b p f k) = (term87 B C P a b p f k x)) = ((term86 B C P a b p f k) = (term88 B C P a k x b p f)).
Proof. exact (MK_COMB (@lem8220670 B C P a b p f k) (@lem8220669 B C P a k x b p f)). Qed.
Lemma lem8220672 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term86 B C P a b p f k) = (term90 B C P a k b p f).
Proof. exact (eq_refl (term86 B C P a b p f k)). Qed.
Lemma lem8220673 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8220674 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term89 B C P a b p f k) = (term91 B C P a k b p f).
Proof. exact (MK_COMB (@lem8220673 P) (@lem8220672 B C P a k b p f)). Qed.
Lemma lem8220675 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term88 B C P a k x b p f) = (term88 B C P a k x b p f).
Proof. exact (eq_refl (term88 B C P a k x b p f)). Qed.
Lemma lem8220676 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : ((term86 B C P a b p f k) = (term88 B C P a k x b p f)) = ((term90 B C P a k b p f) = (term88 B C P a k x b p f)).
Proof. exact (MK_COMB (@lem8220674 B C P a k b p f) (@lem8220675 B C P a k x b p f)). Qed.
Lemma lem8220677 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : ((term86 B C P a b p f k) = (term87 B C P a b p f k x)) = ((term90 B C P a k b p f) = (term88 B C P a k x b p f)).
Proof. exact (TRANS (@lem8220671 B C P a k x b p f) (@lem8220676 B C P a k x b p f)). Qed.
Lemma lem8220678 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term90 B C P a k b p f) = (term88 B C P a k x b p f).
Proof. exact (EQ_MP (@lem8220677 B C P a k x b p f) (@lem8220668 B C P a b p f k x)). Qed.
Lemma lem8220679 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term92 B C P a k b p f x) = (term93 B C P a b p f k x).
Proof. exact (MK_COMB (@lem8220678 B C P a k x b p f) (@lem8220666 P k x)). Qed.
Lemma lem8220680 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term93 B C P a b p f k x) = (term94 B C P a b p f k x).
Proof. exact (eq_refl (term93 B C P a b p f k x)). Qed.
Lemma lem8220681 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term95 B C P a k b p f x) = (term95 B C P a k b p f x).
Proof. exact (eq_refl (term95 B C P a k b p f x)). Qed.
Lemma lem8220682 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p f x) = (term93 B C P a b p f k x)) = ((term92 B C P a k b p f x) = (term94 B C P a b p f k x)).
Proof. exact (MK_COMB (@lem8220681 B C P a k b p f x) (@lem8220680 B C P a b p f k x)). Qed.
Lemma lem8220683 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term92 B C P a k b p f x) = (term96 B C P a k b p f x).
Proof. exact (eq_refl (term92 B C P a k b p f x)). Qed.
Lemma lem8220684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8220685 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term95 B C P a k b p f x) = (term97 B C P a k b p f x).
Proof. exact (MK_COMB (@lem8220684) (@lem8220683 B C P a k b p f x)). Qed.
Lemma lem8220686 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term94 B C P a b p f k x) = (term94 B C P a b p f k x).
Proof. exact (eq_refl (term94 B C P a b p f k x)). Qed.
Lemma lem8220687 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p f x) = (term94 B C P a b p f k x)) = ((term96 B C P a k b p f x) = (term94 B C P a b p f k x)).
Proof. exact (MK_COMB (@lem8220685 B C P a k b p f x) (@lem8220686 B C P a b p f k x)). Qed.
Lemma lem8220688 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p f x) = (term93 B C P a b p f k x)) = ((term96 B C P a k b p f x) = (term94 B C P a b p f k x)).
Proof. exact (TRANS (@lem8220682 B C P a b p f k x) (@lem8220687 B C P a b p f k x)). Qed.
Lemma lem8220689 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term96 B C P a k b p f x) = (term94 B C P a b p f k x).
Proof. exact (EQ_MP (@lem8220688 B C P a b p f k x) (@lem8220679 B C P a b p f k x)). Qed.
Lemma lem8220690 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term94 B C P a b p f k x) = (term96 B C P a k b p f x).
Proof. exact (SYM (@lem8220689 B C P a b p f k x)). Qed.
Lemma lem8220691 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term98 B C P a b p f k x) = (term94 B C P a b p f k x).
Proof. exact (eq_refl (term98 B C P a b p f k x)). Qed.
Lemma lem8220692 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term98 B C P a b p f k x) = (term96 B C P a k b p f x).
Proof. exact (TRANS (@lem8220691 B C P a b p f k x) (@lem8220690 B C P a k b p f x)). Qed.
Lemma lem8220693 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term99 B C P a k b p f.
Proof. exact (fun x : P => @lem8220692 B C P a k b p f x). Qed.
Lemma lem8220694 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term100 B C P a b p f.
Proof. exact (fun k : nat => @lem8220693 B C P a k b p f). Qed.
Lemma lem8220695 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term101 B C P a b p f.
Proof. exact (ex_intro (term102 B C P a b p f) (term103 B C P a b p f) (@lem8220694 B C P a b p f)). Qed.
Lemma lem8220697 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8220698 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8220697 Prop a b). Qed.
Lemma lem8220699 {B C P : Type'} (_109276 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : ((term104 P _109276 k x) = (term96 B C P a k b p f x)) = (term105 B C P _109276 a k b p f x).
Proof. exact (@lem8220698 (term104 P _109276 k x) (term96 B C P a k b p f x)). Qed.
Lemma lem8220700 {B C P : Type'} (_109276 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term106 B C P _109276 a k b p f) = (term107 B C P _109276 a k b p f).
Proof. exact (fun_ext (fun x : P => @lem8220699 B C P _109276 a k b p f x)). Qed.
Lemma lem8220701 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8220702 {B C P : Type'} (_109276 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term108 B C P _109276 a k b p f) = (term109 B C P _109276 a k b p f).
Proof. exact (MK_COMB (@lem8220701 P) (@lem8220700 B C P _109276 a k b p f)). Qed.
Lemma lem8220703 {B C P : Type'} (_109276 : type1310 P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term110 B C P _109276 a b p f) = (term111 B C P _109276 a b p f).
Proof. exact (fun_ext (fun k : nat => @lem8220702 B C P _109276 a k b p f)). Qed.
Lemma lem8220704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8220705 {B C P : Type'} (_109276 : type1310 P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term112 B C P _109276 a b p f) = (term113 B C P _109276 a b p f).
Proof. exact (MK_COMB (@lem8220704) (@lem8220703 B C P _109276 a b p f)). Qed.
Lemma lem8220706 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term102 B C P a b p f) = (term114 B C P a b p f).
Proof. exact (fun_ext (fun _109276 : type1310 P => @lem8220705 B C P _109276 a b p f)). Qed.
Lemma lem8220707 {P : Type'} : (@ex ((prod nat P) -> Prop)) = (@ex ((prod nat P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat P) -> Prop))). Qed.
Lemma lem8220708 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term101 B C P a b p f) = (term115 B C P a b p f).
Proof. exact (MK_COMB (@lem8220707 P) (@lem8220706 B C P a b p f)). Qed.
Lemma lem8220709 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term115 B C P a b p f.
Proof. exact (EQ_MP (@lem8220708 B C P a b p f) (@lem8220695 B C P a b p f)). Qed.
Lemma lem8220711 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8220712 {P : Type'} (P' : type372 P) : term117 P P'.
Proof. exact (@lem8220711 (type1310 P) P'). Qed.
Lemma lem8220713 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term118 B C P a b p f.
Proof. exact (@lem8220712 P (term114 B C P a b p f)). Qed.
Lemma lem8220714 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term119 B C P a b p f.
Proof. exact (@lem8220713 B C P a b p f (@lem8220709 B C P a b p f)). Qed.
Lemma lem8220715 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term119 B C P a b p f) = (term120 B C P a b p f).
Proof. exact (eq_refl (term119 B C P a b p f)). Qed.
Lemma lem8220716 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term120 B C P a b p f.
Proof. exact (EQ_MP (@lem8220715 B C P a b p f) (@lem8220714 B C P a b p f)). Qed.
Lemma lem8220717 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) : term121 B C P a b p f k.
Proof. exact (@lem8220716 B C P a b p f k). Qed.
Lemma lem8220718 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term121 B C P a b p f k) = (term122 B C P a k b p f).
Proof. exact (eq_refl (term121 B C P a b p f k)). Qed.
Lemma lem8220719 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term122 B C P a k b p f.
Proof. exact (EQ_MP (@lem8220718 B C P a k b p f) (@lem8220717 B C P a b p f k)). Qed.
Lemma lem8220720 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : term123 B C P a k b p f x.
Proof. exact (@lem8220719 B C P a k b p f x). Qed.
Lemma lem8220721 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term123 B C P a k b p f x) = (term124 B C P a k b p f x).
Proof. exact (eq_refl (term123 B C P a k b p f x)). Qed.
Lemma lem8220722 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : term124 B C P a k b p f x.
Proof. exact (EQ_MP (@lem8220721 B C P a k b p f x) (@lem8220720 B C P a k b p f x)). Qed.
Lemma lem8220724 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8220725 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8220724 Prop a b). Qed.
Lemma lem8220726 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term124 B C P a k b p f x) = ((term74 B C P a b p f k x) = (term96 B C P a k b p f x)).
Proof. exact (@lem8220725 (term74 B C P a b p f k x) (term96 B C P a k b p f x)). Qed.
Lemma lem8220727 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term74 B C P a b p f k x) = (term96 B C P a k b p f x).
Proof. exact (EQ_MP (@lem8220726 B C P a k b p f x) (@lem8220722 B C P a k b p f x)). Qed.
Lemma lem8220728 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term74 B C P a b p f k x) = (term96 B C P a k b p f x).
Proof. exact (@lem8220727 B C P a k b p f x). Qed.
Lemma lem8220729 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term74 B C P a b p f p1 p2) = (term96 B C P a p1 b p f p2).
Proof. exact (@lem8220728 B C P a p1 b p f p2). Qed.
Lemma lem8220734 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term73 B C P a b p f p1 p2) = (term96 B C P a p1 b p f p2).
Proof. exact (TRANS (@lem8220630 B C P a b p f p1 p2) (@lem8220729 B C P a p1 b p f p2)). Qed.
Lemma lem8220735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8220736 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term125 B C P a b p f p1 p2) = (term126 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8220735) (@lem8220734 B C P a p1 b p f p2)). Qed.
Lemma lem8220740 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8220741 {B C P : Type'} (f : type542 B C P) (y : B -> C) : (term66 B C P f y) = (f y).
Proof. exact (@lem8220740 (B -> C) (type1310 P) f y). Qed.
Lemma lem8220742 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term67 B C P a b p g) = (term68 B C P a b p g).
Proof. exact (@lem8220741 B C P (term42 B C P a b p) g). Qed.
Lemma lem8220743 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term68 B C P a b p f) = (term69 B C P a b p f).
Proof. exact (eq_refl (term68 B C P a b p f)). Qed.
Lemma lem8220744 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) : (term70 B C P a b p) = (term42 B C P a b p).
Proof. exact (fun_ext (fun f : B -> C => @lem8220743 B C P a b p f)). Qed.
Lemma lem8220745 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8220746 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term67 B C P a b p g) = (term68 B C P a b p g).
Proof. exact (MK_COMB (@lem8220744 B C P a b p) (@lem8220745 B C g)). Qed.
Lemma lem8220747 {P : Type'} : (@eq ((prod nat P) -> Prop)) = (@eq ((prod nat P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod nat P) -> Prop))). Qed.
Lemma lem8220748 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term71 B C P a b p g) = (term72 B C P a b p g).
Proof. exact (MK_COMB (@lem8220747 P) (@lem8220746 B C P a b p g)). Qed.
Lemma lem8220749 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term68 B C P a b p g) = (term69 B C P a b p g).
Proof. exact (eq_refl (term68 B C P a b p g)). Qed.
Lemma lem8220750 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : ((term67 B C P a b p g) = (term68 B C P a b p g)) = ((term68 B C P a b p g) = (term69 B C P a b p g)).
Proof. exact (MK_COMB (@lem8220748 B C P a b p g) (@lem8220749 B C P a b p g)). Qed.
Lemma lem8220751 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term68 B C P a b p g) = (term69 B C P a b p g).
Proof. exact (EQ_MP (@lem8220750 B C P a b p g) (@lem8220742 B C P a b p g)). Qed.
Lemma lem8220768 {P : Type'} (p1 : nat) (p2 : P) : (@pair nat P p1 p2) = (@pair nat P p1 p2).
Proof. exact (eq_refl (@pair nat P p1 p2)). Qed.
Lemma lem8220769 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p1 : nat) (p2 : P) : (term73 B C P a b p g p1 p2) = (term74 B C P a b p g p1 p2).
Proof. exact (MK_COMB (@lem8220751 B C P a b p g) (@lem8220768 P p1 p2)). Qed.
Lemma lem8220770 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8220771 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8220770 P k x). Qed.
Lemma lem8220772 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8220773 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8220772 P k x). Qed.
Lemma lem8220774 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8220775 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8220776 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8220775) (@lem8220771 P k x)). Qed.
Lemma lem8220777 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8220778 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8220779 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220778 k) (@lem8220777 P k x)). Qed.
Lemma lem8220780 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8220781 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8220782 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8220781) (@lem8220780 k)). Qed.
Lemma lem8220783 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8220784 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220782 k) (@lem8220783 P k x)). Qed.
Lemma lem8220785 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8220779 P k x) (@lem8220784 P k x)). Qed.
Lemma lem8220786 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8220785 P k x) (@lem8220776 P k x)). Qed.
Lemma lem8220787 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8220788 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220787 k) (@lem8220786 P k x)). Qed.
Lemma lem8220789 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8220788 P k x) (@lem8220774 k)). Qed.
Lemma lem8220790 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8220791 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8220792 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8220791 P) (@lem8220773 P k x)). Qed.
Lemma lem8220793 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8220794 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8220795 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220794 P x) (@lem8220793 P k x)). Qed.
Lemma lem8220796 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8220797 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8220798 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8220797 P) (@lem8220796 P x)). Qed.
Lemma lem8220799 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8220800 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220798 P x) (@lem8220799 P k x)). Qed.
Lemma lem8220801 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8220795 P k x) (@lem8220800 P k x)). Qed.
Lemma lem8220802 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8220801 P k x) (@lem8220792 P k x)). Qed.
Lemma lem8220803 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8220804 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220803 P x) (@lem8220802 P k x)). Qed.
Lemma lem8220805 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8220804 P k x) (@lem8220790 P x)). Qed.
Lemma lem8220806 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term85 B C P a b p g) = (term85 B C P a b p g).
Proof. exact (eq_refl (term85 B C P a b p g)). Qed.
Lemma lem8220807 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term86 B C P a b p g k) = (term87 B C P a b p g k x).
Proof. exact (MK_COMB (@lem8220806 B C P a b p g) (@lem8220789 P k x)). Qed.
Lemma lem8220808 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term87 B C P a b p g k x) = (term88 B C P a k x b p g).
Proof. exact (eq_refl (term87 B C P a b p g k x)). Qed.
Lemma lem8220809 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) : (term89 B C P a b p g k) = (term89 B C P a b p g k).
Proof. exact (eq_refl (term89 B C P a b p g k)). Qed.
Lemma lem8220810 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : ((term86 B C P a b p g k) = (term87 B C P a b p g k x)) = ((term86 B C P a b p g k) = (term88 B C P a k x b p g)).
Proof. exact (MK_COMB (@lem8220809 B C P a b p g k) (@lem8220808 B C P a k x b p g)). Qed.
Lemma lem8220811 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term86 B C P a b p g k) = (term90 B C P a k b p g).
Proof. exact (eq_refl (term86 B C P a b p g k)). Qed.
Lemma lem8220812 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8220813 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term89 B C P a b p g k) = (term91 B C P a k b p g).
Proof. exact (MK_COMB (@lem8220812 P) (@lem8220811 B C P a k b p g)). Qed.
Lemma lem8220814 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term88 B C P a k x b p g) = (term88 B C P a k x b p g).
Proof. exact (eq_refl (term88 B C P a k x b p g)). Qed.
Lemma lem8220815 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : ((term86 B C P a b p g k) = (term88 B C P a k x b p g)) = ((term90 B C P a k b p g) = (term88 B C P a k x b p g)).
Proof. exact (MK_COMB (@lem8220813 B C P a k b p g) (@lem8220814 B C P a k x b p g)). Qed.
Lemma lem8220816 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : ((term86 B C P a b p g k) = (term87 B C P a b p g k x)) = ((term90 B C P a k b p g) = (term88 B C P a k x b p g)).
Proof. exact (TRANS (@lem8220810 B C P a k x b p g) (@lem8220815 B C P a k x b p g)). Qed.
Lemma lem8220817 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term90 B C P a k b p g) = (term88 B C P a k x b p g).
Proof. exact (EQ_MP (@lem8220816 B C P a k x b p g) (@lem8220807 B C P a b p g k x)). Qed.
Lemma lem8220818 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term92 B C P a k b p g x) = (term93 B C P a b p g k x).
Proof. exact (MK_COMB (@lem8220817 B C P a k x b p g) (@lem8220805 P k x)). Qed.
Lemma lem8220819 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term93 B C P a b p g k x) = (term94 B C P a b p g k x).
Proof. exact (eq_refl (term93 B C P a b p g k x)). Qed.
Lemma lem8220820 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term95 B C P a k b p g x) = (term95 B C P a k b p g x).
Proof. exact (eq_refl (term95 B C P a k b p g x)). Qed.
Lemma lem8220821 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p g x) = (term93 B C P a b p g k x)) = ((term92 B C P a k b p g x) = (term94 B C P a b p g k x)).
Proof. exact (MK_COMB (@lem8220820 B C P a k b p g x) (@lem8220819 B C P a b p g k x)). Qed.
Lemma lem8220822 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term92 B C P a k b p g x) = (term96 B C P a k b p g x).
Proof. exact (eq_refl (term92 B C P a k b p g x)). Qed.
Lemma lem8220823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8220824 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term95 B C P a k b p g x) = (term97 B C P a k b p g x).
Proof. exact (MK_COMB (@lem8220823) (@lem8220822 B C P a k b p g x)). Qed.
Lemma lem8220825 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term94 B C P a b p g k x) = (term94 B C P a b p g k x).
Proof. exact (eq_refl (term94 B C P a b p g k x)). Qed.
Lemma lem8220826 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p g x) = (term94 B C P a b p g k x)) = ((term96 B C P a k b p g x) = (term94 B C P a b p g k x)).
Proof. exact (MK_COMB (@lem8220824 B C P a k b p g x) (@lem8220825 B C P a b p g k x)). Qed.
Lemma lem8220827 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p g x) = (term93 B C P a b p g k x)) = ((term96 B C P a k b p g x) = (term94 B C P a b p g k x)).
Proof. exact (TRANS (@lem8220821 B C P a b p g k x) (@lem8220826 B C P a b p g k x)). Qed.
Lemma lem8220828 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term96 B C P a k b p g x) = (term94 B C P a b p g k x).
Proof. exact (EQ_MP (@lem8220827 B C P a b p g k x) (@lem8220818 B C P a b p g k x)). Qed.
Lemma lem8220829 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term94 B C P a b p g k x) = (term96 B C P a k b p g x).
Proof. exact (SYM (@lem8220828 B C P a b p g k x)). Qed.
Lemma lem8220830 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term98 B C P a b p g k x) = (term94 B C P a b p g k x).
Proof. exact (eq_refl (term98 B C P a b p g k x)). Qed.
Lemma lem8220831 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term98 B C P a b p g k x) = (term96 B C P a k b p g x).
Proof. exact (TRANS (@lem8220830 B C P a b p g k x) (@lem8220829 B C P a k b p g x)). Qed.
Lemma lem8220832 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term99 B C P a k b p g.
Proof. exact (fun x : P => @lem8220831 B C P a k b p g x). Qed.
Lemma lem8220833 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term100 B C P a b p g.
Proof. exact (fun k : nat => @lem8220832 B C P a k b p g). Qed.
Lemma lem8220834 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term101 B C P a b p g.
Proof. exact (ex_intro (term102 B C P a b p g) (term103 B C P a b p g) (@lem8220833 B C P a b p g)). Qed.
Lemma lem8220836 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8220837 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8220836 Prop a b). Qed.
Lemma lem8220838 {B C P : Type'} (_109288 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : ((term104 P _109288 k x) = (term96 B C P a k b p g x)) = (term105 B C P _109288 a k b p g x).
Proof. exact (@lem8220837 (term104 P _109288 k x) (term96 B C P a k b p g x)). Qed.
Lemma lem8220839 {B C P : Type'} (_109288 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term106 B C P _109288 a k b p g) = (term107 B C P _109288 a k b p g).
Proof. exact (fun_ext (fun x : P => @lem8220838 B C P _109288 a k b p g x)). Qed.
Lemma lem8220840 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8220841 {B C P : Type'} (_109288 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term108 B C P _109288 a k b p g) = (term109 B C P _109288 a k b p g).
Proof. exact (MK_COMB (@lem8220840 P) (@lem8220839 B C P _109288 a k b p g)). Qed.
Lemma lem8220842 {B C P : Type'} (_109288 : type1310 P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term110 B C P _109288 a b p g) = (term111 B C P _109288 a b p g).
Proof. exact (fun_ext (fun k : nat => @lem8220841 B C P _109288 a k b p g)). Qed.
Lemma lem8220843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8220844 {B C P : Type'} (_109288 : type1310 P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term112 B C P _109288 a b p g) = (term113 B C P _109288 a b p g).
Proof. exact (MK_COMB (@lem8220843) (@lem8220842 B C P _109288 a b p g)). Qed.
Lemma lem8220845 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term102 B C P a b p g) = (term114 B C P a b p g).
Proof. exact (fun_ext (fun _109288 : type1310 P => @lem8220844 B C P _109288 a b p g)). Qed.
Lemma lem8220846 {P : Type'} : (@ex ((prod nat P) -> Prop)) = (@ex ((prod nat P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat P) -> Prop))). Qed.
Lemma lem8220847 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term101 B C P a b p g) = (term115 B C P a b p g).
Proof. exact (MK_COMB (@lem8220846 P) (@lem8220845 B C P a b p g)). Qed.
Lemma lem8220848 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term115 B C P a b p g.
Proof. exact (EQ_MP (@lem8220847 B C P a b p g) (@lem8220834 B C P a b p g)). Qed.
Lemma lem8220850 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8220851 {P : Type'} (P' : type372 P) : term117 P P'.
Proof. exact (@lem8220850 (type1310 P) P'). Qed.
Lemma lem8220852 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term118 B C P a b p g.
Proof. exact (@lem8220851 P (term114 B C P a b p g)). Qed.
Lemma lem8220853 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term119 B C P a b p g.
Proof. exact (@lem8220852 B C P a b p g (@lem8220848 B C P a b p g)). Qed.
Lemma lem8220854 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term119 B C P a b p g) = (term120 B C P a b p g).
Proof. exact (eq_refl (term119 B C P a b p g)). Qed.
Lemma lem8220855 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term120 B C P a b p g.
Proof. exact (EQ_MP (@lem8220854 B C P a b p g) (@lem8220853 B C P a b p g)). Qed.
Lemma lem8220856 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) : term121 B C P a b p g k.
Proof. exact (@lem8220855 B C P a b p g k). Qed.
Lemma lem8220857 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term121 B C P a b p g k) = (term122 B C P a k b p g).
Proof. exact (eq_refl (term121 B C P a b p g k)). Qed.
Lemma lem8220858 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term122 B C P a k b p g.
Proof. exact (EQ_MP (@lem8220857 B C P a k b p g) (@lem8220856 B C P a b p g k)). Qed.
Lemma lem8220859 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : term123 B C P a k b p g x.
Proof. exact (@lem8220858 B C P a k b p g x). Qed.
Lemma lem8220860 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term123 B C P a k b p g x) = (term124 B C P a k b p g x).
Proof. exact (eq_refl (term123 B C P a k b p g x)). Qed.
Lemma lem8220861 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : term124 B C P a k b p g x.
Proof. exact (EQ_MP (@lem8220860 B C P a k b p g x) (@lem8220859 B C P a k b p g x)). Qed.
Lemma lem8220863 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8220864 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8220863 Prop a b). Qed.
Lemma lem8220865 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term124 B C P a k b p g x) = ((term74 B C P a b p g k x) = (term96 B C P a k b p g x)).
Proof. exact (@lem8220864 (term74 B C P a b p g k x) (term96 B C P a k b p g x)). Qed.
Lemma lem8220866 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term74 B C P a b p g k x) = (term96 B C P a k b p g x).
Proof. exact (EQ_MP (@lem8220865 B C P a k b p g x) (@lem8220861 B C P a k b p g x)). Qed.
Lemma lem8220867 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term74 B C P a b p g k x) = (term96 B C P a k b p g x).
Proof. exact (@lem8220866 B C P a k b p g x). Qed.
Lemma lem8220868 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term74 B C P a b p g p1 p2) = (term96 B C P a p1 b p g p2).
Proof. exact (@lem8220867 B C P a p1 b p g p2). Qed.
Lemma lem8220873 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term73 B C P a b p g p1 p2) = (term96 B C P a p1 b p g p2).
Proof. exact (TRANS (@lem8220769 B C P a b p g p1 p2) (@lem8220868 B C P a p1 b p g p2)). Qed.
Lemma lem8220874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8220875 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term125 B C P a b p g p1 p2) = (term126 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8220874) (@lem8220873 B C P a p1 b p g p2)). Qed.
Lemma lem8220884 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8220885 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8220884 P k x). Qed.
Lemma lem8220886 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8220887 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8220886 P k x). Qed.
Lemma lem8220888 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8220889 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8220890 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8220889) (@lem8220885 P k x)). Qed.
Lemma lem8220891 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8220892 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8220893 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220892 k) (@lem8220891 P k x)). Qed.
Lemma lem8220894 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8220895 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8220896 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8220895) (@lem8220894 k)). Qed.
Lemma lem8220897 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8220898 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220896 k) (@lem8220897 P k x)). Qed.
Lemma lem8220899 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8220893 P k x) (@lem8220898 P k x)). Qed.
Lemma lem8220900 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8220899 P k x) (@lem8220890 P k x)). Qed.
Lemma lem8220901 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8220902 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8220901 k) (@lem8220900 P k x)). Qed.
Lemma lem8220903 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8220902 P k x) (@lem8220888 k)). Qed.
Lemma lem8220904 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8220905 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8220906 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8220905 P) (@lem8220887 P k x)). Qed.
Lemma lem8220907 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8220908 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8220909 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220908 P x) (@lem8220907 P k x)). Qed.
Lemma lem8220910 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8220911 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8220912 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8220911 P) (@lem8220910 P x)). Qed.
Lemma lem8220913 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8220914 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220912 P x) (@lem8220913 P k x)). Qed.
Lemma lem8220915 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8220909 P k x) (@lem8220914 P k x)). Qed.
Lemma lem8220916 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8220915 P k x) (@lem8220906 P k x)). Qed.
Lemma lem8220917 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8220918 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8220917 P x) (@lem8220916 P k x)). Qed.
Lemma lem8220919 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8220918 P k x) (@lem8220904 P x)). Qed.
Lemma lem8220920 {A P : Type'} (s : P -> A) : (term127 A P s) = (term127 A P s).
Proof. exact (eq_refl (term127 A P s)). Qed.
Lemma lem8220921 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term128 A P s k) = (term129 A P s k x).
Proof. exact (MK_COMB (@lem8220920 A P s) (@lem8220903 P k x)). Qed.
Lemma lem8220922 {A P : Type'} (k : nat) (x : P) (s : P -> A) : (term129 A P s k x) = (term130 A P s).
Proof. exact (eq_refl (term129 A P s k x)). Qed.
Lemma lem8220923 {A P : Type'} (s : P -> A) (k : nat) : (term131 A P s k) = (term131 A P s k).
Proof. exact (eq_refl (term131 A P s k)). Qed.
Lemma lem8220924 {A P : Type'} (x : P) (k : nat) (s : P -> A) : ((term128 A P s k) = (term129 A P s k x)) = ((term128 A P s k) = (term130 A P s)).
Proof. exact (MK_COMB (@lem8220923 A P s k) (@lem8220922 A P k x s)). Qed.
Lemma lem8220925 {A P : Type'} (k : nat) (s : P -> A) : (term128 A P s k) = (term130 A P s).
Proof. exact (eq_refl (term128 A P s k)). Qed.
Lemma lem8220926 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8220927 {A P : Type'} (k : nat) (s : P -> A) : (term131 A P s k) = (term132 A P s).
Proof. exact (MK_COMB (@lem8220926 A P) (@lem8220925 A P k s)). Qed.
Lemma lem8220928 {A P : Type'} (s : P -> A) : (term130 A P s) = (term130 A P s).
Proof. exact (eq_refl (term130 A P s)). Qed.
Lemma lem8220929 {A P : Type'} (k : nat) (s : P -> A) : ((term128 A P s k) = (term130 A P s)) = ((term130 A P s) = (term130 A P s)).
Proof. exact (MK_COMB (@lem8220927 A P k s) (@lem8220928 A P s)). Qed.
Lemma lem8220930 {A P : Type'} (k : nat) (x : P) (s : P -> A) : ((term128 A P s k) = (term129 A P s k x)) = ((term130 A P s) = (term130 A P s)).
Proof. exact (TRANS (@lem8220924 A P x k s) (@lem8220929 A P k s)). Qed.
Lemma lem8220931 {A P : Type'} (s : P -> A) : (term130 A P s) = (term130 A P s).
Proof. exact (EQ_MP (@lem8220930 A P (@el nat) (@el P) s) (@lem8220921 A P s (@el nat) (@el P))). Qed.
Lemma lem8220932 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term133 A P s x) = (term134 A P s k x).
Proof. exact (MK_COMB (@lem8220931 A P s) (@lem8220919 P k x)). Qed.
Lemma lem8220933 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term134 A P s k x) = (term135 A P s k x).
Proof. exact (eq_refl (term134 A P s k x)). Qed.
Lemma lem8220934 {A P : Type'} (s : P -> A) (x : P) : (term136 A P s x) = (term136 A P s x).
Proof. exact (eq_refl (term136 A P s x)). Qed.
Lemma lem8220935 {A P : Type'} (s : P -> A) (k : nat) (x : P) : ((term133 A P s x) = (term134 A P s k x)) = ((term133 A P s x) = (term135 A P s k x)).
Proof. exact (MK_COMB (@lem8220934 A P s x) (@lem8220933 A P s k x)). Qed.
Lemma lem8220936 {A P : Type'} (s : P -> A) (x : P) : (term133 A P s x) = (s x).
Proof. exact (eq_refl (term133 A P s x)). Qed.
Lemma lem8220937 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8220938 {A P : Type'} (s : P -> A) (x : P) : (term136 A P s x) = (term137 A P s x).
Proof. exact (MK_COMB (@lem8220937 A) (@lem8220936 A P s x)). Qed.
Lemma lem8220939 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term135 A P s k x) = (term135 A P s k x).
Proof. exact (eq_refl (term135 A P s k x)). Qed.
Lemma lem8220940 {A P : Type'} (s : P -> A) (k : nat) (x : P) : ((term133 A P s x) = (term135 A P s k x)) = ((s x) = (term135 A P s k x)).
Proof. exact (MK_COMB (@lem8220938 A P s x) (@lem8220939 A P s k x)). Qed.
Lemma lem8220941 {A P : Type'} (s : P -> A) (k : nat) (x : P) : ((term133 A P s x) = (term134 A P s k x)) = ((s x) = (term135 A P s k x)).
Proof. exact (TRANS (@lem8220935 A P s k x) (@lem8220940 A P s k x)). Qed.
Lemma lem8220942 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (s x) = (term135 A P s k x).
Proof. exact (EQ_MP (@lem8220941 A P s k x) (@lem8220932 A P s k x)). Qed.
Lemma lem8220943 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term135 A P s k x) = (s x).
Proof. exact (SYM (@lem8220942 A P s k x)). Qed.
Lemma lem8220944 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term138 A P s k x) = (term135 A P s k x).
Proof. exact (eq_refl (term138 A P s k x)). Qed.
Lemma lem8220945 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term138 A P s k x) = (s x).
Proof. exact (TRANS (@lem8220944 A P s k x) (@lem8220943 A P k s x)). Qed.
Lemma lem8220946 {A P : Type'} (k : nat) (s : P -> A) : term139 A P k s.
Proof. exact (fun x : P => @lem8220945 A P k s x). Qed.
Lemma lem8220947 {A P : Type'} (s : P -> A) : term140 A P s.
Proof. exact (fun k : nat => @lem8220946 A P k s). Qed.
Lemma lem8220948 {A P : Type'} (s : P -> A) : term141 A P s.
Proof. exact (ex_intro (term142 A P s) (term143 A P s) (@lem8220947 A P s)). Qed.
Lemma lem8220950 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8220951 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (@lem8220950 A a b). Qed.
Lemma lem8220952 {A P : Type'} (_109300 : type1313 A P) (k : nat) (s : P -> A) (x : P) : ((term144 A P _109300 k x) = (s x)) = (term145 A P _109300 k s x).
Proof. exact (@lem8220951 A (term144 A P _109300 k x) (s x)). Qed.
Lemma lem8220953 {A P : Type'} (_109300 : type1313 A P) (k : nat) (s : P -> A) : (term146 A P _109300 k s) = (term147 A P _109300 k s).
Proof. exact (fun_ext (fun x : P => @lem8220952 A P _109300 k s x)). Qed.
Lemma lem8220954 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8220955 {A P : Type'} (_109300 : type1313 A P) (k : nat) (s : P -> A) : (term148 A P _109300 k s) = (term149 A P _109300 k s).
Proof. exact (MK_COMB (@lem8220954 P) (@lem8220953 A P _109300 k s)). Qed.
Lemma lem8220956 {A P : Type'} (_109300 : type1313 A P) (s : P -> A) : (term150 A P _109300 s) = (term151 A P _109300 s).
Proof. exact (fun_ext (fun k : nat => @lem8220955 A P _109300 k s)). Qed.
Lemma lem8220957 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8220958 {A P : Type'} (_109300 : type1313 A P) (s : P -> A) : (term152 A P _109300 s) = (term153 A P _109300 s).
Proof. exact (MK_COMB (@lem8220957) (@lem8220956 A P _109300 s)). Qed.
Lemma lem8220959 {A P : Type'} (s : P -> A) : (term142 A P s) = (term154 A P s).
Proof. exact (fun_ext (fun _109300 : type1313 A P => @lem8220958 A P _109300 s)). Qed.
Lemma lem8220960 {A P : Type'} : (@ex ((prod nat P) -> A)) = (@ex ((prod nat P) -> A)).
Proof. exact (eq_refl (@ex ((prod nat P) -> A))). Qed.
Lemma lem8220961 {A P : Type'} (s : P -> A) : (term141 A P s) = (term155 A P s).
Proof. exact (MK_COMB (@lem8220960 A P) (@lem8220959 A P s)). Qed.
Lemma lem8220962 {A P : Type'} (s : P -> A) : term155 A P s.
Proof. exact (EQ_MP (@lem8220961 A P s) (@lem8220948 A P s)). Qed.
Lemma lem8220964 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8220965 {A P : Type'} (P' : type375 A P) : term156 A P P'.
Proof. exact (@lem8220964 (type1313 A P) P'). Qed.
Lemma lem8220966 {A P : Type'} (s : P -> A) : term157 A P s.
Proof. exact (@lem8220965 A P (term154 A P s)). Qed.
Lemma lem8220967 {A P : Type'} (s : P -> A) : term158 A P s.
Proof. exact (@lem8220966 A P s (@lem8220962 A P s)). Qed.
Lemma lem8220968 {A P : Type'} (s : P -> A) : (term158 A P s) = (term159 A P s).
Proof. exact (eq_refl (term158 A P s)). Qed.
Lemma lem8220969 {A P : Type'} (s : P -> A) : term159 A P s.
Proof. exact (EQ_MP (@lem8220968 A P s) (@lem8220967 A P s)). Qed.
Lemma lem8220970 {A P : Type'} (s : P -> A) (k : nat) : term160 A P s k.
Proof. exact (@lem8220969 A P s k). Qed.
Lemma lem8220971 {A P : Type'} (k : nat) (s : P -> A) : (term160 A P s k) = (term161 A P k s).
Proof. exact (eq_refl (term160 A P s k)). Qed.
Lemma lem8220972 {A P : Type'} (k : nat) (s : P -> A) : term161 A P k s.
Proof. exact (EQ_MP (@lem8220971 A P k s) (@lem8220970 A P s k)). Qed.
Lemma lem8220973 {A P : Type'} (k : nat) (s : P -> A) (x : P) : term162 A P k s x.
Proof. exact (@lem8220972 A P k s x). Qed.
Lemma lem8220974 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term162 A P k s x) = (term163 A P k s x).
Proof. exact (eq_refl (term162 A P k s x)). Qed.
Lemma lem8220975 {A P : Type'} (k : nat) (s : P -> A) (x : P) : term163 A P k s x.
Proof. exact (EQ_MP (@lem8220974 A P k s x) (@lem8220973 A P k s x)). Qed.
Lemma lem8220977 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8220978 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (@lem8220977 A a b). Qed.
Lemma lem8220979 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term163 A P k s x) = ((term164 A P s k x) = (s x)).
Proof. exact (@lem8220978 A (term164 A P s k x) (s x)). Qed.
Lemma lem8220980 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term164 A P s k x) = (s x).
Proof. exact (EQ_MP (@lem8220979 A P k s x) (@lem8220975 A P k s x)). Qed.
Lemma lem8220981 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term164 A P s k x) = (s x).
Proof. exact (@lem8220980 A P k s x). Qed.
Lemma lem8220982 {A P : Type'} (p1 : nat) (s : P -> A) (p2 : P) : (term164 A P s p1 p2) = (s p2).
Proof. exact (@lem8220981 A P p1 s p2). Qed.
Lemma lem8220983 {A B : Type'} (lt2 : type1470 A B) (z : B) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8220984 {A B P : Type'} (p1 : nat) (lt2 : type1470 A B) (z : B) (s : P -> A) (p2 : P) : (term165 A B P lt2 z s p1 p2) = (term166 A B P lt2 z s p2).
Proof. exact (MK_COMB (@lem8220983 A B lt2 z) (@lem8220982 A P p1 s p2)). Qed.
Lemma lem8220985 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8220986 {A B P : Type'} (p1 : nat) (lt2 : type1470 A B) (z : B) (s : P -> A) (p2 : P) : (term167 A B P lt2 z s p1 p2) = (term168 A B P lt2 z s p2).
Proof. exact (MK_COMB (@lem8220985) (@lem8220984 A B P p1 lt2 z s p2)). Qed.
Lemma lem8220989 {B C : Type'} (f : B -> C) (g : B -> C) (z : B) : ((f z) = (g z)) = ((f z) = (g z)).
Proof. exact (eq_refl ((f z) = (g z))). Qed.
Lemma lem8220990 {A B C P : Type'} (p1 : nat) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term169 A B C P lt2 s p1 p2 f g z) = (term170 A B C P lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8220986 A B P p1 lt2 z s p2) (@lem8220989 B C f g z)). Qed.
Lemma lem8220993 {A B C P : Type'} (p1 : nat) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term171 A B C P lt2 s p1 p2 f g) = (term172 A B C P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8220990 A B C P p1 lt2 s p2 f g z)). Qed.
Lemma lem8220994 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8220995 {A B C P : Type'} (p1 : nat) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term173 A B C P lt2 s p1 p2 f g) = (term174 A B C P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8220994 B) (@lem8220993 A B C P p1 lt2 s p2 f g)). Qed.
Lemma lem8221002 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term175 A B C P a b p lt2 s p1 p2 f g) = (term176 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8220875 B C P a p1 b p g p2) (@lem8220995 A B C P p1 lt2 s p2 f g)). Qed.
Lemma lem8221005 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term177 A B C P a b p lt2 s p1 p2 f g) = (term178 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8220736 B C P a p1 b p f p2) (@lem8221002 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8221008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8221009 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term179 A B C P a b p lt2 s p1 p2 f g) = (term180 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8221008) (@lem8221005 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8221013 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8221014 {B C P : Type'} (f : type544 B C P) (y : B -> C) : (term181 B C P f y) = (f y).
Proof. exact (@lem8221013 (B -> C) (type1312 P) f y). Qed.
Lemma lem8221015 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term182 B C P h f) = (term183 B C P h f).
Proof. exact (@lem8221014 B C P (term44 B C P h) f). Qed.
Lemma lem8221016 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term183 B C P h f) = (term184 B C P h f).
Proof. exact (eq_refl (term183 B C P h f)). Qed.
Lemma lem8221017 {B C P : Type'} (h : type556 B C P) : (term185 B C P h) = (term44 B C P h).
Proof. exact (fun_ext (fun f : B -> C => @lem8221016 B C P h f)). Qed.
Lemma lem8221018 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8221019 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term182 B C P h f) = (term183 B C P h f).
Proof. exact (MK_COMB (@lem8221017 B C P h) (@lem8221018 B C f)). Qed.
Lemma lem8221020 {P : Type'} : (@eq ((prod nat P) -> real)) = (@eq ((prod nat P) -> real)).
Proof. exact (eq_refl (@eq ((prod nat P) -> real))). Qed.
Lemma lem8221021 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term186 B C P h f) = (term187 B C P h f).
Proof. exact (MK_COMB (@lem8221020 P) (@lem8221019 B C P h f)). Qed.
Lemma lem8221022 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term183 B C P h f) = (term184 B C P h f).
Proof. exact (eq_refl (term183 B C P h f)). Qed.
Lemma lem8221023 {B C P : Type'} (h : type556 B C P) (f : B -> C) : ((term182 B C P h f) = (term183 B C P h f)) = ((term183 B C P h f) = (term184 B C P h f)).
Proof. exact (MK_COMB (@lem8221021 B C P h f) (@lem8221022 B C P h f)). Qed.
Lemma lem8221024 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term183 B C P h f) = (term184 B C P h f).
Proof. exact (EQ_MP (@lem8221023 B C P h f) (@lem8221015 B C P h f)). Qed.
Lemma lem8221037 {P : Type'} (p1 : nat) (p2 : P) : (@pair nat P p1 p2) = (@pair nat P p1 p2).
Proof. exact (eq_refl (@pair nat P p1 p2)). Qed.
Lemma lem8221038 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p1 : nat) (p2 : P) : (term188 B C P h f p1 p2) = (term189 B C P h f p1 p2).
Proof. exact (MK_COMB (@lem8221024 B C P h f) (@lem8221037 P p1 p2)). Qed.
Lemma lem8221039 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8221040 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8221039 P k x). Qed.
Lemma lem8221041 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8221042 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8221041 P k x). Qed.
Lemma lem8221043 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8221044 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8221045 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8221044) (@lem8221040 P k x)). Qed.
Lemma lem8221046 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8221047 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8221048 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8221047 k) (@lem8221046 P k x)). Qed.
Lemma lem8221049 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8221050 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8221051 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8221050) (@lem8221049 k)). Qed.
Lemma lem8221052 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8221053 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8221051 k) (@lem8221052 P k x)). Qed.
Lemma lem8221054 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8221048 P k x) (@lem8221053 P k x)). Qed.
Lemma lem8221055 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8221054 P k x) (@lem8221045 P k x)). Qed.
Lemma lem8221056 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8221057 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8221056 k) (@lem8221055 P k x)). Qed.
Lemma lem8221058 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8221057 P k x) (@lem8221043 k)). Qed.
Lemma lem8221059 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8221060 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8221061 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8221060 P) (@lem8221042 P k x)). Qed.
Lemma lem8221062 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8221063 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8221064 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8221063 P x) (@lem8221062 P k x)). Qed.
Lemma lem8221065 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8221066 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8221067 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8221066 P) (@lem8221065 P x)). Qed.
Lemma lem8221068 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8221069 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8221067 P x) (@lem8221068 P k x)). Qed.
Lemma lem8221070 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8221064 P k x) (@lem8221069 P k x)). Qed.
Lemma lem8221071 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8221070 P k x) (@lem8221061 P k x)). Qed.
Lemma lem8221072 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8221073 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8221072 P x) (@lem8221071 P k x)). Qed.
Lemma lem8221074 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8221073 P k x) (@lem8221059 P x)). Qed.
Lemma lem8221075 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term190 B C P h f) = (term190 B C P h f).
Proof. exact (eq_refl (term190 B C P h f)). Qed.
Lemma lem8221076 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term191 B C P h f k) = (term192 B C P h f k x).
Proof. exact (MK_COMB (@lem8221075 B C P h f) (@lem8221058 P k x)). Qed.
Lemma lem8221077 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term192 B C P h f k x) = (term193 B C P h f k x).
Proof. exact (eq_refl (term192 B C P h f k x)). Qed.
Lemma lem8221078 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) : (term194 B C P h f k) = (term194 B C P h f k).
Proof. exact (eq_refl (term194 B C P h f k)). Qed.
Lemma lem8221079 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : ((term191 B C P h f k) = (term192 B C P h f k x)) = ((term191 B C P h f k) = (term193 B C P h f k x)).
Proof. exact (MK_COMB (@lem8221078 B C P h f k) (@lem8221077 B C P h f k x)). Qed.
Lemma lem8221080 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) : (term191 B C P h f k) = (term195 B C P h f k).
Proof. exact (eq_refl (term191 B C P h f k)). Qed.
Lemma lem8221081 {P : Type'} : (@eq (P -> real)) = (@eq (P -> real)).
Proof. exact (eq_refl (@eq (P -> real))). Qed.
Lemma lem8221082 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) : (term194 B C P h f k) = (term196 B C P h f k).
Proof. exact (MK_COMB (@lem8221081 P) (@lem8221080 B C P h f k)). Qed.
Lemma lem8221083 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term193 B C P h f k x) = (term193 B C P h f k x).
Proof. exact (eq_refl (term193 B C P h f k x)). Qed.
Lemma lem8221084 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : ((term191 B C P h f k) = (term193 B C P h f k x)) = ((term195 B C P h f k) = (term193 B C P h f k x)).
Proof. exact (MK_COMB (@lem8221082 B C P h f k) (@lem8221083 B C P h f k x)). Qed.
Lemma lem8221085 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : ((term191 B C P h f k) = (term192 B C P h f k x)) = ((term195 B C P h f k) = (term193 B C P h f k x)).
Proof. exact (TRANS (@lem8221079 B C P h f k x) (@lem8221084 B C P h f k x)). Qed.
Lemma lem8221086 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term195 B C P h f k) = (term193 B C P h f k x).
Proof. exact (EQ_MP (@lem8221085 B C P h f k x) (@lem8221076 B C P h f k x)). Qed.
Lemma lem8221087 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term197 B C P h f k x) = (term198 B C P h f k x).
Proof. exact (MK_COMB (@lem8221086 B C P h f k x) (@lem8221074 P k x)). Qed.
Lemma lem8221088 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term198 B C P h f k x) = (term199 B C P h f k x).
Proof. exact (eq_refl (term198 B C P h f k x)). Qed.
Lemma lem8221089 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term200 B C P h f k x) = (term200 B C P h f k x).
Proof. exact (eq_refl (term200 B C P h f k x)). Qed.
Lemma lem8221090 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : ((term197 B C P h f k x) = (term198 B C P h f k x)) = ((term197 B C P h f k x) = (term199 B C P h f k x)).
Proof. exact (MK_COMB (@lem8221089 B C P h f k x) (@lem8221088 B C P h f k x)). Qed.
Lemma lem8221091 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : (term197 B C P h f k x) = (h f x k).
Proof. exact (eq_refl (term197 B C P h f k x)). Qed.
Lemma lem8221092 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem8221093 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : (term200 B C P h f k x) = (term201 B C P h f x k).
Proof. exact (MK_COMB (@lem8221092) (@lem8221091 B C P h f x k)). Qed.
Lemma lem8221094 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term199 B C P h f k x) = (term199 B C P h f k x).
Proof. exact (eq_refl (term199 B C P h f k x)). Qed.
Lemma lem8221095 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : ((term197 B C P h f k x) = (term199 B C P h f k x)) = ((h f x k) = (term199 B C P h f k x)).
Proof. exact (MK_COMB (@lem8221093 B C P h f x k) (@lem8221094 B C P h f k x)). Qed.
Lemma lem8221096 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : ((term197 B C P h f k x) = (term198 B C P h f k x)) = ((h f x k) = (term199 B C P h f k x)).
Proof. exact (TRANS (@lem8221090 B C P h f k x) (@lem8221095 B C P h f k x)). Qed.
Lemma lem8221097 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (h f x k) = (term199 B C P h f k x).
Proof. exact (EQ_MP (@lem8221096 B C P h f k x) (@lem8221087 B C P h f k x)). Qed.
Lemma lem8221098 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : (term199 B C P h f k x) = (h f x k).
Proof. exact (SYM (@lem8221097 B C P h f k x)). Qed.
Lemma lem8221099 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : (term202 B C P h f k x) = (term199 B C P h f k x).
Proof. exact (eq_refl (term202 B C P h f k x)). Qed.
Lemma lem8221100 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : (term202 B C P h f k x) = (h f x k).
Proof. exact (TRANS (@lem8221099 B C P h f k x) (@lem8221098 B C P h f x k)). Qed.
Lemma lem8221101 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) : term203 B C P h f k.
Proof. exact (fun x : P => @lem8221100 B C P h f x k). Qed.
Lemma lem8221102 {B C P : Type'} (h : type556 B C P) (f : B -> C) : term204 B C P h f.
Proof. exact (fun k : nat => @lem8221101 B C P h f k). Qed.
Lemma lem8221103 {B C P : Type'} (h : type556 B C P) (f : B -> C) : term205 B C P h f.
Proof. exact (ex_intro (term206 B C P h f) (term207 B C P h f) (@lem8221102 B C P h f)). Qed.
Lemma lem8221105 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8221106 (a : real) (b : real) : (a = b) = (@GEQ real a b).
Proof. exact (@lem8221105 real a b). Qed.
Lemma lem8221107 {B C P : Type'} (_109312 : type1312 P) (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : ((term208 P _109312 k x) = (h f x k)) = (term209 B C P _109312 h f x k).
Proof. exact (@lem8221106 (term208 P _109312 k x) (h f x k)). Qed.
Lemma lem8221108 {B C P : Type'} (_109312 : type1312 P) (h : type556 B C P) (f : B -> C) (k : nat) : (term210 B C P _109312 h f k) = (term211 B C P _109312 h f k).
Proof. exact (fun_ext (fun x : P => @lem8221107 B C P _109312 h f x k)). Qed.
Lemma lem8221109 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8221110 {B C P : Type'} (_109312 : type1312 P) (h : type556 B C P) (f : B -> C) (k : nat) : (term212 B C P _109312 h f k) = (term213 B C P _109312 h f k).
Proof. exact (MK_COMB (@lem8221109 P) (@lem8221108 B C P _109312 h f k)). Qed.
Lemma lem8221111 {B C P : Type'} (_109312 : type1312 P) (h : type556 B C P) (f : B -> C) : (term214 B C P _109312 h f) = (term215 B C P _109312 h f).
Proof. exact (fun_ext (fun k : nat => @lem8221110 B C P _109312 h f k)). Qed.
Lemma lem8221112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8221113 {B C P : Type'} (_109312 : type1312 P) (h : type556 B C P) (f : B -> C) : (term216 B C P _109312 h f) = (term217 B C P _109312 h f).
Proof. exact (MK_COMB (@lem8221112) (@lem8221111 B C P _109312 h f)). Qed.
Lemma lem8221114 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term206 B C P h f) = (term218 B C P h f).
Proof. exact (fun_ext (fun _109312 : type1312 P => @lem8221113 B C P _109312 h f)). Qed.
Lemma lem8221115 {P : Type'} : (@ex ((prod nat P) -> real)) = (@ex ((prod nat P) -> real)).
Proof. exact (eq_refl (@ex ((prod nat P) -> real))). Qed.
Lemma lem8221116 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term205 B C P h f) = (term219 B C P h f).
Proof. exact (MK_COMB (@lem8221115 P) (@lem8221114 B C P h f)). Qed.
Lemma lem8221117 {B C P : Type'} (h : type556 B C P) (f : B -> C) : term219 B C P h f.
Proof. exact (EQ_MP (@lem8221116 B C P h f) (@lem8221103 B C P h f)). Qed.
Lemma lem8221119 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8221120 {P : Type'} (P' : type374 P) : term220 P P'.
Proof. exact (@lem8221119 (type1312 P) P'). Qed.
Lemma lem8221121 {B C P : Type'} (h : type556 B C P) (f : B -> C) : term221 B C P h f.
Proof. exact (@lem8221120 P (term218 B C P h f)). Qed.
Lemma lem8221122 {B C P : Type'} (h : type556 B C P) (f : B -> C) : term222 B C P h f.
Proof. exact (@lem8221121 B C P h f (@lem8221117 B C P h f)). Qed.
Lemma lem8221123 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term222 B C P h f) = (term223 B C P h f).
Proof. exact (eq_refl (term222 B C P h f)). Qed.
Lemma lem8221124 {B C P : Type'} (h : type556 B C P) (f : B -> C) : term223 B C P h f.
Proof. exact (EQ_MP (@lem8221123 B C P h f) (@lem8221122 B C P h f)). Qed.
Lemma lem8221125 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) : term224 B C P h f k.
Proof. exact (@lem8221124 B C P h f k). Qed.
Lemma lem8221126 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) : (term224 B C P h f k) = (term225 B C P h f k).
Proof. exact (eq_refl (term224 B C P h f k)). Qed.
Lemma lem8221127 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) : term225 B C P h f k.
Proof. exact (EQ_MP (@lem8221126 B C P h f k) (@lem8221125 B C P h f k)). Qed.
Lemma lem8221128 {B C P : Type'} (h : type556 B C P) (f : B -> C) (k : nat) (x : P) : term226 B C P h f k x.
Proof. exact (@lem8221127 B C P h f k x). Qed.
Lemma lem8221129 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : (term226 B C P h f k x) = (term227 B C P h f x k).
Proof. exact (eq_refl (term226 B C P h f k x)). Qed.
Lemma lem8221130 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : term227 B C P h f x k.
Proof. exact (EQ_MP (@lem8221129 B C P h f x k) (@lem8221128 B C P h f k x)). Qed.
Lemma lem8221132 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8221133 (a : real) (b : real) : (@GEQ real a b) = (a = b).
Proof. exact (@lem8221132 real a b). Qed.
Lemma lem8221134 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : (term227 B C P h f x k) = ((term189 B C P h f k x) = (h f x k)).
Proof. exact (@lem8221133 (term189 B C P h f k x) (h f x k)). Qed.
Lemma lem8221135 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : (term189 B C P h f k x) = (h f x k).
Proof. exact (EQ_MP (@lem8221134 B C P h f x k) (@lem8221130 B C P h f x k)). Qed.
Lemma lem8221136 {B C P : Type'} (h : type556 B C P) (f : B -> C) (x : P) (k : nat) : (term189 B C P h f k x) = (h f x k).
Proof. exact (@lem8221135 B C P h f x k). Qed.
Lemma lem8221137 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term189 B C P h f p1 p2) = (h f p2 p1).
Proof. exact (@lem8221136 B C P h f p2 p1). Qed.
Lemma lem8221138 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term188 B C P h f p1 p2) = (h f p2 p1).
Proof. exact (TRANS (@lem8221038 B C P h f p1 p2) (@lem8221137 B C P h f p2 p1)). Qed.
Lemma lem8221139 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem8221140 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term228 B C P h f p1 p2) = (term201 B C P h f p2 p1).
Proof. exact (MK_COMB (@lem8221139) (@lem8221138 B C P h f p2 p1)). Qed.
Lemma lem8221142 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8221143 {B C P : Type'} (f : type544 B C P) (y : B -> C) : (term181 B C P f y) = (f y).
Proof. exact (@lem8221142 (B -> C) (type1312 P) f y). Qed.
Lemma lem8221144 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term182 B C P h g) = (term183 B C P h g).
Proof. exact (@lem8221143 B C P (term44 B C P h) g). Qed.
Lemma lem8221145 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (term183 B C P h f) = (term184 B C P h f).
Proof. exact (eq_refl (term183 B C P h f)). Qed.
Lemma lem8221146 {B C P : Type'} (h : type556 B C P) : (term185 B C P h) = (term44 B C P h).
Proof. exact (fun_ext (fun f : B -> C => @lem8221145 B C P h f)). Qed.
Lemma lem8221147 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8221148 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term182 B C P h g) = (term183 B C P h g).
Proof. exact (MK_COMB (@lem8221146 B C P h) (@lem8221147 B C g)). Qed.
Lemma lem8221149 {P : Type'} : (@eq ((prod nat P) -> real)) = (@eq ((prod nat P) -> real)).
Proof. exact (eq_refl (@eq ((prod nat P) -> real))). Qed.
Lemma lem8221150 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term186 B C P h g) = (term187 B C P h g).
Proof. exact (MK_COMB (@lem8221149 P) (@lem8221148 B C P h g)). Qed.
Lemma lem8221151 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term183 B C P h g) = (term184 B C P h g).
Proof. exact (eq_refl (term183 B C P h g)). Qed.
Lemma lem8221152 {B C P : Type'} (h : type556 B C P) (g : B -> C) : ((term182 B C P h g) = (term183 B C P h g)) = ((term183 B C P h g) = (term184 B C P h g)).
Proof. exact (MK_COMB (@lem8221150 B C P h g) (@lem8221151 B C P h g)). Qed.
Lemma lem8221153 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term183 B C P h g) = (term184 B C P h g).
Proof. exact (EQ_MP (@lem8221152 B C P h g) (@lem8221144 B C P h g)). Qed.
Lemma lem8221166 {P : Type'} (p1 : nat) (p2 : P) : (@pair nat P p1 p2) = (@pair nat P p1 p2).
Proof. exact (eq_refl (@pair nat P p1 p2)). Qed.
Lemma lem8221167 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p1 : nat) (p2 : P) : (term188 B C P h g p1 p2) = (term189 B C P h g p1 p2).
Proof. exact (MK_COMB (@lem8221153 B C P h g) (@lem8221166 P p1 p2)). Qed.
Lemma lem8221168 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8221169 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8221168 P k x). Qed.
Lemma lem8221170 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8221171 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8221170 P k x). Qed.
Lemma lem8221172 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8221173 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8221174 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8221173) (@lem8221169 P k x)). Qed.
Lemma lem8221175 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8221176 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8221177 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8221176 k) (@lem8221175 P k x)). Qed.
Lemma lem8221178 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8221179 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8221180 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8221179) (@lem8221178 k)). Qed.
Lemma lem8221181 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8221182 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8221180 k) (@lem8221181 P k x)). Qed.
Lemma lem8221183 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8221177 P k x) (@lem8221182 P k x)). Qed.
Lemma lem8221184 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8221183 P k x) (@lem8221174 P k x)). Qed.
Lemma lem8221185 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8221186 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8221185 k) (@lem8221184 P k x)). Qed.
Lemma lem8221187 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8221186 P k x) (@lem8221172 k)). Qed.
Lemma lem8221188 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8221189 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8221190 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8221189 P) (@lem8221171 P k x)). Qed.
Lemma lem8221191 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8221192 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8221193 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8221192 P x) (@lem8221191 P k x)). Qed.
Lemma lem8221194 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8221195 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8221196 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8221195 P) (@lem8221194 P x)). Qed.
Lemma lem8221197 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8221198 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8221196 P x) (@lem8221197 P k x)). Qed.
Lemma lem8221199 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8221193 P k x) (@lem8221198 P k x)). Qed.
Lemma lem8221200 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8221199 P k x) (@lem8221190 P k x)). Qed.
Lemma lem8221201 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8221202 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8221201 P x) (@lem8221200 P k x)). Qed.
Lemma lem8221203 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8221202 P k x) (@lem8221188 P x)). Qed.
Lemma lem8221204 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term190 B C P h g) = (term190 B C P h g).
Proof. exact (eq_refl (term190 B C P h g)). Qed.
Lemma lem8221205 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term191 B C P h g k) = (term192 B C P h g k x).
Proof. exact (MK_COMB (@lem8221204 B C P h g) (@lem8221187 P k x)). Qed.
Lemma lem8221206 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term192 B C P h g k x) = (term193 B C P h g k x).
Proof. exact (eq_refl (term192 B C P h g k x)). Qed.
Lemma lem8221207 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) : (term194 B C P h g k) = (term194 B C P h g k).
Proof. exact (eq_refl (term194 B C P h g k)). Qed.
Lemma lem8221208 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : ((term191 B C P h g k) = (term192 B C P h g k x)) = ((term191 B C P h g k) = (term193 B C P h g k x)).
Proof. exact (MK_COMB (@lem8221207 B C P h g k) (@lem8221206 B C P h g k x)). Qed.
Lemma lem8221209 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) : (term191 B C P h g k) = (term195 B C P h g k).
Proof. exact (eq_refl (term191 B C P h g k)). Qed.
Lemma lem8221210 {P : Type'} : (@eq (P -> real)) = (@eq (P -> real)).
Proof. exact (eq_refl (@eq (P -> real))). Qed.
Lemma lem8221211 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) : (term194 B C P h g k) = (term196 B C P h g k).
Proof. exact (MK_COMB (@lem8221210 P) (@lem8221209 B C P h g k)). Qed.
Lemma lem8221212 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term193 B C P h g k x) = (term193 B C P h g k x).
Proof. exact (eq_refl (term193 B C P h g k x)). Qed.
Lemma lem8221213 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : ((term191 B C P h g k) = (term193 B C P h g k x)) = ((term195 B C P h g k) = (term193 B C P h g k x)).
Proof. exact (MK_COMB (@lem8221211 B C P h g k) (@lem8221212 B C P h g k x)). Qed.
Lemma lem8221214 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : ((term191 B C P h g k) = (term192 B C P h g k x)) = ((term195 B C P h g k) = (term193 B C P h g k x)).
Proof. exact (TRANS (@lem8221208 B C P h g k x) (@lem8221213 B C P h g k x)). Qed.
Lemma lem8221215 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term195 B C P h g k) = (term193 B C P h g k x).
Proof. exact (EQ_MP (@lem8221214 B C P h g k x) (@lem8221205 B C P h g k x)). Qed.
Lemma lem8221216 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term197 B C P h g k x) = (term198 B C P h g k x).
Proof. exact (MK_COMB (@lem8221215 B C P h g k x) (@lem8221203 P k x)). Qed.
Lemma lem8221217 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term198 B C P h g k x) = (term199 B C P h g k x).
Proof. exact (eq_refl (term198 B C P h g k x)). Qed.
Lemma lem8221218 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term200 B C P h g k x) = (term200 B C P h g k x).
Proof. exact (eq_refl (term200 B C P h g k x)). Qed.
Lemma lem8221219 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : ((term197 B C P h g k x) = (term198 B C P h g k x)) = ((term197 B C P h g k x) = (term199 B C P h g k x)).
Proof. exact (MK_COMB (@lem8221218 B C P h g k x) (@lem8221217 B C P h g k x)). Qed.
Lemma lem8221220 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : (term197 B C P h g k x) = (h g x k).
Proof. exact (eq_refl (term197 B C P h g k x)). Qed.
Lemma lem8221221 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem8221222 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : (term200 B C P h g k x) = (term201 B C P h g x k).
Proof. exact (MK_COMB (@lem8221221) (@lem8221220 B C P h g x k)). Qed.
Lemma lem8221223 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term199 B C P h g k x) = (term199 B C P h g k x).
Proof. exact (eq_refl (term199 B C P h g k x)). Qed.
Lemma lem8221224 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : ((term197 B C P h g k x) = (term199 B C P h g k x)) = ((h g x k) = (term199 B C P h g k x)).
Proof. exact (MK_COMB (@lem8221222 B C P h g x k) (@lem8221223 B C P h g k x)). Qed.
Lemma lem8221225 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : ((term197 B C P h g k x) = (term198 B C P h g k x)) = ((h g x k) = (term199 B C P h g k x)).
Proof. exact (TRANS (@lem8221219 B C P h g k x) (@lem8221224 B C P h g k x)). Qed.
Lemma lem8221226 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (h g x k) = (term199 B C P h g k x).
Proof. exact (EQ_MP (@lem8221225 B C P h g k x) (@lem8221216 B C P h g k x)). Qed.
Lemma lem8221227 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : (term199 B C P h g k x) = (h g x k).
Proof. exact (SYM (@lem8221226 B C P h g k x)). Qed.
Lemma lem8221228 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : (term202 B C P h g k x) = (term199 B C P h g k x).
Proof. exact (eq_refl (term202 B C P h g k x)). Qed.
Lemma lem8221229 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : (term202 B C P h g k x) = (h g x k).
Proof. exact (TRANS (@lem8221228 B C P h g k x) (@lem8221227 B C P h g x k)). Qed.
Lemma lem8221230 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) : term203 B C P h g k.
Proof. exact (fun x : P => @lem8221229 B C P h g x k). Qed.
Lemma lem8221231 {B C P : Type'} (h : type556 B C P) (g : B -> C) : term204 B C P h g.
Proof. exact (fun k : nat => @lem8221230 B C P h g k). Qed.
Lemma lem8221232 {B C P : Type'} (h : type556 B C P) (g : B -> C) : term205 B C P h g.
Proof. exact (ex_intro (term206 B C P h g) (term207 B C P h g) (@lem8221231 B C P h g)). Qed.
Lemma lem8221234 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8221235 (a : real) (b : real) : (a = b) = (@GEQ real a b).
Proof. exact (@lem8221234 real a b). Qed.
Lemma lem8221236 {B C P : Type'} (_109324 : type1312 P) (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : ((term208 P _109324 k x) = (h g x k)) = (term209 B C P _109324 h g x k).
Proof. exact (@lem8221235 (term208 P _109324 k x) (h g x k)). Qed.
Lemma lem8221237 {B C P : Type'} (_109324 : type1312 P) (h : type556 B C P) (g : B -> C) (k : nat) : (term210 B C P _109324 h g k) = (term211 B C P _109324 h g k).
Proof. exact (fun_ext (fun x : P => @lem8221236 B C P _109324 h g x k)). Qed.
Lemma lem8221238 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8221239 {B C P : Type'} (_109324 : type1312 P) (h : type556 B C P) (g : B -> C) (k : nat) : (term212 B C P _109324 h g k) = (term213 B C P _109324 h g k).
Proof. exact (MK_COMB (@lem8221238 P) (@lem8221237 B C P _109324 h g k)). Qed.
Lemma lem8221240 {B C P : Type'} (_109324 : type1312 P) (h : type556 B C P) (g : B -> C) : (term214 B C P _109324 h g) = (term215 B C P _109324 h g).
Proof. exact (fun_ext (fun k : nat => @lem8221239 B C P _109324 h g k)). Qed.
Lemma lem8221241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8221242 {B C P : Type'} (_109324 : type1312 P) (h : type556 B C P) (g : B -> C) : (term216 B C P _109324 h g) = (term217 B C P _109324 h g).
Proof. exact (MK_COMB (@lem8221241) (@lem8221240 B C P _109324 h g)). Qed.
Lemma lem8221243 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term206 B C P h g) = (term218 B C P h g).
Proof. exact (fun_ext (fun _109324 : type1312 P => @lem8221242 B C P _109324 h g)). Qed.
Lemma lem8221244 {P : Type'} : (@ex ((prod nat P) -> real)) = (@ex ((prod nat P) -> real)).
Proof. exact (eq_refl (@ex ((prod nat P) -> real))). Qed.
Lemma lem8221245 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term205 B C P h g) = (term219 B C P h g).
Proof. exact (MK_COMB (@lem8221244 P) (@lem8221243 B C P h g)). Qed.
Lemma lem8221246 {B C P : Type'} (h : type556 B C P) (g : B -> C) : term219 B C P h g.
Proof. exact (EQ_MP (@lem8221245 B C P h g) (@lem8221232 B C P h g)). Qed.
Lemma lem8221248 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8221249 {P : Type'} (P' : type374 P) : term220 P P'.
Proof. exact (@lem8221248 (type1312 P) P'). Qed.
Lemma lem8221250 {B C P : Type'} (h : type556 B C P) (g : B -> C) : term221 B C P h g.
Proof. exact (@lem8221249 P (term218 B C P h g)). Qed.
Lemma lem8221251 {B C P : Type'} (h : type556 B C P) (g : B -> C) : term222 B C P h g.
Proof. exact (@lem8221250 B C P h g (@lem8221246 B C P h g)). Qed.
Lemma lem8221252 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (term222 B C P h g) = (term223 B C P h g).
Proof. exact (eq_refl (term222 B C P h g)). Qed.
Lemma lem8221253 {B C P : Type'} (h : type556 B C P) (g : B -> C) : term223 B C P h g.
Proof. exact (EQ_MP (@lem8221252 B C P h g) (@lem8221251 B C P h g)). Qed.
Lemma lem8221254 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) : term224 B C P h g k.
Proof. exact (@lem8221253 B C P h g k). Qed.
Lemma lem8221255 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) : (term224 B C P h g k) = (term225 B C P h g k).
Proof. exact (eq_refl (term224 B C P h g k)). Qed.
Lemma lem8221256 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) : term225 B C P h g k.
Proof. exact (EQ_MP (@lem8221255 B C P h g k) (@lem8221254 B C P h g k)). Qed.
Lemma lem8221257 {B C P : Type'} (h : type556 B C P) (g : B -> C) (k : nat) (x : P) : term226 B C P h g k x.
Proof. exact (@lem8221256 B C P h g k x). Qed.
Lemma lem8221258 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : (term226 B C P h g k x) = (term227 B C P h g x k).
Proof. exact (eq_refl (term226 B C P h g k x)). Qed.
Lemma lem8221259 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : term227 B C P h g x k.
Proof. exact (EQ_MP (@lem8221258 B C P h g x k) (@lem8221257 B C P h g k x)). Qed.
Lemma lem8221261 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8221262 (a : real) (b : real) : (@GEQ real a b) = (a = b).
Proof. exact (@lem8221261 real a b). Qed.
Lemma lem8221263 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : (term227 B C P h g x k) = ((term189 B C P h g k x) = (h g x k)).
Proof. exact (@lem8221262 (term189 B C P h g k x) (h g x k)). Qed.
Lemma lem8221264 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : (term189 B C P h g k x) = (h g x k).
Proof. exact (EQ_MP (@lem8221263 B C P h g x k) (@lem8221259 B C P h g x k)). Qed.
Lemma lem8221265 {B C P : Type'} (h : type556 B C P) (g : B -> C) (x : P) (k : nat) : (term189 B C P h g k x) = (h g x k).
Proof. exact (@lem8221264 B C P h g x k). Qed.
Lemma lem8221266 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term189 B C P h g p1 p2) = (h g p2 p1).
Proof. exact (@lem8221265 B C P h g p2 p1). Qed.
Lemma lem8221267 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term188 B C P h g p1 p2) = (h g p2 p1).
Proof. exact (TRANS (@lem8221167 B C P h g p1 p2) (@lem8221266 B C P h g p2 p1)). Qed.
Lemma lem8221268 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((term188 B C P h f p1 p2) = (term188 B C P h g p1 p2)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (MK_COMB (@lem8221140 B C P h f p2 p1) (@lem8221267 B C P h g p2 p1)). Qed.
Lemma lem8221271 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term57 A B C P a b p lt2 s f h g p1 p2) = (term229 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8221009 A B C P a p1 b p lt2 s p2 f g) (@lem8221268 B C P f h g p2 p1)). Qed.
Lemma lem8221274 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term59 A B C P a b p lt2 s f h g p1) = (term230 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8221271 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8221275 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8221276 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term61 A B C P a b p lt2 s f h g p1) = (term231 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8221275 P) (@lem8221274 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8221283 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term63 A B C P a b p lt2 s f h g) = (term232 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8221276 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8221284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8221285 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term64 A B C P a b p lt2 s f h g) = (term233 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8221284) (@lem8221283 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8221292 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term53 A B C P a b p lt2 s f h g) = (term233 A B C P a b p lt2 s f h g).
Proof. exact (TRANS (@lem8220583 A B C P a b p lt2 s f h g) (@lem8221285 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8221293 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term234 A B C P a b p lt2 s f h) = (term235 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8221292 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8221294 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221295 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term236 A B C P a b p lt2 s f h) = (term237 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8221294 B C) (@lem8221293 A B C P a b p lt2 s f h)). Qed.
Lemma lem8221302 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term238 A B C P a b p lt2 s h) = (term239 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8221295 A B C P a b p lt2 s f h)). Qed.
Lemma lem8221303 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221304 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term41 A B C P a b p lt2 s h) = (term240 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8221303 B C) (@lem8221302 A B C P a b p lt2 s h)). Qed.
Lemma lem8221311 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term40 A B C P lt2 a b p s h) = (term240 A B C P a b p lt2 s h).
Proof. exact (TRANS (@lem8220548 A B C P a b p lt2 s h) (@lem8221304 A B C P a b p lt2 s h)). Qed.
Lemma lem8221312 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8221313 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term241 A B C P lt2 a b p s h) = (term242 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8221312) (@lem8221311 A B C P a b p lt2 s h)). Qed.
Lemma lem8221315 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term38 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8220505 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8220504 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8221316 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (t : type562 B C P) : (@admissible A C B real P lt2 p s t) = (term243 A B C P p lt2 s t).
Proof. exact (@lem8221315 A C B real P p lt2 s t). Qed.
Lemma lem8221317 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term244 A B C P lt2 p s a b h) = (term245 A B C P p lt2 s a b h).
Proof. exact (@lem8221316 A B C P p lt2 s (term246 B C P a b h)). Qed.
Lemma lem8221355 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8221356 {B C P : Type'} (f : type562 B C P) (y : B -> C) : (term247 B C P f y) = (f y).
Proof. exact (@lem8221355 (B -> C) (P -> real) f y). Qed.
Lemma lem8221357 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : (term248 B C P a b h f) = (term249 B C P a b h f).
Proof. exact (@lem8221356 B C P (term246 B C P a b h) f). Qed.
Lemma lem8221358 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : (term249 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (eq_refl (term249 B C P a b h f)). Qed.
Lemma lem8221359 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term251 B C P a b h) = (term246 B C P a b h).
Proof. exact (fun_ext (fun f : B -> C => @lem8221358 B C P a b h f)). Qed.
Lemma lem8221360 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8221361 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : (term248 B C P a b h f) = (term249 B C P a b h f).
Proof. exact (MK_COMB (@lem8221359 B C P a b h) (@lem8221360 B C f)). Qed.
Lemma lem8221362 {P : Type'} : (@eq (P -> real)) = (@eq (P -> real)).
Proof. exact (eq_refl (@eq (P -> real))). Qed.
Lemma lem8221363 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : (term252 B C P a b h f) = (term253 B C P a b h f).
Proof. exact (MK_COMB (@lem8221362 P) (@lem8221361 B C P a b h f)). Qed.
Lemma lem8221364 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : (term249 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (eq_refl (term249 B C P a b h f)). Qed.
Lemma lem8221365 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : ((term248 B C P a b h f) = (term249 B C P a b h f)) = ((term249 B C P a b h f) = (term250 B C P a b h f)).
Proof. exact (MK_COMB (@lem8221363 B C P a b h f) (@lem8221364 B C P a b h f)). Qed.
Lemma lem8221366 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : (term249 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (EQ_MP (@lem8221365 B C P a b h f) (@lem8221357 B C P a b h f)). Qed.
Lemma lem8221367 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8221368 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : (term254 B C P a b h f a') = (term255 B C P a b h f a').
Proof. exact (MK_COMB (@lem8221366 B C P a b h f) (@lem8221367 P a')). Qed.
Lemma lem8221370 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8221371 {P : Type'} (f : P -> real) (y : P) : (term256 P f y) = (f y).
Proof. exact (@lem8221370 P real f y). Qed.
Lemma lem8221372 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : (term257 B C P a b h f a') = (term255 B C P a b h f a').
Proof. exact (@lem8221371 P (term250 B C P a b h f) a'). Qed.
Lemma lem8221373 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (x : P) : (term255 B C P a b h f x) = (term258 B C P a b h f x).
Proof. exact (eq_refl (term255 B C P a b h f x)). Qed.
Lemma lem8221374 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : (term259 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (fun_ext (fun x : P => @lem8221373 B C P a b h f x)). Qed.
Lemma lem8221375 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8221376 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : (term257 B C P a b h f a') = (term255 B C P a b h f a').
Proof. exact (MK_COMB (@lem8221374 B C P a b h f) (@lem8221375 P a')). Qed.
Lemma lem8221377 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem8221378 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : (term260 B C P a b h f a') = (term261 B C P a b h f a').
Proof. exact (MK_COMB (@lem8221377) (@lem8221376 B C P a b h f a')). Qed.
Lemma lem8221379 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : (term255 B C P a b h f a') = (term258 B C P a b h f a').
Proof. exact (eq_refl (term255 B C P a b h f a')). Qed.
Lemma lem8221380 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : ((term257 B C P a b h f a') = (term255 B C P a b h f a')) = ((term255 B C P a b h f a') = (term258 B C P a b h f a')).
Proof. exact (MK_COMB (@lem8221378 B C P a b h f a') (@lem8221379 B C P a b h f a')). Qed.
Lemma lem8221381 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : (term255 B C P a b h f a') = (term258 B C P a b h f a').
Proof. exact (EQ_MP (@lem8221380 B C P a b h f a') (@lem8221372 B C P a b h f a')). Qed.
Lemma lem8221382 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : (term254 B C P a b h f a') = (term258 B C P a b h f a').
Proof. exact (TRANS (@lem8221368 B C P a b h f a') (@lem8221381 B C P a b h f a')). Qed.
Lemma lem8221383 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem8221384 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (a' : P) : (term262 B C P a b h f a') = (term263 B C P a b h f a').
Proof. exact (MK_COMB (@lem8221383) (@lem8221382 B C P a b h f a')). Qed.
Lemma lem8221386 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8221387 {B C P : Type'} (f : type562 B C P) (y : B -> C) : (term247 B C P f y) = (f y).
Proof. exact (@lem8221386 (B -> C) (P -> real) f y). Qed.
Lemma lem8221388 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : (term248 B C P a b h g) = (term249 B C P a b h g).
Proof. exact (@lem8221387 B C P (term246 B C P a b h) g). Qed.
Lemma lem8221389 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) : (term249 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (eq_refl (term249 B C P a b h f)). Qed.
Lemma lem8221390 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term251 B C P a b h) = (term246 B C P a b h).
Proof. exact (fun_ext (fun f : B -> C => @lem8221389 B C P a b h f)). Qed.
Lemma lem8221391 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8221392 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : (term248 B C P a b h g) = (term249 B C P a b h g).
Proof. exact (MK_COMB (@lem8221390 B C P a b h) (@lem8221391 B C g)). Qed.
Lemma lem8221393 {P : Type'} : (@eq (P -> real)) = (@eq (P -> real)).
Proof. exact (eq_refl (@eq (P -> real))). Qed.
Lemma lem8221394 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : (term252 B C P a b h g) = (term253 B C P a b h g).
Proof. exact (MK_COMB (@lem8221393 P) (@lem8221392 B C P a b h g)). Qed.
Lemma lem8221395 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : (term249 B C P a b h g) = (term250 B C P a b h g).
Proof. exact (eq_refl (term249 B C P a b h g)). Qed.
Lemma lem8221396 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : ((term248 B C P a b h g) = (term249 B C P a b h g)) = ((term249 B C P a b h g) = (term250 B C P a b h g)).
Proof. exact (MK_COMB (@lem8221394 B C P a b h g) (@lem8221395 B C P a b h g)). Qed.
Lemma lem8221397 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : (term249 B C P a b h g) = (term250 B C P a b h g).
Proof. exact (EQ_MP (@lem8221396 B C P a b h g) (@lem8221388 B C P a b h g)). Qed.
Lemma lem8221398 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8221399 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : (term254 B C P a b h g a') = (term255 B C P a b h g a').
Proof. exact (MK_COMB (@lem8221397 B C P a b h g) (@lem8221398 P a')). Qed.
Lemma lem8221401 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8221402 {P : Type'} (f : P -> real) (y : P) : (term256 P f y) = (f y).
Proof. exact (@lem8221401 P real f y). Qed.
Lemma lem8221403 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : (term257 B C P a b h g a') = (term255 B C P a b h g a').
Proof. exact (@lem8221402 P (term250 B C P a b h g) a'). Qed.
Lemma lem8221404 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (x : P) : (term255 B C P a b h g x) = (term258 B C P a b h g x).
Proof. exact (eq_refl (term255 B C P a b h g x)). Qed.
Lemma lem8221405 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : (term259 B C P a b h g) = (term250 B C P a b h g).
Proof. exact (fun_ext (fun x : P => @lem8221404 B C P a b h g x)). Qed.
Lemma lem8221406 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8221407 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : (term257 B C P a b h g a') = (term255 B C P a b h g a').
Proof. exact (MK_COMB (@lem8221405 B C P a b h g) (@lem8221406 P a')). Qed.
Lemma lem8221408 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem8221409 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : (term260 B C P a b h g a') = (term261 B C P a b h g a').
Proof. exact (MK_COMB (@lem8221408) (@lem8221407 B C P a b h g a')). Qed.
Lemma lem8221410 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : (term255 B C P a b h g a') = (term258 B C P a b h g a').
Proof. exact (eq_refl (term255 B C P a b h g a')). Qed.
Lemma lem8221411 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : ((term257 B C P a b h g a') = (term255 B C P a b h g a')) = ((term255 B C P a b h g a') = (term258 B C P a b h g a')).
Proof. exact (MK_COMB (@lem8221409 B C P a b h g a') (@lem8221410 B C P a b h g a')). Qed.
Lemma lem8221412 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : (term255 B C P a b h g a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8221411 B C P a b h g a') (@lem8221403 B C P a b h g a')). Qed.
Lemma lem8221413 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : (term254 B C P a b h g a') = (term258 B C P a b h g a').
Proof. exact (TRANS (@lem8221399 B C P a b h g a') (@lem8221412 B C P a b h g a')). Qed.
Lemma lem8221414 {B C P : Type'} (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : ((term254 B C P a b h f a') = (term254 B C P a b h g a')) = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (MK_COMB (@lem8221384 B C P a b h f a') (@lem8221413 B C P a b h g a')). Qed.
Lemma lem8221417 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P) (f : B -> C) (g : B -> C) : (term264 A B C P p lt2 s a f g) = (term264 A B C P p lt2 s a f g).
Proof. exact (eq_refl (term264 A B C P p lt2 s a f g)). Qed.
Lemma lem8221418 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : (term265 A B C P p lt2 s f a b h g a') = (term266 A B C P p lt2 s f a b h g a').
Proof. exact (MK_COMB (@lem8221417 A B C P p lt2 s a' f g) (@lem8221414 B C P f a b h g a')). Qed.
Lemma lem8221421 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : (term267 A B C P p lt2 s f a b h g) = (term268 A B C P p lt2 s f a b h g).
Proof. exact (fun_ext (fun a' : P => @lem8221418 A B C P p lt2 s f a b h g a')). Qed.
Lemma lem8221422 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8221423 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) : (term269 A B C P p lt2 s f a b h g) = (term270 A B C P p lt2 s f a b h g).
Proof. exact (MK_COMB (@lem8221422 P) (@lem8221421 A B C P p lt2 s f a b h g)). Qed.
Lemma lem8221430 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term271 A B C P p lt2 s f a b h) = (term272 A B C P p lt2 s f a b h).
Proof. exact (fun_ext (fun g : B -> C => @lem8221423 A B C P p lt2 s f a b h g)). Qed.
Lemma lem8221431 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221432 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term273 A B C P p lt2 s f a b h) = (term274 A B C P p lt2 s f a b h).
Proof. exact (MK_COMB (@lem8221431 B C) (@lem8221430 A B C P p lt2 s f a b h)). Qed.
Lemma lem8221439 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term275 A B C P p lt2 s a b h) = (term276 A B C P p lt2 s a b h).
Proof. exact (fun_ext (fun f : B -> C => @lem8221432 A B C P p lt2 s f a b h)). Qed.
Lemma lem8221440 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221441 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term245 A B C P p lt2 s a b h) = (term277 A B C P p lt2 s a b h).
Proof. exact (MK_COMB (@lem8221440 B C) (@lem8221439 A B C P p lt2 s a b h)). Qed.
Lemma lem8221448 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term244 A B C P lt2 p s a b h) = (term277 A B C P p lt2 s a b h).
Proof. exact (TRANS (@lem8221317 A B C P p lt2 s a b h) (@lem8221441 A B C P p lt2 s a b h)). Qed.
Lemma lem8221449 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) : (term278 A B C P lt2 p s a b h) = (term279 A B C P p lt2 s a b h).
Proof. exact (MK_COMB (@lem8221313 A B C P a b p lt2 s h) (@lem8221448 A B C P p lt2 s a b h)). Qed.
Lemma lem8221452 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (h : type556 B C P) : (term280 A B C P lt2 p s a h) = (term281 A B C P p lt2 s a h).
Proof. exact (fun_ext (fun b : P -> nat => @lem8221449 A B C P p lt2 s a b h)). Qed.
Lemma lem8221453 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8221454 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (h : type556 B C P) : (term282 A B C P lt2 p s a h) = (term283 A B C P p lt2 s a h).
Proof. exact (MK_COMB (@lem8221453 P) (@lem8221452 A B C P p lt2 s a h)). Qed.
Lemma lem8221461 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term284 A B C P lt2 p s h) = (term285 A B C P p lt2 s h).
Proof. exact (fun_ext (fun a : P -> nat => @lem8221454 A B C P p lt2 s a h)). Qed.
Lemma lem8221462 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8221463 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term286 A B C P lt2 p s h) = (term287 A B C P p lt2 s h).
Proof. exact (MK_COMB (@lem8221462 P) (@lem8221461 A B C P p lt2 s h)). Qed.
Lemma lem8221470 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) : (term288 A B C P lt2 p s) = (term289 A B C P p lt2 s).
Proof. exact (fun_ext (fun h : type556 B C P => @lem8221463 A B C P p lt2 s h)). Qed.
Lemma lem8221471 {B C P : Type'} : (@all ((B -> C) -> P -> nat -> real)) = (@all ((B -> C) -> P -> nat -> real)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> nat -> real))). Qed.
Lemma lem8221472 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) : (term290 A B C P lt2 p s) = (term291 A B C P p lt2 s).
Proof. exact (MK_COMB (@lem8221471 B C P) (@lem8221470 A B C P p lt2 s)). Qed.
Lemma lem8221479 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) : (term292 A B C P lt2 p) = (term293 A B C P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8221472 A B C P p lt2 s)). Qed.
Lemma lem8221480 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8221481 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) : (term294 A B C P lt2 p) = (term295 A B C P p lt2).
Proof. exact (MK_COMB (@lem8221480 A P) (@lem8221479 A B C P p lt2)). Qed.
Lemma lem8221488 {A B C P : Type'} (lt2 : type1470 A B) : (term296 A B C P lt2) = (term297 A B C P lt2).
Proof. exact (fun_ext (fun p : type560 B C P => @lem8221481 A B C P p lt2)). Qed.
Lemma lem8221489 {B C P : Type'} : (@all ((B -> C) -> P -> Prop)) = (@all ((B -> C) -> P -> Prop)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> Prop))). Qed.
Lemma lem8221490 {A B C P : Type'} (lt2 : type1470 A B) : (term298 A B C P lt2) = (term299 A B C P lt2).
Proof. exact (MK_COMB (@lem8221489 B C P) (@lem8221488 A B C P lt2)). Qed.
Lemma lem8221497 {A B C P : Type'} : (term300 A B C P) = (term301 A B C P).
Proof. exact (fun_ext (fun lt2 : type1470 A B => @lem8221490 A B C P lt2)). Qed.
Lemma lem8221498 {A B : Type'} : (@all (B -> A -> Prop)) = (@all (B -> A -> Prop)).
Proof. exact (eq_refl (@all (B -> A -> Prop))). Qed.
Lemma lem8221499 {A B C P : Type'} : (term302 A B C P) = (term303 A B C P).
Proof. exact (MK_COMB (@lem8221498 A B) (@lem8221497 A B C P)). Qed.
Lemma lem8221506 {A B C P : Type'} : (term303 A B C P) = (term302 A B C P).
Proof. exact (SYM (@lem8221499 A B C P)). Qed.
Lemma lem8221507 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term240 A B C P a b p lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8221508 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term304 A B C P p lt2 s a' f g) : term304 A B C P p lt2 s a' f g.
Proof. exact (h1). Qed.
Lemma lem8221509 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term305 A B C P p lt2 s a' f g) : term305 A B C P p lt2 s a' f g.
Proof. exact (h1). Qed.
Lemma lem8221510 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : p f a'.
Proof. exact (h1). Qed.
Lemma lem8221511 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term174 A B C P lt2 s a' f g.
Proof. exact (h1). Qed.
Lemma lem8221512 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : p g a'.
Proof. exact (h1). Qed.
Lemma lem8221514 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : term15 f m n g.
Proof. exact (EQ_MP (@lem8220490 f m n g) (@lem8220489 f m n g)). Qed.
Lemma lem8221515 {B C P : Type'} (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type556 B C P) (g : B -> C) (a' : P) : term306 B C P f a b h g a'.
Proof. exact (@lem8221514 (h f a') (a a') (b a') (h g a')). Qed.
Lemma lem8221517 (p : Prop) : p = (term307 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8221518 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term308 B C P a b f h g a') = (term309 B C P a b f h g a').
Proof. exact (@lem8221517 (term308 B C P a b f h g a')). Qed.
Lemma lem8221519 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term309 B C P a b f h g a') = (term308 B C P a b f h g a').
Proof. exact (SYM (@lem8221518 B C P a b f h g a')). Qed.
Lemma lem8221520 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term310 B C P a b f h g a') : term310 B C P a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8221523 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8221524 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term311 A B C P p lt2 s a b f h g a' => @lem8221523 A B C P p lt2 s a b f h g a' h0). Qed.
Lemma lem8221525 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term312 A B C P p lt2 s a b f h g a') : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8221526 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8221527 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') (h2 : term312 A B C P p lt2 s a b f h g a') : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8221525 A B C P p lt2 s a b f h g a' h2 (@lem8221526 A B C P p lt2 s a b f h g a' h1)). Qed.
Lemma lem8221528 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') : term313 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term312 A B C P p lt2 s a b f h g a' => @lem8221527 A B C P p lt2 s a b f h g a' h1 h0). Qed.
Lemma lem8221529 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term312 A B C P p lt2 s a b f h g a') : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8221530 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') (h2 : term312 A B C P p lt2 s a b f h g a') : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8221528 A B C P p lt2 s a b f h g a' h1 (@lem8221529 A B C P p lt2 s a b f h g a' h2)). Qed.
Lemma lem8221531 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (h1 : term312 A B C P p lt2 s a b f h g a') : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term311 A B C P p lt2 s a b f h g a' => @lem8221530 A B C P p lt2 s a b f h g a' h0 h1). Qed.
Lemma lem8221532 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term314 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term312 A B C P p lt2 s a b f h g a' => @lem8221531 A B C P p lt2 s a b f h g a' h0). Qed.
Lemma lem8221535 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8221532 A B C P p lt2 s a b f h g a' (@lem8221524 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8221536 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8221535 A B C P p lt2 s a b f h g a'). Qed.
Lemma lem8221624 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8221625 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term309 B C P a b f h g a') = (term315 B C P a b f h g a').
Proof. exact (@lem8221624 (term310 B C P a b f h g a')). Qed.
Lemma lem8221627 (t : Prop) : (term316 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8221628 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term315 B C P a b f h g a') = (term308 B C P a b f h g a').
Proof. exact (@lem8221627 (term308 B C P a b f h g a')). Qed.
Lemma lem8221633 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term309 B C P a b f h g a') = (term308 B C P a b f h g a').
Proof. exact (TRANS (@lem8221625 B C P a b f h g a') (@lem8221628 B C P a b f h g a')). Qed.
Lemma lem8221638 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term317 A B C P lt2 s a' f g) = (term317 A B C P lt2 s a' f g).
Proof. exact (eq_refl (term317 A B C P lt2 s a' f g)). Qed.
Lemma lem8221639 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term318 A B C P lt2 s a b f h g a') = (term319 A B C P lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221638 A B C P lt2 s a' f g) (@lem8221633 B C P a b f h g a')). Qed.
Lemma lem8221642 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (term320 B C P p g a') = (term320 B C P p g a').
Proof. exact (eq_refl (term320 B C P p g a')). Qed.
Lemma lem8221643 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term321 A B C P p lt2 s a b f h g a') = (term322 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221642 B C P p g a') (@lem8221639 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8221646 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (term320 B C P p f a') = (term320 B C P p f a').
Proof. exact (eq_refl (term320 B C P p f a')). Qed.
Lemma lem8221647 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term323 A B C P p lt2 s a b f h g a') = (term324 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221646 B C P p f a') (@lem8221643 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8221650 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term242 A B C P a b p lt2 s h) = (term242 A B C P a b p lt2 s h).
Proof. exact (eq_refl (term242 A B C P a b p lt2 s h)). Qed.
Lemma lem8221651 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term311 A B C P p lt2 s a b f h g a') = (term325 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221650 A B C P a b p lt2 s h) (@lem8221647 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8221654 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term326 A B C P lt2 s a b f h g a') = (term327 A B C P lt2 s a b f h g a').
Proof. exact (fun_ext (fun p : type560 B C P => @lem8221651 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8221655 {B C P : Type'} : (@all ((B -> C) -> P -> Prop)) = (@all ((B -> C) -> P -> Prop)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> Prop))). Qed.
Lemma lem8221656 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term328 A B C P lt2 s a b f h g a') = (term329 A B C P lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221655 B C P) (@lem8221654 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8221661 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term330 A B C P s a b f h g a') = (term331 A B C P s a b f h g a').
Proof. exact (fun_ext (fun lt2 : type1470 A B => @lem8221656 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8221662 {A B : Type'} : (@all (B -> A -> Prop)) = (@all (B -> A -> Prop)).
Proof. exact (eq_refl (@all (B -> A -> Prop))). Qed.
Lemma lem8221663 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term332 A B C P s a b f h g a') = (term333 A B C P s a b f h g a').
Proof. exact (MK_COMB (@lem8221662 A B) (@lem8221661 A B C P s a b f h g a')). Qed.
Lemma lem8221668 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term334 A B C P a b f h g a') = (term335 A B C P a b f h g a').
Proof. exact (fun_ext (fun s : P -> A => @lem8221663 A B C P s a b f h g a')). Qed.
Lemma lem8221669 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8221670 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term336 A B C P a b f h g a') = (term337 A B C P a b f h g a').
Proof. exact (MK_COMB (@lem8221669 A P) (@lem8221668 A B C P a b f h g a')). Qed.
Lemma lem8221675 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term338 A B C P b f h g a') = (term339 A B C P b f h g a').
Proof. exact (fun_ext (fun a : P -> nat => @lem8221670 A B C P a b f h g a')). Qed.
Lemma lem8221676 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8221677 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term340 A B C P b f h g a') = (term341 A B C P b f h g a').
Proof. exact (MK_COMB (@lem8221676 P) (@lem8221675 A B C P b f h g a')). Qed.
Lemma lem8221682 {A B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term342 A B C P f h g a') = (term343 A B C P f h g a').
Proof. exact (fun_ext (fun b : P -> nat => @lem8221677 A B C P b f h g a')). Qed.
Lemma lem8221683 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8221684 {A B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term344 A B C P f h g a') = (term345 A B C P f h g a').
Proof. exact (MK_COMB (@lem8221683 P) (@lem8221682 A B C P f h g a')). Qed.
Lemma lem8221689 {A B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : (term346 A B C P h g a') = (term347 A B C P h g a').
Proof. exact (fun_ext (fun f : B -> C => @lem8221684 A B C P f h g a')). Qed.
Lemma lem8221690 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221691 {A B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : (term348 A B C P h g a') = (term349 A B C P h g a').
Proof. exact (MK_COMB (@lem8221690 B C) (@lem8221689 A B C P h g a')). Qed.
Lemma lem8221696 {A B C P : Type'} (g : B -> C) (a' : P) : (term350 A B C P g a') = (term351 A B C P g a').
Proof. exact (fun_ext (fun h : type556 B C P => @lem8221691 A B C P h g a')). Qed.
Lemma lem8221697 {B C P : Type'} : (@all ((B -> C) -> P -> nat -> real)) = (@all ((B -> C) -> P -> nat -> real)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> nat -> real))). Qed.
Lemma lem8221698 {A B C P : Type'} (g : B -> C) (a' : P) : (term352 A B C P g a') = (term353 A B C P g a').
Proof. exact (MK_COMB (@lem8221697 B C P) (@lem8221696 A B C P g a')). Qed.
Lemma lem8221703 {A B C P : Type'} (a' : P) : (term354 A B C P a') = (term355 A B C P a').
Proof. exact (fun_ext (fun g : B -> C => @lem8221698 A B C P g a')). Qed.
Lemma lem8221704 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221705 {A B C P : Type'} (a' : P) : (term356 A B C P a') = (term357 A B C P a').
Proof. exact (MK_COMB (@lem8221704 B C) (@lem8221703 A B C P a')). Qed.
Lemma lem8221710 {A B C P : Type'} : (term358 A B C P) = (term359 A B C P).
Proof. exact (fun_ext (fun a' : P => @lem8221705 A B C P a')). Qed.
Lemma lem8221711 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8221720 {A B C P : Type'} : (term360 A B C P) = (term361 A B C P).
Proof. exact (MK_COMB (@lem8221711 P) (@lem8221710 A B C P)). Qed.
Lemma lem8221729 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (term362 B C P a b f h g a' i) = (term362 B C P a b f h g a' i).
Proof. exact (eq_refl (term362 B C P a b f h g a' i)). Qed.
Lemma lem8221730 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term363 B C P a b f h g a') = (term363 B C P a b f h g a').
Proof. exact (fun_ext (fun i : nat => @lem8221729 B C P a b f h g a' i)). Qed.
Lemma lem8221731 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8221732 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term308 B C P a b f h g a') = (term308 B C P a b f h g a').
Proof. exact (MK_COMB (@lem8221731) (@lem8221730 B C P a b f h g a')). Qed.
Lemma lem8221737 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (z : B) : (term170 A B C P lt2 s a' f g z) = (term170 A B C P lt2 s a' f g z).
Proof. exact (eq_refl (term170 A B C P lt2 s a' f g z)). Qed.
Lemma lem8221738 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term172 A B C P lt2 s a' f g) = (term172 A B C P lt2 s a' f g).
Proof. exact (fun_ext (fun z : B => @lem8221737 A B C P lt2 s a' f g z)). Qed.
Lemma lem8221739 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8221740 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term174 A B C P lt2 s a' f g) = (term174 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8221739 B) (@lem8221738 A B C P lt2 s a' f g)). Qed.
Lemma lem8221741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8221742 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term317 A B C P lt2 s a' f g) = (term317 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8221741) (@lem8221740 A B C P lt2 s a' f g)). Qed.
Lemma lem8221743 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term319 A B C P lt2 s a b f h g a') = (term319 A B C P lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221742 A B C P lt2 s a' f g) (@lem8221732 B C P a b f h g a')). Qed.
Lemma lem8221746 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (term320 B C P p g a') = (term320 B C P p g a').
Proof. exact (eq_refl (term320 B C P p g a')). Qed.
Lemma lem8221747 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term322 A B C P p lt2 s a b f h g a') = (term322 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221746 B C P p g a') (@lem8221743 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8221750 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (term320 B C P p f a') = (term320 B C P p f a').
Proof. exact (eq_refl (term320 B C P p f a')). Qed.
Lemma lem8221751 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term324 A B C P p lt2 s a b f h g a') = (term324 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221750 B C P p f a') (@lem8221747 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8221752 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8221757 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term170 A B C P lt2 s p2 f g z) = (term170 A B C P lt2 s p2 f g z).
Proof. exact (eq_refl (term170 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8221758 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term172 A B C P lt2 s p2 f g) = (term172 A B C P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8221757 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8221759 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8221760 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term174 A B C P lt2 s p2 f g) = (term174 A B C P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8221759 B) (@lem8221758 A B C P lt2 s p2 f g)). Qed.
Lemma lem8221771 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term126 B C P a p1 b p g p2) = (term126 B C P a p1 b p g p2).
Proof. exact (eq_refl (term126 B C P a p1 b p g p2)). Qed.
Lemma lem8221772 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term176 A B C P a p1 b p lt2 s p2 f g) = (term176 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8221771 B C P a p1 b p g p2) (@lem8221760 A B C P lt2 s p2 f g)). Qed.
Lemma lem8221783 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term126 B C P a p1 b p f p2) = (term126 B C P a p1 b p f p2).
Proof. exact (eq_refl (term126 B C P a p1 b p f p2)). Qed.
Lemma lem8221784 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term178 A B C P a p1 b p lt2 s p2 f g) = (term178 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8221783 B C P a p1 b p f p2) (@lem8221772 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8221785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8221786 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term180 A B C P a p1 b p lt2 s p2 f g) = (term180 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8221785) (@lem8221784 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8221787 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term229 A B C P a b p lt2 s f h g p2 p1) = (term229 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8221786 A B C P a p1 b p lt2 s p2 f g) (@lem8221752 B C P f h g p2 p1)). Qed.
Lemma lem8221788 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term230 A B C P a b p lt2 s f h g p1) = (term230 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8221787 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8221789 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8221790 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term231 A B C P a b p lt2 s f h g p1) = (term231 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8221789 P) (@lem8221788 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8221791 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term232 A B C P a b p lt2 s f h g) = (term232 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8221790 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8221792 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8221793 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term233 A B C P a b p lt2 s f h g) = (term233 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8221792) (@lem8221791 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8221794 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term235 A B C P a b p lt2 s f h) = (term235 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8221793 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8221795 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221796 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term237 A B C P a b p lt2 s f h) = (term237 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8221795 B C) (@lem8221794 A B C P a b p lt2 s f h)). Qed.
Lemma lem8221797 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term239 A B C P a b p lt2 s h) = (term239 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8221796 A B C P a b p lt2 s f h)). Qed.
Lemma lem8221798 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221799 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term240 A B C P a b p lt2 s h) = (term240 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8221798 B C) (@lem8221797 A B C P a b p lt2 s h)). Qed.
Lemma lem8221800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8221801 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term242 A B C P a b p lt2 s h) = (term242 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8221800) (@lem8221799 A B C P a b p lt2 s h)). Qed.
Lemma lem8221802 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term325 A B C P p lt2 s a b f h g a') = (term325 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221801 A B C P a b p lt2 s h) (@lem8221751 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8221803 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term327 A B C P lt2 s a b f h g a') = (term327 A B C P lt2 s a b f h g a').
Proof. exact (fun_ext (fun p : type560 B C P => @lem8221802 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8221804 {B C P : Type'} : (@all ((B -> C) -> P -> Prop)) = (@all ((B -> C) -> P -> Prop)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> Prop))). Qed.
Lemma lem8221805 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term329 A B C P lt2 s a b f h g a') = (term329 A B C P lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8221804 B C P) (@lem8221803 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8221806 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term331 A B C P s a b f h g a') = (term331 A B C P s a b f h g a').
Proof. exact (fun_ext (fun lt2 : type1470 A B => @lem8221805 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8221807 {A B : Type'} : (@all (B -> A -> Prop)) = (@all (B -> A -> Prop)).
Proof. exact (eq_refl (@all (B -> A -> Prop))). Qed.
Lemma lem8221808 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term333 A B C P s a b f h g a') = (term333 A B C P s a b f h g a').
Proof. exact (MK_COMB (@lem8221807 A B) (@lem8221806 A B C P s a b f h g a')). Qed.
Lemma lem8221809 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term335 A B C P a b f h g a') = (term335 A B C P a b f h g a').
Proof. exact (fun_ext (fun s : P -> A => @lem8221808 A B C P s a b f h g a')). Qed.
Lemma lem8221810 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8221811 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term337 A B C P a b f h g a') = (term337 A B C P a b f h g a').
Proof. exact (MK_COMB (@lem8221810 A P) (@lem8221809 A B C P a b f h g a')). Qed.
Lemma lem8221812 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term339 A B C P b f h g a') = (term339 A B C P b f h g a').
Proof. exact (fun_ext (fun a : P -> nat => @lem8221811 A B C P a b f h g a')). Qed.
Lemma lem8221813 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8221814 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term341 A B C P b f h g a') = (term341 A B C P b f h g a').
Proof. exact (MK_COMB (@lem8221813 P) (@lem8221812 A B C P b f h g a')). Qed.
Lemma lem8221815 {A B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term343 A B C P f h g a') = (term343 A B C P f h g a').
Proof. exact (fun_ext (fun b : P -> nat => @lem8221814 A B C P b f h g a')). Qed.
Lemma lem8221816 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8221817 {A B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term345 A B C P f h g a') = (term345 A B C P f h g a').
Proof. exact (MK_COMB (@lem8221816 P) (@lem8221815 A B C P f h g a')). Qed.
Lemma lem8221818 {A B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : (term347 A B C P h g a') = (term347 A B C P h g a').
Proof. exact (fun_ext (fun f : B -> C => @lem8221817 A B C P f h g a')). Qed.
Lemma lem8221819 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221820 {A B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : (term349 A B C P h g a') = (term349 A B C P h g a').
Proof. exact (MK_COMB (@lem8221819 B C) (@lem8221818 A B C P h g a')). Qed.
Lemma lem8221821 {A B C P : Type'} (g : B -> C) (a' : P) : (term351 A B C P g a') = (term351 A B C P g a').
Proof. exact (fun_ext (fun h : type556 B C P => @lem8221820 A B C P h g a')). Qed.
Lemma lem8221822 {B C P : Type'} : (@all ((B -> C) -> P -> nat -> real)) = (@all ((B -> C) -> P -> nat -> real)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> nat -> real))). Qed.
Lemma lem8221823 {A B C P : Type'} (g : B -> C) (a' : P) : (term353 A B C P g a') = (term353 A B C P g a').
Proof. exact (MK_COMB (@lem8221822 B C P) (@lem8221821 A B C P g a')). Qed.
Lemma lem8221824 {A B C P : Type'} (a' : P) : (term355 A B C P a') = (term355 A B C P a').
Proof. exact (fun_ext (fun g : B -> C => @lem8221823 A B C P g a')). Qed.
Lemma lem8221825 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8221826 {A B C P : Type'} (a' : P) : (term357 A B C P a') = (term357 A B C P a').
Proof. exact (MK_COMB (@lem8221825 B C) (@lem8221824 A B C P a')). Qed.
Lemma lem8221827 {A B C P : Type'} : (term359 A B C P) = (term359 A B C P).
Proof. exact (fun_ext (fun a' : P => @lem8221826 A B C P a')). Qed.
Lemma lem8221828 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8221829 {A B C P : Type'} : (term361 A B C P) = (term361 A B C P).
Proof. exact (MK_COMB (@lem8221828 P) (@lem8221827 A B C P)). Qed.
Lemma lem8221958 {A B C P : Type'} : (term360 A B C P) = (term361 A B C P).
Proof. exact (TRANS (@lem8221720 A B C P) (@lem8221829 A B C P)). Qed.
Lemma lem8221959 {A B C P : Type'} : (term361 A B C P) = (term360 A B C P).
Proof. exact (SYM (@lem8221958 A B C P)). Qed.
Lemma lem8221960 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term240 A B C P a b p lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8221963 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term174 A B C P lt2 s a' f g.
Proof. exact (h1). Qed.
Lemma lem8221966 (p : Prop) : p = (term307 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8221967 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : ((h f a' i) = (h g a' i)) = (term364 B C P f h g a' i).
Proof. exact (@lem8221966 ((h f a' i) = (h g a' i))). Qed.
Lemma lem8221968 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (term364 B C P f h g a' i) = ((h f a' i) = (h g a' i)).
Proof. exact (SYM (@lem8221967 B C P f h g a' i)). Qed.
Lemma lem8221969 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term365 B C P f h g a' i) : term365 B C P f h g a' i.
Proof. exact (h1). Qed.
Lemma lem8221977 {B C P : Type'} (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term366 B C P p1 b p f p2) = (term367 B C P p1 b p f p2).
Proof. exact (@lem17045 (term368 P p1 b p2) (p f p2)). Qed.
Lemma lem8221979 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term369 P a p2 p1) = (term369 P a p2 p1).
Proof. exact (eq_refl (term369 P a p2 p1)). Qed.
Lemma lem8221980 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term370 B C P a p1 b p f p2) = (term371 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8221979 P a p2 p1) (@lem8221977 B C P p1 b p f p2)). Qed.
Lemma lem8221981 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term372 B C P a p1 b p f p2) = (term370 B C P a p1 b p f p2).
Proof. exact (@lem17045 (term373 P a p2 p1) (term374 B C P p1 b p f p2)). Qed.
Lemma lem8221982 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term372 B C P a p1 b p f p2) = (term371 B C P a p1 b p f p2).
Proof. exact (TRANS (@lem8221981 B C P a p1 b p f p2) (@lem8221980 B C P a p1 b p f p2)). Qed.
Lemma lem8221990 {B C P : Type'} (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term366 B C P p1 b p g p2) = (term367 B C P p1 b p g p2).
Proof. exact (@lem17045 (term368 P p1 b p2) (p g p2)). Qed.
Lemma lem8221992 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term369 P a p2 p1) = (term369 P a p2 p1).
Proof. exact (eq_refl (term369 P a p2 p1)). Qed.
Lemma lem8221993 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term370 B C P a p1 b p g p2) = (term371 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8221992 P a p2 p1) (@lem8221990 B C P p1 b p g p2)). Qed.
Lemma lem8221994 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term372 B C P a p1 b p g p2) = (term370 B C P a p1 b p g p2).
Proof. exact (@lem17045 (term373 P a p2 p1) (term374 B C P p1 b p g p2)). Qed.
Lemma lem8221995 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term372 B C P a p1 b p g p2) = (term371 B C P a p1 b p g p2).
Proof. exact (TRANS (@lem8221994 B C P a p1 b p g p2) (@lem8221993 B C P a p1 b p g p2)). Qed.
Lemma lem8222002 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term375 A B C P lt2 s p2 f g z) = (term376 A B C P lt2 s p2 f g z).
Proof. exact (@lem17362 (term166 A B P lt2 z s p2) ((f z) = (g z))). Qed.
Lemma lem8222003 {B : Type'} (P : B -> Prop) : (term377 B P) = (term378 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem8222004 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term379 A B C P lt2 s p2 f g) = (term380 A B C P lt2 s p2 f g).
Proof. exact (@lem8222003 B (term172 A B C P lt2 s p2 f g)). Qed.
Lemma lem8222005 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term381 A B C P lt2 s p2 f g z) = (term170 A B C P lt2 s p2 f g z).
Proof. exact (eq_refl (term381 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8222006 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222007 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term382 A B C P lt2 s p2 f g z) = (term375 A B C P lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8222006) (@lem8222005 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8222008 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term382 A B C P lt2 s p2 f g z) = (term376 A B C P lt2 s p2 f g z).
Proof. exact (TRANS (@lem8222007 A B C P lt2 s p2 f g z) (@lem8222002 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8222009 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term383 A B C P lt2 s p2 f g) = (term384 A B C P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8222008 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8222010 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8222011 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term380 A B C P lt2 s p2 f g) = (term385 A B C P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222010 B) (@lem8222009 A B C P lt2 s p2 f g)). Qed.
Lemma lem8222012 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term379 A B C P lt2 s p2 f g) = (term385 A B C P lt2 s p2 f g).
Proof. exact (TRANS (@lem8222004 A B C P lt2 s p2 f g) (@lem8222011 A B C P lt2 s p2 f g)). Qed.
Lemma lem8222013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222014 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term386 B C P a p1 b p g p2) = (term387 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8222013) (@lem8221995 B C P a p1 b p g p2)). Qed.
Lemma lem8222015 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term388 A B C P a p1 b p lt2 s p2 f g) = (term389 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222014 B C P a p1 b p g p2) (@lem8222012 A B C P lt2 s p2 f g)). Qed.
Lemma lem8222016 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term390 A B C P a p1 b p lt2 s p2 f g) = (term388 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (@lem17045 (term96 B C P a p1 b p g p2) (term174 A B C P lt2 s p2 f g)). Qed.
Lemma lem8222017 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term390 A B C P a p1 b p lt2 s p2 f g) = (term389 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (TRANS (@lem8222016 A B C P a p1 b p lt2 s p2 f g) (@lem8222015 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222019 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term386 B C P a p1 b p f p2) = (term387 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8222018) (@lem8221982 B C P a p1 b p f p2)). Qed.
Lemma lem8222020 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term391 A B C P a p1 b p lt2 s p2 f g) = (term392 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222019 B C P a p1 b p f p2) (@lem8222017 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222021 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term393 A B C P a p1 b p lt2 s p2 f g) = (term391 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (@lem17045 (term96 B C P a p1 b p f p2) (term176 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222022 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term393 A B C P a p1 b p lt2 s p2 f g) = (term392 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (TRANS (@lem8222021 A B C P a p1 b p lt2 s p2 f g) (@lem8222020 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222023 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8222024 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222025 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term394 A B C P a p1 b p lt2 s p2 f g) = (term395 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222024) (@lem8222022 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222026 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term396 A B C P a b p lt2 s f h g p2 p1) = (term397 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8222025 A B C P a p1 b p lt2 s p2 f g) (@lem8222023 B C P f h g p2 p1)). Qed.
Lemma lem8222027 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term229 A B C P a b p lt2 s f h g p2 p1) = (term396 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (@lem17265 (term178 A B C P a p1 b p lt2 s p2 f g) ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8222028 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term229 A B C P a b p lt2 s f h g p2 p1) = (term397 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (TRANS (@lem8222027 A B C P a b p lt2 s f h g p2 p1) (@lem8222026 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222029 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term230 A B C P a b p lt2 s f h g p1) = (term398 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8222028 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222030 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8222031 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term231 A B C P a b p lt2 s f h g p1) = (term399 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8222030 P) (@lem8222029 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222032 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term232 A B C P a b p lt2 s f h g) = (term400 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8222031 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222033 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8222034 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term233 A B C P a b p lt2 s f h g) = (term401 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8222033) (@lem8222032 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222035 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term235 A B C P a b p lt2 s f h) = (term402 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8222034 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222036 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8222037 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term237 A B C P a b p lt2 s f h) = (term403 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8222036 B C) (@lem8222035 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222038 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term239 A B C P a b p lt2 s h) = (term404 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8222037 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222039 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8222040 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term240 A B C P a b p lt2 s h) = (term405 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8222039 B C) (@lem8222038 A B C P a b p lt2 s h)). Qed.
Lemma lem8222151 {A : Type'} (P : Prop) (Q : A -> Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8222152 {B : Type'} (P : Prop) (Q : B -> Prop) : (term406 B P Q) = (term407 B P Q).
Proof. exact (@lem8222151 B P Q). Qed.
Lemma lem8222153 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term408 A B C P a p1 b p lt2 s p2 f g) = (term409 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (@lem8222152 B (term371 B C P a p1 b p g p2) (term384 A B C P lt2 s p2 f g)). Qed.
Lemma lem8222154 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term410 A B C P lt2 s p2 f g z) = (term376 A B C P lt2 s p2 f g z).
Proof. exact (eq_refl (term410 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8222155 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term411 A B C P lt2 s p2 f g) = (term384 A B C P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8222154 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8222156 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8222157 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term412 A B C P lt2 s p2 f g) = (term385 A B C P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222156 B) (@lem8222155 A B C P lt2 s p2 f g)). Qed.
Lemma lem8222158 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term387 B C P a p1 b p g p2) = (term387 B C P a p1 b p g p2).
Proof. exact (eq_refl (term387 B C P a p1 b p g p2)). Qed.
Lemma lem8222159 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term408 A B C P a p1 b p lt2 s p2 f g) = (term389 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222158 B C P a p1 b p g p2) (@lem8222157 A B C P lt2 s p2 f g)). Qed.
Lemma lem8222160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8222161 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term413 A B C P a p1 b p lt2 s p2 f g) = (term414 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222160) (@lem8222159 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222162 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term410 A B C P lt2 s p2 f g z) = (term376 A B C P lt2 s p2 f g z).
Proof. exact (eq_refl (term410 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8222163 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term387 B C P a p1 b p g p2) = (term387 B C P a p1 b p g p2).
Proof. exact (eq_refl (term387 B C P a p1 b p g p2)). Qed.
Lemma lem8222164 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term415 A B C P a p1 b p lt2 s p2 f g z) = (term416 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8222163 B C P a p1 b p g p2) (@lem8222162 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8222165 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term417 A B C P a p1 b p lt2 s p2 f g) = (term418 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8222164 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222166 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8222167 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term409 A B C P a p1 b p lt2 s p2 f g) = (term419 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222166 B) (@lem8222165 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222168 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : ((term408 A B C P a p1 b p lt2 s p2 f g) = (term409 A B C P a p1 b p lt2 s p2 f g)) = ((term389 A B C P a p1 b p lt2 s p2 f g) = (term419 A B C P a p1 b p lt2 s p2 f g)).
Proof. exact (MK_COMB (@lem8222161 A B C P a p1 b p lt2 s p2 f g) (@lem8222167 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222169 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term389 A B C P a p1 b p lt2 s p2 f g) = (term419 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (EQ_MP (@lem8222168 A B C P a p1 b p lt2 s p2 f g) (@lem8222153 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222170 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term387 B C P a p1 b p f p2) = (term387 B C P a p1 b p f p2).
Proof. exact (eq_refl (term387 B C P a p1 b p f p2)). Qed.
Lemma lem8222171 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term392 A B C P a p1 b p lt2 s p2 f g) = (term420 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222170 B C P a p1 b p f p2) (@lem8222169 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222173 {A : Type'} (P : Prop) (Q : A -> Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8222174 {B : Type'} (P : Prop) (Q : B -> Prop) : (term406 B P Q) = (term407 B P Q).
Proof. exact (@lem8222173 B P Q). Qed.
Lemma lem8222175 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term421 A B C P a p1 b p lt2 s p2 f g) = (term422 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (@lem8222174 B (term371 B C P a p1 b p f p2) (term418 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222176 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term423 A B C P a p1 b p lt2 s p2 f g z) = (term416 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (eq_refl (term423 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222177 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term424 A B C P a p1 b p lt2 s p2 f g) = (term418 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8222176 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222178 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8222179 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term425 A B C P a p1 b p lt2 s p2 f g) = (term419 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222178 B) (@lem8222177 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222180 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term387 B C P a p1 b p f p2) = (term387 B C P a p1 b p f p2).
Proof. exact (eq_refl (term387 B C P a p1 b p f p2)). Qed.
Lemma lem8222181 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term421 A B C P a p1 b p lt2 s p2 f g) = (term420 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222180 B C P a p1 b p f p2) (@lem8222179 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8222183 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term426 A B C P a p1 b p lt2 s p2 f g) = (term427 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222182) (@lem8222181 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222184 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term423 A B C P a p1 b p lt2 s p2 f g z) = (term416 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (eq_refl (term423 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222185 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term387 B C P a p1 b p f p2) = (term387 B C P a p1 b p f p2).
Proof. exact (eq_refl (term387 B C P a p1 b p f p2)). Qed.
Lemma lem8222186 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term428 A B C P a p1 b p lt2 s p2 f g z) = (term429 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8222185 B C P a p1 b p f p2) (@lem8222184 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222187 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term430 A B C P a p1 b p lt2 s p2 f g) = (term431 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8222186 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222188 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8222189 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term422 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222188 B) (@lem8222187 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222190 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : ((term421 A B C P a p1 b p lt2 s p2 f g) = (term422 A B C P a p1 b p lt2 s p2 f g)) = ((term420 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g)).
Proof. exact (MK_COMB (@lem8222183 A B C P a p1 b p lt2 s p2 f g) (@lem8222189 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222191 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term420 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (EQ_MP (@lem8222190 A B C P a p1 b p lt2 s p2 f g) (@lem8222175 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222192 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term392 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (TRANS (@lem8222171 A B C P a p1 b p lt2 s p2 f g) (@lem8222191 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222194 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term395 A B C P a p1 b p lt2 s p2 f g) = (term433 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222193) (@lem8222192 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222195 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8222196 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term397 A B C P a b p lt2 s f h g p2 p1) = (term434 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8222194 A B C P a p1 b p lt2 s p2 f g) (@lem8222195 B C P f h g p2 p1)). Qed.
Lemma lem8222198 {A : Type'} (P : A -> Prop) (Q : Prop) : (term435 A P Q) = (term436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8222199 {B : Type'} (P : B -> Prop) (Q : Prop) : (term435 B P Q) = (term436 B P Q).
Proof. exact (@lem8222198 B P Q). Qed.
Lemma lem8222200 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term437 A B C P a b p lt2 s f h g p2 p1) = (term438 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (@lem8222199 B (term431 A B C P a p1 b p lt2 s p2 f g) ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8222201 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term439 A B C P a p1 b p lt2 s p2 f g z) = (term429 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (eq_refl (term439 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222202 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term440 A B C P a p1 b p lt2 s p2 f g) = (term431 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8222201 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222203 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8222204 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term441 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222203 B) (@lem8222202 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222206 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term442 A B C P a p1 b p lt2 s p2 f g) = (term433 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8222205) (@lem8222204 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8222207 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8222208 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term437 A B C P a b p lt2 s f h g p2 p1) = (term434 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8222206 A B C P a p1 b p lt2 s p2 f g) (@lem8222207 B C P f h g p2 p1)). Qed.
Lemma lem8222209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8222210 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term443 A B C P a b p lt2 s f h g p2 p1) = (term444 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8222209) (@lem8222208 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222211 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term439 A B C P a p1 b p lt2 s p2 f g z) = (term429 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (eq_refl (term439 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222213 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term445 A B C P a p1 b p lt2 s p2 f g z) = (term446 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8222212) (@lem8222211 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8222214 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8222215 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term447 A B C P a b p lt2 s z f h g p2 p1) = (term448 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (MK_COMB (@lem8222213 A B C P a p1 b p lt2 s p2 f g z) (@lem8222214 B C P f h g p2 p1)). Qed.
Lemma lem8222216 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term449 A B C P a b p lt2 s f h g p2 p1) = (term450 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (fun_ext (fun z : B => @lem8222215 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8222217 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8222218 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term438 A B C P a b p lt2 s f h g p2 p1) = (term451 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8222217 B) (@lem8222216 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222219 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((term437 A B C P a b p lt2 s f h g p2 p1) = (term438 A B C P a b p lt2 s f h g p2 p1)) = ((term434 A B C P a b p lt2 s f h g p2 p1) = (term451 A B C P a b p lt2 s f h g p2 p1)).
Proof. exact (MK_COMB (@lem8222210 A B C P a b p lt2 s f h g p2 p1) (@lem8222218 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222220 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term434 A B C P a b p lt2 s f h g p2 p1) = (term451 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (EQ_MP (@lem8222219 A B C P a b p lt2 s f h g p2 p1) (@lem8222200 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222221 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term397 A B C P a b p lt2 s f h g p2 p1) = (term451 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (TRANS (@lem8222196 A B C P a b p lt2 s f h g p2 p1) (@lem8222220 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222222 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term398 A B C P a b p lt2 s f h g p1) = (term452 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8222221 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222223 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8222224 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term399 A B C P a b p lt2 s f h g p1) = (term453 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8222223 P) (@lem8222222 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222226 {A B : Type'} (P : type1413 A B) : (term454 A B P) = (term455 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8222227 {B P : Type'} (P' : type1470 B P) : (term456 B P P') = (term457 B P P').
Proof. exact (@lem8222226 P B P'). Qed.
Lemma lem8222228 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term458 A B C P a b p lt2 s f h g p1) = (term459 A B C P a b p lt2 s f h g p1).
Proof. exact (@lem8222227 B P (term460 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222229 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term461 A B C P a b p lt2 s f h g p1 p2) = (term450 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (eq_refl (term461 A B C P a b p lt2 s f h g p1 p2)). Qed.
Lemma lem8222230 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8222231 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) (z : B) : (term462 A B C P a b p lt2 s f h g p1 p2 z) = (term463 A B C P a b p lt2 s f h g p2 p1 z).
Proof. exact (MK_COMB (@lem8222229 A B C P a b p lt2 s f h g p2 p1) (@lem8222230 B z)). Qed.
Lemma lem8222232 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term463 A B C P a b p lt2 s f h g p2 p1 z) = (term448 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (eq_refl (term463 A B C P a b p lt2 s f h g p2 p1 z)). Qed.
Lemma lem8222233 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term462 A B C P a b p lt2 s f h g p1 p2 z) = (term448 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (TRANS (@lem8222231 A B C P a b p lt2 s f h g p2 p1 z) (@lem8222232 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8222234 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term464 A B C P a b p lt2 s f h g p1 p2) = (term450 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (fun_ext (fun z : B => @lem8222233 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8222235 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8222236 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term465 A B C P a b p lt2 s f h g p1 p2) = (term451 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8222235 B) (@lem8222234 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222237 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term466 A B C P a b p lt2 s f h g p1) = (term452 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8222236 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8222238 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8222239 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term458 A B C P a b p lt2 s f h g p1) = (term453 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8222238 P) (@lem8222237 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8222241 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term467 A B C P a b p lt2 s f h g p1) = (term468 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8222240) (@lem8222239 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222242 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term461 A B C P a b p lt2 s f h g p1 p2) = (term450 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (eq_refl (term461 A B C P a b p lt2 s f h g p1 p2)). Qed.
Lemma lem8222243 {B P : Type'} (z : P -> B) (p2 : P) : (z p2) = (z p2).
Proof. exact (eq_refl (z p2)). Qed.
Lemma lem8222244 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) (z : P -> B) (p2 : P) : (term469 A B C P a b p lt2 s f h g p1 z p2) = (term470 A B C P a b p lt2 s f h g p1 z p2).
Proof. exact (MK_COMB (@lem8222242 A B C P a b p lt2 s f h g p2 p1) (@lem8222243 B P z p2)). Qed.
Lemma lem8222245 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term470 A B C P a b p lt2 s f h g p1 z p2) = (term471 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (eq_refl (term470 A B C P a b p lt2 s f h g p1 z p2)). Qed.
Lemma lem8222246 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term469 A B C P a b p lt2 s f h g p1 z p2) = (term471 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (TRANS (@lem8222244 A B C P a b p lt2 s f h g p1 z p2) (@lem8222245 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8222247 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term472 A B C P a b p lt2 s f h g p1 z) = (term473 A B C P a b p lt2 s z f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8222246 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8222248 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8222249 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term474 A B C P a b p lt2 s f h g p1 z) = (term475 A B C P a b p lt2 s z f h g p1).
Proof. exact (MK_COMB (@lem8222248 P) (@lem8222247 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8222250 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term476 A B C P a b p lt2 s f h g p1) = (term477 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun z : P -> B => @lem8222249 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8222251 {B P : Type'} : (@ex (P -> B)) = (@ex (P -> B)).
Proof. exact (eq_refl (@ex (P -> B))). Qed.
Lemma lem8222252 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term459 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8222251 B P) (@lem8222250 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222253 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : ((term458 A B C P a b p lt2 s f h g p1) = (term459 A B C P a b p lt2 s f h g p1)) = ((term453 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1)).
Proof. exact (MK_COMB (@lem8222241 A B C P a b p lt2 s f h g p1) (@lem8222252 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222254 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term453 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1).
Proof. exact (EQ_MP (@lem8222253 A B C P a b p lt2 s f h g p1) (@lem8222228 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222255 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term399 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1).
Proof. exact (TRANS (@lem8222224 A B C P a b p lt2 s f h g p1) (@lem8222254 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222256 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term400 A B C P a b p lt2 s f h g) = (term479 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8222255 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222257 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8222258 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term401 A B C P a b p lt2 s f h g) = (term480 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8222257) (@lem8222256 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222260 {A B : Type'} (P : type1413 A B) : (term454 A B P) = (term455 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8222261 {B P : Type'} (P' : type1579 B P) : (term481 B P P') = (term482 B P P').
Proof. exact (@lem8222260 nat (P -> B) P'). Qed.
Lemma lem8222262 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term483 A B C P a b p lt2 s f h g) = (term484 A B C P a b p lt2 s f h g).
Proof. exact (@lem8222261 B P (term485 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222263 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term486 A B C P a b p lt2 s f h g p1) = (term477 A B C P a b p lt2 s f h g p1).
Proof. exact (eq_refl (term486 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222264 {B P : Type'} (z : P -> B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8222265 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) (z : P -> B) : (term487 A B C P a b p lt2 s f h g p1 z) = (term488 A B C P a b p lt2 s f h g p1 z).
Proof. exact (MK_COMB (@lem8222263 A B C P a b p lt2 s f h g p1) (@lem8222264 B P z)). Qed.
Lemma lem8222266 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term488 A B C P a b p lt2 s f h g p1 z) = (term475 A B C P a b p lt2 s z f h g p1).
Proof. exact (eq_refl (term488 A B C P a b p lt2 s f h g p1 z)). Qed.
Lemma lem8222267 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term487 A B C P a b p lt2 s f h g p1 z) = (term475 A B C P a b p lt2 s z f h g p1).
Proof. exact (TRANS (@lem8222265 A B C P a b p lt2 s f h g p1 z) (@lem8222266 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8222268 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term489 A B C P a b p lt2 s f h g p1) = (term477 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun z : P -> B => @lem8222267 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8222269 {B P : Type'} : (@ex (P -> B)) = (@ex (P -> B)).
Proof. exact (eq_refl (@ex (P -> B))). Qed.
Lemma lem8222270 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term490 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8222269 B P) (@lem8222268 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222271 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term491 A B C P a b p lt2 s f h g) = (term479 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8222270 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8222273 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term483 A B C P a b p lt2 s f h g) = (term480 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8222272) (@lem8222271 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8222275 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term492 A B C P a b p lt2 s f h g) = (term493 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8222274) (@lem8222273 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222276 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term486 A B C P a b p lt2 s f h g p1) = (term477 A B C P a b p lt2 s f h g p1).
Proof. exact (eq_refl (term486 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8222277 {B P : Type'} (z : type1599 B P) (p1 : nat) : (z p1) = (z p1).
Proof. exact (eq_refl (z p1)). Qed.
Lemma lem8222278 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (z : type1599 B P) (p1 : nat) : (term494 A B C P a b p lt2 s f h g z p1) = (term495 A B C P a b p lt2 s f h g z p1).
Proof. exact (MK_COMB (@lem8222276 A B C P a b p lt2 s f h g p1) (@lem8222277 B P z p1)). Qed.
Lemma lem8222279 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term495 A B C P a b p lt2 s f h g z p1) = (term496 A B C P a b p lt2 s z f h g p1).
Proof. exact (eq_refl (term495 A B C P a b p lt2 s f h g z p1)). Qed.
Lemma lem8222280 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term494 A B C P a b p lt2 s f h g z p1) = (term496 A B C P a b p lt2 s z f h g p1).
Proof. exact (TRANS (@lem8222278 A B C P a b p lt2 s f h g z p1) (@lem8222279 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8222281 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term497 A B C P a b p lt2 s f h g z) = (term498 A B C P a b p lt2 s z f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8222280 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8222282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8222283 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term499 A B C P a b p lt2 s f h g z) = (term500 A B C P a b p lt2 s z f h g).
Proof. exact (MK_COMB (@lem8222282) (@lem8222281 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8222284 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term501 A B C P a b p lt2 s f h g) = (term502 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun z : type1599 B P => @lem8222283 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8222285 {B P : Type'} : (@ex (nat -> P -> B)) = (@ex (nat -> P -> B)).
Proof. exact (eq_refl (@ex (nat -> P -> B))). Qed.
Lemma lem8222286 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term484 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8222285 B P) (@lem8222284 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222287 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : ((term483 A B C P a b p lt2 s f h g) = (term484 A B C P a b p lt2 s f h g)) = ((term480 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g)).
Proof. exact (MK_COMB (@lem8222275 A B C P a b p lt2 s f h g) (@lem8222286 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222288 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term480 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g).
Proof. exact (EQ_MP (@lem8222287 A B C P a b p lt2 s f h g) (@lem8222262 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222289 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term401 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g).
Proof. exact (TRANS (@lem8222258 A B C P a b p lt2 s f h g) (@lem8222288 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222290 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term402 A B C P a b p lt2 s f h) = (term504 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8222289 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222291 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8222292 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term403 A B C P a b p lt2 s f h) = (term505 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8222291 B C) (@lem8222290 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222294 {A B : Type'} (P : type1413 A B) : (term454 A B P) = (term455 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8222295 {B C P : Type'} (P' : type539 B C P) : (term506 B C P P') = (term507 B C P P').
Proof. exact (@lem8222294 (B -> C) (type1599 B P) P'). Qed.
Lemma lem8222296 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term508 A B C P a b p lt2 s f h) = (term509 A B C P a b p lt2 s f h).
Proof. exact (@lem8222295 B C P (term510 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222297 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term511 A B C P a b p lt2 s f h g) = (term502 A B C P a b p lt2 s f h g).
Proof. exact (eq_refl (term511 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222298 {B P : Type'} (z : type1599 B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8222299 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) (z : type1599 B P) : (term512 A B C P a b p lt2 s f h g z) = (term513 A B C P a b p lt2 s f h g z).
Proof. exact (MK_COMB (@lem8222297 A B C P a b p lt2 s f h g) (@lem8222298 B P z)). Qed.
Lemma lem8222300 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term513 A B C P a b p lt2 s f h g z) = (term500 A B C P a b p lt2 s z f h g).
Proof. exact (eq_refl (term513 A B C P a b p lt2 s f h g z)). Qed.
Lemma lem8222301 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term512 A B C P a b p lt2 s f h g z) = (term500 A B C P a b p lt2 s z f h g).
Proof. exact (TRANS (@lem8222299 A B C P a b p lt2 s f h g z) (@lem8222300 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8222302 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term514 A B C P a b p lt2 s f h g) = (term502 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun z : type1599 B P => @lem8222301 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8222303 {B P : Type'} : (@ex (nat -> P -> B)) = (@ex (nat -> P -> B)).
Proof. exact (eq_refl (@ex (nat -> P -> B))). Qed.
Lemma lem8222304 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term515 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8222303 B P) (@lem8222302 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222305 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term516 A B C P a b p lt2 s f h) = (term504 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8222304 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222306 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8222307 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term508 A B C P a b p lt2 s f h) = (term505 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8222306 B C) (@lem8222305 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8222309 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term517 A B C P a b p lt2 s f h) = (term518 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8222308) (@lem8222307 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222310 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term511 A B C P a b p lt2 s f h g) = (term502 A B C P a b p lt2 s f h g).
Proof. exact (eq_refl (term511 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8222311 {B C P : Type'} (z : type567 B C P) (g : B -> C) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8222312 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (z : type567 B C P) (g : B -> C) : (term519 A B C P a b p lt2 s f h z g) = (term520 A B C P a b p lt2 s f h z g).
Proof. exact (MK_COMB (@lem8222310 A B C P a b p lt2 s f h g) (@lem8222311 B C P z g)). Qed.
Lemma lem8222313 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term520 A B C P a b p lt2 s f h z g) = (term521 A B C P a b p lt2 s z f h g).
Proof. exact (eq_refl (term520 A B C P a b p lt2 s f h z g)). Qed.
Lemma lem8222314 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term519 A B C P a b p lt2 s f h z g) = (term521 A B C P a b p lt2 s z f h g).
Proof. exact (TRANS (@lem8222312 A B C P a b p lt2 s f h z g) (@lem8222313 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8222315 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type556 B C P) : (term522 A B C P a b p lt2 s f h z) = (term523 A B C P a b p lt2 s z f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8222314 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8222316 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8222317 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type556 B C P) : (term524 A B C P a b p lt2 s f h z) = (term525 A B C P a b p lt2 s z f h).
Proof. exact (MK_COMB (@lem8222316 B C) (@lem8222315 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8222318 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term526 A B C P a b p lt2 s f h) = (term527 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun z : type567 B C P => @lem8222317 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8222319 {B C P : Type'} : (@ex ((B -> C) -> nat -> P -> B)) = (@ex ((B -> C) -> nat -> P -> B)).
Proof. exact (eq_refl (@ex ((B -> C) -> nat -> P -> B))). Qed.
Lemma lem8222320 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term509 A B C P a b p lt2 s f h) = (term528 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8222319 B C P) (@lem8222318 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222321 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : ((term508 A B C P a b p lt2 s f h) = (term509 A B C P a b p lt2 s f h)) = ((term505 A B C P a b p lt2 s f h) = (term528 A B C P a b p lt2 s f h)).
Proof. exact (MK_COMB (@lem8222309 A B C P a b p lt2 s f h) (@lem8222320 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222322 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term505 A B C P a b p lt2 s f h) = (term528 A B C P a b p lt2 s f h).
Proof. exact (EQ_MP (@lem8222321 A B C P a b p lt2 s f h) (@lem8222296 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222323 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term403 A B C P a b p lt2 s f h) = (term528 A B C P a b p lt2 s f h).
Proof. exact (TRANS (@lem8222292 A B C P a b p lt2 s f h) (@lem8222322 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222324 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term404 A B C P a b p lt2 s h) = (term529 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8222323 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222325 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8222326 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term405 A B C P a b p lt2 s h) = (term530 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8222325 B C) (@lem8222324 A B C P a b p lt2 s h)). Qed.
Lemma lem8222328 {A B : Type'} (P : type1413 A B) : (term454 A B P) = (term455 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8222329 {B C P : Type'} (P' : type498 B C P) : (term531 B C P P') = (term532 B C P P').
Proof. exact (@lem8222328 (B -> C) (type567 B C P) P'). Qed.
Lemma lem8222330 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term533 A B C P a b p lt2 s h) = (term534 A B C P a b p lt2 s h).
Proof. exact (@lem8222329 B C P (term535 A B C P a b p lt2 s h)). Qed.
Lemma lem8222331 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term536 A B C P a b p lt2 s h f) = (term527 A B C P a b p lt2 s f h).
Proof. exact (eq_refl (term536 A B C P a b p lt2 s h f)). Qed.
Lemma lem8222332 {B C P : Type'} (z : type567 B C P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8222333 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) (z : type567 B C P) : (term537 A B C P a b p lt2 s h f z) = (term538 A B C P a b p lt2 s f h z).
Proof. exact (MK_COMB (@lem8222331 A B C P a b p lt2 s f h) (@lem8222332 B C P z)). Qed.
Lemma lem8222334 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type556 B C P) : (term538 A B C P a b p lt2 s f h z) = (term525 A B C P a b p lt2 s z f h).
Proof. exact (eq_refl (term538 A B C P a b p lt2 s f h z)). Qed.
Lemma lem8222335 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type556 B C P) : (term537 A B C P a b p lt2 s h f z) = (term525 A B C P a b p lt2 s z f h).
Proof. exact (TRANS (@lem8222333 A B C P a b p lt2 s f h z) (@lem8222334 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8222336 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term539 A B C P a b p lt2 s h f) = (term527 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun z : type567 B C P => @lem8222335 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8222337 {B C P : Type'} : (@ex ((B -> C) -> nat -> P -> B)) = (@ex ((B -> C) -> nat -> P -> B)).
Proof. exact (eq_refl (@ex ((B -> C) -> nat -> P -> B))). Qed.
Lemma lem8222338 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term540 A B C P a b p lt2 s h f) = (term528 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8222337 B C P) (@lem8222336 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222339 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term541 A B C P a b p lt2 s h) = (term529 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8222338 A B C P a b p lt2 s f h)). Qed.
Lemma lem8222340 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8222341 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term533 A B C P a b p lt2 s h) = (term530 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8222340 B C) (@lem8222339 A B C P a b p lt2 s h)). Qed.
Lemma lem8222342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8222343 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term542 A B C P a b p lt2 s h) = (term543 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8222342) (@lem8222341 A B C P a b p lt2 s h)). Qed.
Lemma lem8222344 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type556 B C P) : (term536 A B C P a b p lt2 s h f) = (term527 A B C P a b p lt2 s f h).
Proof. exact (eq_refl (term536 A B C P a b p lt2 s h f)). Qed.
Lemma lem8222345 {B C P : Type'} (z : type521 B C P) (f : B -> C) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8222346 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (z : type521 B C P) (f : B -> C) : (term544 A B C P a b p lt2 s h z f) = (term545 A B C P a b p lt2 s h z f).
Proof. exact (MK_COMB (@lem8222344 A B C P a b p lt2 s f h) (@lem8222345 B C P z f)). Qed.
Lemma lem8222347 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) : (term545 A B C P a b p lt2 s h z f) = (term546 A B C P a b p lt2 s z f h).
Proof. exact (eq_refl (term545 A B C P a b p lt2 s h z f)). Qed.
Lemma lem8222348 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) : (term544 A B C P a b p lt2 s h z f) = (term546 A B C P a b p lt2 s z f h).
Proof. exact (TRANS (@lem8222346 A B C P a b p lt2 s h z f) (@lem8222347 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8222349 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) : (term547 A B C P a b p lt2 s h z) = (term548 A B C P a b p lt2 s z h).
Proof. exact (fun_ext (fun f : B -> C => @lem8222348 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8222350 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8222351 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) : (term549 A B C P a b p lt2 s h z) = (term550 A B C P a b p lt2 s z h).
Proof. exact (MK_COMB (@lem8222350 B C) (@lem8222349 A B C P a b p lt2 s z h)). Qed.
Lemma lem8222352 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term551 A B C P a b p lt2 s h) = (term552 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun z : type521 B C P => @lem8222351 A B C P a b p lt2 s z h)). Qed.
Lemma lem8222353 {B C P : Type'} : (@ex ((B -> C) -> (B -> C) -> nat -> P -> B)) = (@ex ((B -> C) -> (B -> C) -> nat -> P -> B)).
Proof. exact (eq_refl (@ex ((B -> C) -> (B -> C) -> nat -> P -> B))). Qed.
Lemma lem8222354 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term534 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8222353 B C P) (@lem8222352 A B C P a b p lt2 s h)). Qed.
Lemma lem8222355 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : ((term533 A B C P a b p lt2 s h) = (term534 A B C P a b p lt2 s h)) = ((term530 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h)).
Proof. exact (MK_COMB (@lem8222343 A B C P a b p lt2 s h) (@lem8222354 A B C P a b p lt2 s h)). Qed.
Lemma lem8222356 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term530 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h).
Proof. exact (EQ_MP (@lem8222355 A B C P a b p lt2 s h) (@lem8222330 A B C P a b p lt2 s h)). Qed.
Lemma lem8222358 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term405 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h).
Proof. exact (TRANS (@lem8222326 A B C P a b p lt2 s h) (@lem8222356 A B C P a b p lt2 s h)). Qed.
Lemma lem8222359 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : (term240 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h).
Proof. exact (TRANS (@lem8222040 A B C P a b p lt2 s h) (@lem8222358 A B C P a b p lt2 s h)). Qed.
Lemma lem8222360 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term553 A B C P a b p lt2 s h.
Proof. exact (EQ_MP (@lem8222359 A B C P a b p lt2 s h) (@lem8221960 A B C P a b p lt2 s h h1)). Qed.
Lemma lem8222366 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : p f a'.
Proof. exact (h1). Qed.
Lemma lem8222372 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : p g a'.
Proof. exact (h1). Qed.
Lemma lem8222379 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (z : B) : (term170 A B C P lt2 s a' f g z) = (term554 A B C P lt2 s a' f g z).
Proof. exact (@lem17265 (term166 A B P lt2 z s a') ((f z) = (g z))). Qed.
Lemma lem8222380 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term172 A B C P lt2 s a' f g) = (term555 A B C P lt2 s a' f g).
Proof. exact (fun_ext (fun z : B => @lem8222379 A B C P lt2 s a' f g z)). Qed.
Lemma lem8222381 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8222434 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term174 A B C P lt2 s a' f g) = (term556 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8222381 B) (@lem8222380 A B C P lt2 s a' f g)). Qed.
Lemma lem8222435 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term556 A B C P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8222434 A B C P lt2 s a' f g) (@lem8221963 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8222445 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term557 P a i b a'.
Proof. exact (h1). Qed.
Lemma lem8222451 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term365 B C P f h g a' i) : term365 B C P f h g a' i.
Proof. exact (h1). Qed.
Lemma lem8222452 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term550 A B C P a b p lt2 s z h.
Proof. exact (h1). Qed.
Lemma lem8222459 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222460 {B C P : Type'} (f : type560 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> Prop) f x).
Proof. exact (@lem8222459 (B -> C) (P -> Prop) f x). Qed.
Lemma lem8222461 {B C P : Type'} (p : type560 B C P) (f : B -> C) : (p f) = (@I ((B -> C) -> P -> Prop) p f).
Proof. exact (@lem8222460 B C P p f). Qed.
Lemma lem8222462 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8222463 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (p f a') = (@I ((B -> C) -> P -> Prop) p f a').
Proof. exact (MK_COMB (@lem8222461 B C P p f) (@lem8222462 P a')). Qed.
Lemma lem8222465 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222466 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8222465 P Prop f x). Qed.
Lemma lem8222467 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (@I ((B -> C) -> P -> Prop) p f a') = (term558 B C P p f a').
Proof. exact (@lem8222466 P (@I ((B -> C) -> P -> Prop) p f) a'). Qed.
Lemma lem8222469 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (p f a') = (term558 B C P p f a').
Proof. exact (TRANS (@lem8222463 B C P p f a') (@lem8222467 B C P p f a')). Qed.
Lemma lem8222477 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222478 {B C P : Type'} (f : type560 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> Prop) f x).
Proof. exact (@lem8222477 (B -> C) (P -> Prop) f x). Qed.
Lemma lem8222479 {B C P : Type'} (p : type560 B C P) (g : B -> C) : (p g) = (@I ((B -> C) -> P -> Prop) p g).
Proof. exact (@lem8222478 B C P p g). Qed.
Lemma lem8222480 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8222481 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (p g a') = (@I ((B -> C) -> P -> Prop) p g a').
Proof. exact (MK_COMB (@lem8222479 B C P p g) (@lem8222480 P a')). Qed.
Lemma lem8222483 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222484 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8222483 P Prop f x). Qed.
Lemma lem8222485 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (@I ((B -> C) -> P -> Prop) p g a') = (term558 B C P p g a').
Proof. exact (@lem8222484 P (@I ((B -> C) -> P -> Prop) p g) a'). Qed.
Lemma lem8222487 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (p g a') = (term558 B C P p g a').
Proof. exact (TRANS (@lem8222481 B C P p g a') (@lem8222485 B C P p g a')). Qed.
Lemma lem8222489 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8222494 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222495 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem8222494 B C f x). Qed.
Lemma lem8222497 {B C : Type'} (f : B -> C) (z : B) : (f z) = (@I (B -> C) f z).
Proof. exact (@lem8222495 B C f z). Qed.
Lemma lem8222502 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222503 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem8222502 B C f x). Qed.
Lemma lem8222505 {B C : Type'} (g : B -> C) (z : B) : (g z) = (@I (B -> C) g z).
Proof. exact (@lem8222503 B C g z). Qed.
Lemma lem8222506 {B C : Type'} (f : B -> C) (z : B) : (term559 B C f z) = (term560 B C f z).
Proof. exact (MK_COMB (@lem8222489 C) (@lem8222497 B C f z)). Qed.
Lemma lem8222507 {B C : Type'} (f : B -> C) (g : B -> C) (z : B) : ((f z) = (g z)) = ((@I (B -> C) f z) = (@I (B -> C) g z)).
Proof. exact (MK_COMB (@lem8222506 B C f z) (@lem8222505 B C g z)). Qed.
Lemma lem8222508 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222515 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222516 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8222515 P A f x). Qed.
Lemma lem8222518 {A P : Type'} (s : P -> A) (a' : P) : (s a') = (@I (P -> A) s a').
Proof. exact (@lem8222516 A P s a'). Qed.
Lemma lem8222519 {A B : Type'} (lt2 : type1470 A B) (z : B) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8222520 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term166 A B P lt2 z s a') = (term561 A B P lt2 z s a').
Proof. exact (MK_COMB (@lem8222519 A B lt2 z) (@lem8222518 A P s a')). Qed.
Lemma lem8222522 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222523 {A B : Type'} (f : type1470 A B) (x : B) : (f x) = (@I (B -> A -> Prop) f x).
Proof. exact (@lem8222522 B (A -> Prop) f x). Qed.
Lemma lem8222524 {A B : Type'} (lt2 : type1470 A B) (z : B) : (lt2 z) = (@I (B -> A -> Prop) lt2 z).
Proof. exact (@lem8222523 A B lt2 z). Qed.
Lemma lem8222525 {A P : Type'} (s : P -> A) (a' : P) : (@I (P -> A) s a') = (@I (P -> A) s a').
Proof. exact (eq_refl (@I (P -> A) s a')). Qed.
Lemma lem8222526 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term561 A B P lt2 z s a') = (term562 A B P lt2 z s a').
Proof. exact (MK_COMB (@lem8222524 A B lt2 z) (@lem8222525 A P s a')). Qed.
Lemma lem8222528 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222529 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8222528 A Prop f x). Qed.
Lemma lem8222530 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term562 A B P lt2 z s a') = (term563 A B P lt2 z s a').
Proof. exact (@lem8222529 A (@I (B -> A -> Prop) lt2 z) (@I (P -> A) s a')). Qed.
Lemma lem8222531 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term561 A B P lt2 z s a') = (term563 A B P lt2 z s a').
Proof. exact (TRANS (@lem8222526 A B P lt2 z s a') (@lem8222530 A B P lt2 z s a')). Qed.
Lemma lem8222532 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term166 A B P lt2 z s a') = (term563 A B P lt2 z s a').
Proof. exact (TRANS (@lem8222520 A B P lt2 z s a') (@lem8222531 A B P lt2 z s a')). Qed.
Lemma lem8222533 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term564 A B P lt2 z s a') = (term565 A B P lt2 z s a').
Proof. exact (MK_COMB (@lem8222508) (@lem8222532 A B P lt2 z s a')). Qed.
Lemma lem8222534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222535 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term566 A B P lt2 z s a') = (term567 A B P lt2 z s a').
Proof. exact (MK_COMB (@lem8222534) (@lem8222533 A B P lt2 z s a')). Qed.
Lemma lem8222536 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (z : B) : (term554 A B C P lt2 s a' f g z) = (term568 A B C P lt2 s a' f g z).
Proof. exact (MK_COMB (@lem8222535 A B P lt2 z s a') (@lem8222507 B C f g z)). Qed.
Lemma lem8222537 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term555 A B C P lt2 s a' f g) = (term569 A B C P lt2 s a' f g).
Proof. exact (fun_ext (fun z : B => @lem8222536 A B C P lt2 s a' f g z)). Qed.
Lemma lem8222538 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8222539 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term556 A B C P lt2 s a' f g) = (term570 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8222538 B) (@lem8222537 A B C P lt2 s a' f g)). Qed.
Lemma lem8222540 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term570 A B C P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8222539 A B C P lt2 s a' f g) (@lem8222435 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8222547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222548 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8222547 P nat f x). Qed.
Lemma lem8222550 {P : Type'} (b : P -> nat) (a' : P) : (b a') = (@I (P -> nat) b a').
Proof. exact (@lem8222548 P b a'). Qed.
Lemma lem8222551 (i : nat) : (Peano.le i) = (Peano.le i).
Proof. exact (eq_refl (Peano.le i)). Qed.
Lemma lem8222552 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term368 P i b a') = (term571 P i b a').
Proof. exact (MK_COMB (@lem8222551 i) (@lem8222550 P b a')). Qed.
Lemma lem8222554 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222555 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8222554 nat (nat -> Prop) f x). Qed.
Lemma lem8222556 (i : nat) : (Peano.le i) = (@I (nat -> nat -> Prop) Peano.le i).
Proof. exact (@lem8222555 Peano.le i). Qed.
Lemma lem8222557 {P : Type'} (b : P -> nat) (a' : P) : (@I (P -> nat) b a') = (@I (P -> nat) b a').
Proof. exact (eq_refl (@I (P -> nat) b a')). Qed.
Lemma lem8222558 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term571 P i b a') = (term572 P i b a').
Proof. exact (MK_COMB (@lem8222556 i) (@lem8222557 P b a')). Qed.
Lemma lem8222560 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222561 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8222560 nat Prop f x). Qed.
Lemma lem8222562 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term572 P i b a') = (term573 P i b a').
Proof. exact (@lem8222561 (@I (nat -> nat -> Prop) Peano.le i) (@I (P -> nat) b a')). Qed.
Lemma lem8222563 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term571 P i b a') = (term573 P i b a').
Proof. exact (TRANS (@lem8222558 P i b a') (@lem8222562 P i b a')). Qed.
Lemma lem8222564 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term368 P i b a') = (term573 P i b a').
Proof. exact (TRANS (@lem8222552 P i b a') (@lem8222563 P i b a')). Qed.
Lemma lem8222565 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem8222570 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222571 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8222570 P nat f x). Qed.
Lemma lem8222573 {P : Type'} (a : P -> nat) (a' : P) : (a a') = (@I (P -> nat) a a').
Proof. exact (@lem8222571 P a a'). Qed.
Lemma lem8222574 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem8222575 {P : Type'} (a : P -> nat) (a' : P) : (term574 P a a') = (term575 P a a').
Proof. exact (MK_COMB (@lem8222565) (@lem8222573 P a a')). Qed.
Lemma lem8222576 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term373 P a a' i) = (term576 P a a' i).
Proof. exact (MK_COMB (@lem8222575 P a a') (@lem8222574 i)). Qed.
Lemma lem8222578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222579 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8222578 nat (nat -> Prop) f x). Qed.
Lemma lem8222580 {P : Type'} (a : P -> nat) (a' : P) : (term575 P a a') = (term577 P a a').
Proof. exact (@lem8222579 Peano.le (@I (P -> nat) a a')). Qed.
Lemma lem8222581 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem8222582 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term576 P a a' i) = (term578 P a a' i).
Proof. exact (MK_COMB (@lem8222580 P a a') (@lem8222581 i)). Qed.
Lemma lem8222584 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222585 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8222584 nat Prop f x). Qed.
Lemma lem8222586 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term578 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8222585 (term577 P a a') i). Qed.
Lemma lem8222587 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term576 P a a' i) = (term579 P a a' i).
Proof. exact (TRANS (@lem8222582 P a a' i) (@lem8222586 P a a' i)). Qed.
Lemma lem8222588 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term373 P a a' i) = (term579 P a a' i).
Proof. exact (TRANS (@lem8222576 P a a' i) (@lem8222587 P a a' i)). Qed.
Lemma lem8222589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8222590 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term580 P a a' i) = (term581 P a a' i).
Proof. exact (MK_COMB (@lem8222589) (@lem8222588 P a a' i)). Qed.
Lemma lem8222591 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) : (term557 P a i b a') = (term582 P a i b a').
Proof. exact (MK_COMB (@lem8222590 P a a' i) (@lem8222564 P i b a')). Qed.
Lemma lem8222592 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term582 P a i b a'.
Proof. exact (EQ_MP (@lem8222591 P a i b a') (@lem8222445 P a i b a' h1)). Qed.
Lemma lem8222593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222594 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem8222603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222604 {B C P : Type'} (f : type556 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> nat -> real) f x).
Proof. exact (@lem8222603 (B -> C) (type1426 P) f x). Qed.
Lemma lem8222605 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (h f) = (@I ((B -> C) -> P -> nat -> real) h f).
Proof. exact (@lem8222604 B C P h f). Qed.
Lemma lem8222606 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8222607 {B C P : Type'} (h : type556 B C P) (f : B -> C) (a' : P) : (h f a') = (@I ((B -> C) -> P -> nat -> real) h f a').
Proof. exact (MK_COMB (@lem8222605 B C P h f) (@lem8222606 P a')). Qed.
Lemma lem8222609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222610 {P : Type'} (f : type1426 P) (x : P) : (f x) = (@I (P -> nat -> real) f x).
Proof. exact (@lem8222609 P (nat -> real) f x). Qed.
Lemma lem8222611 {B C P : Type'} (h : type556 B C P) (f : B -> C) (a' : P) : (@I ((B -> C) -> P -> nat -> real) h f a') = (term583 B C P h f a').
Proof. exact (@lem8222610 P (@I ((B -> C) -> P -> nat -> real) h f) a'). Qed.
Lemma lem8222612 {B C P : Type'} (h : type556 B C P) (f : B -> C) (a' : P) : (h f a') = (term583 B C P h f a').
Proof. exact (TRANS (@lem8222607 B C P h f a') (@lem8222611 B C P h f a')). Qed.
Lemma lem8222613 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem8222614 {B C P : Type'} (h : type556 B C P) (f : B -> C) (a' : P) (i : nat) : (h f a' i) = (term584 B C P h f a' i).
Proof. exact (MK_COMB (@lem8222612 B C P h f a') (@lem8222613 i)). Qed.
Lemma lem8222616 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222617 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem8222616 nat real f x). Qed.
Lemma lem8222618 {B C P : Type'} (h : type556 B C P) (f : B -> C) (a' : P) (i : nat) : (term584 B C P h f a' i) = (term585 B C P h f a' i).
Proof. exact (@lem8222617 (term583 B C P h f a') i). Qed.
Lemma lem8222620 {B C P : Type'} (h : type556 B C P) (f : B -> C) (a' : P) (i : nat) : (h f a' i) = (term585 B C P h f a' i).
Proof. exact (TRANS (@lem8222614 B C P h f a' i) (@lem8222618 B C P h f a' i)). Qed.
Lemma lem8222629 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222630 {B C P : Type'} (f : type556 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> nat -> real) f x).
Proof. exact (@lem8222629 (B -> C) (type1426 P) f x). Qed.
Lemma lem8222631 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (h g) = (@I ((B -> C) -> P -> nat -> real) h g).
Proof. exact (@lem8222630 B C P h g). Qed.
Lemma lem8222632 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8222633 {B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : (h g a') = (@I ((B -> C) -> P -> nat -> real) h g a').
Proof. exact (MK_COMB (@lem8222631 B C P h g) (@lem8222632 P a')). Qed.
Lemma lem8222635 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222636 {P : Type'} (f : type1426 P) (x : P) : (f x) = (@I (P -> nat -> real) f x).
Proof. exact (@lem8222635 P (nat -> real) f x). Qed.
Lemma lem8222637 {B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : (@I ((B -> C) -> P -> nat -> real) h g a') = (term583 B C P h g a').
Proof. exact (@lem8222636 P (@I ((B -> C) -> P -> nat -> real) h g) a'). Qed.
Lemma lem8222638 {B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : (h g a') = (term583 B C P h g a').
Proof. exact (TRANS (@lem8222633 B C P h g a') (@lem8222637 B C P h g a')). Qed.
Lemma lem8222639 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem8222640 {B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (h g a' i) = (term584 B C P h g a' i).
Proof. exact (MK_COMB (@lem8222638 B C P h g a') (@lem8222639 i)). Qed.
Lemma lem8222642 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222643 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem8222642 nat real f x). Qed.
Lemma lem8222644 {B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (term584 B C P h g a' i) = (term585 B C P h g a' i).
Proof. exact (@lem8222643 (term583 B C P h g a') i). Qed.
Lemma lem8222646 {B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (h g a' i) = (term585 B C P h g a' i).
Proof. exact (TRANS (@lem8222640 B C P h g a' i) (@lem8222644 B C P h g a' i)). Qed.
Lemma lem8222647 {B C P : Type'} (h : type556 B C P) (f : B -> C) (a' : P) (i : nat) : (term201 B C P h f a' i) = (term586 B C P h f a' i).
Proof. exact (MK_COMB (@lem8222594) (@lem8222620 B C P h f a' i)). Qed.
Lemma lem8222648 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : ((h f a' i) = (h g a' i)) = ((term585 B C P h f a' i) = (term585 B C P h g a' i)).
Proof. exact (MK_COMB (@lem8222647 B C P h f a' i) (@lem8222646 B C P h g a' i)). Qed.
Lemma lem8222649 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (term365 B C P f h g a' i) = (term587 B C P f h g a' i).
Proof. exact (MK_COMB (@lem8222593) (@lem8222648 B C P f h g a' i)). Qed.
Lemma lem8222651 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem8222660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222661 {B C P : Type'} (f : type556 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> nat -> real) f x).
Proof. exact (@lem8222660 (B -> C) (type1426 P) f x). Qed.
Lemma lem8222662 {B C P : Type'} (h : type556 B C P) (f : B -> C) : (h f) = (@I ((B -> C) -> P -> nat -> real) h f).
Proof. exact (@lem8222661 B C P h f). Qed.
Lemma lem8222663 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8222664 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) : (h f p2) = (@I ((B -> C) -> P -> nat -> real) h f p2).
Proof. exact (MK_COMB (@lem8222662 B C P h f) (@lem8222663 P p2)). Qed.
Lemma lem8222666 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222667 {P : Type'} (f : type1426 P) (x : P) : (f x) = (@I (P -> nat -> real) f x).
Proof. exact (@lem8222666 P (nat -> real) f x). Qed.
Lemma lem8222668 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) : (@I ((B -> C) -> P -> nat -> real) h f p2) = (term583 B C P h f p2).
Proof. exact (@lem8222667 P (@I ((B -> C) -> P -> nat -> real) h f) p2). Qed.
Lemma lem8222669 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) : (h f p2) = (term583 B C P h f p2).
Proof. exact (TRANS (@lem8222664 B C P h f p2) (@lem8222668 B C P h f p2)). Qed.
Lemma lem8222670 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8222671 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (h f p2 p1) = (term584 B C P h f p2 p1).
Proof. exact (MK_COMB (@lem8222669 B C P h f p2) (@lem8222670 p1)). Qed.
Lemma lem8222673 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222674 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem8222673 nat real f x). Qed.
Lemma lem8222675 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term584 B C P h f p2 p1) = (term585 B C P h f p2 p1).
Proof. exact (@lem8222674 (term583 B C P h f p2) p1). Qed.
Lemma lem8222677 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (h f p2 p1) = (term585 B C P h f p2 p1).
Proof. exact (TRANS (@lem8222671 B C P h f p2 p1) (@lem8222675 B C P h f p2 p1)). Qed.
Lemma lem8222686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222687 {B C P : Type'} (f : type556 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> nat -> real) f x).
Proof. exact (@lem8222686 (B -> C) (type1426 P) f x). Qed.
Lemma lem8222688 {B C P : Type'} (h : type556 B C P) (g : B -> C) : (h g) = (@I ((B -> C) -> P -> nat -> real) h g).
Proof. exact (@lem8222687 B C P h g). Qed.
Lemma lem8222689 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8222690 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p2 : P) : (h g p2) = (@I ((B -> C) -> P -> nat -> real) h g p2).
Proof. exact (MK_COMB (@lem8222688 B C P h g) (@lem8222689 P p2)). Qed.
Lemma lem8222692 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222693 {P : Type'} (f : type1426 P) (x : P) : (f x) = (@I (P -> nat -> real) f x).
Proof. exact (@lem8222692 P (nat -> real) f x). Qed.
Lemma lem8222694 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p2 : P) : (@I ((B -> C) -> P -> nat -> real) h g p2) = (term583 B C P h g p2).
Proof. exact (@lem8222693 P (@I ((B -> C) -> P -> nat -> real) h g) p2). Qed.
Lemma lem8222695 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p2 : P) : (h g p2) = (term583 B C P h g p2).
Proof. exact (TRANS (@lem8222690 B C P h g p2) (@lem8222694 B C P h g p2)). Qed.
Lemma lem8222696 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8222697 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (h g p2 p1) = (term584 B C P h g p2 p1).
Proof. exact (MK_COMB (@lem8222695 B C P h g p2) (@lem8222696 p1)). Qed.
Lemma lem8222699 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222700 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem8222699 nat real f x). Qed.
Lemma lem8222701 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term584 B C P h g p2 p1) = (term585 B C P h g p2 p1).
Proof. exact (@lem8222700 (term583 B C P h g p2) p1). Qed.
Lemma lem8222703 {B C P : Type'} (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (h g p2 p1) = (term585 B C P h g p2 p1).
Proof. exact (TRANS (@lem8222697 B C P h g p2 p1) (@lem8222701 B C P h g p2 p1)). Qed.
Lemma lem8222704 {B C P : Type'} (h : type556 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term201 B C P h f p2 p1) = (term586 B C P h f p2 p1).
Proof. exact (MK_COMB (@lem8222651) (@lem8222677 B C P h f p2 p1)). Qed.
Lemma lem8222705 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1)).
Proof. exact (MK_COMB (@lem8222704 B C P h f p2 p1) (@lem8222703 B C P h g p2 p1)). Qed.
Lemma lem8222706 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222707 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8222708 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8222719 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222720 {B C P : Type'} (f : type521 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8222719 (B -> C) (type567 B C P) f x). Qed.
Lemma lem8222721 {B C P : Type'} (z : type521 B C P) (f : B -> C) : (z f) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f).
Proof. exact (@lem8222720 B C P z f). Qed.
Lemma lem8222722 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8222723 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g).
Proof. exact (MK_COMB (@lem8222721 B C P z f) (@lem8222722 B C g)). Qed.
Lemma lem8222725 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222726 {B C P : Type'} (f : type567 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8222725 (B -> C) (type1599 B P) f x). Qed.
Lemma lem8222727 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g) = (term588 B C P z f g).
Proof. exact (@lem8222726 B C P (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f) g). Qed.
Lemma lem8222728 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (term588 B C P z f g).
Proof. exact (TRANS (@lem8222723 B C P z f g) (@lem8222727 B C P z f g)). Qed.
Lemma lem8222729 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8222730 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term589 B C P z f g p1).
Proof. exact (MK_COMB (@lem8222728 B C P z f g) (@lem8222729 p1)). Qed.
Lemma lem8222732 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222733 {B P : Type'} (f : type1599 B P) (x : nat) : (f x) = (@I (nat -> P -> B) f x).
Proof. exact (@lem8222732 nat (P -> B) f x). Qed.
Lemma lem8222734 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (term589 B C P z f g p1) = (term590 B C P z f g p1).
Proof. exact (@lem8222733 B P (term588 B C P z f g) p1). Qed.
Lemma lem8222735 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term590 B C P z f g p1).
Proof. exact (TRANS (@lem8222730 B C P z f g p1) (@lem8222734 B C P z f g p1)). Qed.
Lemma lem8222736 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8222737 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term591 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8222735 B C P z f g p1) (@lem8222736 P p2)). Qed.
Lemma lem8222739 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222740 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8222739 P B f x). Qed.
Lemma lem8222741 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term591 B C P z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (@lem8222740 B P (term590 B C P z f g p1) p2). Qed.
Lemma lem8222743 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8222737 B C P z f g p1 p2) (@lem8222741 B C P z f g p1 p2)). Qed.
Lemma lem8222744 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term593 B C P z f g p1 p2) = (term594 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8222708 B C f) (@lem8222743 B C P z f g p1 p2)). Qed.
Lemma lem8222746 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222747 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem8222746 B C f x). Qed.
Lemma lem8222748 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term594 B C P z f g p1 p2) = (term595 B C P z f g p1 p2).
Proof. exact (@lem8222747 B C f (term592 B C P z f g p1 p2)). Qed.
Lemma lem8222749 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term593 B C P z f g p1 p2) = (term595 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8222744 B C P z f g p1 p2) (@lem8222748 B C P z f g p1 p2)). Qed.
Lemma lem8222750 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8222761 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222762 {B C P : Type'} (f : type521 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8222761 (B -> C) (type567 B C P) f x). Qed.
Lemma lem8222763 {B C P : Type'} (z : type521 B C P) (f : B -> C) : (z f) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f).
Proof. exact (@lem8222762 B C P z f). Qed.
Lemma lem8222764 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8222765 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g).
Proof. exact (MK_COMB (@lem8222763 B C P z f) (@lem8222764 B C g)). Qed.
Lemma lem8222767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222768 {B C P : Type'} (f : type567 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8222767 (B -> C) (type1599 B P) f x). Qed.
Lemma lem8222769 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g) = (term588 B C P z f g).
Proof. exact (@lem8222768 B C P (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f) g). Qed.
Lemma lem8222770 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (term588 B C P z f g).
Proof. exact (TRANS (@lem8222765 B C P z f g) (@lem8222769 B C P z f g)). Qed.
Lemma lem8222771 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8222772 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term589 B C P z f g p1).
Proof. exact (MK_COMB (@lem8222770 B C P z f g) (@lem8222771 p1)). Qed.
Lemma lem8222774 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222775 {B P : Type'} (f : type1599 B P) (x : nat) : (f x) = (@I (nat -> P -> B) f x).
Proof. exact (@lem8222774 nat (P -> B) f x). Qed.
Lemma lem8222776 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (term589 B C P z f g p1) = (term590 B C P z f g p1).
Proof. exact (@lem8222775 B P (term588 B C P z f g) p1). Qed.
Lemma lem8222777 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term590 B C P z f g p1).
Proof. exact (TRANS (@lem8222772 B C P z f g p1) (@lem8222776 B C P z f g p1)). Qed.
Lemma lem8222778 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8222779 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term591 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8222777 B C P z f g p1) (@lem8222778 P p2)). Qed.
Lemma lem8222781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222782 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8222781 P B f x). Qed.
Lemma lem8222783 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term591 B C P z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (@lem8222782 B P (term590 B C P z f g p1) p2). Qed.
Lemma lem8222785 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8222779 B C P z f g p1 p2) (@lem8222783 B C P z f g p1 p2)). Qed.
Lemma lem8222786 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term596 B C P z f g p1 p2) = (term597 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8222750 B C g) (@lem8222785 B C P z f g p1 p2)). Qed.
Lemma lem8222788 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222789 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem8222788 B C f x). Qed.
Lemma lem8222790 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term597 B C P z f g p1 p2) = (term598 B C P z f g p1 p2).
Proof. exact (@lem8222789 B C g (term592 B C P z f g p1 p2)). Qed.
Lemma lem8222791 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term596 B C P z f g p1 p2) = (term598 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8222786 B C P z f g p1 p2) (@lem8222790 B C P z f g p1 p2)). Qed.
Lemma lem8222792 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term599 B C P z f g p1 p2) = (term600 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8222707 C) (@lem8222749 B C P z f g p1 p2)). Qed.
Lemma lem8222793 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : ((term593 B C P z f g p1 p2) = (term596 B C P z f g p1 p2)) = ((term595 B C P z f g p1 p2) = (term598 B C P z f g p1 p2)).
Proof. exact (MK_COMB (@lem8222792 B C P z f g p1 p2) (@lem8222791 B C P z f g p1 p2)). Qed.
Lemma lem8222794 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term601 B C P z f g p1 p2) = (term602 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8222706) (@lem8222793 B C P z f g p1 p2)). Qed.
Lemma lem8222795 {A B : Type'} (lt2 : type1470 A B) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8222806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222807 {B C P : Type'} (f : type521 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8222806 (B -> C) (type567 B C P) f x). Qed.
Lemma lem8222808 {B C P : Type'} (z : type521 B C P) (f : B -> C) : (z f) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f).
Proof. exact (@lem8222807 B C P z f). Qed.
Lemma lem8222809 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8222810 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g).
Proof. exact (MK_COMB (@lem8222808 B C P z f) (@lem8222809 B C g)). Qed.
Lemma lem8222812 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222813 {B C P : Type'} (f : type567 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8222812 (B -> C) (type1599 B P) f x). Qed.
Lemma lem8222814 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g) = (term588 B C P z f g).
Proof. exact (@lem8222813 B C P (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f) g). Qed.
Lemma lem8222815 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (term588 B C P z f g).
Proof. exact (TRANS (@lem8222810 B C P z f g) (@lem8222814 B C P z f g)). Qed.
Lemma lem8222816 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8222817 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term589 B C P z f g p1).
Proof. exact (MK_COMB (@lem8222815 B C P z f g) (@lem8222816 p1)). Qed.
Lemma lem8222819 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222820 {B P : Type'} (f : type1599 B P) (x : nat) : (f x) = (@I (nat -> P -> B) f x).
Proof. exact (@lem8222819 nat (P -> B) f x). Qed.
Lemma lem8222821 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (term589 B C P z f g p1) = (term590 B C P z f g p1).
Proof. exact (@lem8222820 B P (term588 B C P z f g) p1). Qed.
Lemma lem8222822 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term590 B C P z f g p1).
Proof. exact (TRANS (@lem8222817 B C P z f g p1) (@lem8222821 B C P z f g p1)). Qed.
Lemma lem8222823 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8222824 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term591 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8222822 B C P z f g p1) (@lem8222823 P p2)). Qed.
Lemma lem8222826 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222827 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8222826 P B f x). Qed.
Lemma lem8222828 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term591 B C P z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (@lem8222827 B P (term590 B C P z f g p1) p2). Qed.
Lemma lem8222830 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8222824 B C P z f g p1 p2) (@lem8222828 B C P z f g p1 p2)). Qed.
Lemma lem8222835 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222836 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8222835 P A f x). Qed.
Lemma lem8222838 {A P : Type'} (s : P -> A) (p2 : P) : (s p2) = (@I (P -> A) s p2).
Proof. exact (@lem8222836 A P s p2). Qed.
Lemma lem8222839 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term603 A B C P lt2 z f g p1 p2) = (term604 A B C P lt2 z f g p1 p2).
Proof. exact (MK_COMB (@lem8222795 A B lt2) (@lem8222830 B C P z f g p1 p2)). Qed.
Lemma lem8222840 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term605 A B C P lt2 z f g p1 s p2) = (term606 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8222839 A B C P lt2 z f g p1 p2) (@lem8222838 A P s p2)). Qed.
Lemma lem8222842 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222843 {A B : Type'} (f : type1470 A B) (x : B) : (f x) = (@I (B -> A -> Prop) f x).
Proof. exact (@lem8222842 B (A -> Prop) f x). Qed.
Lemma lem8222844 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term604 A B C P lt2 z f g p1 p2) = (term607 A B C P lt2 z f g p1 p2).
Proof. exact (@lem8222843 A B lt2 (term592 B C P z f g p1 p2)). Qed.
Lemma lem8222845 {A P : Type'} (s : P -> A) (p2 : P) : (@I (P -> A) s p2) = (@I (P -> A) s p2).
Proof. exact (eq_refl (@I (P -> A) s p2)). Qed.
Lemma lem8222846 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term606 A B C P lt2 z f g p1 s p2) = (term608 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8222844 A B C P lt2 z f g p1 p2) (@lem8222845 A P s p2)). Qed.
Lemma lem8222848 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222849 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8222848 A Prop f x). Qed.
Lemma lem8222850 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term608 A B C P lt2 z f g p1 s p2) = (term609 A B C P lt2 z f g p1 s p2).
Proof. exact (@lem8222849 A (term607 A B C P lt2 z f g p1 p2) (@I (P -> A) s p2)). Qed.
Lemma lem8222851 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term606 A B C P lt2 z f g p1 s p2) = (term609 A B C P lt2 z f g p1 s p2).
Proof. exact (TRANS (@lem8222846 A B C P lt2 z f g p1 s p2) (@lem8222850 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8222852 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term605 A B C P lt2 z f g p1 s p2) = (term609 A B C P lt2 z f g p1 s p2).
Proof. exact (TRANS (@lem8222840 A B C P lt2 z f g p1 s p2) (@lem8222851 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8222853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8222854 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term610 A B C P lt2 z f g p1 s p2) = (term611 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8222853) (@lem8222852 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8222855 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term612 A B C P lt2 s z f g p1 p2) = (term613 A B C P lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8222854 A B C P lt2 z f g p1 s p2) (@lem8222794 B C P z f g p1 p2)). Qed.
Lemma lem8222856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222863 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222864 {B C P : Type'} (f : type560 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> Prop) f x).
Proof. exact (@lem8222863 (B -> C) (P -> Prop) f x). Qed.
Lemma lem8222865 {B C P : Type'} (p : type560 B C P) (g : B -> C) : (p g) = (@I ((B -> C) -> P -> Prop) p g).
Proof. exact (@lem8222864 B C P p g). Qed.
Lemma lem8222866 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8222867 {B C P : Type'} (p : type560 B C P) (g : B -> C) (p2 : P) : (p g p2) = (@I ((B -> C) -> P -> Prop) p g p2).
Proof. exact (MK_COMB (@lem8222865 B C P p g) (@lem8222866 P p2)). Qed.
Lemma lem8222869 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222870 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8222869 P Prop f x). Qed.
Lemma lem8222871 {B C P : Type'} (p : type560 B C P) (g : B -> C) (p2 : P) : (@I ((B -> C) -> P -> Prop) p g p2) = (term558 B C P p g p2).
Proof. exact (@lem8222870 P (@I ((B -> C) -> P -> Prop) p g) p2). Qed.
Lemma lem8222873 {B C P : Type'} (p : type560 B C P) (g : B -> C) (p2 : P) : (p g p2) = (term558 B C P p g p2).
Proof. exact (TRANS (@lem8222867 B C P p g p2) (@lem8222871 B C P p g p2)). Qed.
Lemma lem8222874 {B C P : Type'} (p : type560 B C P) (g : B -> C) (p2 : P) : (term614 B C P p g p2) = (term615 B C P p g p2).
Proof. exact (MK_COMB (@lem8222856) (@lem8222873 B C P p g p2)). Qed.
Lemma lem8222875 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222883 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8222882 P nat f x). Qed.
Lemma lem8222885 {P : Type'} (b : P -> nat) (p2 : P) : (b p2) = (@I (P -> nat) b p2).
Proof. exact (@lem8222883 P b p2). Qed.
Lemma lem8222886 (p1 : nat) : (Peano.le p1) = (Peano.le p1).
Proof. exact (eq_refl (Peano.le p1)). Qed.
Lemma lem8222887 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term368 P p1 b p2) = (term571 P p1 b p2).
Proof. exact (MK_COMB (@lem8222886 p1) (@lem8222885 P b p2)). Qed.
Lemma lem8222889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222890 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8222889 nat (nat -> Prop) f x). Qed.
Lemma lem8222891 (p1 : nat) : (Peano.le p1) = (@I (nat -> nat -> Prop) Peano.le p1).
Proof. exact (@lem8222890 Peano.le p1). Qed.
Lemma lem8222892 {P : Type'} (b : P -> nat) (p2 : P) : (@I (P -> nat) b p2) = (@I (P -> nat) b p2).
Proof. exact (eq_refl (@I (P -> nat) b p2)). Qed.
Lemma lem8222893 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term571 P p1 b p2) = (term572 P p1 b p2).
Proof. exact (MK_COMB (@lem8222891 p1) (@lem8222892 P b p2)). Qed.
Lemma lem8222895 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222896 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8222895 nat Prop f x). Qed.
Lemma lem8222897 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term572 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (@lem8222896 (@I (nat -> nat -> Prop) Peano.le p1) (@I (P -> nat) b p2)). Qed.
Lemma lem8222898 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term571 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (TRANS (@lem8222893 P p1 b p2) (@lem8222897 P p1 b p2)). Qed.
Lemma lem8222899 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term368 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (TRANS (@lem8222887 P p1 b p2) (@lem8222898 P p1 b p2)). Qed.
Lemma lem8222900 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term616 P p1 b p2) = (term617 P p1 b p2).
Proof. exact (MK_COMB (@lem8222875) (@lem8222899 P p1 b p2)). Qed.
Lemma lem8222901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222902 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term618 P p1 b p2) = (term619 P p1 b p2).
Proof. exact (MK_COMB (@lem8222901) (@lem8222900 P p1 b p2)). Qed.
Lemma lem8222903 {B C P : Type'} (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term367 B C P p1 b p g p2) = (term620 B C P p1 b p g p2).
Proof. exact (MK_COMB (@lem8222902 P p1 b p2) (@lem8222874 B C P p g p2)). Qed.
Lemma lem8222904 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222905 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem8222910 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222911 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8222910 P nat f x). Qed.
Lemma lem8222913 {P : Type'} (a : P -> nat) (p2 : P) : (a p2) = (@I (P -> nat) a p2).
Proof. exact (@lem8222911 P a p2). Qed.
Lemma lem8222914 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8222915 {P : Type'} (a : P -> nat) (p2 : P) : (term574 P a p2) = (term575 P a p2).
Proof. exact (MK_COMB (@lem8222905) (@lem8222913 P a p2)). Qed.
Lemma lem8222916 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term373 P a p2 p1) = (term576 P a p2 p1).
Proof. exact (MK_COMB (@lem8222915 P a p2) (@lem8222914 p1)). Qed.
Lemma lem8222918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222919 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8222918 nat (nat -> Prop) f x). Qed.
Lemma lem8222920 {P : Type'} (a : P -> nat) (p2 : P) : (term575 P a p2) = (term577 P a p2).
Proof. exact (@lem8222919 Peano.le (@I (P -> nat) a p2)). Qed.
Lemma lem8222921 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8222922 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term576 P a p2 p1) = (term578 P a p2 p1).
Proof. exact (MK_COMB (@lem8222920 P a p2) (@lem8222921 p1)). Qed.
Lemma lem8222924 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222925 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8222924 nat Prop f x). Qed.
Lemma lem8222926 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term578 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (@lem8222925 (term577 P a p2) p1). Qed.
Lemma lem8222927 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term576 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (TRANS (@lem8222922 P a p2 p1) (@lem8222926 P a p2 p1)). Qed.
Lemma lem8222928 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term373 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (TRANS (@lem8222916 P a p2 p1) (@lem8222927 P a p2 p1)). Qed.
Lemma lem8222929 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term621 P a p2 p1) = (term622 P a p2 p1).
Proof. exact (MK_COMB (@lem8222904) (@lem8222928 P a p2 p1)). Qed.
Lemma lem8222930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222931 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term369 P a p2 p1) = (term623 P a p2 p1).
Proof. exact (MK_COMB (@lem8222930) (@lem8222929 P a p2 p1)). Qed.
Lemma lem8222932 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term371 B C P a p1 b p g p2) = (term624 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8222931 P a p2 p1) (@lem8222903 B C P p1 b p g p2)). Qed.
Lemma lem8222933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222934 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term387 B C P a p1 b p g p2) = (term625 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8222933) (@lem8222932 B C P a p1 b p g p2)). Qed.
Lemma lem8222935 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term626 A B C P a b p lt2 s z f g p1 p2) = (term627 A B C P a b p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8222934 B C P a p1 b p g p2) (@lem8222855 A B C P lt2 s z f g p1 p2)). Qed.
Lemma lem8222936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222944 {B C P : Type'} (f : type560 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> Prop) f x).
Proof. exact (@lem8222943 (B -> C) (P -> Prop) f x). Qed.
Lemma lem8222945 {B C P : Type'} (p : type560 B C P) (f : B -> C) : (p f) = (@I ((B -> C) -> P -> Prop) p f).
Proof. exact (@lem8222944 B C P p f). Qed.
Lemma lem8222946 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8222947 {B C P : Type'} (p : type560 B C P) (f : B -> C) (p2 : P) : (p f p2) = (@I ((B -> C) -> P -> Prop) p f p2).
Proof. exact (MK_COMB (@lem8222945 B C P p f) (@lem8222946 P p2)). Qed.
Lemma lem8222949 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222950 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8222949 P Prop f x). Qed.
Lemma lem8222951 {B C P : Type'} (p : type560 B C P) (f : B -> C) (p2 : P) : (@I ((B -> C) -> P -> Prop) p f p2) = (term558 B C P p f p2).
Proof. exact (@lem8222950 P (@I ((B -> C) -> P -> Prop) p f) p2). Qed.
Lemma lem8222953 {B C P : Type'} (p : type560 B C P) (f : B -> C) (p2 : P) : (p f p2) = (term558 B C P p f p2).
Proof. exact (TRANS (@lem8222947 B C P p f p2) (@lem8222951 B C P p f p2)). Qed.
Lemma lem8222954 {B C P : Type'} (p : type560 B C P) (f : B -> C) (p2 : P) : (term614 B C P p f p2) = (term615 B C P p f p2).
Proof. exact (MK_COMB (@lem8222936) (@lem8222953 B C P p f p2)). Qed.
Lemma lem8222955 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222962 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222963 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8222962 P nat f x). Qed.
Lemma lem8222965 {P : Type'} (b : P -> nat) (p2 : P) : (b p2) = (@I (P -> nat) b p2).
Proof. exact (@lem8222963 P b p2). Qed.
Lemma lem8222966 (p1 : nat) : (Peano.le p1) = (Peano.le p1).
Proof. exact (eq_refl (Peano.le p1)). Qed.
Lemma lem8222967 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term368 P p1 b p2) = (term571 P p1 b p2).
Proof. exact (MK_COMB (@lem8222966 p1) (@lem8222965 P b p2)). Qed.
Lemma lem8222969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222970 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8222969 nat (nat -> Prop) f x). Qed.
Lemma lem8222971 (p1 : nat) : (Peano.le p1) = (@I (nat -> nat -> Prop) Peano.le p1).
Proof. exact (@lem8222970 Peano.le p1). Qed.
Lemma lem8222972 {P : Type'} (b : P -> nat) (p2 : P) : (@I (P -> nat) b p2) = (@I (P -> nat) b p2).
Proof. exact (eq_refl (@I (P -> nat) b p2)). Qed.
Lemma lem8222973 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term571 P p1 b p2) = (term572 P p1 b p2).
Proof. exact (MK_COMB (@lem8222971 p1) (@lem8222972 P b p2)). Qed.
Lemma lem8222975 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222976 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8222975 nat Prop f x). Qed.
Lemma lem8222977 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term572 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (@lem8222976 (@I (nat -> nat -> Prop) Peano.le p1) (@I (P -> nat) b p2)). Qed.
Lemma lem8222978 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term571 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (TRANS (@lem8222973 P p1 b p2) (@lem8222977 P p1 b p2)). Qed.
Lemma lem8222979 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term368 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (TRANS (@lem8222967 P p1 b p2) (@lem8222978 P p1 b p2)). Qed.
Lemma lem8222980 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term616 P p1 b p2) = (term617 P p1 b p2).
Proof. exact (MK_COMB (@lem8222955) (@lem8222979 P p1 b p2)). Qed.
Lemma lem8222981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8222982 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term618 P p1 b p2) = (term619 P p1 b p2).
Proof. exact (MK_COMB (@lem8222981) (@lem8222980 P p1 b p2)). Qed.
Lemma lem8222983 {B C P : Type'} (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term367 B C P p1 b p f p2) = (term620 B C P p1 b p f p2).
Proof. exact (MK_COMB (@lem8222982 P p1 b p2) (@lem8222954 B C P p f p2)). Qed.
Lemma lem8222984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8222985 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem8222990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222991 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8222990 P nat f x). Qed.
Lemma lem8222993 {P : Type'} (a : P -> nat) (p2 : P) : (a p2) = (@I (P -> nat) a p2).
Proof. exact (@lem8222991 P a p2). Qed.
Lemma lem8222994 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8222995 {P : Type'} (a : P -> nat) (p2 : P) : (term574 P a p2) = (term575 P a p2).
Proof. exact (MK_COMB (@lem8222985) (@lem8222993 P a p2)). Qed.
Lemma lem8222996 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term373 P a p2 p1) = (term576 P a p2 p1).
Proof. exact (MK_COMB (@lem8222995 P a p2) (@lem8222994 p1)). Qed.
Lemma lem8222998 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8222999 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8222998 nat (nat -> Prop) f x). Qed.
Lemma lem8223000 {P : Type'} (a : P -> nat) (p2 : P) : (term575 P a p2) = (term577 P a p2).
Proof. exact (@lem8222999 Peano.le (@I (P -> nat) a p2)). Qed.
Lemma lem8223001 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8223002 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term576 P a p2 p1) = (term578 P a p2 p1).
Proof. exact (MK_COMB (@lem8223000 P a p2) (@lem8223001 p1)). Qed.
Lemma lem8223004 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8223005 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8223004 nat Prop f x). Qed.
Lemma lem8223006 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term578 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (@lem8223005 (term577 P a p2) p1). Qed.
Lemma lem8223007 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term576 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (TRANS (@lem8223002 P a p2 p1) (@lem8223006 P a p2 p1)). Qed.
Lemma lem8223008 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term373 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (TRANS (@lem8222996 P a p2 p1) (@lem8223007 P a p2 p1)). Qed.
Lemma lem8223009 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term621 P a p2 p1) = (term622 P a p2 p1).
Proof. exact (MK_COMB (@lem8222984) (@lem8223008 P a p2 p1)). Qed.
Lemma lem8223010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8223011 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term369 P a p2 p1) = (term623 P a p2 p1).
Proof. exact (MK_COMB (@lem8223010) (@lem8223009 P a p2 p1)). Qed.
Lemma lem8223012 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term371 B C P a p1 b p f p2) = (term624 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8223011 P a p2 p1) (@lem8222983 B C P p1 b p f p2)). Qed.
Lemma lem8223013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8223014 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term387 B C P a p1 b p f p2) = (term625 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8223013) (@lem8223012 B C P a p1 b p f p2)). Qed.
Lemma lem8223015 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term628 A B C P a b p lt2 s z f g p1 p2) = (term629 A B C P a b p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8223014 B C P a p1 b p f p2) (@lem8222935 A B C P a b p lt2 s z f g p1 p2)). Qed.
Lemma lem8223016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8223017 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term630 A B C P a b p lt2 s z f g p1 p2) = (term631 A B C P a b p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8223016) (@lem8223015 A B C P a b p lt2 s z f g p1 p2)). Qed.
Lemma lem8223018 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term632 A B C P a b p lt2 s z f h g p2 p1) = (term633 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (MK_COMB (@lem8223017 A B C P a b p lt2 s z f g p1 p2) (@lem8222705 B C P f h g p2 p1)). Qed.
Lemma lem8223019 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term634 A B C P a b p lt2 s z f h g p1) = (term635 A B C P a b p lt2 s z f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8223018 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8223020 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8223021 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term636 A B C P a b p lt2 s z f h g p1) = (term637 A B C P a b p lt2 s z f h g p1).
Proof. exact (MK_COMB (@lem8223020 P) (@lem8223019 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8223022 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term638 A B C P a b p lt2 s z f h g) = (term639 A B C P a b p lt2 s z f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8223021 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8223023 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8223024 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term640 A B C P a b p lt2 s z f h g) = (term641 A B C P a b p lt2 s z f h g).
Proof. exact (MK_COMB (@lem8223023) (@lem8223022 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8223025 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) : (term642 A B C P a b p lt2 s z f h) = (term643 A B C P a b p lt2 s z f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8223024 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8223026 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8223027 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type556 B C P) : (term546 A B C P a b p lt2 s z f h) = (term644 A B C P a b p lt2 s z f h).
Proof. exact (MK_COMB (@lem8223026 B C) (@lem8223025 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8223028 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) : (term548 A B C P a b p lt2 s z h) = (term645 A B C P a b p lt2 s z h).
Proof. exact (fun_ext (fun f : B -> C => @lem8223027 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8223029 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8223030 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) : (term550 A B C P a b p lt2 s z h) = (term646 A B C P a b p lt2 s z h).
Proof. exact (MK_COMB (@lem8223029 B C) (@lem8223028 A B C P a b p lt2 s z h)). Qed.
Lemma lem8223031 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term646 A B C P a b p lt2 s z h.
Proof. exact (EQ_MP (@lem8223030 A B C P a b p lt2 s z h) (@lem8222452 A B C P a b p lt2 s z h h1)). Qed.
Lemma lem8223049 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (z : B) : (term568 A B C P lt2 s a' f g z) = (term568 A B C P lt2 s a' f g z).
Proof. exact (eq_refl (term568 A B C P lt2 s a' f g z)). Qed.
Lemma lem8223050 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term569 A B C P lt2 s a' f g) = (term569 A B C P lt2 s a' f g).
Proof. exact (fun_ext (fun z : B => @lem8223049 A B C P lt2 s a' f g z)). Qed.
Lemma lem8223051 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8223053 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term570 A B C P lt2 s a' f g) = (term570 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8223051 B) (@lem8223050 A B C P lt2 s a' f g)). Qed.
Lemma lem8223054 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term570 A B C P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8223053 A B C P lt2 s a' f g) (@lem8222540 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8223060 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1)) = ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1)).
Proof. exact (eq_refl ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1))). Qed.
Lemma lem8223089 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term627 A B C P a b p lt2 s z f g p1 p2) = (term647 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (@lem19490 (term609 A B C P lt2 z f g p1 s p2) (term624 B C P a p1 b p g p2) (term602 B C P z f g p1 p2)). Qed.
Lemma lem8223104 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term625 B C P a p1 b p f p2) = (term625 B C P a p1 b p f p2).
Proof. exact (eq_refl (term625 B C P a p1 b p f p2)). Qed.
Lemma lem8223105 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term629 A B C P a b p lt2 s z f g p1 p2) = (term648 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (MK_COMB (@lem8223104 B C P a p1 b p f p2) (@lem8223089 A B C P lt2 s a b p z f g p1 p2)). Qed.
Lemma lem8223112 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term648 A B C P lt2 s a b p z f g p1 p2) = (term649 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (@lem19490 (term650 A B C P a b p lt2 z f g p1 s p2) (term624 B C P a p1 b p f p2) (term651 B C P a b p z f g p1 p2)). Qed.
Lemma lem8223113 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term629 A B C P a b p lt2 s z f g p1 p2) = (term649 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (TRANS (@lem8223105 A B C P lt2 s a b p z f g p1 p2) (@lem8223112 A B C P lt2 s a b p z f g p1 p2)). Qed.
Lemma lem8223114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8223115 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term631 A B C P a b p lt2 s z f g p1 p2) = (term652 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (MK_COMB (@lem8223114) (@lem8223113 A B C P lt2 s a b p z f g p1 p2)). Qed.
Lemma lem8223116 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term633 A B C P a b p lt2 s z f h g p2 p1) = (term653 A B C P lt2 s a b p z f h g p2 p1).
Proof. exact (MK_COMB (@lem8223115 A B C P lt2 s a b p z f g p1 p2) (@lem8223060 B C P f h g p2 p1)). Qed.
Lemma lem8223123 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term653 A B C P lt2 s a b p z f h g p2 p1) = (term654 A B C P lt2 s a b p z f h g p2 p1).
Proof. exact (@lem19699 (term655 A B C P a b p lt2 z f g p1 s p2) (term656 B C P a b p z f g p1 p2) ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1))). Qed.
Lemma lem8223124 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term633 A B C P a b p lt2 s z f h g p2 p1) = (term654 A B C P lt2 s a b p z f h g p2 p1).
Proof. exact (TRANS (@lem8223116 A B C P lt2 s a b p z f h g p2 p1) (@lem8223123 A B C P lt2 s a b p z f h g p2 p1)). Qed.
Lemma lem8223125 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term635 A B C P a b p lt2 s z f h g p1) = (term657 A B C P lt2 s a b p z f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8223124 A B C P lt2 s a b p z f h g p2 p1)). Qed.
Lemma lem8223126 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8223127 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) (p1 : nat) : (term637 A B C P a b p lt2 s z f h g p1) = (term658 A B C P lt2 s a b p z f h g p1).
Proof. exact (MK_COMB (@lem8223126 P) (@lem8223125 A B C P lt2 s a b p z f h g p1)). Qed.
Lemma lem8223128 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term639 A B C P a b p lt2 s z f h g) = (term659 A B C P lt2 s a b p z f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8223127 A B C P lt2 s a b p z f h g p1)). Qed.
Lemma lem8223129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8223130 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) (g : B -> C) : (term641 A B C P a b p lt2 s z f h g) = (term660 A B C P lt2 s a b p z f h g).
Proof. exact (MK_COMB (@lem8223129) (@lem8223128 A B C P lt2 s a b p z f h g)). Qed.
Lemma lem8223131 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) : (term643 A B C P a b p lt2 s z f h) = (term661 A B C P lt2 s a b p z f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8223130 A B C P lt2 s a b p z f h g)). Qed.
Lemma lem8223132 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8223133 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type556 B C P) : (term644 A B C P a b p lt2 s z f h) = (term662 A B C P lt2 s a b p z f h).
Proof. exact (MK_COMB (@lem8223132 B C) (@lem8223131 A B C P lt2 s a b p z f h)). Qed.
Lemma lem8223134 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (h : type556 B C P) : (term645 A B C P a b p lt2 s z h) = (term663 A B C P lt2 s a b p z h).
Proof. exact (fun_ext (fun f : B -> C => @lem8223133 A B C P lt2 s a b p z f h)). Qed.
Lemma lem8223135 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8223137 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (h : type556 B C P) : (term646 A B C P a b p lt2 s z h) = (term664 A B C P lt2 s a b p z h).
Proof. exact (MK_COMB (@lem8223135 B C) (@lem8223134 A B C P lt2 s a b p z h)). Qed.
Lemma lem8223138 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term664 A B C P lt2 s a b p z h.
Proof. exact (EQ_MP (@lem8223137 A B C P lt2 s a b p z h) (@lem8223031 A B C P a b p lt2 s z h h1)). Qed.
Lemma lem8223147 {A B C P : Type'} (_109326 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term665 A B C P lt2 s a' f g _109326.
Proof. exact (@lem8223054 A B C P lt2 s a' f g h1 _109326). Qed.
Lemma lem8223148 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (_109326 : B) : (term665 A B C P lt2 s a' f g _109326) = (term568 A B C P lt2 s a' f g _109326).
Proof. exact (eq_refl (term665 A B C P lt2 s a' f g _109326)). Qed.
Lemma lem8223150 {A B C P : Type'} (_109327 : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term666 A B C P lt2 s a b p z h _109327.
Proof. exact (@lem8223138 A B C P a b p lt2 s z h h1 _109327). Qed.
Lemma lem8223151 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) : (term666 A B C P lt2 s a b p z h _109327) = (term662 A B C P lt2 s a b p z _109327 h).
Proof. exact (eq_refl (term666 A B C P lt2 s a b p z h _109327)). Qed.
Lemma lem8223152 {A B C P : Type'} (_109327 : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term662 A B C P lt2 s a b p z _109327 h.
Proof. exact (EQ_MP (@lem8223151 A B C P lt2 s a b p z _109327 h) (@lem8223150 A B C P _109327 a b p lt2 s z h h1)). Qed.
Lemma lem8223153 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term667 A B C P lt2 s a b p z _109327 h _109328.
Proof. exact (@lem8223152 A B C P _109327 a b p lt2 s z h h1 _109328). Qed.
Lemma lem8223154 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) : (term667 A B C P lt2 s a b p z _109327 h _109328) = (term660 A B C P lt2 s a b p z _109327 h _109328).
Proof. exact (eq_refl (term667 A B C P lt2 s a b p z _109327 h _109328)). Qed.
Lemma lem8223155 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term660 A B C P lt2 s a b p z _109327 h _109328.
Proof. exact (EQ_MP (@lem8223154 A B C P lt2 s a b p z _109327 h _109328) (@lem8223153 A B C P _109327 _109328 a b p lt2 s z h h1)). Qed.
Lemma lem8223156 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term668 A B C P lt2 s a b p z _109327 h _109328 _109329.
Proof. exact (@lem8223155 A B C P _109327 _109328 a b p lt2 s z h h1 _109329). Qed.
Lemma lem8223157 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109329 : nat) : (term668 A B C P lt2 s a b p z _109327 h _109328 _109329) = (term658 A B C P lt2 s a b p z _109327 h _109328 _109329).
Proof. exact (eq_refl (term668 A B C P lt2 s a b p z _109327 h _109328 _109329)). Qed.
Lemma lem8223158 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term658 A B C P lt2 s a b p z _109327 h _109328 _109329.
Proof. exact (EQ_MP (@lem8223157 A B C P lt2 s a b p z _109327 h _109328 _109329) (@lem8223156 A B C P _109327 _109328 _109329 a b p lt2 s z h h1)). Qed.
Lemma lem8223159 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term669 A B C P lt2 s a b p z _109327 h _109328 _109329 _109330.
Proof. exact (@lem8223158 A B C P _109327 _109328 _109329 a b p lt2 s z h h1 _109330). Qed.
Lemma lem8223160 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term669 A B C P lt2 s a b p z _109327 h _109328 _109329 _109330) = (term654 A B C P lt2 s a b p z _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term669 A B C P lt2 s a b p z _109327 h _109328 _109329 _109330)). Qed.
Lemma lem8223161 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109330 : P) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term654 A B C P lt2 s a b p z _109327 h _109328 _109330 _109329.
Proof. exact (EQ_MP (@lem8223160 A B C P lt2 s a b p z _109327 h _109328 _109330 _109329) (@lem8223159 A B C P _109327 _109328 _109329 _109330 a b p lt2 s z h h1)). Qed.
Lemma lem8223162 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109330 : P) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term670 B C P a b p z _109327 h _109328 _109330 _109329.
Proof. exact (proj2 (@lem8223161 A B C P _109327 _109328 _109330 _109329 a b p lt2 s z h h1)). Qed.
Lemma lem8223163 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109330 : P) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term671 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329.
Proof. exact (proj1 (@lem8223161 A B C P _109327 _109328 _109330 _109329 a b p lt2 s z h h1)). Qed.
Lemma lem8223173 {A B C P : Type'} (_109326 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term568 A B C P lt2 s a' f g _109326.
Proof. exact (EQ_MP (@lem8223148 A B C P lt2 s a' f g _109326) (@lem8223147 A B C P _109326 lt2 s a' f g h1)). Qed.
Lemma lem8223175 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term365 B C P f h g a' i) : term587 B C P f h g a' i.
Proof. exact (EQ_MP (@lem8222649 B C P f h g a' i) (@lem8222451 B C P f h g a' i h1)). Qed.
Lemma lem8223183 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term671 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term672 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term624 B C P a _109329 b p _109327 _109330) (term650 A B C P a b p lt2 z _109327 _109328 _109329 s _109330) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8223184 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term673 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term674 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term624 B C P a _109329 b p _109328 _109330) (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8223188 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term674 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term675 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term622 P a _109330 _109329) (term620 B C P _109329 b p _109328 _109330) (term676 A B C P lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223195 {A B C P : Type'} (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term677 A B C P b p lt2 z s _109327 h _109328 _109330 _109329) = (term678 A B C P b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term617 P _109329 b _109330) (term615 B C P p _109328 _109330) (term676 A B C P lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223196 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term623 P a _109330 _109329) = (term623 P a _109330 _109329).
Proof. exact (eq_refl (term623 P a _109330 _109329)). Qed.
Lemma lem8223199 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term675 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term679 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8223196 P a _109330 _109329) (@lem8223195 A B C P b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223201 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term674 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term679 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223188 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223199 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223202 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term673 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term679 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223184 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223201 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223203 {B C P : Type'} (a : P -> nat) (_109329 : nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term625 B C P a _109329 b p _109327 _109330) = (term625 B C P a _109329 b p _109327 _109330).
Proof. exact (eq_refl (term625 B C P a _109329 b p _109327 _109330)). Qed.
Lemma lem8223204 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term672 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term680 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8223203 B C P a _109329 b p _109327 _109330) (@lem8223202 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223205 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term680 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term681 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term622 P a _109330 _109329) (term620 B C P _109329 b p _109327 _109330) (term679 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223212 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term682 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term683 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term617 P _109329 b _109330) (term615 B C P p _109327 _109330) (term679 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223213 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term623 P a _109330 _109329) = (term623 P a _109330 _109329).
Proof. exact (eq_refl (term623 P a _109330 _109329)). Qed.
Lemma lem8223216 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term681 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8223213 P a _109330 _109329) (@lem8223212 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223217 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term680 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223205 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223216 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223218 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term672 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223204 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223217 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223220 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term671 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223183 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223218 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223221 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109330 : P) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329.
Proof. exact (EQ_MP (@lem8223220 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223163 A B C P _109327 _109328 _109330 _109329 a b p lt2 s z h h1)). Qed.
Lemma lem8223225 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term670 B C P a b p z _109327 h _109328 _109330 _109329) = (term685 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term624 B C P a _109329 b p _109327 _109330) (term651 B C P a b p z _109327 _109328 _109329 _109330) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8223226 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term686 B C P a b p z _109327 h _109328 _109330 _109329) = (term687 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term624 B C P a _109329 b p _109328 _109330) (term602 B C P z _109327 _109328 _109329 _109330) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8223230 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term687 B C P a b p z _109327 h _109328 _109330 _109329) = (term688 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term622 P a _109330 _109329) (term620 B C P _109329 b p _109328 _109330) (term689 B C P z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223237 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term690 B C P b p z _109327 h _109328 _109330 _109329) = (term691 B C P b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term617 P _109329 b _109330) (term615 B C P p _109328 _109330) (term689 B C P z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223238 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term623 P a _109330 _109329) = (term623 P a _109330 _109329).
Proof. exact (eq_refl (term623 P a _109330 _109329)). Qed.
Lemma lem8223241 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term688 B C P a b p z _109327 h _109328 _109330 _109329) = (term692 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8223238 P a _109330 _109329) (@lem8223237 B C P b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223243 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term687 B C P a b p z _109327 h _109328 _109330 _109329) = (term692 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223230 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8223241 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223244 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term686 B C P a b p z _109327 h _109328 _109330 _109329) = (term692 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223226 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8223243 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223245 {B C P : Type'} (a : P -> nat) (_109329 : nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term625 B C P a _109329 b p _109327 _109330) = (term625 B C P a _109329 b p _109327 _109330).
Proof. exact (eq_refl (term625 B C P a _109329 b p _109327 _109330)). Qed.
Lemma lem8223246 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term685 B C P a b p z _109327 h _109328 _109330 _109329) = (term693 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8223245 B C P a _109329 b p _109327 _109330) (@lem8223244 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223247 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term693 B C P a b p z _109327 h _109328 _109330 _109329) = (term694 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term622 P a _109330 _109329) (term620 B C P _109329 b p _109327 _109330) (term692 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223254 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term695 B C P a b p z _109327 h _109328 _109330 _109329) = (term696 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8220454 (term617 P _109329 b _109330) (term615 B C P p _109327 _109330) (term692 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223255 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term623 P a _109330 _109329) = (term623 P a _109330 _109329).
Proof. exact (eq_refl (term623 P a _109330 _109329)). Qed.
Lemma lem8223258 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term694 B C P a b p z _109327 h _109328 _109330 _109329) = (term697 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8223255 P a _109330 _109329) (@lem8223254 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223259 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term693 B C P a b p z _109327 h _109328 _109330 _109329) = (term697 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223247 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8223258 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223260 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term685 B C P a b p z _109327 h _109328 _109330 _109329) = (term697 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223246 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8223259 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223262 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term670 B C P a b p z _109327 h _109328 _109330 _109329) = (term697 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223225 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8223260 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223263 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109330 : P) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term697 B C P a b p z _109327 h _109328 _109330 _109329.
Proof. exact (EQ_MP (@lem8223262 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8223162 A B C P _109327 _109328 _109330 _109329 a b p lt2 s z h h1)). Qed.
Lemma lem8223561 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (proj1 (@lem8222592 P a i b a' h1)). Qed.
Lemma lem8223562 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term698 P a a' i.
Proof. exact (fun h0 : term622 P a a' i => @lem8223561 P a i b a' h1). Qed.
Lemma lem8223564 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223565 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term698 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8223564 (term579 P a a' i)). Qed.
Lemma lem8223566 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (EQ_MP (@lem8223565 P a a' i) (@lem8223562 P a i b a' h1)). Qed.
Lemma lem8223568 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (proj2 (@lem8222592 P a i b a' h1)). Qed.
Lemma lem8223569 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term700 P i b a'.
Proof. exact (fun h0 : term617 P i b a' => @lem8223568 P a i b a' h1). Qed.
Lemma lem8223571 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223572 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term700 P i b a') = (term573 P i b a').
Proof. exact (@lem8223571 (term573 P i b a')). Qed.
Lemma lem8223573 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (EQ_MP (@lem8223572 P i b a') (@lem8223569 P a i b a' h1)). Qed.
Lemma lem8223575 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term558 B C P p f a'.
Proof. exact (EQ_MP (@lem8222469 B C P p f a') (@lem8222366 B C P p f a' h1)). Qed.
Lemma lem8223576 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term701 B C P p f a'.
Proof. exact (fun h0 : term615 B C P p f a' => @lem8223575 B C P p f a' h1). Qed.
Lemma lem8223578 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223579 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (term701 B C P p f a') = (term558 B C P p f a').
Proof. exact (@lem8223578 (term558 B C P p f a')). Qed.
Lemma lem8223580 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term558 B C P p f a'.
Proof. exact (EQ_MP (@lem8223579 B C P p f a') (@lem8223576 B C P p f a' h1)). Qed.
Lemma lem8223582 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (proj1 (@lem8222592 P a i b a' h1)). Qed.
Lemma lem8223583 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term698 P a a' i.
Proof. exact (fun h0 : term622 P a a' i => @lem8223582 P a i b a' h1). Qed.
Lemma lem8223585 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223586 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term698 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8223585 (term579 P a a' i)). Qed.
Lemma lem8223587 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (EQ_MP (@lem8223586 P a a' i) (@lem8223583 P a i b a' h1)). Qed.
Lemma lem8223589 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (proj2 (@lem8222592 P a i b a' h1)). Qed.
Lemma lem8223590 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term700 P i b a'.
Proof. exact (fun h0 : term617 P i b a' => @lem8223589 P a i b a' h1). Qed.
Lemma lem8223592 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223593 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term700 P i b a') = (term573 P i b a').
Proof. exact (@lem8223592 (term573 P i b a')). Qed.
Lemma lem8223594 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (EQ_MP (@lem8223593 P i b a') (@lem8223590 P a i b a' h1)). Qed.
Lemma lem8223596 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term558 B C P p g a'.
Proof. exact (EQ_MP (@lem8222487 B C P p g a') (@lem8222372 B C P p g a' h1)). Qed.
Lemma lem8223597 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term701 B C P p g a'.
Proof. exact (fun h0 : term615 B C P p g a' => @lem8223596 B C P p g a' h1). Qed.
Lemma lem8223599 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223600 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (term701 B C P p g a') = (term558 B C P p g a').
Proof. exact (@lem8223599 (term558 B C P p g a')). Qed.
Lemma lem8223601 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term558 B C P p g a'.
Proof. exact (EQ_MP (@lem8223600 B C P p g a') (@lem8223597 B C P p g a' h1)). Qed.
Lemma lem8223603 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (proj1 (@lem8222592 P a i b a' h1)). Qed.
Lemma lem8223604 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term698 P a a' i.
Proof. exact (fun h0 : term622 P a a' i => @lem8223603 P a i b a' h1). Qed.
Lemma lem8223606 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223607 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term698 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8223606 (term579 P a a' i)). Qed.
Lemma lem8223608 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (EQ_MP (@lem8223607 P a a' i) (@lem8223604 P a i b a' h1)). Qed.
Lemma lem8223610 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (proj2 (@lem8222592 P a i b a' h1)). Qed.
Lemma lem8223611 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term700 P i b a'.
Proof. exact (fun h0 : term617 P i b a' => @lem8223610 P a i b a' h1). Qed.
Lemma lem8223613 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223614 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term700 P i b a') = (term573 P i b a').
Proof. exact (@lem8223613 (term573 P i b a')). Qed.
Lemma lem8223615 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (EQ_MP (@lem8223614 P i b a') (@lem8223611 P a i b a' h1)). Qed.
Lemma lem8223617 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term558 B C P p f a'.
Proof. exact (EQ_MP (@lem8222469 B C P p f a') (@lem8222366 B C P p f a' h1)). Qed.
Lemma lem8223618 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term701 B C P p f a'.
Proof. exact (fun h0 : term615 B C P p f a' => @lem8223617 B C P p f a' h1). Qed.
Lemma lem8223620 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223621 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (term701 B C P p f a') = (term558 B C P p f a').
Proof. exact (@lem8223620 (term558 B C P p f a')). Qed.
Lemma lem8223622 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term558 B C P p f a'.
Proof. exact (EQ_MP (@lem8223621 B C P p f a') (@lem8223618 B C P p f a' h1)). Qed.
Lemma lem8223624 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (proj1 (@lem8222592 P a i b a' h1)). Qed.
Lemma lem8223625 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term698 P a a' i.
Proof. exact (fun h0 : term622 P a a' i => @lem8223624 P a i b a' h1). Qed.
Lemma lem8223627 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223628 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term698 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8223627 (term579 P a a' i)). Qed.
Lemma lem8223629 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (EQ_MP (@lem8223628 P a a' i) (@lem8223625 P a i b a' h1)). Qed.
Lemma lem8223631 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (proj2 (@lem8222592 P a i b a' h1)). Qed.
Lemma lem8223632 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term700 P i b a'.
Proof. exact (fun h0 : term617 P i b a' => @lem8223631 P a i b a' h1). Qed.
Lemma lem8223634 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223635 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term700 P i b a') = (term573 P i b a').
Proof. exact (@lem8223634 (term573 P i b a')). Qed.
Lemma lem8223636 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (EQ_MP (@lem8223635 P i b a') (@lem8223632 P a i b a' h1)). Qed.
Lemma lem8223638 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term558 B C P p g a'.
Proof. exact (EQ_MP (@lem8222487 B C P p g a') (@lem8222372 B C P p g a' h1)). Qed.
Lemma lem8223639 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term701 B C P p g a'.
Proof. exact (fun h0 : term615 B C P p g a' => @lem8223638 B C P p g a' h1). Qed.
Lemma lem8223641 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8223642 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (term701 B C P p g a') = (term558 B C P p g a').
Proof. exact (@lem8223641 (term558 B C P p g a')). Qed.
Lemma lem8223643 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term558 B C P p g a'.
Proof. exact (EQ_MP (@lem8223642 B C P p g a') (@lem8223639 B C P p g a' h1)). Qed.
Lemma lem8223646 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term587 B C P f h g a' i) : term587 B C P f h g a' i.
Proof. exact (h1). Qed.
Lemma lem8223647 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term587 B C P f h g a' i) : term702 B C P f h g a' i.
Proof. exact (fun h0 : (term585 B C P h f a' i) = (term585 B C P h g a' i) => @lem8223646 B C P f h g a' i h1). Qed.
Lemma lem8223649 (p : Prop) : (term703 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8223650 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (term702 B C P f h g a' i) = (term587 B C P f h g a' i).
Proof. exact (@lem8223649 ((term585 B C P h f a' i) = (term585 B C P h g a' i))). Qed.
Lemma lem8223651 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term587 B C P f h g a' i) : term587 B C P f h g a' i.
Proof. exact (EQ_MP (@lem8223650 B C P f h g a' i) (@lem8223647 B C P f h g a' i h1)). Qed.
Lemma lem8223657 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223658 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term704 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8223657 (term617 P _109329 b _109330) (term622 P a _109330 _109329) (term705 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223672 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223673 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term706 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term707 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8223672 (term615 B C P p _109327 _109330) (term622 P a _109330 _109329) (term679 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223685 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8223686 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term709 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term679 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8223685 (term622 P a _109330 _109329) (term678 A B C P b p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223690 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223691 {A B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term679 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term710 A B C P b a p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8223690 (term617 P _109329 b _109330) (term622 P a _109330 _109329) (term711 A B C P p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223702 {A B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term709 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term710 A B C P b a p lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8223686 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223691 A B C P b a p lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223706 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223707 {A B C P : Type'} (p : type560 B C P) (a : P -> nat) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term712 A B C P a p lt2 z s _109327 h _109328 _109330 _109329) = (term713 A B C P p a lt2 z s _109327 h _109328 _109330 _109329).
Proof. exact (@lem8223706 (term615 B C P p _109328 _109330) (term622 P a _109330 _109329) (term676 A B C P lt2 z s _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223721 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223722 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (a : P -> nat) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term714 A B C P a lt2 z s _109327 h _109328 _109330 _109329) = (term715 A B C P lt2 z s a _109327 h _109328 _109330 _109329).
Proof. exact (@lem8223721 (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) (term622 P a _109330 _109329) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8223736 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8223737 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term716 B C P a _109327 h _109328 _109330 _109329) = (term717 B C P _109327 h _109328 a _109330 _109329).
Proof. exact (@lem8223736 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term622 P a _109330 _109329)). Qed.
Lemma lem8223745 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (s : P -> A) (_109330 : P) : (term718 A B C P lt2 z _109327 _109328 _109329 s _109330) = (term718 A B C P lt2 z _109327 _109328 _109329 s _109330).
Proof. exact (eq_refl (term718 A B C P lt2 z _109327 _109328 _109329 s _109330)). Qed.
Lemma lem8223746 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term715 A B C P lt2 z s a _109327 h _109328 _109330 _109329) = (term719 A B C P lt2 z s _109327 h _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8223745 A B C P lt2 z _109327 _109328 _109329 s _109330) (@lem8223737 B C P _109327 h _109328 a _109330 _109329)). Qed.
Lemma lem8223750 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223751 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (s : P -> A) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term719 A B C P lt2 z s _109327 h _109328 a _109330 _109329) = (term720 A B C P h lt2 z _109327 _109328 s a _109330 _109329).
Proof. exact (@lem8223750 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8223769 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (s : P -> A) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term715 A B C P lt2 z s a _109327 h _109328 _109330 _109329) = (term720 A B C P h lt2 z _109327 _109328 s a _109330 _109329).
Proof. exact (TRANS (@lem8223746 A B C P lt2 z s _109327 h _109328 a _109330 _109329) (@lem8223751 A B C P h lt2 z _109327 _109328 s a _109330 _109329)). Qed.
Lemma lem8223770 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (s : P -> A) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term714 A B C P a lt2 z s _109327 h _109328 _109330 _109329) = (term720 A B C P h lt2 z _109327 _109328 s a _109330 _109329).
Proof. exact (TRANS (@lem8223722 A B C P lt2 z s a _109327 h _109328 _109330 _109329) (@lem8223769 A B C P h lt2 z _109327 _109328 s a _109330 _109329)). Qed.
Lemma lem8223771 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term721 B C P p _109328 _109330) = (term721 B C P p _109328 _109330).
Proof. exact (eq_refl (term721 B C P p _109328 _109330)). Qed.
Lemma lem8223772 {A B C P : Type'} (p : type560 B C P) (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (s : P -> A) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term713 A B C P p a lt2 z s _109327 h _109328 _109330 _109329) = (term722 A B C P p h lt2 z _109327 _109328 s a _109330 _109329).
Proof. exact (MK_COMB (@lem8223771 B C P p _109328 _109330) (@lem8223770 A B C P h lt2 z _109327 _109328 s a _109330 _109329)). Qed.
Lemma lem8223776 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223777 {A B C P : Type'} (h : type556 B C P) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (s : P -> A) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term722 A B C P p h lt2 z _109327 _109328 s a _109330 _109329) = (term723 A B C P h p lt2 z _109327 _109328 s a _109330 _109329).
Proof. exact (@lem8223776 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term615 B C P p _109328 _109330) (term724 A B C P lt2 z _109327 _109328 s a _109330 _109329)). Qed.
Lemma lem8223793 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223794 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term725 A B C P p lt2 z _109327 _109328 s a _109330 _109329) = (term726 A B C P lt2 z _109327 s p _109328 a _109330 _109329).
Proof. exact (@lem8223793 (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) (term615 B C P p _109328 _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8223810 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223811 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term723 A B C P h p lt2 z _109327 _109328 s a _109330 _109329) = (term728 A B C P h lt2 z _109327 s p _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8223810 B C P _109327 h _109328 _109330 _109329) (@lem8223794 A B C P lt2 z _109327 s p _109328 a _109330 _109329)). Qed.
Lemma lem8223822 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term722 A B C P p h lt2 z _109327 _109328 s a _109330 _109329) = (term728 A B C P h lt2 z _109327 s p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8223777 A B C P h p lt2 z _109327 _109328 s a _109330 _109329) (@lem8223811 A B C P h lt2 z _109327 s p _109328 a _109330 _109329)). Qed.
Lemma lem8223823 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term713 A B C P p a lt2 z s _109327 h _109328 _109330 _109329) = (term728 A B C P h lt2 z _109327 s p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8223772 A B C P p h lt2 z _109327 _109328 s a _109330 _109329) (@lem8223822 A B C P h lt2 z _109327 s p _109328 a _109330 _109329)). Qed.
Lemma lem8223824 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term712 A B C P a p lt2 z s _109327 h _109328 _109330 _109329) = (term728 A B C P h lt2 z _109327 s p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8223707 A B C P p a lt2 z s _109327 h _109328 _109330 _109329) (@lem8223823 A B C P h lt2 z _109327 s p _109328 a _109330 _109329)). Qed.
Lemma lem8223825 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term619 P _109329 b _109330) = (term619 P _109329 b _109330).
Proof. exact (eq_refl (term619 P _109329 b _109330)). Qed.
Lemma lem8223826 {A B C P : Type'} (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term710 A B C P b a p lt2 z s _109327 h _109328 _109330 _109329) = (term729 A B C P b h lt2 z _109327 s p _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8223825 P _109329 b _109330) (@lem8223824 A B C P h lt2 z _109327 s p _109328 a _109330 _109329)). Qed.
Lemma lem8223830 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223831 {A B C P : Type'} (h : type556 B C P) (b : P -> nat) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term729 A B C P b h lt2 z _109327 s p _109328 a _109330 _109329) = (term730 A B C P h b lt2 z _109327 s p _109328 a _109330 _109329).
Proof. exact (@lem8223830 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term617 P _109329 b _109330) (term726 A B C P lt2 z _109327 s p _109328 a _109330 _109329)). Qed.
Lemma lem8223847 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223848 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (b : P -> nat) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term731 A B C P b lt2 z _109327 s p _109328 a _109330 _109329) = (term732 A B C P lt2 z _109327 s b p _109328 a _109330 _109329).
Proof. exact (@lem8223847 (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) (term617 P _109329 b _109330) (term733 B C P p _109328 a _109330 _109329)). Qed.
Lemma lem8223862 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223863 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term734 B C P b p _109328 a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (@lem8223862 (term615 B C P p _109328 _109330) (term617 P _109329 b _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8223879 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (s : P -> A) (_109330 : P) : (term718 A B C P lt2 z _109327 _109328 _109329 s _109330) = (term718 A B C P lt2 z _109327 _109328 _109329 s _109330).
Proof. exact (eq_refl (term718 A B C P lt2 z _109327 _109328 _109329 s _109330)). Qed.
Lemma lem8223880 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term732 A B C P lt2 z _109327 s b p _109328 a _109330 _109329) = (term736 A B C P lt2 z _109327 s p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8223879 A B C P lt2 z _109327 _109328 _109329 s _109330) (@lem8223863 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8223891 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term731 A B C P b lt2 z _109327 s p _109328 a _109330 _109329) = (term736 A B C P lt2 z _109327 s p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223848 A B C P lt2 z _109327 s b p _109328 a _109330 _109329) (@lem8223880 A B C P lt2 z _109327 s p _109328 b a _109330 _109329)). Qed.
Lemma lem8223892 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223893 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term730 A B C P h b lt2 z _109327 s p _109328 a _109330 _109329) = (term737 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8223892 B C P _109327 h _109328 _109330 _109329) (@lem8223891 A B C P lt2 z _109327 s p _109328 b a _109330 _109329)). Qed.
Lemma lem8223904 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term729 A B C P b h lt2 z _109327 s p _109328 a _109330 _109329) = (term737 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223831 A B C P h b lt2 z _109327 s p _109328 a _109330 _109329) (@lem8223893 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329)). Qed.
Lemma lem8223905 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term710 A B C P b a p lt2 z s _109327 h _109328 _109330 _109329) = (term737 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223826 A B C P b h lt2 z _109327 s p _109328 a _109330 _109329) (@lem8223904 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329)). Qed.
Lemma lem8223906 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term709 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term737 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223702 A B C P b a p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223905 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329)). Qed.
Lemma lem8223907 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term721 B C P p _109327 _109330) = (term721 B C P p _109327 _109330).
Proof. exact (eq_refl (term721 B C P p _109327 _109330)). Qed.
Lemma lem8223908 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term707 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term738 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8223907 B C P p _109327 _109330) (@lem8223906 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329)). Qed.
Lemma lem8223912 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223913 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (s : P -> A) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term738 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329) = (term739 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329).
Proof. exact (@lem8223912 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term615 B C P p _109327 _109330) (term736 A B C P lt2 z _109327 s p _109328 b a _109330 _109329)). Qed.
Lemma lem8223929 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223930 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term740 A B C P lt2 z _109327 s p _109328 b a _109330 _109329) = (term741 A B C P lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8223929 (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) (term615 B C P p _109327 _109330) (term735 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8223966 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8223967 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term739 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8223966 B C P _109327 h _109328 _109330 _109329) (@lem8223930 A B C P lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8223978 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term738 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223913 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329) (@lem8223967 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8223979 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term707 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223908 A B C P h lt2 z _109327 s p _109328 b a _109330 _109329) (@lem8223978 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8223980 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term706 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223673 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8223979 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8223981 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term619 P _109329 b _109330) = (term619 P _109329 b _109330).
Proof. exact (eq_refl (term619 P _109329 b _109330)). Qed.
Lemma lem8223982 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term704 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term743 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8223981 P _109329 b _109330) (@lem8223980 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8223986 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8223987 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term743 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) = (term744 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8223986 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term617 P _109329 b _109330) (term741 A B C P lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224003 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224004 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term745 A B C P lt2 z s _109327 p _109328 b a _109330 _109329) = (term746 A B C P lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224003 (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) (term617 P _109329 b _109330) (term747 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224018 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224019 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term748 B C P _109327 p _109328 b a _109330 _109329) = (term749 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224018 (term615 B C P p _109327 _109330) (term617 P _109329 b _109330) (term735 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224033 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224034 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term750 B C P p _109328 b a _109330 _109329) = (term751 B C P p _109328 b a _109330 _109329).
Proof. exact (@lem8224033 (term615 B C P p _109328 _109330) (term617 P _109329 b _109330) (term752 P b a _109330 _109329)). Qed.
Lemma lem8224046 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8224047 {P : Type'} (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term753 P b a _109330 _109329) = (term752 P b a _109330 _109329).
Proof. exact (@lem8224046 (term617 P _109329 b _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8224053 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term721 B C P p _109328 _109330) = (term721 B C P p _109328 _109330).
Proof. exact (eq_refl (term721 B C P p _109328 _109330)). Qed.
Lemma lem8224054 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term751 B C P p _109328 b a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224053 B C P p _109328 _109330) (@lem8224047 P b a _109330 _109329)). Qed.
Lemma lem8224065 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term750 B C P p _109328 b a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224034 B C P p _109328 b a _109330 _109329) (@lem8224054 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224066 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term721 B C P p _109327 _109330) = (term721 B C P p _109327 _109330).
Proof. exact (eq_refl (term721 B C P p _109327 _109330)). Qed.
Lemma lem8224067 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term749 B C P _109327 p _109328 b a _109330 _109329) = (term747 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224066 B C P p _109327 _109330) (@lem8224065 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224078 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term748 B C P _109327 p _109328 b a _109330 _109329) = (term747 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224019 B C P _109327 p _109328 b a _109330 _109329) (@lem8224067 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224079 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (s : P -> A) (_109330 : P) : (term718 A B C P lt2 z _109327 _109328 _109329 s _109330) = (term718 A B C P lt2 z _109327 _109328 _109329 s _109330).
Proof. exact (eq_refl (term718 A B C P lt2 z _109327 _109328 _109329 s _109330)). Qed.
Lemma lem8224080 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term746 A B C P lt2 z s _109327 p _109328 b a _109330 _109329) = (term741 A B C P lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224079 A B C P lt2 z _109327 _109328 _109329 s _109330) (@lem8224078 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224091 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term745 A B C P lt2 z s _109327 p _109328 b a _109330 _109329) = (term741 A B C P lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224004 A B C P lt2 z s _109327 p _109328 b a _109330 _109329) (@lem8224080 A B C P lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224092 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224093 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term744 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224092 B C P _109327 h _109328 _109330 _109329) (@lem8224091 A B C P lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224104 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term743 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223987 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) (@lem8224093 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224105 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term704 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223982 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) (@lem8224104 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224106 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8223658 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) (@lem8224105 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8224108 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term754 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term755 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224107) (@lem8224106 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224122 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224123 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term756 B C P a b p _109327 h _109328 _109330 _109329) = (term757 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224122 (term617 P _109329 b _109330) (term622 P a _109330 _109329) (term758 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224137 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224138 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term759 B C P a b p _109327 h _109328 _109330 _109329) = (term760 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224137 (term615 B C P p _109327 _109330) (term622 P a _109330 _109329) (term761 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224150 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8224151 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term762 B C P a b p _109327 h _109328 _109330 _109329) = (term761 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224150 (term622 P a _109330 _109329) (term763 B C P b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224155 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224156 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term761 B C P a b p _109327 h _109328 _109330 _109329) = (term764 B C P b a p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224155 (term617 P _109329 b _109330) (term622 P a _109330 _109329) (term765 B C P p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224167 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term762 B C P a b p _109327 h _109328 _109330 _109329) = (term764 B C P b a p _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8224151 B C P a b p _109327 h _109328 _109330 _109329) (@lem8224156 B C P b a p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224171 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224172 {B C P : Type'} (p : type560 B C P) (a : P -> nat) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term766 B C P a p _109327 h _109328 _109330 _109329) = (term767 B C P p a _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224171 (term615 B C P p _109328 _109330) (term622 P a _109330 _109329) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8224186 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8224187 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term716 B C P a _109327 h _109328 _109330 _109329) = (term717 B C P _109327 h _109328 a _109330 _109329).
Proof. exact (@lem8224186 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term622 P a _109330 _109329)). Qed.
Lemma lem8224195 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term721 B C P p _109328 _109330) = (term721 B C P p _109328 _109330).
Proof. exact (eq_refl (term721 B C P p _109328 _109330)). Qed.
Lemma lem8224196 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term767 B C P p a _109327 h _109328 _109330 _109329) = (term768 B C P p _109327 h _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8224195 B C P p _109328 _109330) (@lem8224187 B C P _109327 h _109328 a _109330 _109329)). Qed.
Lemma lem8224200 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224201 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term768 B C P p _109327 h _109328 a _109330 _109329) = (term769 B C P _109327 h p _109328 a _109330 _109329).
Proof. exact (@lem8224200 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term615 B C P p _109328 _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8224219 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term767 B C P p a _109327 h _109328 _109330 _109329) = (term769 B C P _109327 h p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8224196 B C P p _109327 h _109328 a _109330 _109329) (@lem8224201 B C P _109327 h p _109328 a _109330 _109329)). Qed.
Lemma lem8224220 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term766 B C P a p _109327 h _109328 _109330 _109329) = (term769 B C P _109327 h p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8224172 B C P p a _109327 h _109328 _109330 _109329) (@lem8224219 B C P _109327 h p _109328 a _109330 _109329)). Qed.
Lemma lem8224221 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term619 P _109329 b _109330) = (term619 P _109329 b _109330).
Proof. exact (eq_refl (term619 P _109329 b _109330)). Qed.
Lemma lem8224222 {B C P : Type'} (b : P -> nat) (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term764 B C P b a p _109327 h _109328 _109330 _109329) = (term770 B C P b _109327 h p _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8224221 P _109329 b _109330) (@lem8224220 B C P _109327 h p _109328 a _109330 _109329)). Qed.
Lemma lem8224226 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224227 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (b : P -> nat) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term770 B C P b _109327 h p _109328 a _109330 _109329) = (term771 B C P _109327 h b p _109328 a _109330 _109329).
Proof. exact (@lem8224226 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term617 P _109329 b _109330) (term733 B C P p _109328 a _109330 _109329)). Qed.
Lemma lem8224243 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224244 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term734 B C P b p _109328 a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (@lem8224243 (term615 B C P p _109328 _109330) (term617 P _109329 b _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8224260 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224261 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term771 B C P _109327 h b p _109328 a _109330 _109329) = (term772 B C P _109327 h p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224260 B C P _109327 h _109328 _109330 _109329) (@lem8224244 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224272 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term770 B C P b _109327 h p _109328 a _109330 _109329) = (term772 B C P _109327 h p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224227 B C P _109327 h b p _109328 a _109330 _109329) (@lem8224261 B C P _109327 h p _109328 b a _109330 _109329)). Qed.
Lemma lem8224273 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term764 B C P b a p _109327 h _109328 _109330 _109329) = (term772 B C P _109327 h p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224222 B C P b _109327 h p _109328 a _109330 _109329) (@lem8224272 B C P _109327 h p _109328 b a _109330 _109329)). Qed.
Lemma lem8224274 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term762 B C P a b p _109327 h _109328 _109330 _109329) = (term772 B C P _109327 h p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224167 B C P b a p _109327 h _109328 _109330 _109329) (@lem8224273 B C P _109327 h p _109328 b a _109330 _109329)). Qed.
Lemma lem8224275 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term721 B C P p _109327 _109330) = (term721 B C P p _109327 _109330).
Proof. exact (eq_refl (term721 B C P p _109327 _109330)). Qed.
Lemma lem8224276 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term760 B C P a b p _109327 h _109328 _109330 _109329) = (term773 B C P _109327 h p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224275 B C P p _109327 _109330) (@lem8224274 B C P _109327 h p _109328 b a _109330 _109329)). Qed.
Lemma lem8224280 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224281 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term773 B C P _109327 h p _109328 b a _109330 _109329) = (term774 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224280 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term615 B C P p _109327 _109330) (term735 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224319 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term760 B C P a b p _109327 h _109328 _109330 _109329) = (term774 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224276 B C P _109327 h p _109328 b a _109330 _109329) (@lem8224281 B C P h _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224320 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term759 B C P a b p _109327 h _109328 _109330 _109329) = (term774 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224138 B C P a b p _109327 h _109328 _109330 _109329) (@lem8224319 B C P h _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224321 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term619 P _109329 b _109330) = (term619 P _109329 b _109330).
Proof. exact (eq_refl (term619 P _109329 b _109330)). Qed.
Lemma lem8224322 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term757 B C P a b p _109327 h _109328 _109330 _109329) = (term775 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224321 P _109329 b _109330) (@lem8224320 B C P h _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224326 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224327 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term775 B C P h _109327 p _109328 b a _109330 _109329) = (term776 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224326 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term617 P _109329 b _109330) (term747 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224343 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224344 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term748 B C P _109327 p _109328 b a _109330 _109329) = (term749 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224343 (term615 B C P p _109327 _109330) (term617 P _109329 b _109330) (term735 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224358 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224359 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term750 B C P p _109328 b a _109330 _109329) = (term751 B C P p _109328 b a _109330 _109329).
Proof. exact (@lem8224358 (term615 B C P p _109328 _109330) (term617 P _109329 b _109330) (term752 P b a _109330 _109329)). Qed.
Lemma lem8224371 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8224372 {P : Type'} (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term753 P b a _109330 _109329) = (term752 P b a _109330 _109329).
Proof. exact (@lem8224371 (term617 P _109329 b _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8224378 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term721 B C P p _109328 _109330) = (term721 B C P p _109328 _109330).
Proof. exact (eq_refl (term721 B C P p _109328 _109330)). Qed.
Lemma lem8224379 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term751 B C P p _109328 b a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224378 B C P p _109328 _109330) (@lem8224372 P b a _109330 _109329)). Qed.
Lemma lem8224390 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term750 B C P p _109328 b a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224359 B C P p _109328 b a _109330 _109329) (@lem8224379 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224391 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term721 B C P p _109327 _109330) = (term721 B C P p _109327 _109330).
Proof. exact (eq_refl (term721 B C P p _109327 _109330)). Qed.
Lemma lem8224392 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term749 B C P _109327 p _109328 b a _109330 _109329) = (term747 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224391 B C P p _109327 _109330) (@lem8224390 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224403 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term748 B C P _109327 p _109328 b a _109330 _109329) = (term747 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224344 B C P _109327 p _109328 b a _109330 _109329) (@lem8224392 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224404 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224405 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term776 B C P h _109327 p _109328 b a _109330 _109329) = (term774 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224404 B C P _109327 h _109328 _109330 _109329) (@lem8224403 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224416 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term775 B C P h _109327 p _109328 b a _109330 _109329) = (term774 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224327 B C P h _109327 p _109328 b a _109330 _109329) (@lem8224405 B C P h _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224417 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term757 B C P a b p _109327 h _109328 _109330 _109329) = (term774 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224322 B C P h _109327 p _109328 b a _109330 _109329) (@lem8224416 B C P h _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224418 {B C P : Type'} (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term756 B C P a b p _109327 h _109328 _109330 _109329) = (term774 B C P h _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224123 B C P a b p _109327 h _109328 _109330 _109329) (@lem8224417 B C P h _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224419 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (s : P -> A) (_109330 : P) : (term718 A B C P lt2 z _109327 _109328 _109329 s _109330) = (term718 A B C P lt2 z _109327 _109328 _109329 s _109330).
Proof. exact (eq_refl (term718 A B C P lt2 z _109327 _109328 _109329 s _109330)). Qed.
Lemma lem8224420 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (h : type556 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329) = (term778 A B C P lt2 z s h _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224419 A B C P lt2 z _109327 _109328 _109329 s _109330) (@lem8224418 B C P h _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224424 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224425 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term778 A B C P lt2 z s h _109327 p _109328 b a _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224424 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) (term747 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224473 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224420 A B C P lt2 z s h _109327 p _109328 b a _109330 _109329) (@lem8224425 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224474 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : ((term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329)) = ((term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)).
Proof. exact (MK_COMB (@lem8224108 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) (@lem8224473 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224476 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8224477 (x : Prop) : (x = x) = True.
Proof. exact (@lem8224476 Prop x). Qed.
Lemma lem8224478 {A B C P : Type'} (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : ((term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) = (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)) = True.
Proof. exact (@lem8224477 (term742 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224479 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : ((term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329)) = True.
Proof. exact (TRANS (@lem8224474 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329) (@lem8224478 A B C P h lt2 z s _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224480 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : True = ((term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329)).
Proof. exact (SYM (@lem8224479 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224481 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term684 A B C P a b p lt2 z s _109327 h _109328 _109330 _109329) = (term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329).
Proof. exact (EQ_MP (@lem8224480 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329) (@lem0)). Qed.
Lemma lem8224482 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109330 : P) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329.
Proof. exact (EQ_MP (@lem8224481 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329) (@lem8223221 A B C P _109327 _109328 _109330 _109329 a b p lt2 s z h h1)). Qed.
Lemma lem8224484 (b : Prop) (a : Prop) : (a \/ b) = (term779 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8224485 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (s : P -> A) (_109330 : P) : (term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329) = (term780 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330).
Proof. exact (@lem8224484 (term756 B C P a b p _109327 h _109328 _109330 _109329) (term609 A B C P lt2 z _109327 _109328 _109329 s _109330)). Qed.
Lemma lem8224487 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8224488 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term783 B C P a b p _109327 h _109328 _109330 _109329) = (term784 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224487 (term622 P a _109330 _109329) (term785 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224490 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8224491 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term786 P a _109330 _109329) = (term579 P a _109330 _109329).
Proof. exact (@lem8224490 (term579 P a _109330 _109329)). Qed.
Lemma lem8224492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8224493 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term787 P a _109330 _109329) = (term581 P a _109330 _109329).
Proof. exact (MK_COMB (@lem8224492) (@lem8224491 P a _109330 _109329)). Qed.
Lemma lem8224495 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8224496 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term788 B C P a b p _109327 h _109328 _109330 _109329) = (term789 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224495 (term617 P _109329 b _109330) (term758 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224498 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8224499 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term790 P _109329 b _109330) = (term573 P _109329 b _109330).
Proof. exact (@lem8224498 (term573 P _109329 b _109330)). Qed.
Lemma lem8224500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8224501 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term791 P _109329 b _109330) = (term792 P _109329 b _109330).
Proof. exact (MK_COMB (@lem8224500) (@lem8224499 P _109329 b _109330)). Qed.
Lemma lem8224503 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8224504 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term793 B C P a b p _109327 h _109328 _109330 _109329) = (term794 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224503 (term615 B C P p _109327 _109330) (term761 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224506 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8224507 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term795 B C P p _109327 _109330) = (term558 B C P p _109327 _109330).
Proof. exact (@lem8224506 (term558 B C P p _109327 _109330)). Qed.
Lemma lem8224508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8224509 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term796 B C P p _109327 _109330) = (term797 B C P p _109327 _109330).
Proof. exact (MK_COMB (@lem8224508) (@lem8224507 B C P p _109327 _109330)). Qed.
Lemma lem8224511 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8224512 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term798 B C P a b p _109327 h _109328 _109330 _109329) = (term799 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224511 (term622 P a _109330 _109329) (term763 B C P b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224514 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8224515 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term786 P a _109330 _109329) = (term579 P a _109330 _109329).
Proof. exact (@lem8224514 (term579 P a _109330 _109329)). Qed.
Lemma lem8224516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8224517 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term787 P a _109330 _109329) = (term581 P a _109330 _109329).
Proof. exact (MK_COMB (@lem8224516) (@lem8224515 P a _109330 _109329)). Qed.
Lemma lem8224519 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8224520 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term800 B C P b p _109327 h _109328 _109330 _109329) = (term801 B C P b p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224519 (term617 P _109329 b _109330) (term765 B C P p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224522 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8224523 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term790 P _109329 b _109330) = (term573 P _109329 b _109330).
Proof. exact (@lem8224522 (term573 P _109329 b _109330)). Qed.
Lemma lem8224524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8224525 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term791 P _109329 b _109330) = (term792 P _109329 b _109330).
Proof. exact (MK_COMB (@lem8224524) (@lem8224523 P _109329 b _109330)). Qed.
Lemma lem8224527 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8224528 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term802 B C P p _109327 h _109328 _109330 _109329) = (term803 B C P p _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224527 (term615 B C P p _109328 _109330) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8224530 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8224531 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term795 B C P p _109328 _109330) = (term558 B C P p _109328 _109330).
Proof. exact (@lem8224530 (term558 B C P p _109328 _109330)). Qed.
Lemma lem8224532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8224533 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term796 B C P p _109328 _109330) = (term797 B C P p _109328 _109330).
Proof. exact (MK_COMB (@lem8224532) (@lem8224531 B C P p _109328 _109330)). Qed.
Lemma lem8224534 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term587 B C P _109327 h _109328 _109330 _109329) = (term587 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term587 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224535 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term803 B C P p _109327 h _109328 _109330 _109329) = (term804 B C P p _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8224533 B C P p _109328 _109330) (@lem8224534 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224536 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term802 B C P p _109327 h _109328 _109330 _109329) = (term804 B C P p _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8224528 B C P p _109327 h _109328 _109330 _109329) (@lem8224535 B C P p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224537 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term801 B C P b p _109327 h _109328 _109330 _109329) = (term805 B C P b p _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8224525 P _109329 b _109330) (@lem8224536 B C P p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224538 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term800 B C P b p _109327 h _109328 _109330 _109329) = (term805 B C P b p _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8224520 B C P b p _109327 h _109328 _109330 _109329) (@lem8224537 B C P b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224539 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term799 B C P a b p _109327 h _109328 _109330 _109329) = (term806 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8224517 P a _109330 _109329) (@lem8224538 B C P b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224540 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term798 B C P a b p _109327 h _109328 _109330 _109329) = (term806 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8224512 B C P a b p _109327 h _109328 _109330 _109329) (@lem8224539 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224541 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term794 B C P a b p _109327 h _109328 _109330 _109329) = (term807 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8224509 B C P p _109327 _109330) (@lem8224540 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224542 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term793 B C P a b p _109327 h _109328 _109330 _109329) = (term807 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8224504 B C P a b p _109327 h _109328 _109330 _109329) (@lem8224541 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224543 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term789 B C P a b p _109327 h _109328 _109330 _109329) = (term808 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8224501 P _109329 b _109330) (@lem8224542 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224544 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term788 B C P a b p _109327 h _109328 _109330 _109329) = (term808 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8224496 B C P a b p _109327 h _109328 _109330 _109329) (@lem8224543 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224545 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term784 B C P a b p _109327 h _109328 _109330 _109329) = (term809 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8224493 P a _109330 _109329) (@lem8224544 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224546 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term783 B C P a b p _109327 h _109328 _109330 _109329) = (term809 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8224488 B C P a b p _109327 h _109328 _109330 _109329) (@lem8224545 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8224548 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term810 B C P a b p _109327 h _109328 _109330 _109329) = (term811 B C P a b p _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8224547) (@lem8224546 B C P a b p _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224549 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (s : P -> A) (_109330 : P) : (term609 A B C P lt2 z _109327 _109328 _109329 s _109330) = (term609 A B C P lt2 z _109327 _109328 _109329 s _109330).
Proof. exact (eq_refl (term609 A B C P lt2 z _109327 _109328 _109329 s _109330)). Qed.
Lemma lem8224550 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (s : P -> A) (_109330 : P) : (term780 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330) = (term812 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330).
Proof. exact (MK_COMB (@lem8224548 B C P a b p _109327 h _109328 _109330 _109329) (@lem8224549 A B C P lt2 z _109327 _109328 _109329 s _109330)). Qed.
Lemma lem8224551 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (h : type556 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (s : P -> A) (_109330 : P) : (term777 A B C P lt2 z s a b p _109327 h _109328 _109330 _109329) = (term812 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330).
Proof. exact (TRANS (@lem8224485 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330) (@lem8224550 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330)). Qed.
Lemma lem8224553 {B C P : Type'} (f : B -> C) (h : type556 B C P) (i : nat) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : p g a') : term804 B C P p f h g a' i.
Proof. exact (conj (@lem8223643 B C P p g a' h2) (@lem8223651 B C P f h g a' i h1)). Qed.
Lemma lem8224554 {B C P : Type'} (f : B -> C) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p g a') : term805 B C P b p f h g a' i.
Proof. exact (conj (@lem8223636 P a i b a' h2) (@lem8224553 B C P f h i p g a' h1 h3)). Qed.
Lemma lem8224555 {B C P : Type'} (f : B -> C) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p g a') : term806 B C P a b p f h g a' i.
Proof. exact (conj (@lem8223629 P a i b a' h2) (@lem8224554 B C P f h a i b p g a' h1 h2 h3)). Qed.
Lemma lem8224556 {B C P : Type'} (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p f a') (h4 : p g a') : term807 B C P a b p f h g a' i.
Proof. exact (conj (@lem8223622 B C P p f a' h3) (@lem8224555 B C P f h a i b p g a' h1 h2 h4)). Qed.
Lemma lem8224557 {B C P : Type'} (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p f a') (h4 : p g a') : term808 B C P a b p f h g a' i.
Proof. exact (conj (@lem8223615 P a i b a' h2) (@lem8224556 B C P h a i b f p g a' h1 h2 h3 h4)). Qed.
Lemma lem8224558 {B C P : Type'} (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p f a') (h4 : p g a') : term809 B C P a b p f h g a' i.
Proof. exact (conj (@lem8223608 P a i b a' h2) (@lem8224557 B C P h a i b f p g a' h1 h2 h3 h4)). Qed.
Lemma lem8224560 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term812 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330.
Proof. exact (EQ_MP (@lem8224551 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330) (@lem8224482 A B C P _109327 _109328 _109330 _109329 a b p lt2 s z h h1)). Qed.
Lemma lem8224561 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term812 A B C P a b p h lt2 z _109327 _109328 _109329 s _109330.
Proof. exact (@lem8224560 A B C P _109327 _109328 _109329 _109330 a b p lt2 s z h h1). Qed.
Lemma lem8224562 {A B C P : Type'} (f : B -> C) (g : B -> C) (i : nat) (a' : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term812 A B C P a b p h lt2 z f g i s a'.
Proof. exact (@lem8224561 A B C P f g i a' a b p lt2 s z h h1). Qed.
Lemma lem8224565 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term550 A B C P a b p lt2 s z h) (h2 : term587 B C P f h g a' i) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term609 A B C P lt2 z f g i s a'.
Proof. exact (@lem8224562 A B C P f g i a' a b p lt2 s z h h1 (@lem8224558 B C P h a i b f p g a' h2 h3 h4 h5)). Qed.
Lemma lem8224566 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term550 A B C P a b p lt2 s z h) (h2 : term587 B C P f h g a' i) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term813 A B C P lt2 z f g i s a'.
Proof. exact (fun h0 : term814 A B C P lt2 z f g i s a' => @lem8224565 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5). Qed.
Lemma lem8224568 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8224569 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (i : nat) (s : P -> A) (a' : P) : (term813 A B C P lt2 z f g i s a') = (term609 A B C P lt2 z f g i s a').
Proof. exact (@lem8224568 (term609 A B C P lt2 z f g i s a')). Qed.
Lemma lem8224570 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term550 A B C P a b p lt2 s z h) (h2 : term587 B C P f h g a' i) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term609 A B C P lt2 z f g i s a'.
Proof. exact (EQ_MP (@lem8224569 A B C P lt2 z f g i s a') (@lem8224566 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5)). Qed.
Lemma lem8224576 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8224577 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : (term568 A B C P lt2 s a' f g _109326) = (term815 A B C P f g lt2 _109326 s a').
Proof. exact (@lem8224576 ((@I (B -> C) f _109326) = (@I (B -> C) g _109326)) (term565 A B P lt2 _109326 s a')). Qed.
Lemma lem8224585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8224586 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : (term816 A B C P lt2 s a' f g _109326) = (term817 A B C P f g lt2 _109326 s a').
Proof. exact (MK_COMB (@lem8224585) (@lem8224577 A B C P f g lt2 _109326 s a')). Qed.
Lemma lem8224594 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : (term815 A B C P f g lt2 _109326 s a') = (term815 A B C P f g lt2 _109326 s a').
Proof. exact (eq_refl (term815 A B C P f g lt2 _109326 s a')). Qed.
Lemma lem8224595 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : ((term568 A B C P lt2 s a' f g _109326) = (term815 A B C P f g lt2 _109326 s a')) = ((term815 A B C P f g lt2 _109326 s a') = (term815 A B C P f g lt2 _109326 s a')).
Proof. exact (MK_COMB (@lem8224586 A B C P f g lt2 _109326 s a') (@lem8224594 A B C P f g lt2 _109326 s a')). Qed.
Lemma lem8224597 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8224598 (x : Prop) : (x = x) = True.
Proof. exact (@lem8224597 Prop x). Qed.
Lemma lem8224599 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : ((term815 A B C P f g lt2 _109326 s a') = (term815 A B C P f g lt2 _109326 s a')) = True.
Proof. exact (@lem8224598 (term815 A B C P f g lt2 _109326 s a')). Qed.
Lemma lem8224600 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : ((term568 A B C P lt2 s a' f g _109326) = (term815 A B C P f g lt2 _109326 s a')) = True.
Proof. exact (TRANS (@lem8224595 A B C P f g lt2 _109326 s a') (@lem8224599 A B C P f g lt2 _109326 s a')). Qed.
Lemma lem8224601 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : True = ((term568 A B C P lt2 s a' f g _109326) = (term815 A B C P f g lt2 _109326 s a')).
Proof. exact (SYM (@lem8224600 A B C P f g lt2 _109326 s a')). Qed.
Lemma lem8224602 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : (term568 A B C P lt2 s a' f g _109326) = (term815 A B C P f g lt2 _109326 s a').
Proof. exact (EQ_MP (@lem8224601 A B C P f g lt2 _109326 s a') (@lem0)). Qed.
Lemma lem8224603 {A B C P : Type'} (_109326 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term815 A B C P f g lt2 _109326 s a'.
Proof. exact (EQ_MP (@lem8224602 A B C P f g lt2 _109326 s a') (@lem8223173 A B C P _109326 lt2 s a' f g h1)). Qed.
Lemma lem8224605 (b : Prop) (a : Prop) : (a \/ b) = (term779 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8224606 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (_109326 : B) : (term815 A B C P f g lt2 _109326 s a') = (term818 A B C P lt2 s a' f g _109326).
Proof. exact (@lem8224605 (term565 A B P lt2 _109326 s a') ((@I (B -> C) f _109326) = (@I (B -> C) g _109326))). Qed.
Lemma lem8224608 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8224609 {A B P : Type'} (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : (term819 A B P lt2 _109326 s a') = (term563 A B P lt2 _109326 s a').
Proof. exact (@lem8224608 (term563 A B P lt2 _109326 s a')). Qed.
Lemma lem8224610 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8224611 {A B P : Type'} (lt2 : type1470 A B) (_109326 : B) (s : P -> A) (a' : P) : (term820 A B P lt2 _109326 s a') = (term821 A B P lt2 _109326 s a').
Proof. exact (MK_COMB (@lem8224610) (@lem8224609 A B P lt2 _109326 s a')). Qed.
Lemma lem8224612 {B C : Type'} (f : B -> C) (g : B -> C) (_109326 : B) : ((@I (B -> C) f _109326) = (@I (B -> C) g _109326)) = ((@I (B -> C) f _109326) = (@I (B -> C) g _109326)).
Proof. exact (eq_refl ((@I (B -> C) f _109326) = (@I (B -> C) g _109326))). Qed.
Lemma lem8224613 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (_109326 : B) : (term818 A B C P lt2 s a' f g _109326) = (term822 A B C P lt2 s a' f g _109326).
Proof. exact (MK_COMB (@lem8224611 A B P lt2 _109326 s a') (@lem8224612 B C f g _109326)). Qed.
Lemma lem8224614 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (_109326 : B) : (term815 A B C P f g lt2 _109326 s a') = (term822 A B C P lt2 s a' f g _109326).
Proof. exact (TRANS (@lem8224606 A B C P lt2 s a' f g _109326) (@lem8224613 A B C P lt2 s a' f g _109326)). Qed.
Lemma lem8224617 {A B C P : Type'} (_109326 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term822 A B C P lt2 s a' f g _109326.
Proof. exact (EQ_MP (@lem8224614 A B C P lt2 s a' f g _109326) (@lem8224603 A B C P _109326 lt2 s a' f g h1)). Qed.
Lemma lem8224618 {A B C P : Type'} (_109326 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term822 A B C P lt2 s a' f g _109326.
Proof. exact (@lem8224617 A B C P _109326 lt2 s a' f g h1). Qed.
Lemma lem8224619 {A B C P : Type'} (z : type521 B C P) (i : nat) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term823 A B C P lt2 s z f g i a'.
Proof. exact (@lem8224618 A B C P (term592 B C P z f g i a') lt2 s a' f g h1). Qed.
Lemma lem8224622 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term595 B C P z f g i a') = (term598 B C P z f g i a').
Proof. exact (@lem8224619 A B C P z i lt2 s a' f g h1 (@lem8224570 A B C P lt2 s z h a i b f p g a' h2 h3 h4 h5 h6)). Qed.
Lemma lem8224623 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term824 B C P z f g i a'.
Proof. exact (fun h0 : term602 B C P z f g i a' => @lem8224622 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem8224625 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8224626 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (i : nat) (a' : P) : (term824 B C P z f g i a') = ((term595 B C P z f g i a') = (term598 B C P z f g i a')).
Proof. exact (@lem8224625 ((term595 B C P z f g i a') = (term598 B C P z f g i a'))). Qed.
Lemma lem8224627 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term595 B C P z f g i a') = (term598 B C P z f g i a').
Proof. exact (EQ_MP (@lem8224626 B C P z f g i a') (@lem8224623 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8224633 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224634 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term697 B C P a b p z _109327 h _109328 _109330 _109329) = (term825 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224633 (term617 P _109329 b _109330) (term622 P a _109330 _109329) (term826 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224648 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224649 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term827 B C P a b p z _109327 h _109328 _109330 _109329) = (term828 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224648 (term615 B C P p _109327 _109330) (term622 P a _109330 _109329) (term692 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224661 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8224662 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term829 B C P a b p z _109327 h _109328 _109330 _109329) = (term692 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224661 (term622 P a _109330 _109329) (term691 B C P b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224666 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224667 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term692 B C P a b p z _109327 h _109328 _109330 _109329) = (term830 B C P b a p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224666 (term617 P _109329 b _109330) (term622 P a _109330 _109329) (term831 B C P p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224678 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term829 B C P a b p z _109327 h _109328 _109330 _109329) = (term830 B C P b a p z _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8224662 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8224667 B C P b a p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224682 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224683 {B C P : Type'} (p : type560 B C P) (a : P -> nat) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term832 B C P a p z _109327 h _109328 _109330 _109329) = (term833 B C P p a z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224682 (term615 B C P p _109328 _109330) (term622 P a _109330 _109329) (term689 B C P z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224697 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224698 {B C P : Type'} (z : type521 B C P) (a : P -> nat) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term834 B C P a z _109327 h _109328 _109330 _109329) = (term835 B C P z a _109327 h _109328 _109330 _109329).
Proof. exact (@lem8224697 (term602 B C P z _109327 _109328 _109329 _109330) (term622 P a _109330 _109329) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8224714 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8224715 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term716 B C P a _109327 h _109328 _109330 _109329) = (term717 B C P _109327 h _109328 a _109330 _109329).
Proof. exact (@lem8224714 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term622 P a _109330 _109329)). Qed.
Lemma lem8224723 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term836 B C P z _109327 _109328 _109329 _109330) = (term836 B C P z _109327 _109328 _109329 _109330).
Proof. exact (eq_refl (term836 B C P z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8224724 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term835 B C P z a _109327 h _109328 _109330 _109329) = (term837 B C P z _109327 h _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8224723 B C P z _109327 _109328 _109329 _109330) (@lem8224715 B C P _109327 h _109328 a _109330 _109329)). Qed.
Lemma lem8224728 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224729 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term837 B C P z _109327 h _109328 a _109330 _109329) = (term838 B C P h z _109327 _109328 a _109330 _109329).
Proof. exact (@lem8224728 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term602 B C P z _109327 _109328 _109329 _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8224749 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term835 B C P z a _109327 h _109328 _109330 _109329) = (term838 B C P h z _109327 _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8224724 B C P z _109327 h _109328 a _109330 _109329) (@lem8224729 B C P h z _109327 _109328 a _109330 _109329)). Qed.
Lemma lem8224750 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term834 B C P a z _109327 h _109328 _109330 _109329) = (term838 B C P h z _109327 _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8224698 B C P z a _109327 h _109328 _109330 _109329) (@lem8224749 B C P h z _109327 _109328 a _109330 _109329)). Qed.
Lemma lem8224751 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term721 B C P p _109328 _109330) = (term721 B C P p _109328 _109330).
Proof. exact (eq_refl (term721 B C P p _109328 _109330)). Qed.
Lemma lem8224752 {B C P : Type'} (p : type560 B C P) (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term833 B C P p a z _109327 h _109328 _109330 _109329) = (term839 B C P p h z _109327 _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8224751 B C P p _109328 _109330) (@lem8224750 B C P h z _109327 _109328 a _109330 _109329)). Qed.
Lemma lem8224756 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224757 {B C P : Type'} (h : type556 B C P) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term839 B C P p h z _109327 _109328 a _109330 _109329) = (term840 B C P h p z _109327 _109328 a _109330 _109329).
Proof. exact (@lem8224756 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term615 B C P p _109328 _109330) (term841 B C P z _109327 _109328 a _109330 _109329)). Qed.
Lemma lem8224773 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224774 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term842 B C P p z _109327 _109328 a _109330 _109329) = (term843 B C P z _109327 p _109328 a _109330 _109329).
Proof. exact (@lem8224773 (term602 B C P z _109327 _109328 _109329 _109330) (term615 B C P p _109328 _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8224792 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224793 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term840 B C P h p z _109327 _109328 a _109330 _109329) = (term844 B C P h z _109327 p _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8224792 B C P _109327 h _109328 _109330 _109329) (@lem8224774 B C P z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8224804 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term839 B C P p h z _109327 _109328 a _109330 _109329) = (term844 B C P h z _109327 p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8224757 B C P h p z _109327 _109328 a _109330 _109329) (@lem8224793 B C P h z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8224805 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term833 B C P p a z _109327 h _109328 _109330 _109329) = (term844 B C P h z _109327 p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8224752 B C P p h z _109327 _109328 a _109330 _109329) (@lem8224804 B C P h z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8224806 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term832 B C P a p z _109327 h _109328 _109330 _109329) = (term844 B C P h z _109327 p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8224683 B C P p a z _109327 h _109328 _109330 _109329) (@lem8224805 B C P h z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8224807 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term619 P _109329 b _109330) = (term619 P _109329 b _109330).
Proof. exact (eq_refl (term619 P _109329 b _109330)). Qed.
Lemma lem8224808 {B C P : Type'} (b : P -> nat) (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term830 B C P b a p z _109327 h _109328 _109330 _109329) = (term845 B C P b h z _109327 p _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8224807 P _109329 b _109330) (@lem8224806 B C P h z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8224812 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224813 {B C P : Type'} (h : type556 B C P) (b : P -> nat) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term845 B C P b h z _109327 p _109328 a _109330 _109329) = (term846 B C P h b z _109327 p _109328 a _109330 _109329).
Proof. exact (@lem8224812 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term617 P _109329 b _109330) (term843 B C P z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8224829 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224830 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (b : P -> nat) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term847 B C P b z _109327 p _109328 a _109330 _109329) = (term848 B C P z _109327 b p _109328 a _109330 _109329).
Proof. exact (@lem8224829 (term602 B C P z _109327 _109328 _109329 _109330) (term617 P _109329 b _109330) (term733 B C P p _109328 a _109330 _109329)). Qed.
Lemma lem8224846 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224847 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term734 B C P b p _109328 a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (@lem8224846 (term615 B C P p _109328 _109330) (term617 P _109329 b _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8224863 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term836 B C P z _109327 _109328 _109329 _109330) = (term836 B C P z _109327 _109328 _109329 _109330).
Proof. exact (eq_refl (term836 B C P z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8224864 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term848 B C P z _109327 b p _109328 a _109330 _109329) = (term849 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224863 B C P z _109327 _109328 _109329 _109330) (@lem8224847 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224875 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term847 B C P b z _109327 p _109328 a _109330 _109329) = (term849 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224830 B C P z _109327 b p _109328 a _109330 _109329) (@lem8224864 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224876 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224877 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term846 B C P h b z _109327 p _109328 a _109330 _109329) = (term850 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224876 B C P _109327 h _109328 _109330 _109329) (@lem8224875 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224888 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term845 B C P b h z _109327 p _109328 a _109330 _109329) = (term850 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224813 B C P h b z _109327 p _109328 a _109330 _109329) (@lem8224877 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224889 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term830 B C P b a p z _109327 h _109328 _109330 _109329) = (term850 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224808 B C P b h z _109327 p _109328 a _109330 _109329) (@lem8224888 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224890 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term829 B C P a b p z _109327 h _109328 _109330 _109329) = (term850 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224678 B C P b a p z _109327 h _109328 _109330 _109329) (@lem8224889 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224891 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term721 B C P p _109327 _109330) = (term721 B C P p _109327 _109330).
Proof. exact (eq_refl (term721 B C P p _109327 _109330)). Qed.
Lemma lem8224892 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term828 B C P a b p z _109327 h _109328 _109330 _109329) = (term851 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224891 B C P p _109327 _109330) (@lem8224890 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224896 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224897 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term851 B C P h z _109327 p _109328 b a _109330 _109329) = (term852 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224896 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term615 B C P p _109327 _109330) (term849 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224913 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224914 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term853 B C P z _109327 p _109328 b a _109330 _109329) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224913 (term602 B C P z _109327 _109328 _109329 _109330) (term615 B C P p _109327 _109330) (term735 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8224952 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8224953 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term852 B C P h z _109327 p _109328 b a _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224952 B C P _109327 h _109328 _109330 _109329) (@lem8224914 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224964 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term851 B C P h z _109327 p _109328 b a _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224897 B C P h z _109327 p _109328 b a _109330 _109329) (@lem8224953 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224965 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term828 B C P a b p z _109327 h _109328 _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224892 B C P h z _109327 p _109328 b a _109330 _109329) (@lem8224964 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224966 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term827 B C P a b p z _109327 h _109328 _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224649 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8224965 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224967 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term619 P _109329 b _109330) = (term619 P _109329 b _109330).
Proof. exact (eq_refl (term619 P _109329 b _109330)). Qed.
Lemma lem8224968 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term825 B C P a b p z _109327 h _109328 _109330 _109329) = (term856 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8224967 P _109329 b _109330) (@lem8224966 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224972 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224973 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term856 B C P h z _109327 p _109328 b a _109330 _109329) = (term857 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224972 ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) (term617 P _109329 b _109330) (term854 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8224989 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8224990 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term858 B C P z _109327 p _109328 b a _109330 _109329) = (term859 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8224989 (term602 B C P z _109327 _109328 _109329 _109330) (term617 P _109329 b _109330) (term747 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225006 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225007 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term748 B C P _109327 p _109328 b a _109330 _109329) = (term749 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8225006 (term615 B C P p _109327 _109330) (term617 P _109329 b _109330) (term735 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8225021 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225022 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term750 B C P p _109328 b a _109330 _109329) = (term751 B C P p _109328 b a _109330 _109329).
Proof. exact (@lem8225021 (term615 B C P p _109328 _109330) (term617 P _109329 b _109330) (term752 P b a _109330 _109329)). Qed.
Lemma lem8225034 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8225035 {P : Type'} (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term753 P b a _109330 _109329) = (term752 P b a _109330 _109329).
Proof. exact (@lem8225034 (term617 P _109329 b _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8225041 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term721 B C P p _109328 _109330) = (term721 B C P p _109328 _109330).
Proof. exact (eq_refl (term721 B C P p _109328 _109330)). Qed.
Lemma lem8225042 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term751 B C P p _109328 b a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225041 B C P p _109328 _109330) (@lem8225035 P b a _109330 _109329)). Qed.
Lemma lem8225053 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term750 B C P p _109328 b a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225022 B C P p _109328 b a _109330 _109329) (@lem8225042 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8225054 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term721 B C P p _109327 _109330) = (term721 B C P p _109327 _109330).
Proof. exact (eq_refl (term721 B C P p _109327 _109330)). Qed.
Lemma lem8225055 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term749 B C P _109327 p _109328 b a _109330 _109329) = (term747 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225054 B C P p _109327 _109330) (@lem8225053 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8225066 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term748 B C P _109327 p _109328 b a _109330 _109329) = (term747 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225007 B C P _109327 p _109328 b a _109330 _109329) (@lem8225055 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225067 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term836 B C P z _109327 _109328 _109329 _109330) = (term836 B C P z _109327 _109328 _109329 _109330).
Proof. exact (eq_refl (term836 B C P z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225068 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term859 B C P z _109327 p _109328 b a _109330 _109329) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225067 B C P z _109327 _109328 _109329 _109330) (@lem8225066 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225079 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term858 B C P z _109327 p _109328 b a _109330 _109329) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224990 B C P z _109327 p _109328 b a _109330 _109329) (@lem8225068 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225080 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8225081 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term857 B C P h z _109327 p _109328 b a _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225080 B C P _109327 h _109328 _109330 _109329) (@lem8225079 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225092 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term856 B C P h z _109327 p _109328 b a _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224973 B C P h z _109327 p _109328 b a _109330 _109329) (@lem8225081 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225093 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term825 B C P a b p z _109327 h _109328 _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224968 B C P h z _109327 p _109328 b a _109330 _109329) (@lem8225092 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225094 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term697 B C P a b p z _109327 h _109328 _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8224634 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8225093 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8225096 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term860 B C P a b p z _109327 h _109328 _109330 _109329) = (term861 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225095) (@lem8225094 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225112 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225113 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term862 B C P a b p z _109327 _109328 _109329 _109330) = (term863 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225112 (term617 P _109329 b _109330) (term622 P a _109330 _109329) (term864 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225127 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225128 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term865 B C P a b p z _109327 _109328 _109329 _109330) = (term866 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225127 (term615 B C P p _109327 _109330) (term622 P a _109330 _109329) (term867 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225140 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8225141 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term868 B C P a b p z _109327 _109328 _109329 _109330) = (term867 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225140 (term622 P a _109330 _109329) (term869 B C P b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225145 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225146 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term867 B C P a b p z _109327 _109328 _109329 _109330) = (term870 B C P b a p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225145 (term617 P _109329 b _109330) (term622 P a _109330 _109329) (term871 B C P p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225157 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term868 B C P a b p z _109327 _109328 _109329 _109330) = (term870 B C P b a p z _109327 _109328 _109329 _109330).
Proof. exact (TRANS (@lem8225141 B C P a b p z _109327 _109328 _109329 _109330) (@lem8225146 B C P b a p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225161 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225162 {B C P : Type'} (p : type560 B C P) (a : P -> nat) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term872 B C P a p z _109327 _109328 _109329 _109330) = (term873 B C P p a z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225161 (term615 B C P p _109328 _109330) (term622 P a _109330 _109329) (term602 B C P z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225176 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8225177 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term874 B C P a z _109327 _109328 _109329 _109330) = (term841 B C P z _109327 _109328 a _109330 _109329).
Proof. exact (@lem8225176 (term602 B C P z _109327 _109328 _109329 _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8225185 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term721 B C P p _109328 _109330) = (term721 B C P p _109328 _109330).
Proof. exact (eq_refl (term721 B C P p _109328 _109330)). Qed.
Lemma lem8225186 {B C P : Type'} (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term873 B C P p a z _109327 _109328 _109329 _109330) = (term842 B C P p z _109327 _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8225185 B C P p _109328 _109330) (@lem8225177 B C P z _109327 _109328 a _109330 _109329)). Qed.
Lemma lem8225190 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225191 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term842 B C P p z _109327 _109328 a _109330 _109329) = (term843 B C P z _109327 p _109328 a _109330 _109329).
Proof. exact (@lem8225190 (term602 B C P z _109327 _109328 _109329 _109330) (term615 B C P p _109328 _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8225209 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term873 B C P p a z _109327 _109328 _109329 _109330) = (term843 B C P z _109327 p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8225186 B C P p z _109327 _109328 a _109330 _109329) (@lem8225191 B C P z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8225210 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term872 B C P a p z _109327 _109328 _109329 _109330) = (term843 B C P z _109327 p _109328 a _109330 _109329).
Proof. exact (TRANS (@lem8225162 B C P p a z _109327 _109328 _109329 _109330) (@lem8225209 B C P z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8225211 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term619 P _109329 b _109330) = (term619 P _109329 b _109330).
Proof. exact (eq_refl (term619 P _109329 b _109330)). Qed.
Lemma lem8225212 {B C P : Type'} (b : P -> nat) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term870 B C P b a p z _109327 _109328 _109329 _109330) = (term847 B C P b z _109327 p _109328 a _109330 _109329).
Proof. exact (MK_COMB (@lem8225211 P _109329 b _109330) (@lem8225210 B C P z _109327 p _109328 a _109330 _109329)). Qed.
Lemma lem8225216 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225217 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (b : P -> nat) (p : type560 B C P) (_109328 : B -> C) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term847 B C P b z _109327 p _109328 a _109330 _109329) = (term848 B C P z _109327 b p _109328 a _109330 _109329).
Proof. exact (@lem8225216 (term602 B C P z _109327 _109328 _109329 _109330) (term617 P _109329 b _109330) (term733 B C P p _109328 a _109330 _109329)). Qed.
Lemma lem8225233 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225234 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term734 B C P b p _109328 a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (@lem8225233 (term615 B C P p _109328 _109330) (term617 P _109329 b _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8225250 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term836 B C P z _109327 _109328 _109329 _109330) = (term836 B C P z _109327 _109328 _109329 _109330).
Proof. exact (eq_refl (term836 B C P z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225251 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term848 B C P z _109327 b p _109328 a _109330 _109329) = (term849 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225250 B C P z _109327 _109328 _109329 _109330) (@lem8225234 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8225262 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term847 B C P b z _109327 p _109328 a _109330 _109329) = (term849 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225217 B C P z _109327 b p _109328 a _109330 _109329) (@lem8225251 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225263 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term870 B C P b a p z _109327 _109328 _109329 _109330) = (term849 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225212 B C P b z _109327 p _109328 a _109330 _109329) (@lem8225262 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225264 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term868 B C P a b p z _109327 _109328 _109329 _109330) = (term849 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225157 B C P b a p z _109327 _109328 _109329 _109330) (@lem8225263 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225265 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term721 B C P p _109327 _109330) = (term721 B C P p _109327 _109330).
Proof. exact (eq_refl (term721 B C P p _109327 _109330)). Qed.
Lemma lem8225266 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term866 B C P a b p z _109327 _109328 _109329 _109330) = (term853 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225265 B C P p _109327 _109330) (@lem8225264 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225270 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225271 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term853 B C P z _109327 p _109328 b a _109330 _109329) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8225270 (term602 B C P z _109327 _109328 _109329 _109330) (term615 B C P p _109327 _109330) (term735 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8225309 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term866 B C P a b p z _109327 _109328 _109329 _109330) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225266 B C P z _109327 p _109328 b a _109330 _109329) (@lem8225271 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225310 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term865 B C P a b p z _109327 _109328 _109329 _109330) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225128 B C P a b p z _109327 _109328 _109329 _109330) (@lem8225309 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225311 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term619 P _109329 b _109330) = (term619 P _109329 b _109330).
Proof. exact (eq_refl (term619 P _109329 b _109330)). Qed.
Lemma lem8225312 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term863 B C P a b p z _109327 _109328 _109329 _109330) = (term858 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225311 P _109329 b _109330) (@lem8225310 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225316 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225317 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term858 B C P z _109327 p _109328 b a _109330 _109329) = (term859 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8225316 (term602 B C P z _109327 _109328 _109329 _109330) (term617 P _109329 b _109330) (term747 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225333 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225334 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term748 B C P _109327 p _109328 b a _109330 _109329) = (term749 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (@lem8225333 (term615 B C P p _109327 _109330) (term617 P _109329 b _109330) (term735 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8225348 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8225349 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term750 B C P p _109328 b a _109330 _109329) = (term751 B C P p _109328 b a _109330 _109329).
Proof. exact (@lem8225348 (term615 B C P p _109328 _109330) (term617 P _109329 b _109330) (term752 P b a _109330 _109329)). Qed.
Lemma lem8225361 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8225362 {P : Type'} (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term753 P b a _109330 _109329) = (term752 P b a _109330 _109329).
Proof. exact (@lem8225361 (term617 P _109329 b _109330) (term622 P a _109330 _109329)). Qed.
Lemma lem8225368 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term721 B C P p _109328 _109330) = (term721 B C P p _109328 _109330).
Proof. exact (eq_refl (term721 B C P p _109328 _109330)). Qed.
Lemma lem8225369 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term751 B C P p _109328 b a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225368 B C P p _109328 _109330) (@lem8225362 P b a _109330 _109329)). Qed.
Lemma lem8225380 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term750 B C P p _109328 b a _109330 _109329) = (term735 B C P p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225349 B C P p _109328 b a _109330 _109329) (@lem8225369 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8225381 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term721 B C P p _109327 _109330) = (term721 B C P p _109327 _109330).
Proof. exact (eq_refl (term721 B C P p _109327 _109330)). Qed.
Lemma lem8225382 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term749 B C P _109327 p _109328 b a _109330 _109329) = (term747 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225381 B C P p _109327 _109330) (@lem8225380 B C P p _109328 b a _109330 _109329)). Qed.
Lemma lem8225393 {B C P : Type'} (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term748 B C P _109327 p _109328 b a _109330 _109329) = (term747 B C P _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225334 B C P _109327 p _109328 b a _109330 _109329) (@lem8225382 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225394 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term836 B C P z _109327 _109328 _109329 _109330) = (term836 B C P z _109327 _109328 _109329 _109330).
Proof. exact (eq_refl (term836 B C P z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225395 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term859 B C P z _109327 p _109328 b a _109330 _109329) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225394 B C P z _109327 _109328 _109329 _109330) (@lem8225393 B C P _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225406 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term858 B C P z _109327 p _109328 b a _109330 _109329) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225317 B C P z _109327 p _109328 b a _109330 _109329) (@lem8225395 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225407 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term863 B C P a b p z _109327 _109328 _109329 _109330) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225312 B C P z _109327 p _109328 b a _109330 _109329) (@lem8225406 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225408 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term862 B C P a b p z _109327 _109328 _109329 _109330) = (term854 B C P z _109327 p _109328 b a _109330 _109329).
Proof. exact (TRANS (@lem8225113 B C P a b p z _109327 _109328 _109329 _109330) (@lem8225407 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225409 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term727 B C P _109327 h _109328 _109330 _109329) = (term727 B C P _109327 h _109328 _109330 _109329).
Proof. exact (eq_refl (term727 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8225410 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : (term875 B C P h a b p z _109327 _109328 _109329 _109330) = (term855 B C P h z _109327 p _109328 b a _109330 _109329).
Proof. exact (MK_COMB (@lem8225409 B C P _109327 h _109328 _109330 _109329) (@lem8225408 B C P z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225421 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : ((term697 B C P a b p z _109327 h _109328 _109330 _109329) = (term875 B C P h a b p z _109327 _109328 _109329 _109330)) = ((term855 B C P h z _109327 p _109328 b a _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329)).
Proof. exact (MK_COMB (@lem8225096 B C P h z _109327 p _109328 b a _109330 _109329) (@lem8225410 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225423 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8225424 (x : Prop) : (x = x) = True.
Proof. exact (@lem8225423 Prop x). Qed.
Lemma lem8225425 {B C P : Type'} (h : type556 B C P) (z : type521 B C P) (_109327 : B -> C) (p : type560 B C P) (_109328 : B -> C) (b : P -> nat) (a : P -> nat) (_109330 : P) (_109329 : nat) : ((term855 B C P h z _109327 p _109328 b a _109330 _109329) = (term855 B C P h z _109327 p _109328 b a _109330 _109329)) = True.
Proof. exact (@lem8225424 (term855 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225426 {B C P : Type'} (h : type556 B C P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : ((term697 B C P a b p z _109327 h _109328 _109330 _109329) = (term875 B C P h a b p z _109327 _109328 _109329 _109330)) = True.
Proof. exact (TRANS (@lem8225421 B C P h z _109327 p _109328 b a _109330 _109329) (@lem8225425 B C P h z _109327 p _109328 b a _109330 _109329)). Qed.
Lemma lem8225427 {B C P : Type'} (h : type556 B C P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : True = ((term697 B C P a b p z _109327 h _109328 _109330 _109329) = (term875 B C P h a b p z _109327 _109328 _109329 _109330)).
Proof. exact (SYM (@lem8225426 B C P h a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225428 {B C P : Type'} (h : type556 B C P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term697 B C P a b p z _109327 h _109328 _109330 _109329) = (term875 B C P h a b p z _109327 _109328 _109329 _109330).
Proof. exact (EQ_MP (@lem8225427 B C P h a b p z _109327 _109328 _109329 _109330) (@lem0)). Qed.
Lemma lem8225429 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term875 B C P h a b p z _109327 _109328 _109329 _109330.
Proof. exact (EQ_MP (@lem8225428 B C P h a b p z _109327 _109328 _109329 _109330) (@lem8223263 A B C P _109327 _109328 _109330 _109329 a b p lt2 s z h h1)). Qed.
Lemma lem8225431 (b : Prop) (a : Prop) : (a \/ b) = (term779 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8225432 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term875 B C P h a b p z _109327 _109328 _109329 _109330) = (term876 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (@lem8225431 (term862 B C P a b p z _109327 _109328 _109329 _109330) ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8225434 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8225435 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term877 B C P a b p z _109327 _109328 _109329 _109330) = (term878 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225434 (term622 P a _109330 _109329) (term879 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225437 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8225438 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term786 P a _109330 _109329) = (term579 P a _109330 _109329).
Proof. exact (@lem8225437 (term579 P a _109330 _109329)). Qed.
Lemma lem8225439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8225440 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term787 P a _109330 _109329) = (term581 P a _109330 _109329).
Proof. exact (MK_COMB (@lem8225439) (@lem8225438 P a _109330 _109329)). Qed.
Lemma lem8225442 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8225443 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term880 B C P a b p z _109327 _109328 _109329 _109330) = (term881 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225442 (term617 P _109329 b _109330) (term864 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225445 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8225446 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term790 P _109329 b _109330) = (term573 P _109329 b _109330).
Proof. exact (@lem8225445 (term573 P _109329 b _109330)). Qed.
Lemma lem8225447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8225448 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term791 P _109329 b _109330) = (term792 P _109329 b _109330).
Proof. exact (MK_COMB (@lem8225447) (@lem8225446 P _109329 b _109330)). Qed.
Lemma lem8225450 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8225451 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term882 B C P a b p z _109327 _109328 _109329 _109330) = (term883 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225450 (term615 B C P p _109327 _109330) (term867 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225453 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8225454 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term795 B C P p _109327 _109330) = (term558 B C P p _109327 _109330).
Proof. exact (@lem8225453 (term558 B C P p _109327 _109330)). Qed.
Lemma lem8225455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8225456 {B C P : Type'} (p : type560 B C P) (_109327 : B -> C) (_109330 : P) : (term796 B C P p _109327 _109330) = (term797 B C P p _109327 _109330).
Proof. exact (MK_COMB (@lem8225455) (@lem8225454 B C P p _109327 _109330)). Qed.
Lemma lem8225458 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8225459 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term884 B C P a b p z _109327 _109328 _109329 _109330) = (term885 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225458 (term622 P a _109330 _109329) (term869 B C P b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225461 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8225462 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term786 P a _109330 _109329) = (term579 P a _109330 _109329).
Proof. exact (@lem8225461 (term579 P a _109330 _109329)). Qed.
Lemma lem8225463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8225464 {P : Type'} (a : P -> nat) (_109330 : P) (_109329 : nat) : (term787 P a _109330 _109329) = (term581 P a _109330 _109329).
Proof. exact (MK_COMB (@lem8225463) (@lem8225462 P a _109330 _109329)). Qed.
Lemma lem8225466 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8225467 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term886 B C P b p z _109327 _109328 _109329 _109330) = (term887 B C P b p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225466 (term617 P _109329 b _109330) (term871 B C P p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225469 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8225470 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term790 P _109329 b _109330) = (term573 P _109329 b _109330).
Proof. exact (@lem8225469 (term573 P _109329 b _109330)). Qed.
Lemma lem8225471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8225472 {P : Type'} (_109329 : nat) (b : P -> nat) (_109330 : P) : (term791 P _109329 b _109330) = (term792 P _109329 b _109330).
Proof. exact (MK_COMB (@lem8225471) (@lem8225470 P _109329 b _109330)). Qed.
Lemma lem8225474 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8225475 {B C P : Type'} (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term888 B C P p z _109327 _109328 _109329 _109330) = (term889 B C P p z _109327 _109328 _109329 _109330).
Proof. exact (@lem8225474 (term615 B C P p _109328 _109330) (term602 B C P z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225477 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8225478 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term795 B C P p _109328 _109330) = (term558 B C P p _109328 _109330).
Proof. exact (@lem8225477 (term558 B C P p _109328 _109330)). Qed.
Lemma lem8225479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8225480 {B C P : Type'} (p : type560 B C P) (_109328 : B -> C) (_109330 : P) : (term796 B C P p _109328 _109330) = (term797 B C P p _109328 _109330).
Proof. exact (MK_COMB (@lem8225479) (@lem8225478 B C P p _109328 _109330)). Qed.
Lemma lem8225482 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8225483 {B C P : Type'} (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term890 B C P z _109327 _109328 _109329 _109330) = ((term595 B C P z _109327 _109328 _109329 _109330) = (term598 B C P z _109327 _109328 _109329 _109330)).
Proof. exact (@lem8225482 ((term595 B C P z _109327 _109328 _109329 _109330) = (term598 B C P z _109327 _109328 _109329 _109330))). Qed.
Lemma lem8225484 {B C P : Type'} (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term889 B C P p z _109327 _109328 _109329 _109330) = (term891 B C P p z _109327 _109328 _109329 _109330).
Proof. exact (MK_COMB (@lem8225480 B C P p _109328 _109330) (@lem8225483 B C P z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225485 {B C P : Type'} (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term888 B C P p z _109327 _109328 _109329 _109330) = (term891 B C P p z _109327 _109328 _109329 _109330).
Proof. exact (TRANS (@lem8225475 B C P p z _109327 _109328 _109329 _109330) (@lem8225484 B C P p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225486 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term887 B C P b p z _109327 _109328 _109329 _109330) = (term892 B C P b p z _109327 _109328 _109329 _109330).
Proof. exact (MK_COMB (@lem8225472 P _109329 b _109330) (@lem8225485 B C P p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225487 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term886 B C P b p z _109327 _109328 _109329 _109330) = (term892 B C P b p z _109327 _109328 _109329 _109330).
Proof. exact (TRANS (@lem8225467 B C P b p z _109327 _109328 _109329 _109330) (@lem8225486 B C P b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225488 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term885 B C P a b p z _109327 _109328 _109329 _109330) = (term893 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (MK_COMB (@lem8225464 P a _109330 _109329) (@lem8225487 B C P b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225489 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term884 B C P a b p z _109327 _109328 _109329 _109330) = (term893 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (TRANS (@lem8225459 B C P a b p z _109327 _109328 _109329 _109330) (@lem8225488 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225490 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term883 B C P a b p z _109327 _109328 _109329 _109330) = (term894 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (MK_COMB (@lem8225456 B C P p _109327 _109330) (@lem8225489 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225491 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term882 B C P a b p z _109327 _109328 _109329 _109330) = (term894 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (TRANS (@lem8225451 B C P a b p z _109327 _109328 _109329 _109330) (@lem8225490 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225492 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term881 B C P a b p z _109327 _109328 _109329 _109330) = (term895 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (MK_COMB (@lem8225448 P _109329 b _109330) (@lem8225491 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225493 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term880 B C P a b p z _109327 _109328 _109329 _109330) = (term895 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (TRANS (@lem8225443 B C P a b p z _109327 _109328 _109329 _109330) (@lem8225492 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225494 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term878 B C P a b p z _109327 _109328 _109329 _109330) = (term896 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (MK_COMB (@lem8225440 P a _109330 _109329) (@lem8225493 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225495 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term877 B C P a b p z _109327 _109328 _109329 _109330) = (term896 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (TRANS (@lem8225435 B C P a b p z _109327 _109328 _109329 _109330) (@lem8225494 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8225497 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (_109328 : B -> C) (_109329 : nat) (_109330 : P) : (term897 B C P a b p z _109327 _109328 _109329 _109330) = (term898 B C P a b p z _109327 _109328 _109329 _109330).
Proof. exact (MK_COMB (@lem8225496) (@lem8225495 B C P a b p z _109327 _109328 _109329 _109330)). Qed.
Lemma lem8225498 {B C P : Type'} (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)) = ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329)).
Proof. exact (eq_refl ((term585 B C P h _109327 _109330 _109329) = (term585 B C P h _109328 _109330 _109329))). Qed.
Lemma lem8225499 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term876 B C P a b p z _109327 h _109328 _109330 _109329) = (term899 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (MK_COMB (@lem8225497 B C P a b p z _109327 _109328 _109329 _109330) (@lem8225498 B C P _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8225500 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109327 : B -> C) (h : type556 B C P) (_109328 : B -> C) (_109330 : P) (_109329 : nat) : (term875 B C P h a b p z _109327 _109328 _109329 _109330) = (term899 B C P a b p z _109327 h _109328 _109330 _109329).
Proof. exact (TRANS (@lem8225432 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8225499 B C P a b p z _109327 h _109328 _109330 _109329)). Qed.
Lemma lem8225502 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term891 B C P p z f g i a'.
Proof. exact (conj (@lem8223601 B C P p g a' h6) (@lem8224627 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8225503 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term892 B C P b p z f g i a'.
Proof. exact (conj (@lem8223594 P a i b a' h4) (@lem8225502 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8225504 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term893 B C P a b p z f g i a'.
Proof. exact (conj (@lem8223587 P a i b a' h4) (@lem8225503 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8225505 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term894 B C P a b p z f g i a'.
Proof. exact (conj (@lem8223580 B C P p f a' h5) (@lem8225504 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8225506 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term895 B C P a b p z f g i a'.
Proof. exact (conj (@lem8223573 P a i b a' h4) (@lem8225505 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8225507 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term896 B C P a b p z f g i a'.
Proof. exact (conj (@lem8223566 P a i b a' h4) (@lem8225506 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8225509 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109330 : P) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term899 B C P a b p z _109327 h _109328 _109330 _109329.
Proof. exact (EQ_MP (@lem8225500 B C P a b p z _109327 h _109328 _109330 _109329) (@lem8225429 A B C P _109327 _109328 _109329 _109330 a b p lt2 s z h h1)). Qed.
Lemma lem8225510 {A B C P : Type'} (_109327 : B -> C) (_109328 : B -> C) (_109330 : P) (_109329 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term899 B C P a b p z _109327 h _109328 _109330 _109329.
Proof. exact (@lem8225509 A B C P _109327 _109328 _109330 _109329 a b p lt2 s z h h1). Qed.
Lemma lem8225511 {A B C P : Type'} (f : B -> C) (g : B -> C) (a' : P) (i : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term899 B C P a b p z f h g a' i.
Proof. exact (@lem8225510 A B C P f g a' i a b p lt2 s z h h1). Qed.
Lemma lem8225514 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term585 B C P h f a' i) = (term585 B C P h g a' i).
Proof. exact (@lem8225511 A B C P f g a' i a b p lt2 s z h h2 (@lem8225507 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8225515 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term900 B C P f h g a' i.
Proof. exact (fun h0 : term587 B C P f h g a' i => @lem8225514 A B C P lt2 s z h a i b f p g a' h1 h2 h0 h3 h4 h5). Qed.
Lemma lem8225517 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8225518 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (term900 B C P f h g a' i) = ((term585 B C P h f a' i) = (term585 B C P h g a' i)).
Proof. exact (@lem8225517 ((term585 B C P h f a' i) = (term585 B C P h g a' i))). Qed.
Lemma lem8225519 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : (term585 B C P h f a' i) = (term585 B C P h g a' i).
Proof. exact (EQ_MP (@lem8225518 B C P f h g a' i) (@lem8225515 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5)). Qed.
Lemma lem8225522 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8225524 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) : (term587 B C P f h g a' i) = (term901 B C P f h g a' i).
Proof. exact (@lem8225522 ((term585 B C P h f a' i) = (term585 B C P h g a' i))). Qed.
Lemma lem8225527 {B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term365 B C P f h g a' i) : term901 B C P f h g a' i.
Proof. exact (EQ_MP (@lem8225524 B C P f h g a' i) (@lem8223175 B C P f h g a' i h1)). Qed.
Lemma lem8225530 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (@lem8225527 B C P f h g a' i h3 (@lem8225519 A B C P lt2 s z h a i b f p g a' h1 h2 h4 h5 h6)). Qed.
Lemma lem8225531 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term902.
Proof. exact (fun h0 : ~ False => @lem8225530 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem8225533 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8225534 : term902 = False.
Proof. exact (@lem8225533 False). Qed.
Lemma lem8225535 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8225534) (@lem8225531 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8225536 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (ex_elim (@lem8222360 A B C P a b p lt2 s h h2) (fun z : type521 B C P => fun h0 : term552 A B C P a b p lt2 s h z => @lem8225535 A B C P lt2 s z h a i b f p g a' h1 h0 h3 h4 h5 h6)). Qed.
Lemma lem8225537 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term365 B C P f h g a' i) = False.
Proof. exact (prop_ext (fun h7 : term365 B C P f h g a' i => @lem8225536 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8222451 B C P f h g a' i h3)). Qed.
Lemma lem8225538 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8225537 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8222451 B C P f h g a' i h3)). Qed.
Lemma lem8225539 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term557 P a i b a') = False.
Proof. exact (prop_ext (fun h7 : term557 P a i b a' => @lem8225538 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8222445 P a i b a' h4)). Qed.
Lemma lem8225540 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8225539 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8222445 P a i b a' h4)). Qed.
Lemma lem8225541 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (p g a') = False.
Proof. exact (prop_ext (fun h7 : p g a' => @lem8225540 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8222372 B C P p g a' h6)). Qed.
Lemma lem8225542 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8225541 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8222372 B C P p g a' h6)). Qed.
Lemma lem8225543 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (p f a') = False.
Proof. exact (prop_ext (fun h7 : p f a' => @lem8225542 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8222366 B C P p f a' h5)). Qed.
Lemma lem8225544 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8225543 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8222366 B C P p f a' h5)). Qed.
Lemma lem8225545 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term365 B C P f h g a' i) = False.
Proof. exact (prop_ext (fun h7 : term365 B C P f h g a' i => @lem8225544 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8221969 B C P f h g a' i h3)). Qed.
Lemma lem8225546 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8225545 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8221969 B C P f h g a' i h3)). Qed.
Lemma lem8225547 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term364 B C P f h g a' i.
Proof. exact (fun h0 : term365 B C P f h g a' i => @lem8225546 A B C P lt2 s h a i b f p g a' h1 h2 h0 h3 h4 h5). Qed.
Lemma lem8225548 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : (h f a' i) = (h g a' i).
Proof. exact (EQ_MP (@lem8221968 B C P f h g a' i) (@lem8225547 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5)). Qed.
Lemma lem8225549 {A B C P : Type'} (i : nat) (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term362 B C P a b f h g a' i.
Proof. exact (fun h0 : term557 P a i b a' => @lem8225548 A B C P lt2 s h a i b f p g a' h1 h2 h0 h3 h4). Qed.
Lemma lem8225554 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term308 B C P a b f h g a'.
Proof. exact (fun i : nat => @lem8225549 A B C P i a b lt2 s h f p g a' h1 h2 h3 h4). Qed.
Lemma lem8225555 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : p f a') (h3 : p g a') : term319 A B C P lt2 s a b f h g a'.
Proof. exact (fun h0 : term174 A B C P lt2 s a' f g => @lem8225554 A B C P a b lt2 s h f p g a' h0 h1 h2 h3). Qed.
Lemma lem8225556 {A B C P : Type'} (g : B -> C) (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : p f a') : term322 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : p g a' => @lem8225555 A B C P a b lt2 s h f p g a' h1 h2 h0). Qed.
Lemma lem8225557 {A B C P : Type'} (f : B -> C) (g : B -> C) (a' : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term324 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : p f a' => @lem8225556 A B C P g a b lt2 s h p f a' h1 h0). Qed.
Lemma lem8225558 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term325 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term240 A B C P a b p lt2 s h => @lem8225557 A B C P f g a' a b p lt2 s h h0). Qed.
Lemma lem8225563 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term329 A B C P lt2 s a b f h g a'.
Proof. exact (fun p : type560 B C P => @lem8225558 A B C P p lt2 s a b f h g a'). Qed.
Lemma lem8225568 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term333 A B C P s a b f h g a'.
Proof. exact (fun lt2 : type1470 A B => @lem8225563 A B C P lt2 s a b f h g a'). Qed.
Lemma lem8225573 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term337 A B C P a b f h g a'.
Proof. exact (fun s : P -> A => @lem8225568 A B C P s a b f h g a'). Qed.
Lemma lem8225578 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term341 A B C P b f h g a'.
Proof. exact (fun a : P -> nat => @lem8225573 A B C P a b f h g a'). Qed.
Lemma lem8225583 {A B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term345 A B C P f h g a'.
Proof. exact (fun b : P -> nat => @lem8225578 A B C P b f h g a'). Qed.
Lemma lem8225588 {A B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : term349 A B C P h g a'.
Proof. exact (fun f : B -> C => @lem8225583 A B C P f h g a'). Qed.
Lemma lem8225593 {A B C P : Type'} (g : B -> C) (a' : P) : term353 A B C P g a'.
Proof. exact (fun h : type556 B C P => @lem8225588 A B C P h g a'). Qed.
Lemma lem8225598 {A B C P : Type'} (a' : P) : term357 A B C P a'.
Proof. exact (fun g : B -> C => @lem8225593 A B C P g a'). Qed.
Lemma lem8225603 {A B C P : Type'} : term361 A B C P.
Proof. exact (fun a' : P => @lem8225598 A B C P a'). Qed.
Lemma lem8225604 {A B C P : Type'} : term360 A B C P.
Proof. exact (EQ_MP (@lem8221959 A B C P) (@lem8225603 A B C P)). Qed.
Lemma lem8225605 {A B C P : Type'} (a' : P) : term903 A B C P a'.
Proof. exact (@lem8225604 A B C P a'). Qed.
Lemma lem8225606 {A B C P : Type'} (a' : P) : (term903 A B C P a') = (term356 A B C P a').
Proof. exact (eq_refl (term903 A B C P a')). Qed.
Lemma lem8225607 {A B C P : Type'} (a' : P) : term356 A B C P a'.
Proof. exact (EQ_MP (@lem8225606 A B C P a') (@lem8225605 A B C P a')). Qed.
Lemma lem8225608 {A B C P : Type'} (a' : P) (g : B -> C) : term904 A B C P a' g.
Proof. exact (@lem8225607 A B C P a' g). Qed.
Lemma lem8225609 {A B C P : Type'} (g : B -> C) (a' : P) : (term904 A B C P a' g) = (term352 A B C P g a').
Proof. exact (eq_refl (term904 A B C P a' g)). Qed.
Lemma lem8225610 {A B C P : Type'} (g : B -> C) (a' : P) : term352 A B C P g a'.
Proof. exact (EQ_MP (@lem8225609 A B C P g a') (@lem8225608 A B C P a' g)). Qed.
Lemma lem8225611 {A B C P : Type'} (g : B -> C) (a' : P) (h : type556 B C P) : term905 A B C P g a' h.
Proof. exact (@lem8225610 A B C P g a' h). Qed.
Lemma lem8225612 {A B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : (term905 A B C P g a' h) = (term348 A B C P h g a').
Proof. exact (eq_refl (term905 A B C P g a' h)). Qed.
Lemma lem8225613 {A B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) : term348 A B C P h g a'.
Proof. exact (EQ_MP (@lem8225612 A B C P h g a') (@lem8225611 A B C P g a' h)). Qed.
Lemma lem8225614 {A B C P : Type'} (h : type556 B C P) (g : B -> C) (a' : P) (f : B -> C) : term906 A B C P h g a' f.
Proof. exact (@lem8225613 A B C P h g a' f). Qed.
Lemma lem8225615 {A B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term906 A B C P h g a' f) = (term344 A B C P f h g a').
Proof. exact (eq_refl (term906 A B C P h g a' f)). Qed.
Lemma lem8225616 {A B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term344 A B C P f h g a'.
Proof. exact (EQ_MP (@lem8225615 A B C P f h g a') (@lem8225614 A B C P h g a' f)). Qed.
Lemma lem8225617 {A B C P : Type'} (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (b : P -> nat) : term907 A B C P f h g a' b.
Proof. exact (@lem8225616 A B C P f h g a' b). Qed.
Lemma lem8225618 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term907 A B C P f h g a' b) = (term340 A B C P b f h g a').
Proof. exact (eq_refl (term907 A B C P f h g a' b)). Qed.
Lemma lem8225619 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term340 A B C P b f h g a'.
Proof. exact (EQ_MP (@lem8225618 A B C P b f h g a') (@lem8225617 A B C P f h g a' b)). Qed.
Lemma lem8225620 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (a : P -> nat) : term908 A B C P b f h g a' a.
Proof. exact (@lem8225619 A B C P b f h g a' a). Qed.
Lemma lem8225621 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term908 A B C P b f h g a' a) = (term336 A B C P a b f h g a').
Proof. exact (eq_refl (term908 A B C P b f h g a' a)). Qed.
Lemma lem8225622 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term336 A B C P a b f h g a'.
Proof. exact (EQ_MP (@lem8225621 A B C P a b f h g a') (@lem8225620 A B C P b f h g a' a)). Qed.
Lemma lem8225623 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (s : P -> A) : term909 A B C P a b f h g a' s.
Proof. exact (@lem8225622 A B C P a b f h g a' s). Qed.
Lemma lem8225624 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term909 A B C P a b f h g a' s) = (term332 A B C P s a b f h g a').
Proof. exact (eq_refl (term909 A B C P a b f h g a' s)). Qed.
Lemma lem8225625 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term332 A B C P s a b f h g a'.
Proof. exact (EQ_MP (@lem8225624 A B C P s a b f h g a') (@lem8225623 A B C P a b f h g a' s)). Qed.
Lemma lem8225626 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (lt2 : type1470 A B) : term910 A B C P s a b f h g a' lt2.
Proof. exact (@lem8225625 A B C P s a b f h g a' lt2). Qed.
Lemma lem8225627 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term910 A B C P s a b f h g a' lt2) = (term328 A B C P lt2 s a b f h g a').
Proof. exact (eq_refl (term910 A B C P s a b f h g a' lt2)). Qed.
Lemma lem8225628 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term328 A B C P lt2 s a b f h g a'.
Proof. exact (EQ_MP (@lem8225627 A B C P lt2 s a b f h g a') (@lem8225626 A B C P s a b f h g a' lt2)). Qed.
Lemma lem8225629 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) (p : type560 B C P) : term911 A B C P lt2 s a b f h g a' p.
Proof. exact (@lem8225628 A B C P lt2 s a b f h g a' p). Qed.
Lemma lem8225630 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : (term911 A B C P lt2 s a b f h g a' p) = (term311 A B C P p lt2 s a b f h g a').
Proof. exact (eq_refl (term911 A B C P lt2 s a b f h g a' p)). Qed.
Lemma lem8225631 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (EQ_MP (@lem8225630 A B C P p lt2 s a b f h g a') (@lem8225629 A B C P lt2 s a b f h g a' p)). Qed.
Lemma lem8225633 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type556 B C P) (g : B -> C) (a' : P) : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8221536 A B C P p lt2 s a b f h g a' (@lem8225631 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8225634 {A B C P : Type'} (f : B -> C) (g : B -> C) (a' : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term323 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8225633 A B C P p lt2 s a b f h g a' (@lem8221507 A B C P a b p lt2 s h h1)). Qed.
Lemma lem8225635 {A B C P : Type'} (g : B -> C) (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : p f a') : term321 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8225634 A B C P f g a' a b p lt2 s h h1 (@lem8221510 B C P p f a' h2)). Qed.
Lemma lem8225636 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : p f a') (h3 : p g a') : term318 A B C P lt2 s a b f h g a'.
Proof. exact (@lem8225635 A B C P g a b lt2 s h p f a' h1 h2 (@lem8221512 B C P p g a' h3)). Qed.
Lemma lem8225637 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term309 B C P a b f h g a'.
Proof. exact (@lem8225636 A B C P a b lt2 s h f p g a' h2 h3 h4 (@lem8221511 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8225638 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term310 B C P a b f h g a') (h4 : p f a') (h5 : p g a') : False.
Proof. exact (@lem8225637 A B C P a b lt2 s h f p g a' h1 h2 h4 h5 (@lem8221520 B C P a b f h g a' h3)). Qed.
Lemma lem8225639 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term310 B C P a b f h g a') (h4 : p f a') (h5 : p g a') : (term310 B C P a b f h g a') = False.
Proof. exact (prop_ext (fun h6 : term310 B C P a b f h g a' => @lem8225638 A B C P lt2 s a b h f p g a' h1 h2 h3 h4 h5) (fun h6 : False => @lem8221520 B C P a b f h g a' h3)). Qed.
Lemma lem8225640 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term310 B C P a b f h g a') (h4 : p f a') (h5 : p g a') : False.
Proof. exact (EQ_MP (@lem8225639 A B C P lt2 s a b h f p g a' h1 h2 h3 h4 h5) (@lem8221520 B C P a b f h g a' h3)). Qed.
Lemma lem8225641 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term309 B C P a b f h g a'.
Proof. exact (fun h0 : term310 B C P a b f h g a' => @lem8225640 A B C P lt2 s a b h f p g a' h1 h2 h0 h3 h4). Qed.
Lemma lem8225642 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term308 B C P a b f h g a'.
Proof. exact (EQ_MP (@lem8221519 B C P a b f h g a') (@lem8225641 A B C P a b lt2 s h f p g a' h1 h2 h3 h4)). Qed.
Lemma lem8225643 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (@lem8221515 B C P f a b h g a' (@lem8225642 A B C P a b lt2 s h f p g a' h1 h2 h3 h4)). Qed.
Lemma lem8225644 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term304 A B C P p lt2 s a' f g) : term305 A B C P p lt2 s a' f g.
Proof. exact (proj2 (@lem8221508 A B C P p lt2 s a' f g h1)). Qed.
Lemma lem8225645 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term304 A B C P p lt2 s a' f g) : p f a'.
Proof. exact (proj1 (@lem8221508 A B C P p lt2 s a' f g h1)). Qed.
Lemma lem8225646 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term305 A B C P p lt2 s a' f g) : term174 A B C P lt2 s a' f g.
Proof. exact (proj2 (@lem8221509 A B C P p lt2 s a' f g h1)). Qed.
Lemma lem8225647 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term305 A B C P p lt2 s a' f g) : p g a'.
Proof. exact (proj1 (@lem8221509 A B C P p lt2 s a' f g h1)). Qed.
Lemma lem8225648 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (term174 A B C P lt2 s a' f g) = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h5 : term174 A B C P lt2 s a' f g => @lem8225643 A B C P a b lt2 s h f p g a' h1 h2 h3 h4) (fun h5 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8221511 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8225649 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8225648 A B C P a b lt2 s h f p g a' h1 h2 h3 h4) (@lem8221511 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8225650 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (p g a') = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h5 : p g a' => @lem8225649 A B C P a b lt2 s h f p g a' h1 h2 h3 h4) (fun h5 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8221512 B C P p g a' h4)). Qed.
Lemma lem8225651 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8225650 A B C P a b lt2 s h f p g a' h1 h2 h3 h4) (@lem8221512 B C P p g a' h4)). Qed.
Lemma lem8225652 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') (h4 : p g a') : (term174 A B C P lt2 s a' f g) = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h5 : term174 A B C P lt2 s a' f g => @lem8225651 A B C P a b lt2 s h f p g a' h5 h1 h3 h4) (fun h5 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8225646 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8225653 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') (h4 : p g a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8225652 A B C P a b h lt2 s f p g a' h1 h2 h3 h4) (@lem8225646 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8225654 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') : (p g a') = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h4 : p g a' => @lem8225653 A B C P a b h lt2 s f p g a' h1 h2 h3 h4) (fun h4 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8225647 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8225655 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8225654 A B C P a b h lt2 s g p f a' h1 h2 h3) (@lem8225647 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8225656 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') : (p f a') = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h4 : p f a' => @lem8225655 A B C P a b h lt2 s g p f a' h1 h2 h3) (fun h4 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8221510 B C P p f a' h3)). Qed.
Lemma lem8225657 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8225656 A B C P a b h lt2 s g p f a' h1 h2 h3) (@lem8221510 B C P p f a' h3)). Qed.
Lemma lem8225658 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term304 A B C P p lt2 s a' f g) (h3 : p f a') : (term305 A B C P p lt2 s a' f g) = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h4 : term305 A B C P p lt2 s a' f g => @lem8225657 A B C P a b h lt2 s g p f a' h1 h4 h3) (fun h4 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8225644 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8225659 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term304 A B C P p lt2 s a' f g) (h3 : p f a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8225658 A B C P a b h lt2 s g p f a' h1 h2 h3) (@lem8225644 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8225660 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term240 A B C P a b p lt2 s h) (h2 : term304 A B C P p lt2 s a' f g) : (p f a') = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h3 : p f a' => @lem8225659 A B C P a b h lt2 s g p f a' h1 h2 h3) (fun h3 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8225645 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8225661 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type556 B C P) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term240 A B C P a b p lt2 s h) (h2 : term304 A B C P p lt2 s a' f g) : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8225660 A B C P a b h p lt2 s a' f g h1 h2) (@lem8225645 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8225662 {A B C P : Type'} (f : B -> C) (g : B -> C) (a' : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term266 A B C P p lt2 s f a b h g a'.
Proof. exact (fun h0 : term304 A B C P p lt2 s a' f g => @lem8225661 A B C P a b h p lt2 s a' f g h1 h0). Qed.
Lemma lem8225667 {A B C P : Type'} (f : B -> C) (g : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term270 A B C P p lt2 s f a b h g.
Proof. exact (fun a' : P => @lem8225662 A B C P f g a' a b p lt2 s h h1). Qed.
Lemma lem8225672 {A B C P : Type'} (f : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term274 A B C P p lt2 s f a b h.
Proof. exact (fun g : B -> C => @lem8225667 A B C P f g a b p lt2 s h h1). Qed.
Lemma lem8225677 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term277 A B C P p lt2 s a b h.
Proof. exact (fun f : B -> C => @lem8225672 A B C P f a b p lt2 s h h1). Qed.
Lemma lem8225678 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : (term240 A B C P a b p lt2 s h) = (term277 A B C P p lt2 s a b h).
Proof. exact (prop_ext (fun h2 : term240 A B C P a b p lt2 s h => @lem8225677 A B C P a b p lt2 s h h1) (fun h2 : term277 A B C P p lt2 s a b h => @lem8221507 A B C P a b p lt2 s h h1)). Qed.
Lemma lem8225679 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) (h1 : term240 A B C P a b p lt2 s h) : term277 A B C P p lt2 s a b h.
Proof. exact (EQ_MP (@lem8225678 A B C P a b p lt2 s h h1) (@lem8221507 A B C P a b p lt2 s h h1)). Qed.
Lemma lem8225680 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type556 B C P) : term279 A B C P p lt2 s a b h.
Proof. exact (fun h0 : term240 A B C P a b p lt2 s h => @lem8225679 A B C P a b p lt2 s h h0). Qed.
Lemma lem8225685 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (h : type556 B C P) : term283 A B C P p lt2 s a h.
Proof. exact (fun b : P -> nat => @lem8225680 A B C P p lt2 s a b h). Qed.
Lemma lem8225690 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type556 B C P) : term287 A B C P p lt2 s h.
Proof. exact (fun a : P -> nat => @lem8225685 A B C P p lt2 s a h). Qed.
Lemma lem8225695 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) : term291 A B C P p lt2 s.
Proof. exact (fun h : type556 B C P => @lem8225690 A B C P p lt2 s h). Qed.
Lemma lem8225700 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) : term295 A B C P p lt2.
Proof. exact (fun s : P -> A => @lem8225695 A B C P p lt2 s). Qed.
Lemma lem8225705 {A B C P : Type'} (lt2 : type1470 A B) : term299 A B C P lt2.
Proof. exact (fun p : type560 B C P => @lem8225700 A B C P p lt2). Qed.
Lemma lem8225710 {A B C P : Type'} : term303 A B C P.
Proof. exact (fun lt2 : type1470 A B => @lem8225705 A B C P lt2). Qed.
Lemma lem8225711 {A B C P : Type'} : term302 A B C P.
Proof. exact (EQ_MP (@lem8221506 A B C P) (@lem8225710 A B C P)). Qed.
