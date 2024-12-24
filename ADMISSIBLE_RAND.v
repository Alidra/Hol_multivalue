Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_RAND_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm4211_spec.
Lemma lem8116285 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8116286 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8116287 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8116286 t1) (@lem8116285 t1)). Qed.
Lemma lem8116288 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8116287 t1 t2). Qed.
Lemma lem8116289 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8116290 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8116289 t1 t2) (@lem8116288 t1 t2)). Qed.
Lemma lem8116291 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8116290 t1 t2 t3). Qed.
Lemma lem8116292 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8116293 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8116292 t1 t2 t3) (@lem8116291 t1 t2 t3)). Qed.
Lemma lem8116294 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8116293 t1 t2 t3)). Qed.
Lemma lem8116295 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term7 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8116296 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term7 _143449 _143452 _143456 _143457 _143462 p) = (term8 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term7 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8116297 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term8 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8116296 _143449 _143452 _143456 _143457 _143462 p) (@lem8116295 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8116298 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term9 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8116297 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8116299 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term9 _143449 _143452 _143456 _143457 _143462 p lt2) = (term10 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term9 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8116300 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term10 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8116299 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8116298 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8116301 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term11 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8116300 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8116302 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term11 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term12 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term11 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8116303 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term12 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8116302 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8116301 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8116304 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8116303 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8116305 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8116330 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8116331 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem8116330 p q p' q'). Qed.
Lemma lem8116332 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem8116331 p q p'). Qed.
Lemma lem8116333 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : term18 A B C D P lt2 p s g y.
Proof. exact (@lem8116332 (@admissible A B A C P lt2 p s y) (term19 A B C D P lt2 p s g y)). Qed.
Lemma lem8116334 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) (p' : Prop) : term20 A B C D P lt2 p s g y p'.
Proof. exact (@lem8116333 A B C D P lt2 p s g y p'). Qed.
Lemma lem8116335 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) (p' : Prop) : (term20 A B C D P lt2 p s g y p') = (term21 A B C D P lt2 p s g y p').
Proof. exact (eq_refl (term20 A B C D P lt2 p s g y p')). Qed.
Lemma lem8116336 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) (p' : Prop) : term21 A B C D P lt2 p s g y p'.
Proof. exact (EQ_MP (@lem8116335 A B C D P lt2 p s g y p') (@lem8116334 A B C D P lt2 p s g y p')). Qed.
Lemma lem8116337 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) (p' : Prop) (q' : Prop) : term22 A B C D P lt2 p s g y p' q'.
Proof. exact (@lem8116336 A B C D P lt2 p s g y p' q'). Qed.
Lemma lem8116338 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) (p' : Prop) (q' : Prop) : (term22 A B C D P lt2 p s g y p' q') = (term23 A B C D P lt2 p s g y p' q').
Proof. exact (eq_refl (term22 A B C D P lt2 p s g y p' q')). Qed.
Lemma lem8116339 {A B C D P : Type'} (lt2 : type1402 A) (p : type560 A B P) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) (p' : Prop) (q' : Prop) : term23 A B C D P lt2 p s g y p' q'.
Proof. exact (EQ_MP (@lem8116338 A B C D P lt2 p s g y p' q') (@lem8116337 A B C D P lt2 p s g y p' q')). Qed.
Lemma lem8116341 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8116305 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8116304 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8116342 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type564 A B C P) : (@admissible A B A C P lt2 p s t) = (term24 A B C P p lt2 s t).
Proof. exact (@lem8116341 A B A C P p lt2 s t). Qed.
Lemma lem8116343 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (@admissible A B A C P lt2 p s y) = (term24 A B C P p lt2 s y).
Proof. exact (@lem8116342 A B C P p lt2 s y). Qed.
Lemma lem8116469 {A B C D P : Type'} (g : type1514 C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (q' : Prop) : term25 A B C D P g p lt2 s y q'.
Proof. exact (@lem8116339 A B C D P lt2 p s g y (term24 A B C P p lt2 s y) q'). Qed.
Lemma lem8116470 {A B C D P : Type'} (g : type1514 C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (q' : Prop) : term26 A B C D P g p lt2 s y q'.
Proof. exact (@lem8116469 A B C D P g p lt2 s y q' (@lem8116343 A B C P p lt2 s y)). Qed.
Lemma lem8116489 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8116305 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8116304 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8116490 {A B D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type564 A B D P) : (@admissible A B A D P lt2 p s t) = (term24 A B D P p lt2 s t).
Proof. exact (@lem8116489 A B A D P p lt2 s t). Qed.
Lemma lem8116491 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : (term19 A B C D P lt2 p s g y) = (term27 A B C D P p lt2 s g y).
Proof. exact (@lem8116490 A B D P p lt2 s (term28 A B C D P g y)). Qed.
Lemma lem8116507 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term15 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8116508 (p : Prop) (q : Prop) (p' : Prop) : term16 p q p'.
Proof. exact (fun q' : Prop => @lem8116507 p q p' q'). Qed.
Lemma lem8116509 (p : Prop) (q : Prop) : term17 p q.
Proof. exact (fun p' : Prop => @lem8116508 p q p'). Qed.
Lemma lem8116510 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : term29 A B C D P p lt2 s f g y g' a.
Proof. exact (@lem8116509 (term30 A B P p lt2 s a f g') ((term31 A B C D P g y f a) = (term31 A B C D P g y g' a))). Qed.
Lemma lem8116511 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) : term32 A B C D P p lt2 s f g y g' a p'.
Proof. exact (@lem8116510 A B C D P p lt2 s f g y g' a p'). Qed.
Lemma lem8116512 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) : (term32 A B C D P p lt2 s f g y g' a p') = (term33 A B C D P p lt2 s f g y g' a p').
Proof. exact (eq_refl (term32 A B C D P p lt2 s f g y g' a p')). Qed.
Lemma lem8116513 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) : term33 A B C D P p lt2 s f g y g' a p'.
Proof. exact (EQ_MP (@lem8116512 A B C D P p lt2 s f g y g' a p') (@lem8116511 A B C D P p lt2 s f g y g' a p')). Qed.
Lemma lem8116514 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) (q' : Prop) : term34 A B C D P p lt2 s f g y g' a p' q'.
Proof. exact (@lem8116513 A B C D P p lt2 s f g y g' a p' q'). Qed.
Lemma lem8116515 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) (q' : Prop) : (term34 A B C D P p lt2 s f g y g' a p' q') = (term35 A B C D P p lt2 s f g y g' a p' q').
Proof. exact (eq_refl (term34 A B C D P p lt2 s f g y g' a p' q')). Qed.
Lemma lem8116516 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (p' : Prop) (q' : Prop) : term35 A B C D P p lt2 s f g y g' a p' q'.
Proof. exact (EQ_MP (@lem8116515 A B C D P p lt2 s f g y g' a p' q') (@lem8116514 A B C D P p lt2 s f g y g' a p' q')). Qed.
Lemma lem8116552 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term30 A B P p lt2 s a f g) = (term30 A B P p lt2 s a f g).
Proof. exact (eq_refl (term30 A B P p lt2 s a f g)). Qed.
Lemma lem8116553 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (q' : Prop) : term36 A B C D P g y p lt2 s a f g' q'.
Proof. exact (@lem8116516 A B C D P p lt2 s f g y g' a (term30 A B P p lt2 s a f g') q'). Qed.
Lemma lem8116554 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (q' : Prop) : term37 A B C D P g y p lt2 s a f g' q'.
Proof. exact (@lem8116553 A B C D P g y p lt2 s a f g' q' (@lem8116552 A B P p lt2 s a f g')). Qed.
Lemma lem8116577 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8116578 {A B D P : Type'} (f : type564 A B D P) (y : A -> B) : (term39 A B D P f y) = (f y).
Proof. exact (@lem8116577 (A -> B) (P -> D) f y). Qed.
Lemma lem8116579 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : (term40 A B C D P g y f) = (term41 A B C D P g y f).
Proof. exact (@lem8116578 A B D P (term28 A B C D P g y) f). Qed.
Lemma lem8116580 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : (term41 A B C D P g y f) = (term42 A B C D P g y f).
Proof. exact (eq_refl (term41 A B C D P g y f)). Qed.
Lemma lem8116581 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) : (term43 A B C D P g y) = (term28 A B C D P g y).
Proof. exact (fun_ext (fun f : A -> B => @lem8116580 A B C D P g y f)). Qed.
Lemma lem8116582 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8116583 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : (term40 A B C D P g y f) = (term41 A B C D P g y f).
Proof. exact (MK_COMB (@lem8116581 A B C D P g y) (@lem8116582 A B f)). Qed.
Lemma lem8116584 {D P : Type'} : (@eq (P -> D)) = (@eq (P -> D)).
Proof. exact (eq_refl (@eq (P -> D))). Qed.
Lemma lem8116585 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : (term44 A B C D P g y f) = (term45 A B C D P g y f).
Proof. exact (MK_COMB (@lem8116584 D P) (@lem8116583 A B C D P g y f)). Qed.
Lemma lem8116586 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : (term41 A B C D P g y f) = (term42 A B C D P g y f).
Proof. exact (eq_refl (term41 A B C D P g y f)). Qed.
Lemma lem8116587 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : ((term40 A B C D P g y f) = (term41 A B C D P g y f)) = ((term41 A B C D P g y f) = (term42 A B C D P g y f)).
Proof. exact (MK_COMB (@lem8116585 A B C D P g y f) (@lem8116586 A B C D P g y f)). Qed.
Lemma lem8116588 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : (term41 A B C D P g y f) = (term42 A B C D P g y f).
Proof. exact (EQ_MP (@lem8116587 A B C D P g y f) (@lem8116579 A B C D P g y f)). Qed.
Lemma lem8116593 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8116594 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term31 A B C D P g y f a) = (term46 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8116588 A B C D P g y f) (@lem8116593 P a)). Qed.
Lemma lem8116596 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8116597 {D P : Type'} (f : P -> D) (y : P) : (term47 D P f y) = (f y).
Proof. exact (@lem8116596 P D f y). Qed.
Lemma lem8116598 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term48 A B C D P g y f a) = (term46 A B C D P g y f a).
Proof. exact (@lem8116597 D P (term42 A B C D P g y f) a). Qed.
Lemma lem8116599 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (x : P) : (term46 A B C D P g y f x) = (term49 A B C D P g y f x).
Proof. exact (eq_refl (term46 A B C D P g y f x)). Qed.
Lemma lem8116600 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : (term50 A B C D P g y f) = (term42 A B C D P g y f).
Proof. exact (fun_ext (fun x : P => @lem8116599 A B C D P g y f x)). Qed.
Lemma lem8116601 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8116602 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term48 A B C D P g y f a) = (term46 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8116600 A B C D P g y f) (@lem8116601 P a)). Qed.
Lemma lem8116603 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem8116604 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term51 A B C D P g y f a) = (term52 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8116603 D) (@lem8116602 A B C D P g y f a)). Qed.
Lemma lem8116605 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term46 A B C D P g y f a) = (term49 A B C D P g y f a).
Proof. exact (eq_refl (term46 A B C D P g y f a)). Qed.
Lemma lem8116606 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : ((term48 A B C D P g y f a) = (term46 A B C D P g y f a)) = ((term46 A B C D P g y f a) = (term49 A B C D P g y f a)).
Proof. exact (MK_COMB (@lem8116604 A B C D P g y f a) (@lem8116605 A B C D P g y f a)). Qed.
Lemma lem8116607 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term46 A B C D P g y f a) = (term49 A B C D P g y f a).
Proof. exact (EQ_MP (@lem8116606 A B C D P g y f a) (@lem8116598 A B C D P g y f a)). Qed.
Lemma lem8116611 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term31 A B C D P g y f a) = (term49 A B C D P g y f a).
Proof. exact (TRANS (@lem8116594 A B C D P g y f a) (@lem8116607 A B C D P g y f a)). Qed.
Lemma lem8116612 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem8116613 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term53 A B C D P g y f a) = (term54 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8116612 D) (@lem8116611 A B C D P g y f a)). Qed.
Lemma lem8116618 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8116619 {A B D P : Type'} (f : type564 A B D P) (y : A -> B) : (term39 A B D P f y) = (f y).
Proof. exact (@lem8116618 (A -> B) (P -> D) f y). Qed.
Lemma lem8116620 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term40 A B C D P g y g') = (term41 A B C D P g y g').
Proof. exact (@lem8116619 A B D P (term28 A B C D P g y) g'). Qed.
Lemma lem8116621 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) : (term41 A B C D P g y f) = (term42 A B C D P g y f).
Proof. exact (eq_refl (term41 A B C D P g y f)). Qed.
Lemma lem8116622 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) : (term43 A B C D P g y) = (term28 A B C D P g y).
Proof. exact (fun_ext (fun f : A -> B => @lem8116621 A B C D P g y f)). Qed.
Lemma lem8116623 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8116624 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term40 A B C D P g y g') = (term41 A B C D P g y g').
Proof. exact (MK_COMB (@lem8116622 A B C D P g y) (@lem8116623 A B g')). Qed.
Lemma lem8116625 {D P : Type'} : (@eq (P -> D)) = (@eq (P -> D)).
Proof. exact (eq_refl (@eq (P -> D))). Qed.
Lemma lem8116626 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term44 A B C D P g y g') = (term45 A B C D P g y g').
Proof. exact (MK_COMB (@lem8116625 D P) (@lem8116624 A B C D P g y g')). Qed.
Lemma lem8116627 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term41 A B C D P g y g') = (term42 A B C D P g y g').
Proof. exact (eq_refl (term41 A B C D P g y g')). Qed.
Lemma lem8116628 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : ((term40 A B C D P g y g') = (term41 A B C D P g y g')) = ((term41 A B C D P g y g') = (term42 A B C D P g y g')).
Proof. exact (MK_COMB (@lem8116626 A B C D P g y g') (@lem8116627 A B C D P g y g')). Qed.
Lemma lem8116629 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term41 A B C D P g y g') = (term42 A B C D P g y g').
Proof. exact (EQ_MP (@lem8116628 A B C D P g y g') (@lem8116620 A B C D P g y g')). Qed.
Lemma lem8116634 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8116635 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term31 A B C D P g y g' a) = (term46 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8116629 A B C D P g y g') (@lem8116634 P a)). Qed.
Lemma lem8116637 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8116638 {D P : Type'} (f : P -> D) (y : P) : (term47 D P f y) = (f y).
Proof. exact (@lem8116637 P D f y). Qed.
Lemma lem8116639 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term48 A B C D P g y g' a) = (term46 A B C D P g y g' a).
Proof. exact (@lem8116638 D P (term42 A B C D P g y g') a). Qed.
Lemma lem8116640 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (x : P) : (term46 A B C D P g y g' x) = (term49 A B C D P g y g' x).
Proof. exact (eq_refl (term46 A B C D P g y g' x)). Qed.
Lemma lem8116641 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term50 A B C D P g y g') = (term42 A B C D P g y g').
Proof. exact (fun_ext (fun x : P => @lem8116640 A B C D P g y g' x)). Qed.
Lemma lem8116642 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8116643 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term48 A B C D P g y g' a) = (term46 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8116641 A B C D P g y g') (@lem8116642 P a)). Qed.
Lemma lem8116644 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem8116645 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term51 A B C D P g y g' a) = (term52 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8116644 D) (@lem8116643 A B C D P g y g' a)). Qed.
Lemma lem8116646 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term46 A B C D P g y g' a) = (term49 A B C D P g y g' a).
Proof. exact (eq_refl (term46 A B C D P g y g' a)). Qed.
Lemma lem8116647 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term48 A B C D P g y g' a) = (term46 A B C D P g y g' a)) = ((term46 A B C D P g y g' a) = (term49 A B C D P g y g' a)).
Proof. exact (MK_COMB (@lem8116645 A B C D P g y g' a) (@lem8116646 A B C D P g y g' a)). Qed.
Lemma lem8116648 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term46 A B C D P g y g' a) = (term49 A B C D P g y g' a).
Proof. exact (EQ_MP (@lem8116647 A B C D P g y g' a) (@lem8116639 A B C D P g y g' a)). Qed.
Lemma lem8116653 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term31 A B C D P g y g' a) = (term49 A B C D P g y g' a).
Proof. exact (TRANS (@lem8116635 A B C D P g y g' a) (@lem8116648 A B C D P g y g' a)). Qed.
Lemma lem8116654 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term31 A B C D P g y f a) = (term31 A B C D P g y g' a)) = ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a)).
Proof. exact (MK_COMB (@lem8116613 A B C D P g y f a) (@lem8116653 A B C D P g y g' a)). Qed.
Lemma lem8116664 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : term55 A B C D P p lt2 s f g y g' a.
Proof. exact (fun h0 : term30 A B P p lt2 s a f g' => @lem8116654 A B C D P f g y g' a). Qed.
Lemma lem8116665 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : term56 A B C D P p lt2 s f g y g' a.
Proof. exact (@lem8116554 A B C D P g y p lt2 s a f g' ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a))). Qed.
Lemma lem8116666 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term57 A B C D P p lt2 s f g y g' a) = (term58 A B C D P p lt2 s f g y g' a).
Proof. exact (@lem8116665 A B C D P p lt2 s f g y g' a (@lem8116664 A B C D P p lt2 s f g y g' a)). Qed.
Lemma lem8116794 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term59 A B C D P p lt2 s f g y g') = (term60 A B C D P p lt2 s f g y g').
Proof. exact (fun_ext (fun a : P => @lem8116666 A B C D P p lt2 s f g y g' a)). Qed.
Lemma lem8116922 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8116923 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term61 A B C D P p lt2 s f g y g') = (term62 A B C D P p lt2 s f g y g').
Proof. exact (MK_COMB (@lem8116922 P) (@lem8116794 A B C D P p lt2 s f g y g')). Qed.
Lemma lem8117055 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) : (term63 A B C D P p lt2 s f g y) = (term64 A B C D P p lt2 s f g y).
Proof. exact (fun_ext (fun g' : A -> B => @lem8116923 A B C D P p lt2 s f g y g')). Qed.
Lemma lem8117187 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8117188 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) : (term65 A B C D P p lt2 s f g y) = (term66 A B C D P p lt2 s f g y).
Proof. exact (MK_COMB (@lem8117187 A B) (@lem8117055 A B C D P p lt2 s f g y)). Qed.
Lemma lem8117324 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : (term67 A B C D P p lt2 s g y) = (term68 A B C D P p lt2 s g y).
Proof. exact (fun_ext (fun f : A -> B => @lem8117188 A B C D P p lt2 s f g y)). Qed.
Lemma lem8117460 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8117461 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : (term27 A B C D P p lt2 s g y) = (term69 A B C D P p lt2 s g y).
Proof. exact (MK_COMB (@lem8117460 A B) (@lem8117324 A B C D P p lt2 s g y)). Qed.
Lemma lem8117601 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : (term19 A B C D P lt2 p s g y) = (term69 A B C D P p lt2 s g y).
Proof. exact (TRANS (@lem8116491 A B C D P p lt2 s g y) (@lem8117461 A B C D P p lt2 s g y)). Qed.
Lemma lem8117602 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : term70 A B C D P p lt2 s g y.
Proof. exact (fun h0 : term24 A B C P p lt2 s y => @lem8117601 A B C D P p lt2 s g y). Qed.
Lemma lem8117603 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : term71 A B C D P p lt2 s g y.
Proof. exact (@lem8116470 A B C D P g p lt2 s y (term69 A B C D P p lt2 s g y)). Qed.
Lemma lem8117604 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : (term72 A B C D P lt2 p s g y) = (term73 A B C D P p lt2 s g y).
Proof. exact (@lem8117603 A B C D P p lt2 s g y (@lem8117602 A B C D P p lt2 s g y)). Qed.
Lemma lem8118156 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) : (term74 A B C D P lt2 p s g) = (term75 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun y : type564 A B C P => @lem8117604 A B C D P p lt2 s g y)). Qed.
Lemma lem8118708 {A B C P : Type'} : (@all ((A -> B) -> P -> C)) = (@all ((A -> B) -> P -> C)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> C))). Qed.
Lemma lem8118709 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) : (term76 A B C D P lt2 p s g) = (term77 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8118708 A B C P) (@lem8118156 A B C D P p lt2 s g)). Qed.
Lemma lem8119265 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term78 A B C D P lt2 p s) = (term79 A B C D P p lt2 s).
Proof. exact (fun_ext (fun g : type1514 C D P => @lem8118709 A B C D P p lt2 s g)). Qed.
Lemma lem8119821 {C D P : Type'} : (@all (P -> C -> D)) = (@all (P -> C -> D)).
Proof. exact (eq_refl (@all (P -> C -> D))). Qed.
Lemma lem8119822 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term80 A B C D P lt2 p s) = (term81 A B C D P p lt2 s).
Proof. exact (MK_COMB (@lem8119821 C D P) (@lem8119265 A B C D P p lt2 s)). Qed.
Lemma lem8120382 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term82 A B C D P lt2 p) = (term83 A B C D P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8119822 A B C D P p lt2 s)). Qed.
Lemma lem8120942 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8120943 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term84 A B C D P lt2 p) = (term85 A B C D P p lt2).
Proof. exact (MK_COMB (@lem8120942 A P) (@lem8120382 A B C D P p lt2)). Qed.
Lemma lem8121507 {A B C D P : Type'} (lt2 : type1402 A) : (term86 A B C D P lt2) = (term87 A B C D P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8120943 A B C D P p lt2)). Qed.
Lemma lem8122071 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8122072 {A B C D P : Type'} (lt2 : type1402 A) : (term88 A B C D P lt2) = (term89 A B C D P lt2).
Proof. exact (MK_COMB (@lem8122071 A B P) (@lem8121507 A B C D P lt2)). Qed.
Lemma lem8122640 {A B C D P : Type'} : (term90 A B C D P) = (term91 A B C D P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8122072 A B C D P lt2)). Qed.
Lemma lem8123208 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8123209 {A B C D P : Type'} : (term92 A B C D P) = (term93 A B C D P).
Proof. exact (MK_COMB (@lem8123208 A) (@lem8122640 A B C D P)). Qed.
Lemma lem8123781 {A B C D P : Type'} : (term93 A B C D P) = (term92 A B C D P).
Proof. exact (SYM (@lem8123209 A B C D P)). Qed.
Lemma lem8123783 (p : Prop) : p = (term94 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8123784 {A B C D P : Type'} : (term93 A B C D P) = (term95 A B C D P).
Proof. exact (@lem8123783 (term93 A B C D P)). Qed.
Lemma lem8123785 {A B C D P : Type'} : (term95 A B C D P) = (term93 A B C D P).
Proof. exact (SYM (@lem8123784 A B C D P)). Qed.
Lemma lem8123786 {A B C D P : Type'} (h1 : term96 A B C D P) : term96 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8123789 {A B C D P : Type'} (h1 : term95 A B C D P) : term95 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8123790 {A B C D P : Type'} : term97 A B C D P.
Proof. exact (fun h0 : term95 A B C D P => @lem8123789 A B C D P h0). Qed.
Lemma lem8123791 {A B C D P : Type'} (h1 : term97 A B C D P) : term97 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8123792 {A B C D P : Type'} (h1 : term95 A B C D P) : term95 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8123793 {A B C D P : Type'} (h1 : term95 A B C D P) (h2 : term97 A B C D P) : term95 A B C D P.
Proof. exact (@lem8123791 A B C D P h2 (@lem8123792 A B C D P h1)). Qed.
Lemma lem8123794 {A B C D P : Type'} (h1 : term95 A B C D P) : term98 A B C D P.
Proof. exact (fun h0 : term97 A B C D P => @lem8123793 A B C D P h1 h0). Qed.
Lemma lem8123795 {A B C D P : Type'} (h1 : term97 A B C D P) : term97 A B C D P.
Proof. exact (h1). Qed.
Lemma lem8123796 {A B C D P : Type'} (h1 : term95 A B C D P) (h2 : term97 A B C D P) : term95 A B C D P.
Proof. exact (@lem8123794 A B C D P h1 (@lem8123795 A B C D P h2)). Qed.
Lemma lem8123797 {A B C D P : Type'} (h1 : term97 A B C D P) : term97 A B C D P.
Proof. exact (fun h0 : term95 A B C D P => @lem8123796 A B C D P h0 h1). Qed.
Lemma lem8123798 {A B C D P : Type'} : term99 A B C D P.
Proof. exact (fun h0 : term97 A B C D P => @lem8123797 A B C D P h0). Qed.
Lemma lem8123801 {A B C D P : Type'} : term97 A B C D P.
Proof. exact (@lem8123798 A B C D P (@lem8123790 A B C D P)). Qed.
Lemma lem8123802 {A B C D P : Type'} : term97 A B C D P.
Proof. exact (@lem8123801 A B C D P). Qed.
Lemma lem8123804 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8123805 {A B C D P : Type'} : (term95 A B C D P) = (term100 A B C D P).
Proof. exact (@lem8123804 (term96 A B C D P)). Qed.
Lemma lem8123807 (t : Prop) : (term101 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8123808 {A B C D P : Type'} : (term100 A B C D P) = (term93 A B C D P).
Proof. exact (@lem8123807 (term93 A B C D P)). Qed.
Lemma lem8123883 {A B C D P : Type'} : (term95 A B C D P) = (term93 A B C D P).
Proof. exact (TRANS (@lem8123805 A B C D P) (@lem8123808 A B C D P)). Qed.
Lemma lem8123884 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a)) = ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a)).
Proof. exact (eq_refl ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a))). Qed.
Lemma lem8123889 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term102 A B P lt2 s a f g z) = (term102 A B P lt2 s a f g z).
Proof. exact (eq_refl (term102 A B P lt2 s a f g z)). Qed.
Lemma lem8123890 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term103 A B P lt2 s a f g) = (term103 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8123889 A B P lt2 s a f g z)). Qed.
Lemma lem8123891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8123892 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term104 A B P lt2 s a f g) = (term104 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8123891 A) (@lem8123890 A B P lt2 s a f g)). Qed.
Lemma lem8123895 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term105 A B P p g a) = (term105 A B P p g a).
Proof. exact (eq_refl (term105 A B P p g a)). Qed.
Lemma lem8123896 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term106 A B P p lt2 s a f g) = (term106 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8123895 A B P p g a) (@lem8123892 A B P lt2 s a f g)). Qed.
Lemma lem8123899 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term105 A B P p f a) = (term105 A B P p f a).
Proof. exact (eq_refl (term105 A B P p f a)). Qed.
Lemma lem8123900 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term30 A B P p lt2 s a f g) = (term30 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8123899 A B P p f a) (@lem8123896 A B P p lt2 s a f g)). Qed.
Lemma lem8123901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8123902 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term107 A B P p lt2 s a f g) = (term107 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8123901) (@lem8123900 A B P p lt2 s a f g)). Qed.
Lemma lem8123903 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term58 A B C D P p lt2 s f g y g' a) = (term58 A B C D P p lt2 s f g y g' a).
Proof. exact (MK_COMB (@lem8123902 A B P p lt2 s a f g') (@lem8123884 A B C D P f g y g' a)). Qed.
Lemma lem8123904 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term60 A B C D P p lt2 s f g y g') = (term60 A B C D P p lt2 s f g y g').
Proof. exact (fun_ext (fun a : P => @lem8123903 A B C D P p lt2 s f g y g' a)). Qed.
Lemma lem8123905 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8123906 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) : (term62 A B C D P p lt2 s f g y g') = (term62 A B C D P p lt2 s f g y g').
Proof. exact (MK_COMB (@lem8123905 P) (@lem8123904 A B C D P p lt2 s f g y g')). Qed.
Lemma lem8123907 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) : (term64 A B C D P p lt2 s f g y) = (term64 A B C D P p lt2 s f g y).
Proof. exact (fun_ext (fun g' : A -> B => @lem8123906 A B C D P p lt2 s f g y g')). Qed.
Lemma lem8123908 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8123909 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) : (term66 A B C D P p lt2 s f g y) = (term66 A B C D P p lt2 s f g y).
Proof. exact (MK_COMB (@lem8123908 A B) (@lem8123907 A B C D P p lt2 s f g y)). Qed.
Lemma lem8123910 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : (term68 A B C D P p lt2 s g y) = (term68 A B C D P p lt2 s g y).
Proof. exact (fun_ext (fun f : A -> B => @lem8123909 A B C D P p lt2 s f g y)). Qed.
Lemma lem8123911 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8123912 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : (term69 A B C D P p lt2 s g y) = (term69 A B C D P p lt2 s g y).
Proof. exact (MK_COMB (@lem8123911 A B) (@lem8123910 A B C D P p lt2 s g y)). Qed.
Lemma lem8123913 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8123918 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term102 A B P lt2 s a f g z) = (term102 A B P lt2 s a f g z).
Proof. exact (eq_refl (term102 A B P lt2 s a f g z)). Qed.
Lemma lem8123919 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term103 A B P lt2 s a f g) = (term103 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8123918 A B P lt2 s a f g z)). Qed.
Lemma lem8123920 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8123921 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term104 A B P lt2 s a f g) = (term104 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8123920 A) (@lem8123919 A B P lt2 s a f g)). Qed.
Lemma lem8123924 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term105 A B P p g a) = (term105 A B P p g a).
Proof. exact (eq_refl (term105 A B P p g a)). Qed.
Lemma lem8123925 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term106 A B P p lt2 s a f g) = (term106 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8123924 A B P p g a) (@lem8123921 A B P lt2 s a f g)). Qed.
Lemma lem8123928 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term105 A B P p f a) = (term105 A B P p f a).
Proof. exact (eq_refl (term105 A B P p f a)). Qed.
Lemma lem8123929 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term30 A B P p lt2 s a f g) = (term30 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8123928 A B P p f a) (@lem8123925 A B P p lt2 s a f g)). Qed.
Lemma lem8123930 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8123931 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term107 A B P p lt2 s a f g) = (term107 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8123930) (@lem8123929 A B P p lt2 s a f g)). Qed.
Lemma lem8123932 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term108 A B C P p lt2 s f y g a) = (term108 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8123931 A B P p lt2 s a f g) (@lem8123913 A B C P f y g a)). Qed.
Lemma lem8123933 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term109 A B C P p lt2 s f y g) = (term109 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun a : P => @lem8123932 A B C P p lt2 s f y g a)). Qed.
Lemma lem8123934 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8123935 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term110 A B C P p lt2 s f y g) = (term110 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8123934 P) (@lem8123933 A B C P p lt2 s f y g)). Qed.
Lemma lem8123936 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term111 A B C P p lt2 s f y) = (term111 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8123935 A B C P p lt2 s f y g)). Qed.
Lemma lem8123937 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8123938 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term112 A B C P p lt2 s f y) = (term112 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8123937 A B) (@lem8123936 A B C P p lt2 s f y)). Qed.
Lemma lem8123939 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term113 A B C P p lt2 s y) = (term113 A B C P p lt2 s y).
Proof. exact (fun_ext (fun f : A -> B => @lem8123938 A B C P p lt2 s f y)). Qed.
Lemma lem8123940 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8123941 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term24 A B C P p lt2 s y) = (term24 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8123940 A B) (@lem8123939 A B C P p lt2 s y)). Qed.
Lemma lem8123942 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8123943 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term114 A B C P p lt2 s y) = (term114 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8123942) (@lem8123941 A B C P p lt2 s y)). Qed.
Lemma lem8123944 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : (term73 A B C D P p lt2 s g y) = (term73 A B C D P p lt2 s g y).
Proof. exact (MK_COMB (@lem8123943 A B C P p lt2 s y) (@lem8123912 A B C D P p lt2 s g y)). Qed.
Lemma lem8123945 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) : (term75 A B C D P p lt2 s g) = (term75 A B C D P p lt2 s g).
Proof. exact (fun_ext (fun y : type564 A B C P => @lem8123944 A B C D P p lt2 s g y)). Qed.
Lemma lem8123946 {A B C P : Type'} : (@all ((A -> B) -> P -> C)) = (@all ((A -> B) -> P -> C)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> C))). Qed.
Lemma lem8123947 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) : (term77 A B C D P p lt2 s g) = (term77 A B C D P p lt2 s g).
Proof. exact (MK_COMB (@lem8123946 A B C P) (@lem8123945 A B C D P p lt2 s g)). Qed.
Lemma lem8123948 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term79 A B C D P p lt2 s) = (term79 A B C D P p lt2 s).
Proof. exact (fun_ext (fun g : type1514 C D P => @lem8123947 A B C D P p lt2 s g)). Qed.
Lemma lem8123949 {C D P : Type'} : (@all (P -> C -> D)) = (@all (P -> C -> D)).
Proof. exact (eq_refl (@all (P -> C -> D))). Qed.
Lemma lem8123950 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term81 A B C D P p lt2 s) = (term81 A B C D P p lt2 s).
Proof. exact (MK_COMB (@lem8123949 C D P) (@lem8123948 A B C D P p lt2 s)). Qed.
Lemma lem8123951 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term83 A B C D P p lt2) = (term83 A B C D P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8123950 A B C D P p lt2 s)). Qed.
Lemma lem8123952 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8123953 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term85 A B C D P p lt2) = (term85 A B C D P p lt2).
Proof. exact (MK_COMB (@lem8123952 A P) (@lem8123951 A B C D P p lt2)). Qed.
Lemma lem8123954 {A B C D P : Type'} (lt2 : type1402 A) : (term87 A B C D P lt2) = (term87 A B C D P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8123953 A B C D P p lt2)). Qed.
Lemma lem8123955 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8123956 {A B C D P : Type'} (lt2 : type1402 A) : (term89 A B C D P lt2) = (term89 A B C D P lt2).
Proof. exact (MK_COMB (@lem8123955 A B P) (@lem8123954 A B C D P lt2)). Qed.
Lemma lem8123957 {A B C D P : Type'} : (term91 A B C D P) = (term91 A B C D P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8123956 A B C D P lt2)). Qed.
Lemma lem8123958 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8123959 {A B C D P : Type'} : (term93 A B C D P) = (term93 A B C D P).
Proof. exact (MK_COMB (@lem8123958 A) (@lem8123957 A B C D P)). Qed.
Lemma lem8124058 {A B C D P : Type'} : (term95 A B C D P) = (term93 A B C D P).
Proof. exact (TRANS (@lem8123883 A B C D P) (@lem8123959 A B C D P)). Qed.
Lemma lem8124059 {A B C D P : Type'} : (term93 A B C D P) = (term95 A B C D P).
Proof. exact (SYM (@lem8124058 A B C D P)). Qed.
Lemma lem8124060 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term24 A B C P p lt2 s y) : term24 A B C P p lt2 s y.
Proof. exact (h1). Qed.
Lemma lem8124061 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term30 A B P p lt2 s a f g'.
Proof. exact (h1). Qed.
Lemma lem8124063 (p : Prop) : p = (term94 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8124064 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a)) = (term115 A B C D P f g y g' a).
Proof. exact (@lem8124063 ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a))). Qed.
Lemma lem8124065 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term115 A B C D P f g y g' a) = ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a)).
Proof. exact (SYM (@lem8124064 A B C D P f g y g' a)). Qed.
Lemma lem8124066 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term116 A B C D P f g y g' a) : term116 A B C D P f g y g' a.
Proof. exact (h1). Qed.
Lemma lem8124075 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term117 A B P lt2 s a f g z) = (term118 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term119 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8124076 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8124077 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term122 A B P lt2 s a f g) = (term123 A B P lt2 s a f g).
Proof. exact (@lem8124076 A (term103 A B P lt2 s a f g)). Qed.
Lemma lem8124078 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term124 A B P lt2 s a f g z) = (term102 A B P lt2 s a f g z).
Proof. exact (eq_refl (term124 A B P lt2 s a f g z)). Qed.
Lemma lem8124079 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8124080 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term125 A B P lt2 s a f g z) = (term117 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8124079) (@lem8124078 A B P lt2 s a f g z)). Qed.
Lemma lem8124081 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term125 A B P lt2 s a f g z) = (term118 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8124080 A B P lt2 s a f g z) (@lem8124075 A B P lt2 s a f g z)). Qed.
Lemma lem8124082 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term126 A B P lt2 s a f g) = (term127 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8124081 A B P lt2 s a f g z)). Qed.
Lemma lem8124083 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8124084 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term123 A B P lt2 s a f g) = (term128 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8124083 A) (@lem8124082 A B P lt2 s a f g)). Qed.
Lemma lem8124085 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term122 A B P lt2 s a f g) = (term128 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8124077 A B P lt2 s a f g) (@lem8124084 A B P lt2 s a f g)). Qed.
Lemma lem8124087 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term129 A B P p g a) = (term129 A B P p g a).
Proof. exact (eq_refl (term129 A B P p g a)). Qed.
Lemma lem8124088 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term130 A B P p lt2 s a f g) = (term131 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124087 A B P p g a) (@lem8124085 A B P lt2 s a f g)). Qed.
Lemma lem8124089 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term132 A B P p lt2 s a f g) = (term130 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p g a) (term104 A B P lt2 s a f g)). Qed.
Lemma lem8124090 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term132 A B P p lt2 s a f g) = (term131 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8124089 A B P p lt2 s a f g) (@lem8124088 A B P p lt2 s a f g)). Qed.
Lemma lem8124092 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term129 A B P p f a) = (term129 A B P p f a).
Proof. exact (eq_refl (term129 A B P p f a)). Qed.
Lemma lem8124093 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term133 A B P p lt2 s a f g) = (term134 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124092 A B P p f a) (@lem8124090 A B P p lt2 s a f g)). Qed.
Lemma lem8124094 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term135 A B P p lt2 s a f g) = (term133 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p f a) (term106 A B P p lt2 s a f g)). Qed.
Lemma lem8124095 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term135 A B P p lt2 s a f g) = (term134 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8124094 A B P p lt2 s a f g) (@lem8124093 A B P p lt2 s a f g)). Qed.
Lemma lem8124096 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8124097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124098 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term136 A B P p lt2 s a f g) = (term137 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124097) (@lem8124095 A B P p lt2 s a f g)). Qed.
Lemma lem8124099 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term138 A B C P p lt2 s f y g a) = (term139 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8124098 A B P p lt2 s a f g) (@lem8124096 A B C P f y g a)). Qed.
Lemma lem8124100 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term108 A B C P p lt2 s f y g a) = (term138 A B C P p lt2 s f y g a).
Proof. exact (@lem17265 (term30 A B P p lt2 s a f g) ((y f a) = (y g a))). Qed.
Lemma lem8124101 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term108 A B C P p lt2 s f y g a) = (term139 A B C P p lt2 s f y g a).
Proof. exact (TRANS (@lem8124100 A B C P p lt2 s f y g a) (@lem8124099 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124102 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term109 A B C P p lt2 s f y g) = (term140 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun a : P => @lem8124101 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124103 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8124104 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term110 A B C P p lt2 s f y g) = (term141 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8124103 P) (@lem8124102 A B C P p lt2 s f y g)). Qed.
Lemma lem8124105 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term111 A B C P p lt2 s f y) = (term142 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8124104 A B C P p lt2 s f y g)). Qed.
Lemma lem8124106 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124107 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term112 A B C P p lt2 s f y) = (term143 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8124106 A B) (@lem8124105 A B C P p lt2 s f y)). Qed.
Lemma lem8124108 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term113 A B C P p lt2 s y) = (term144 A B C P p lt2 s y).
Proof. exact (fun_ext (fun f : A -> B => @lem8124107 A B C P p lt2 s f y)). Qed.
Lemma lem8124109 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124110 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term24 A B C P p lt2 s y) = (term145 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8124109 A B) (@lem8124108 A B C P p lt2 s y)). Qed.
Lemma lem8124217 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8124218 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (@lem8124217 A P Q). Qed.
Lemma lem8124219 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term148 A B P p lt2 s a f g) = (term149 A B P p lt2 s a f g).
Proof. exact (@lem8124218 A (term150 A B P p g a) (term127 A B P lt2 s a f g)). Qed.
Lemma lem8124220 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term151 A B P lt2 s a f g z) = (term118 A B P lt2 s a f g z).
Proof. exact (eq_refl (term151 A B P lt2 s a f g z)). Qed.
Lemma lem8124221 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term152 A B P lt2 s a f g) = (term127 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8124220 A B P lt2 s a f g z)). Qed.
Lemma lem8124222 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8124223 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term153 A B P lt2 s a f g) = (term128 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8124222 A) (@lem8124221 A B P lt2 s a f g)). Qed.
Lemma lem8124224 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term129 A B P p g a) = (term129 A B P p g a).
Proof. exact (eq_refl (term129 A B P p g a)). Qed.
Lemma lem8124225 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term148 A B P p lt2 s a f g) = (term131 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124224 A B P p g a) (@lem8124223 A B P lt2 s a f g)). Qed.
Lemma lem8124226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8124227 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term154 A B P p lt2 s a f g) = (term155 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124226) (@lem8124225 A B P p lt2 s a f g)). Qed.
Lemma lem8124228 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term151 A B P lt2 s a f g z) = (term118 A B P lt2 s a f g z).
Proof. exact (eq_refl (term151 A B P lt2 s a f g z)). Qed.
Lemma lem8124229 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term129 A B P p g a) = (term129 A B P p g a).
Proof. exact (eq_refl (term129 A B P p g a)). Qed.
Lemma lem8124230 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term156 A B P p lt2 s a f g z) = (term157 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8124229 A B P p g a) (@lem8124228 A B P lt2 s a f g z)). Qed.
Lemma lem8124231 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term158 A B P p lt2 s a f g) = (term159 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8124230 A B P p lt2 s a f g z)). Qed.
Lemma lem8124232 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8124233 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term149 A B P p lt2 s a f g) = (term160 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124232 A) (@lem8124231 A B P p lt2 s a f g)). Qed.
Lemma lem8124234 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term148 A B P p lt2 s a f g) = (term149 A B P p lt2 s a f g)) = ((term131 A B P p lt2 s a f g) = (term160 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8124227 A B P p lt2 s a f g) (@lem8124233 A B P p lt2 s a f g)). Qed.
Lemma lem8124235 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term131 A B P p lt2 s a f g) = (term160 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8124234 A B P p lt2 s a f g) (@lem8124219 A B P p lt2 s a f g)). Qed.
Lemma lem8124236 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term129 A B P p f a) = (term129 A B P p f a).
Proof. exact (eq_refl (term129 A B P p f a)). Qed.
Lemma lem8124237 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term134 A B P p lt2 s a f g) = (term161 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124236 A B P p f a) (@lem8124235 A B P p lt2 s a f g)). Qed.
Lemma lem8124239 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8124240 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (@lem8124239 A P Q). Qed.
Lemma lem8124241 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term162 A B P p lt2 s a f g) = (term163 A B P p lt2 s a f g).
Proof. exact (@lem8124240 A (term150 A B P p f a) (term159 A B P p lt2 s a f g)). Qed.
Lemma lem8124242 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term164 A B P p lt2 s a f g z) = (term157 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term164 A B P p lt2 s a f g z)). Qed.
Lemma lem8124243 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term165 A B P p lt2 s a f g) = (term159 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8124242 A B P p lt2 s a f g z)). Qed.
Lemma lem8124244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8124245 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term166 A B P p lt2 s a f g) = (term160 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124244 A) (@lem8124243 A B P p lt2 s a f g)). Qed.
Lemma lem8124246 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term129 A B P p f a) = (term129 A B P p f a).
Proof. exact (eq_refl (term129 A B P p f a)). Qed.
Lemma lem8124247 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term162 A B P p lt2 s a f g) = (term161 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124246 A B P p f a) (@lem8124245 A B P p lt2 s a f g)). Qed.
Lemma lem8124248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8124249 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term167 A B P p lt2 s a f g) = (term168 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124248) (@lem8124247 A B P p lt2 s a f g)). Qed.
Lemma lem8124250 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term164 A B P p lt2 s a f g z) = (term157 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term164 A B P p lt2 s a f g z)). Qed.
Lemma lem8124251 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term129 A B P p f a) = (term129 A B P p f a).
Proof. exact (eq_refl (term129 A B P p f a)). Qed.
Lemma lem8124252 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term169 A B P p lt2 s a f g z) = (term170 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8124251 A B P p f a) (@lem8124250 A B P p lt2 s a f g z)). Qed.
Lemma lem8124253 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term171 A B P p lt2 s a f g) = (term172 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8124252 A B P p lt2 s a f g z)). Qed.
Lemma lem8124254 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8124255 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term163 A B P p lt2 s a f g) = (term173 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124254 A) (@lem8124253 A B P p lt2 s a f g)). Qed.
Lemma lem8124256 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term162 A B P p lt2 s a f g) = (term163 A B P p lt2 s a f g)) = ((term161 A B P p lt2 s a f g) = (term173 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8124249 A B P p lt2 s a f g) (@lem8124255 A B P p lt2 s a f g)). Qed.
Lemma lem8124257 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term161 A B P p lt2 s a f g) = (term173 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8124256 A B P p lt2 s a f g) (@lem8124241 A B P p lt2 s a f g)). Qed.
Lemma lem8124258 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term134 A B P p lt2 s a f g) = (term173 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8124237 A B P p lt2 s a f g) (@lem8124257 A B P p lt2 s a f g)). Qed.
Lemma lem8124259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124260 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term137 A B P p lt2 s a f g) = (term174 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124259) (@lem8124258 A B P p lt2 s a f g)). Qed.
Lemma lem8124261 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8124262 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term139 A B C P p lt2 s f y g a) = (term175 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8124260 A B P p lt2 s a f g) (@lem8124261 A B C P f y g a)). Qed.
Lemma lem8124264 {A : Type'} (P : A -> Prop) (Q : Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8124265 {A : Type'} (P : A -> Prop) (Q : Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (@lem8124264 A P Q). Qed.
Lemma lem8124266 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term178 A B C P p lt2 s f y g a) = (term179 A B C P p lt2 s f y g a).
Proof. exact (@lem8124265 A (term172 A B P p lt2 s a f g) ((y f a) = (y g a))). Qed.
Lemma lem8124267 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term180 A B P p lt2 s a f g z) = (term170 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term180 A B P p lt2 s a f g z)). Qed.
Lemma lem8124268 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term181 A B P p lt2 s a f g) = (term172 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8124267 A B P p lt2 s a f g z)). Qed.
Lemma lem8124269 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8124270 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term182 A B P p lt2 s a f g) = (term173 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124269 A) (@lem8124268 A B P p lt2 s a f g)). Qed.
Lemma lem8124271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124272 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term183 A B P p lt2 s a f g) = (term174 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8124271) (@lem8124270 A B P p lt2 s a f g)). Qed.
Lemma lem8124273 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8124274 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term178 A B C P p lt2 s f y g a) = (term175 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8124272 A B P p lt2 s a f g) (@lem8124273 A B C P f y g a)). Qed.
Lemma lem8124275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8124276 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term184 A B C P p lt2 s f y g a) = (term185 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8124275) (@lem8124274 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124277 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term180 A B P p lt2 s a f g z) = (term170 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term180 A B P p lt2 s a f g z)). Qed.
Lemma lem8124278 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124279 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term186 A B P p lt2 s a f g z) = (term187 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8124278) (@lem8124277 A B P p lt2 s a f g z)). Qed.
Lemma lem8124280 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((y f a) = (y g a)).
Proof. exact (eq_refl ((y f a) = (y g a))). Qed.
Lemma lem8124281 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term188 A B C P p lt2 s z f y g a) = (term189 A B C P p lt2 s z f y g a).
Proof. exact (MK_COMB (@lem8124279 A B P p lt2 s a f g z) (@lem8124280 A B C P f y g a)). Qed.
Lemma lem8124282 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term190 A B C P p lt2 s f y g a) = (term191 A B C P p lt2 s f y g a).
Proof. exact (fun_ext (fun z : A => @lem8124281 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8124283 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8124284 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term179 A B C P p lt2 s f y g a) = (term192 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8124283 A) (@lem8124282 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124285 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((term178 A B C P p lt2 s f y g a) = (term179 A B C P p lt2 s f y g a)) = ((term175 A B C P p lt2 s f y g a) = (term192 A B C P p lt2 s f y g a)).
Proof. exact (MK_COMB (@lem8124276 A B C P p lt2 s f y g a) (@lem8124284 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124286 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term175 A B C P p lt2 s f y g a) = (term192 A B C P p lt2 s f y g a).
Proof. exact (EQ_MP (@lem8124285 A B C P p lt2 s f y g a) (@lem8124266 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124287 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term139 A B C P p lt2 s f y g a) = (term192 A B C P p lt2 s f y g a).
Proof. exact (TRANS (@lem8124262 A B C P p lt2 s f y g a) (@lem8124286 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124288 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term140 A B C P p lt2 s f y g) = (term193 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun a : P => @lem8124287 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124289 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8124290 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term141 A B C P p lt2 s f y g) = (term194 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8124289 P) (@lem8124288 A B C P p lt2 s f y g)). Qed.
Lemma lem8124292 {A B : Type'} (P : type1413 A B) : (term195 A B P) = (term196 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8124293 {A P : Type'} (P' : type1470 A P) : (term197 A P P') = (term198 A P P').
Proof. exact (@lem8124292 P A P'). Qed.
Lemma lem8124294 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term199 A B C P p lt2 s f y g) = (term200 A B C P p lt2 s f y g).
Proof. exact (@lem8124293 A P (term201 A B C P p lt2 s f y g)). Qed.
Lemma lem8124295 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term202 A B C P p lt2 s f y g a) = (term191 A B C P p lt2 s f y g a).
Proof. exact (eq_refl (term202 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124296 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8124297 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) (z : A) : (term203 A B C P p lt2 s f y g a z) = (term204 A B C P p lt2 s f y g a z).
Proof. exact (MK_COMB (@lem8124295 A B C P p lt2 s f y g a) (@lem8124296 A z)). Qed.
Lemma lem8124298 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term204 A B C P p lt2 s f y g a z) = (term189 A B C P p lt2 s z f y g a).
Proof. exact (eq_refl (term204 A B C P p lt2 s f y g a z)). Qed.
Lemma lem8124299 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term203 A B C P p lt2 s f y g a z) = (term189 A B C P p lt2 s z f y g a).
Proof. exact (TRANS (@lem8124297 A B C P p lt2 s f y g a z) (@lem8124298 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8124300 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term205 A B C P p lt2 s f y g a) = (term191 A B C P p lt2 s f y g a).
Proof. exact (fun_ext (fun z : A => @lem8124299 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8124301 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8124302 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term206 A B C P p lt2 s f y g a) = (term192 A B C P p lt2 s f y g a).
Proof. exact (MK_COMB (@lem8124301 A) (@lem8124300 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124303 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term207 A B C P p lt2 s f y g) = (term193 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun a : P => @lem8124302 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124304 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8124305 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term199 A B C P p lt2 s f y g) = (term194 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8124304 P) (@lem8124303 A B C P p lt2 s f y g)). Qed.
Lemma lem8124306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8124307 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term208 A B C P p lt2 s f y g) = (term209 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8124306) (@lem8124305 A B C P p lt2 s f y g)). Qed.
Lemma lem8124308 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term202 A B C P p lt2 s f y g a) = (term191 A B C P p lt2 s f y g a).
Proof. exact (eq_refl (term202 A B C P p lt2 s f y g a)). Qed.
Lemma lem8124309 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8124310 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (z : P -> A) (a : P) : (term210 A B C P p lt2 s f y g z a) = (term211 A B C P p lt2 s f y g z a).
Proof. exact (MK_COMB (@lem8124308 A B C P p lt2 s f y g a) (@lem8124309 A P z a)). Qed.
Lemma lem8124311 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term211 A B C P p lt2 s f y g z a) = (term212 A B C P p lt2 s z f y g a).
Proof. exact (eq_refl (term211 A B C P p lt2 s f y g z a)). Qed.
Lemma lem8124312 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term210 A B C P p lt2 s f y g z a) = (term212 A B C P p lt2 s z f y g a).
Proof. exact (TRANS (@lem8124310 A B C P p lt2 s f y g z a) (@lem8124311 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8124313 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term213 A B C P p lt2 s f y g z) = (term214 A B C P p lt2 s z f y g).
Proof. exact (fun_ext (fun a : P => @lem8124312 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8124314 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8124315 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term215 A B C P p lt2 s f y g z) = (term216 A B C P p lt2 s z f y g).
Proof. exact (MK_COMB (@lem8124314 P) (@lem8124313 A B C P p lt2 s z f y g)). Qed.
Lemma lem8124316 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term217 A B C P p lt2 s f y g) = (term218 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun z : P -> A => @lem8124315 A B C P p lt2 s z f y g)). Qed.
Lemma lem8124317 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8124318 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term200 A B C P p lt2 s f y g) = (term219 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8124317 A P) (@lem8124316 A B C P p lt2 s f y g)). Qed.
Lemma lem8124319 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : ((term199 A B C P p lt2 s f y g) = (term200 A B C P p lt2 s f y g)) = ((term194 A B C P p lt2 s f y g) = (term219 A B C P p lt2 s f y g)).
Proof. exact (MK_COMB (@lem8124307 A B C P p lt2 s f y g) (@lem8124318 A B C P p lt2 s f y g)). Qed.
Lemma lem8124320 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term194 A B C P p lt2 s f y g) = (term219 A B C P p lt2 s f y g).
Proof. exact (EQ_MP (@lem8124319 A B C P p lt2 s f y g) (@lem8124294 A B C P p lt2 s f y g)). Qed.
Lemma lem8124321 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term141 A B C P p lt2 s f y g) = (term219 A B C P p lt2 s f y g).
Proof. exact (TRANS (@lem8124290 A B C P p lt2 s f y g) (@lem8124320 A B C P p lt2 s f y g)). Qed.
Lemma lem8124322 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term142 A B C P p lt2 s f y) = (term220 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8124321 A B C P p lt2 s f y g)). Qed.
Lemma lem8124323 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124324 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term143 A B C P p lt2 s f y) = (term221 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8124323 A B) (@lem8124322 A B C P p lt2 s f y)). Qed.
Lemma lem8124326 {A B : Type'} (P : type1413 A B) : (term195 A B P) = (term196 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8124327 {A B P : Type'} (P' : type537 A B P) : (term222 A B P P') = (term223 A B P P').
Proof. exact (@lem8124326 (A -> B) (P -> A) P'). Qed.
Lemma lem8124328 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term224 A B C P p lt2 s f y) = (term225 A B C P p lt2 s f y).
Proof. exact (@lem8124327 A B P (term226 A B C P p lt2 s f y)). Qed.
Lemma lem8124329 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term227 A B C P p lt2 s f y g) = (term218 A B C P p lt2 s f y g).
Proof. exact (eq_refl (term227 A B C P p lt2 s f y g)). Qed.
Lemma lem8124330 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8124331 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) (z : P -> A) : (term228 A B C P p lt2 s f y g z) = (term229 A B C P p lt2 s f y g z).
Proof. exact (MK_COMB (@lem8124329 A B C P p lt2 s f y g) (@lem8124330 A P z)). Qed.
Lemma lem8124332 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term229 A B C P p lt2 s f y g z) = (term216 A B C P p lt2 s z f y g).
Proof. exact (eq_refl (term229 A B C P p lt2 s f y g z)). Qed.
Lemma lem8124333 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term228 A B C P p lt2 s f y g z) = (term216 A B C P p lt2 s z f y g).
Proof. exact (TRANS (@lem8124331 A B C P p lt2 s f y g z) (@lem8124332 A B C P p lt2 s z f y g)). Qed.
Lemma lem8124334 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term230 A B C P p lt2 s f y g) = (term218 A B C P p lt2 s f y g).
Proof. exact (fun_ext (fun z : P -> A => @lem8124333 A B C P p lt2 s z f y g)). Qed.
Lemma lem8124335 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8124336 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term231 A B C P p lt2 s f y g) = (term219 A B C P p lt2 s f y g).
Proof. exact (MK_COMB (@lem8124335 A P) (@lem8124334 A B C P p lt2 s f y g)). Qed.
Lemma lem8124337 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term232 A B C P p lt2 s f y) = (term220 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8124336 A B C P p lt2 s f y g)). Qed.
Lemma lem8124338 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124339 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term224 A B C P p lt2 s f y) = (term221 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8124338 A B) (@lem8124337 A B C P p lt2 s f y)). Qed.
Lemma lem8124340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8124341 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term233 A B C P p lt2 s f y) = (term234 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8124340) (@lem8124339 A B C P p lt2 s f y)). Qed.
Lemma lem8124342 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term227 A B C P p lt2 s f y g) = (term218 A B C P p lt2 s f y g).
Proof. exact (eq_refl (term227 A B C P p lt2 s f y g)). Qed.
Lemma lem8124343 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8124344 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (z : type557 A B P) (g : A -> B) : (term235 A B C P p lt2 s f y z g) = (term236 A B C P p lt2 s f y z g).
Proof. exact (MK_COMB (@lem8124342 A B C P p lt2 s f y g) (@lem8124343 A B P z g)). Qed.
Lemma lem8124345 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term236 A B C P p lt2 s f y z g) = (term237 A B C P p lt2 s z f y g).
Proof. exact (eq_refl (term236 A B C P p lt2 s f y z g)). Qed.
Lemma lem8124346 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term235 A B C P p lt2 s f y z g) = (term237 A B C P p lt2 s z f y g).
Proof. exact (TRANS (@lem8124344 A B C P p lt2 s f y z g) (@lem8124345 A B C P p lt2 s z f y g)). Qed.
Lemma lem8124347 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) : (term238 A B C P p lt2 s f y z) = (term239 A B C P p lt2 s z f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8124346 A B C P p lt2 s z f y g)). Qed.
Lemma lem8124348 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124349 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) : (term240 A B C P p lt2 s f y z) = (term241 A B C P p lt2 s z f y).
Proof. exact (MK_COMB (@lem8124348 A B) (@lem8124347 A B C P p lt2 s z f y)). Qed.
Lemma lem8124350 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term242 A B C P p lt2 s f y) = (term243 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8124349 A B C P p lt2 s z f y)). Qed.
Lemma lem8124351 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8124352 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term225 A B C P p lt2 s f y) = (term244 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8124351 A B P) (@lem8124350 A B C P p lt2 s f y)). Qed.
Lemma lem8124353 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : ((term224 A B C P p lt2 s f y) = (term225 A B C P p lt2 s f y)) = ((term221 A B C P p lt2 s f y) = (term244 A B C P p lt2 s f y)).
Proof. exact (MK_COMB (@lem8124341 A B C P p lt2 s f y) (@lem8124352 A B C P p lt2 s f y)). Qed.
Lemma lem8124354 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term221 A B C P p lt2 s f y) = (term244 A B C P p lt2 s f y).
Proof. exact (EQ_MP (@lem8124353 A B C P p lt2 s f y) (@lem8124328 A B C P p lt2 s f y)). Qed.
Lemma lem8124355 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term143 A B C P p lt2 s f y) = (term244 A B C P p lt2 s f y).
Proof. exact (TRANS (@lem8124324 A B C P p lt2 s f y) (@lem8124354 A B C P p lt2 s f y)). Qed.
Lemma lem8124356 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term144 A B C P p lt2 s y) = (term245 A B C P p lt2 s y).
Proof. exact (fun_ext (fun f : A -> B => @lem8124355 A B C P p lt2 s f y)). Qed.
Lemma lem8124357 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124358 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term145 A B C P p lt2 s y) = (term246 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8124357 A B) (@lem8124356 A B C P p lt2 s y)). Qed.
Lemma lem8124360 {A B : Type'} (P : type1413 A B) : (term195 A B P) = (term196 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8124361 {A B P : Type'} (P' : type495 A B P) : (term247 A B P P') = (term248 A B P P').
Proof. exact (@lem8124360 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8124362 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term249 A B C P p lt2 s y) = (term250 A B C P p lt2 s y).
Proof. exact (@lem8124361 A B P (term251 A B C P p lt2 s y)). Qed.
Lemma lem8124363 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term252 A B C P p lt2 s y f) = (term243 A B C P p lt2 s f y).
Proof. exact (eq_refl (term252 A B C P p lt2 s y f)). Qed.
Lemma lem8124364 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8124365 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) (z : type557 A B P) : (term253 A B C P p lt2 s y f z) = (term254 A B C P p lt2 s f y z).
Proof. exact (MK_COMB (@lem8124363 A B C P p lt2 s f y) (@lem8124364 A B P z)). Qed.
Lemma lem8124366 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) : (term254 A B C P p lt2 s f y z) = (term241 A B C P p lt2 s z f y).
Proof. exact (eq_refl (term254 A B C P p lt2 s f y z)). Qed.
Lemma lem8124367 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (y : type564 A B C P) : (term253 A B C P p lt2 s y f z) = (term241 A B C P p lt2 s z f y).
Proof. exact (TRANS (@lem8124365 A B C P p lt2 s f y z) (@lem8124366 A B C P p lt2 s z f y)). Qed.
Lemma lem8124368 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term255 A B C P p lt2 s y f) = (term243 A B C P p lt2 s f y).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8124367 A B C P p lt2 s z f y)). Qed.
Lemma lem8124369 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8124370 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term256 A B C P p lt2 s y f) = (term244 A B C P p lt2 s f y).
Proof. exact (MK_COMB (@lem8124369 A B P) (@lem8124368 A B C P p lt2 s f y)). Qed.
Lemma lem8124371 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term257 A B C P p lt2 s y) = (term245 A B C P p lt2 s y).
Proof. exact (fun_ext (fun f : A -> B => @lem8124370 A B C P p lt2 s f y)). Qed.
Lemma lem8124372 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124373 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term249 A B C P p lt2 s y) = (term246 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8124372 A B) (@lem8124371 A B C P p lt2 s y)). Qed.
Lemma lem8124374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8124375 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term258 A B C P p lt2 s y) = (term259 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8124374) (@lem8124373 A B C P p lt2 s y)). Qed.
Lemma lem8124376 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (y : type564 A B C P) : (term252 A B C P p lt2 s y f) = (term243 A B C P p lt2 s f y).
Proof. exact (eq_refl (term252 A B C P p lt2 s y f)). Qed.
Lemma lem8124377 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8124378 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (z : type518 A B P) (f : A -> B) : (term260 A B C P p lt2 s y z f) = (term261 A B C P p lt2 s y z f).
Proof. exact (MK_COMB (@lem8124376 A B C P p lt2 s f y) (@lem8124377 A B P z f)). Qed.
Lemma lem8124379 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term261 A B C P p lt2 s y z f) = (term262 A B C P p lt2 s z f y).
Proof. exact (eq_refl (term261 A B C P p lt2 s y z f)). Qed.
Lemma lem8124380 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term260 A B C P p lt2 s y z f) = (term262 A B C P p lt2 s z f y).
Proof. exact (TRANS (@lem8124378 A B C P p lt2 s y z f) (@lem8124379 A B C P p lt2 s z f y)). Qed.
Lemma lem8124381 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) : (term263 A B C P p lt2 s y z) = (term264 A B C P p lt2 s z y).
Proof. exact (fun_ext (fun f : A -> B => @lem8124380 A B C P p lt2 s z f y)). Qed.
Lemma lem8124382 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124383 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) : (term265 A B C P p lt2 s y z) = (term266 A B C P p lt2 s z y).
Proof. exact (MK_COMB (@lem8124382 A B) (@lem8124381 A B C P p lt2 s z y)). Qed.
Lemma lem8124384 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term267 A B C P p lt2 s y) = (term268 A B C P p lt2 s y).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8124383 A B C P p lt2 s z y)). Qed.
Lemma lem8124385 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8124386 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term250 A B C P p lt2 s y) = (term269 A B C P p lt2 s y).
Proof. exact (MK_COMB (@lem8124385 A B P) (@lem8124384 A B C P p lt2 s y)). Qed.
Lemma lem8124387 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : ((term249 A B C P p lt2 s y) = (term250 A B C P p lt2 s y)) = ((term246 A B C P p lt2 s y) = (term269 A B C P p lt2 s y)).
Proof. exact (MK_COMB (@lem8124375 A B C P p lt2 s y) (@lem8124386 A B C P p lt2 s y)). Qed.
Lemma lem8124388 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term246 A B C P p lt2 s y) = (term269 A B C P p lt2 s y).
Proof. exact (EQ_MP (@lem8124387 A B C P p lt2 s y) (@lem8124362 A B C P p lt2 s y)). Qed.
Lemma lem8124390 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term145 A B C P p lt2 s y) = (term269 A B C P p lt2 s y).
Proof. exact (TRANS (@lem8124358 A B C P p lt2 s y) (@lem8124388 A B C P p lt2 s y)). Qed.
Lemma lem8124391 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) : (term24 A B C P p lt2 s y) = (term269 A B C P p lt2 s y).
Proof. exact (TRANS (@lem8124110 A B C P p lt2 s y) (@lem8124390 A B C P p lt2 s y)). Qed.
Lemma lem8124392 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term24 A B C P p lt2 s y) : term269 A B C P p lt2 s y.
Proof. exact (EQ_MP (@lem8124391 A B C P p lt2 s y) (@lem8124060 A B C P p lt2 s y h1)). Qed.
Lemma lem8124401 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (z : A) : (term102 A B P lt2 s a f g' z) = (term270 A B P lt2 s a f g' z).
Proof. exact (@lem17265 (term119 A P lt2 z s a) ((f z) = (g' z))). Qed.
Lemma lem8124402 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term103 A B P lt2 s a f g') = (term271 A B P lt2 s a f g').
Proof. exact (fun_ext (fun z : A => @lem8124401 A B P lt2 s a f g' z)). Qed.
Lemma lem8124403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8124404 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term104 A B P lt2 s a f g') = (term272 A B P lt2 s a f g').
Proof. exact (MK_COMB (@lem8124403 A) (@lem8124402 A B P lt2 s a f g')). Qed.
Lemma lem8124406 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term105 A B P p g' a) = (term105 A B P p g' a).
Proof. exact (eq_refl (term105 A B P p g' a)). Qed.
Lemma lem8124407 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term106 A B P p lt2 s a f g') = (term273 A B P p lt2 s a f g').
Proof. exact (MK_COMB (@lem8124406 A B P p g' a) (@lem8124404 A B P lt2 s a f g')). Qed.
Lemma lem8124409 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term105 A B P p f a) = (term105 A B P p f a).
Proof. exact (eq_refl (term105 A B P p f a)). Qed.
Lemma lem8124462 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term30 A B P p lt2 s a f g') = (term274 A B P p lt2 s a f g').
Proof. exact (MK_COMB (@lem8124409 A B P p f a) (@lem8124407 A B P p lt2 s a f g')). Qed.
Lemma lem8124463 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term274 A B P p lt2 s a f g'.
Proof. exact (EQ_MP (@lem8124462 A B P p lt2 s a f g') (@lem8124061 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8124469 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term116 A B C D P f g y g' a) : term116 A B C D P f g y g' a.
Proof. exact (h1). Qed.
Lemma lem8124470 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term266 A B C P p lt2 s z y.
Proof. exact (h1). Qed.
Lemma lem8124471 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8124476 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124477 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8124476 A B f x). Qed.
Lemma lem8124479 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8124477 A B f z). Qed.
Lemma lem8124484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124485 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8124484 A B f x). Qed.
Lemma lem8124487 {A B : Type'} (g' : A -> B) (z : A) : (g' z) = (@I (A -> B) g' z).
Proof. exact (@lem8124485 A B g' z). Qed.
Lemma lem8124488 {A B : Type'} (f : A -> B) (z : A) : (term275 A B f z) = (term276 A B f z).
Proof. exact (MK_COMB (@lem8124471 B) (@lem8124479 A B f z)). Qed.
Lemma lem8124489 {A B : Type'} (f : A -> B) (g' : A -> B) (z : A) : ((f z) = (g' z)) = ((@I (A -> B) f z) = (@I (A -> B) g' z)).
Proof. exact (MK_COMB (@lem8124488 A B f z) (@lem8124487 A B g' z)). Qed.
Lemma lem8124490 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8124497 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124498 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8124497 P A f x). Qed.
Lemma lem8124500 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8124498 A P s a). Qed.
Lemma lem8124501 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8124502 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term119 A P lt2 z s a) = (term277 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8124501 A lt2 z) (@lem8124500 A P s a)). Qed.
Lemma lem8124504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124505 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8124504 A (A -> Prop) f x). Qed.
Lemma lem8124506 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8124505 A lt2 z). Qed.
Lemma lem8124507 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8124508 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term277 A P lt2 z s a) = (term278 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8124506 A lt2 z) (@lem8124507 A P s a)). Qed.
Lemma lem8124510 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124511 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8124510 A Prop f x). Qed.
Lemma lem8124512 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term278 A P lt2 z s a) = (term279 A P lt2 z s a).
Proof. exact (@lem8124511 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a)). Qed.
Lemma lem8124513 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term277 A P lt2 z s a) = (term279 A P lt2 z s a).
Proof. exact (TRANS (@lem8124508 A P lt2 z s a) (@lem8124512 A P lt2 z s a)). Qed.
Lemma lem8124514 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term119 A P lt2 z s a) = (term279 A P lt2 z s a).
Proof. exact (TRANS (@lem8124502 A P lt2 z s a) (@lem8124513 A P lt2 z s a)). Qed.
Lemma lem8124515 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term280 A P lt2 z s a) = (term281 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8124490) (@lem8124514 A P lt2 z s a)). Qed.
Lemma lem8124516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124517 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term282 A P lt2 z s a) = (term283 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8124516) (@lem8124515 A P lt2 z s a)). Qed.
Lemma lem8124518 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (z : A) : (term270 A B P lt2 s a f g' z) = (term284 A B P lt2 s a f g' z).
Proof. exact (MK_COMB (@lem8124517 A P lt2 z s a) (@lem8124489 A B f g' z)). Qed.
Lemma lem8124519 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term271 A B P lt2 s a f g') = (term285 A B P lt2 s a f g').
Proof. exact (fun_ext (fun z : A => @lem8124518 A B P lt2 s a f g' z)). Qed.
Lemma lem8124520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8124521 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term272 A B P lt2 s a f g') = (term286 A B P lt2 s a f g').
Proof. exact (MK_COMB (@lem8124520 A) (@lem8124519 A B P lt2 s a f g')). Qed.
Lemma lem8124528 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124529 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8124528 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8124530 {A B P : Type'} (p : type560 A B P) (g' : A -> B) : (p g') = (@I ((A -> B) -> P -> Prop) p g').
Proof. exact (@lem8124529 A B P p g'). Qed.
Lemma lem8124531 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124532 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (p g' a) = (@I ((A -> B) -> P -> Prop) p g' a).
Proof. exact (MK_COMB (@lem8124530 A B P p g') (@lem8124531 P a)). Qed.
Lemma lem8124534 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124535 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8124534 P Prop f x). Qed.
Lemma lem8124536 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g' a) = (term287 A B P p g' a).
Proof. exact (@lem8124535 P (@I ((A -> B) -> P -> Prop) p g') a). Qed.
Lemma lem8124538 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (p g' a) = (term287 A B P p g' a).
Proof. exact (TRANS (@lem8124532 A B P p g' a) (@lem8124536 A B P p g' a)). Qed.
Lemma lem8124539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8124540 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term105 A B P p g' a) = (term288 A B P p g' a).
Proof. exact (MK_COMB (@lem8124539) (@lem8124538 A B P p g' a)). Qed.
Lemma lem8124541 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term273 A B P p lt2 s a f g') = (term289 A B P p lt2 s a f g').
Proof. exact (MK_COMB (@lem8124540 A B P p g' a) (@lem8124521 A B P lt2 s a f g')). Qed.
Lemma lem8124548 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124549 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8124548 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8124550 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8124549 A B P p f). Qed.
Lemma lem8124551 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124552 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8124550 A B P p f) (@lem8124551 P a)). Qed.
Lemma lem8124554 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124555 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8124554 P Prop f x). Qed.
Lemma lem8124556 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term287 A B P p f a).
Proof. exact (@lem8124555 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8124558 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term287 A B P p f a).
Proof. exact (TRANS (@lem8124552 A B P p f a) (@lem8124556 A B P p f a)). Qed.
Lemma lem8124559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8124560 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term105 A B P p f a) = (term288 A B P p f a).
Proof. exact (MK_COMB (@lem8124559) (@lem8124558 A B P p f a)). Qed.
Lemma lem8124561 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term274 A B P p lt2 s a f g') = (term290 A B P p lt2 s a f g').
Proof. exact (MK_COMB (@lem8124560 A B P p f a) (@lem8124541 A B P p lt2 s a f g')). Qed.
Lemma lem8124562 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term290 A B P p lt2 s a f g'.
Proof. exact (EQ_MP (@lem8124561 A B P p lt2 s a f g') (@lem8124463 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8124563 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8124564 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem8124573 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124574 {A B C P : Type'} (f : type564 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C) f x).
Proof. exact (@lem8124573 (A -> B) (P -> C) f x). Qed.
Lemma lem8124575 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) : (y f) = (@I ((A -> B) -> P -> C) y f).
Proof. exact (@lem8124574 A B C P y f). Qed.
Lemma lem8124576 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124577 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (y f a) = (@I ((A -> B) -> P -> C) y f a).
Proof. exact (MK_COMB (@lem8124575 A B C P y f) (@lem8124576 P a)). Qed.
Lemma lem8124579 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124580 {C P : Type'} (f : P -> C) (x : P) : (f x) = (@I (P -> C) f x).
Proof. exact (@lem8124579 P C f x). Qed.
Lemma lem8124581 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> C) y f a) = (term291 A B C P y f a).
Proof. exact (@lem8124580 C P (@I ((A -> B) -> P -> C) y f) a). Qed.
Lemma lem8124583 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (y f a) = (term291 A B C P y f a).
Proof. exact (TRANS (@lem8124577 A B C P y f a) (@lem8124581 A B C P y f a)). Qed.
Lemma lem8124584 {C D P : Type'} (g : type1514 C D P) (a : P) : (g a) = (g a).
Proof. exact (eq_refl (g a)). Qed.
Lemma lem8124585 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term49 A B C D P g y f a) = (term292 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8124584 C D P g a) (@lem8124583 A B C P y f a)). Qed.
Lemma lem8124587 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124588 {C D P : Type'} (f : type1514 C D P) (x : P) : (f x) = (@I (P -> C -> D) f x).
Proof. exact (@lem8124587 P (C -> D) f x). Qed.
Lemma lem8124589 {C D P : Type'} (g : type1514 C D P) (a : P) : (g a) = (@I (P -> C -> D) g a).
Proof. exact (@lem8124588 C D P g a). Qed.
Lemma lem8124590 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (term291 A B C P y f a) = (term291 A B C P y f a).
Proof. exact (eq_refl (term291 A B C P y f a)). Qed.
Lemma lem8124591 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term292 A B C D P g y f a) = (term293 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8124589 C D P g a) (@lem8124590 A B C P y f a)). Qed.
Lemma lem8124593 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124594 {C D : Type'} (f : C -> D) (x : C) : (f x) = (@I (C -> D) f x).
Proof. exact (@lem8124593 C D f x). Qed.
Lemma lem8124595 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term293 A B C D P g y f a) = (term294 A B C D P g y f a).
Proof. exact (@lem8124594 C D (@I (P -> C -> D) g a) (term291 A B C P y f a)). Qed.
Lemma lem8124596 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term292 A B C D P g y f a) = (term294 A B C D P g y f a).
Proof. exact (TRANS (@lem8124591 A B C D P g y f a) (@lem8124595 A B C D P g y f a)). Qed.
Lemma lem8124597 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term49 A B C D P g y f a) = (term294 A B C D P g y f a).
Proof. exact (TRANS (@lem8124585 A B C D P g y f a) (@lem8124596 A B C D P g y f a)). Qed.
Lemma lem8124606 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124607 {A B C P : Type'} (f : type564 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C) f x).
Proof. exact (@lem8124606 (A -> B) (P -> C) f x). Qed.
Lemma lem8124608 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) : (y g') = (@I ((A -> B) -> P -> C) y g').
Proof. exact (@lem8124607 A B C P y g'). Qed.
Lemma lem8124609 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124610 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) (a : P) : (y g' a) = (@I ((A -> B) -> P -> C) y g' a).
Proof. exact (MK_COMB (@lem8124608 A B C P y g') (@lem8124609 P a)). Qed.
Lemma lem8124612 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124613 {C P : Type'} (f : P -> C) (x : P) : (f x) = (@I (P -> C) f x).
Proof. exact (@lem8124612 P C f x). Qed.
Lemma lem8124614 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) (a : P) : (@I ((A -> B) -> P -> C) y g' a) = (term291 A B C P y g' a).
Proof. exact (@lem8124613 C P (@I ((A -> B) -> P -> C) y g') a). Qed.
Lemma lem8124616 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) (a : P) : (y g' a) = (term291 A B C P y g' a).
Proof. exact (TRANS (@lem8124610 A B C P y g' a) (@lem8124614 A B C P y g' a)). Qed.
Lemma lem8124617 {C D P : Type'} (g : type1514 C D P) (a : P) : (g a) = (g a).
Proof. exact (eq_refl (g a)). Qed.
Lemma lem8124618 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term49 A B C D P g y g' a) = (term292 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8124617 C D P g a) (@lem8124616 A B C P y g' a)). Qed.
Lemma lem8124620 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124621 {C D P : Type'} (f : type1514 C D P) (x : P) : (f x) = (@I (P -> C -> D) f x).
Proof. exact (@lem8124620 P (C -> D) f x). Qed.
Lemma lem8124622 {C D P : Type'} (g : type1514 C D P) (a : P) : (g a) = (@I (P -> C -> D) g a).
Proof. exact (@lem8124621 C D P g a). Qed.
Lemma lem8124623 {A B C P : Type'} (y : type564 A B C P) (g' : A -> B) (a : P) : (term291 A B C P y g' a) = (term291 A B C P y g' a).
Proof. exact (eq_refl (term291 A B C P y g' a)). Qed.
Lemma lem8124624 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term292 A B C D P g y g' a) = (term293 A B C D P g y g' a).
Proof. exact (MK_COMB (@lem8124622 C D P g a) (@lem8124623 A B C P y g' a)). Qed.
Lemma lem8124626 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124627 {C D : Type'} (f : C -> D) (x : C) : (f x) = (@I (C -> D) f x).
Proof. exact (@lem8124626 C D f x). Qed.
Lemma lem8124628 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term293 A B C D P g y g' a) = (term294 A B C D P g y g' a).
Proof. exact (@lem8124627 C D (@I (P -> C -> D) g a) (term291 A B C P y g' a)). Qed.
Lemma lem8124629 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term292 A B C D P g y g' a) = (term294 A B C D P g y g' a).
Proof. exact (TRANS (@lem8124624 A B C D P g y g' a) (@lem8124628 A B C D P g y g' a)). Qed.
Lemma lem8124630 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term49 A B C D P g y g' a) = (term294 A B C D P g y g' a).
Proof. exact (TRANS (@lem8124618 A B C D P g y g' a) (@lem8124629 A B C D P g y g' a)). Qed.
Lemma lem8124631 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (f : A -> B) (a : P) : (term54 A B C D P g y f a) = (term295 A B C D P g y f a).
Proof. exact (MK_COMB (@lem8124564 D) (@lem8124597 A B C D P g y f a)). Qed.
Lemma lem8124632 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : ((term49 A B C D P g y f a) = (term49 A B C D P g y g' a)) = ((term294 A B C D P g y f a) = (term294 A B C D P g y g' a)).
Proof. exact (MK_COMB (@lem8124631 A B C D P g y f a) (@lem8124630 A B C D P g y g' a)). Qed.
Lemma lem8124633 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term116 A B C D P f g y g' a) = (term296 A B C D P f g y g' a).
Proof. exact (MK_COMB (@lem8124563) (@lem8124632 A B C D P f g y g' a)). Qed.
Lemma lem8124635 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8124642 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124643 {A B C P : Type'} (f : type564 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C) f x).
Proof. exact (@lem8124642 (A -> B) (P -> C) f x). Qed.
Lemma lem8124644 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) : (y f) = (@I ((A -> B) -> P -> C) y f).
Proof. exact (@lem8124643 A B C P y f). Qed.
Lemma lem8124645 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124646 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (y f a) = (@I ((A -> B) -> P -> C) y f a).
Proof. exact (MK_COMB (@lem8124644 A B C P y f) (@lem8124645 P a)). Qed.
Lemma lem8124648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124649 {C P : Type'} (f : P -> C) (x : P) : (f x) = (@I (P -> C) f x).
Proof. exact (@lem8124648 P C f x). Qed.
Lemma lem8124650 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> C) y f a) = (term291 A B C P y f a).
Proof. exact (@lem8124649 C P (@I ((A -> B) -> P -> C) y f) a). Qed.
Lemma lem8124652 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (y f a) = (term291 A B C P y f a).
Proof. exact (TRANS (@lem8124646 A B C P y f a) (@lem8124650 A B C P y f a)). Qed.
Lemma lem8124659 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124660 {A B C P : Type'} (f : type564 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> C) f x).
Proof. exact (@lem8124659 (A -> B) (P -> C) f x). Qed.
Lemma lem8124661 {A B C P : Type'} (y : type564 A B C P) (g : A -> B) : (y g) = (@I ((A -> B) -> P -> C) y g).
Proof. exact (@lem8124660 A B C P y g). Qed.
Lemma lem8124662 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124663 {A B C P : Type'} (y : type564 A B C P) (g : A -> B) (a : P) : (y g a) = (@I ((A -> B) -> P -> C) y g a).
Proof. exact (MK_COMB (@lem8124661 A B C P y g) (@lem8124662 P a)). Qed.
Lemma lem8124665 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124666 {C P : Type'} (f : P -> C) (x : P) : (f x) = (@I (P -> C) f x).
Proof. exact (@lem8124665 P C f x). Qed.
Lemma lem8124667 {A B C P : Type'} (y : type564 A B C P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> C) y g a) = (term291 A B C P y g a).
Proof. exact (@lem8124666 C P (@I ((A -> B) -> P -> C) y g) a). Qed.
Lemma lem8124669 {A B C P : Type'} (y : type564 A B C P) (g : A -> B) (a : P) : (y g a) = (term291 A B C P y g a).
Proof. exact (TRANS (@lem8124663 A B C P y g a) (@lem8124667 A B C P y g a)). Qed.
Lemma lem8124670 {A B C P : Type'} (y : type564 A B C P) (f : A -> B) (a : P) : (term297 A B C P y f a) = (term298 A B C P y f a).
Proof. exact (MK_COMB (@lem8124635 C) (@lem8124652 A B C P y f a)). Qed.
Lemma lem8124671 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((y f a) = (y g a)) = ((term291 A B C P y f a) = (term291 A B C P y g a)).
Proof. exact (MK_COMB (@lem8124670 A B C P y f a) (@lem8124669 A B C P y g a)). Qed.
Lemma lem8124672 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8124673 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8124674 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8124683 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124684 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8124683 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8124685 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8124684 A B P z f). Qed.
Lemma lem8124686 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8124687 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8124685 A B P z f) (@lem8124686 A B g)). Qed.
Lemma lem8124689 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124690 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8124689 (A -> B) (P -> A) f x). Qed.
Lemma lem8124691 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term299 A B P z f g).
Proof. exact (@lem8124690 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8124692 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term299 A B P z f g).
Proof. exact (TRANS (@lem8124687 A B P z f g) (@lem8124691 A B P z f g)). Qed.
Lemma lem8124693 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124694 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term300 A B P z f g a).
Proof. exact (MK_COMB (@lem8124692 A B P z f g) (@lem8124693 P a)). Qed.
Lemma lem8124696 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124697 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8124696 P A f x). Qed.
Lemma lem8124698 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term300 A B P z f g a) = (term301 A B P z f g a).
Proof. exact (@lem8124697 A P (term299 A B P z f g) a). Qed.
Lemma lem8124700 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term301 A B P z f g a).
Proof. exact (TRANS (@lem8124694 A B P z f g a) (@lem8124698 A B P z f g a)). Qed.
Lemma lem8124701 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term302 A B P z f g a) = (term303 A B P z f g a).
Proof. exact (MK_COMB (@lem8124674 A B f) (@lem8124700 A B P z f g a)). Qed.
Lemma lem8124703 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124704 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8124703 A B f x). Qed.
Lemma lem8124705 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term303 A B P z f g a) = (term304 A B P z f g a).
Proof. exact (@lem8124704 A B f (term301 A B P z f g a)). Qed.
Lemma lem8124706 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term302 A B P z f g a) = (term304 A B P z f g a).
Proof. exact (TRANS (@lem8124701 A B P z f g a) (@lem8124705 A B P z f g a)). Qed.
Lemma lem8124707 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8124716 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124717 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8124716 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8124718 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8124717 A B P z f). Qed.
Lemma lem8124719 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8124720 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8124718 A B P z f) (@lem8124719 A B g)). Qed.
Lemma lem8124722 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124723 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8124722 (A -> B) (P -> A) f x). Qed.
Lemma lem8124724 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term299 A B P z f g).
Proof. exact (@lem8124723 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8124725 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term299 A B P z f g).
Proof. exact (TRANS (@lem8124720 A B P z f g) (@lem8124724 A B P z f g)). Qed.
Lemma lem8124726 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124727 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term300 A B P z f g a).
Proof. exact (MK_COMB (@lem8124725 A B P z f g) (@lem8124726 P a)). Qed.
Lemma lem8124729 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124730 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8124729 P A f x). Qed.
Lemma lem8124731 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term300 A B P z f g a) = (term301 A B P z f g a).
Proof. exact (@lem8124730 A P (term299 A B P z f g) a). Qed.
Lemma lem8124733 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term301 A B P z f g a).
Proof. exact (TRANS (@lem8124727 A B P z f g a) (@lem8124731 A B P z f g a)). Qed.
Lemma lem8124734 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term305 A B P z f g a) = (term306 A B P z f g a).
Proof. exact (MK_COMB (@lem8124707 A B g) (@lem8124733 A B P z f g a)). Qed.
Lemma lem8124736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124737 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8124736 A B f x). Qed.
Lemma lem8124738 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term306 A B P z f g a) = (term307 A B P z f g a).
Proof. exact (@lem8124737 A B g (term301 A B P z f g a)). Qed.
Lemma lem8124739 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term305 A B P z f g a) = (term307 A B P z f g a).
Proof. exact (TRANS (@lem8124734 A B P z f g a) (@lem8124738 A B P z f g a)). Qed.
Lemma lem8124740 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term308 A B P z f g a) = (term309 A B P z f g a).
Proof. exact (MK_COMB (@lem8124673 B) (@lem8124706 A B P z f g a)). Qed.
Lemma lem8124741 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term302 A B P z f g a) = (term305 A B P z f g a)) = ((term304 A B P z f g a) = (term307 A B P z f g a)).
Proof. exact (MK_COMB (@lem8124740 A B P z f g a) (@lem8124739 A B P z f g a)). Qed.
Lemma lem8124742 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term310 A B P z f g a) = (term311 A B P z f g a).
Proof. exact (MK_COMB (@lem8124672) (@lem8124741 A B P z f g a)). Qed.
Lemma lem8124743 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8124752 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124753 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8124752 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8124754 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8124753 A B P z f). Qed.
Lemma lem8124755 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8124756 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8124754 A B P z f) (@lem8124755 A B g)). Qed.
Lemma lem8124758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124759 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8124758 (A -> B) (P -> A) f x). Qed.
Lemma lem8124760 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term299 A B P z f g).
Proof. exact (@lem8124759 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8124761 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term299 A B P z f g).
Proof. exact (TRANS (@lem8124756 A B P z f g) (@lem8124760 A B P z f g)). Qed.
Lemma lem8124762 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124763 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term300 A B P z f g a).
Proof. exact (MK_COMB (@lem8124761 A B P z f g) (@lem8124762 P a)). Qed.
Lemma lem8124765 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124766 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8124765 P A f x). Qed.
Lemma lem8124767 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term300 A B P z f g a) = (term301 A B P z f g a).
Proof. exact (@lem8124766 A P (term299 A B P z f g) a). Qed.
Lemma lem8124769 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term301 A B P z f g a).
Proof. exact (TRANS (@lem8124763 A B P z f g a) (@lem8124767 A B P z f g a)). Qed.
Lemma lem8124774 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124775 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8124774 P A f x). Qed.
Lemma lem8124777 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8124775 A P s a). Qed.
Lemma lem8124778 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term312 A B P lt2 z f g a) = (term313 A B P lt2 z f g a).
Proof. exact (MK_COMB (@lem8124743 A lt2) (@lem8124769 A B P z f g a)). Qed.
Lemma lem8124779 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term314 A B P lt2 z f g s a) = (term315 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8124778 A B P lt2 z f g a) (@lem8124777 A P s a)). Qed.
Lemma lem8124781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124782 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8124781 A (A -> Prop) f x). Qed.
Lemma lem8124783 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term313 A B P lt2 z f g a) = (term316 A B P lt2 z f g a).
Proof. exact (@lem8124782 A lt2 (term301 A B P z f g a)). Qed.
Lemma lem8124784 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8124785 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term315 A B P lt2 z f g s a) = (term317 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8124783 A B P lt2 z f g a) (@lem8124784 A P s a)). Qed.
Lemma lem8124787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124788 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8124787 A Prop f x). Qed.
Lemma lem8124789 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term317 A B P lt2 z f g s a) = (term318 A B P lt2 z f g s a).
Proof. exact (@lem8124788 A (term316 A B P lt2 z f g a) (@I (P -> A) s a)). Qed.
Lemma lem8124790 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term315 A B P lt2 z f g s a) = (term318 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8124785 A B P lt2 z f g s a) (@lem8124789 A B P lt2 z f g s a)). Qed.
Lemma lem8124791 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term314 A B P lt2 z f g s a) = (term318 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8124779 A B P lt2 z f g s a) (@lem8124790 A B P lt2 z f g s a)). Qed.
Lemma lem8124792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8124793 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term319 A B P lt2 z f g s a) = (term320 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8124792) (@lem8124791 A B P lt2 z f g s a)). Qed.
Lemma lem8124794 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term321 A B P lt2 s z f g a) = (term322 A B P lt2 s z f g a).
Proof. exact (MK_COMB (@lem8124793 A B P lt2 z f g s a) (@lem8124742 A B P z f g a)). Qed.
Lemma lem8124795 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8124802 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124803 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8124802 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8124804 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8124803 A B P p g). Qed.
Lemma lem8124805 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124806 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8124804 A B P p g) (@lem8124805 P a)). Qed.
Lemma lem8124808 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124809 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8124808 P Prop f x). Qed.
Lemma lem8124810 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term287 A B P p g a).
Proof. exact (@lem8124809 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8124812 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term287 A B P p g a).
Proof. exact (TRANS (@lem8124806 A B P p g a) (@lem8124810 A B P p g a)). Qed.
Lemma lem8124813 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term150 A B P p g a) = (term323 A B P p g a).
Proof. exact (MK_COMB (@lem8124795) (@lem8124812 A B P p g a)). Qed.
Lemma lem8124814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124815 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term129 A B P p g a) = (term324 A B P p g a).
Proof. exact (MK_COMB (@lem8124814) (@lem8124813 A B P p g a)). Qed.
Lemma lem8124816 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term325 A B P p lt2 s z f g a) = (term326 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8124815 A B P p g a) (@lem8124794 A B P lt2 s z f g a)). Qed.
Lemma lem8124817 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8124824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124825 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8124824 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8124826 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8124825 A B P p f). Qed.
Lemma lem8124827 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8124828 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8124826 A B P p f) (@lem8124827 P a)). Qed.
Lemma lem8124830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8124831 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8124830 P Prop f x). Qed.
Lemma lem8124832 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term287 A B P p f a).
Proof. exact (@lem8124831 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8124834 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term287 A B P p f a).
Proof. exact (TRANS (@lem8124828 A B P p f a) (@lem8124832 A B P p f a)). Qed.
Lemma lem8124835 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term150 A B P p f a) = (term323 A B P p f a).
Proof. exact (MK_COMB (@lem8124817) (@lem8124834 A B P p f a)). Qed.
Lemma lem8124836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124837 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term129 A B P p f a) = (term324 A B P p f a).
Proof. exact (MK_COMB (@lem8124836) (@lem8124835 A B P p f a)). Qed.
Lemma lem8124838 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term327 A B P p lt2 s z f g a) = (term328 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8124837 A B P p f a) (@lem8124816 A B P p lt2 s z f g a)). Qed.
Lemma lem8124839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124840 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term329 A B P p lt2 s z f g a) = (term330 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8124839) (@lem8124838 A B P p lt2 s z f g a)). Qed.
Lemma lem8124841 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term331 A B C P p lt2 s z f y g a) = (term332 A B C P p lt2 s z f y g a).
Proof. exact (MK_COMB (@lem8124840 A B P p lt2 s z f g a) (@lem8124671 A B C P f y g a)). Qed.
Lemma lem8124842 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term333 A B C P p lt2 s z f y g) = (term334 A B C P p lt2 s z f y g).
Proof. exact (fun_ext (fun a : P => @lem8124841 A B C P p lt2 s z f y g a)). Qed.
Lemma lem8124843 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8124844 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term335 A B C P p lt2 s z f y g) = (term336 A B C P p lt2 s z f y g).
Proof. exact (MK_COMB (@lem8124843 P) (@lem8124842 A B C P p lt2 s z f y g)). Qed.
Lemma lem8124845 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term337 A B C P p lt2 s z f y) = (term338 A B C P p lt2 s z f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8124844 A B C P p lt2 s z f y g)). Qed.
Lemma lem8124846 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124847 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term262 A B C P p lt2 s z f y) = (term339 A B C P p lt2 s z f y).
Proof. exact (MK_COMB (@lem8124846 A B) (@lem8124845 A B C P p lt2 s z f y)). Qed.
Lemma lem8124848 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) : (term264 A B C P p lt2 s z y) = (term340 A B C P p lt2 s z y).
Proof. exact (fun_ext (fun f : A -> B => @lem8124847 A B C P p lt2 s z f y)). Qed.
Lemma lem8124849 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124850 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) : (term266 A B C P p lt2 s z y) = (term341 A B C P p lt2 s z y).
Proof. exact (MK_COMB (@lem8124849 A B) (@lem8124848 A B C P p lt2 s z y)). Qed.
Lemma lem8124851 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term341 A B C P p lt2 s z y.
Proof. exact (EQ_MP (@lem8124850 A B C P p lt2 s z y) (@lem8124470 A B C P p lt2 s z y h1)). Qed.
Lemma lem8124852 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term289 A B P p lt2 s a f g'.
Proof. exact (proj2 (@lem8124562 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8124854 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term286 A B P lt2 s a f g'.
Proof. exact (proj2 (@lem8124852 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8124861 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : ((term291 A B C P y f a) = (term291 A B C P y g a)) = ((term291 A B C P y f a) = (term291 A B C P y g a)).
Proof. exact (eq_refl ((term291 A B C P y f a) = (term291 A B C P y g a))). Qed.
Lemma lem8124878 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term326 A B P p lt2 s z f g a) = (term342 A B P lt2 s p z f g a).
Proof. exact (@lem19490 (term318 A B P lt2 z f g s a) (term323 A B P p g a) (term311 A B P z f g a)). Qed.
Lemma lem8124881 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term324 A B P p f a) = (term324 A B P p f a).
Proof. exact (eq_refl (term324 A B P p f a)). Qed.
Lemma lem8124882 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term328 A B P p lt2 s z f g a) = (term343 A B P lt2 s p z f g a).
Proof. exact (MK_COMB (@lem8124881 A B P p f a) (@lem8124878 A B P lt2 s p z f g a)). Qed.
Lemma lem8124889 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term343 A B P lt2 s p z f g a) = (term344 A B P lt2 s p z f g a).
Proof. exact (@lem19490 (term345 A B P p lt2 z f g s a) (term323 A B P p f a) (term346 A B P p z f g a)). Qed.
Lemma lem8124890 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term328 A B P p lt2 s z f g a) = (term344 A B P lt2 s p z f g a).
Proof. exact (TRANS (@lem8124882 A B P lt2 s p z f g a) (@lem8124889 A B P lt2 s p z f g a)). Qed.
Lemma lem8124891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8124892 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term330 A B P p lt2 s z f g a) = (term347 A B P lt2 s p z f g a).
Proof. exact (MK_COMB (@lem8124891) (@lem8124890 A B P lt2 s p z f g a)). Qed.
Lemma lem8124893 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term332 A B C P p lt2 s z f y g a) = (term348 A B C P lt2 s p z f y g a).
Proof. exact (MK_COMB (@lem8124892 A B P lt2 s p z f g a) (@lem8124861 A B C P f y g a)). Qed.
Lemma lem8124900 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term348 A B C P lt2 s p z f y g a) = (term349 A B C P lt2 s p z f y g a).
Proof. exact (@lem19699 (term350 A B P p lt2 z f g s a) (term351 A B P p z f g a) ((term291 A B C P y f a) = (term291 A B C P y g a))). Qed.
Lemma lem8124901 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) (a : P) : (term332 A B C P p lt2 s z f y g a) = (term349 A B C P lt2 s p z f y g a).
Proof. exact (TRANS (@lem8124893 A B C P lt2 s p z f y g a) (@lem8124900 A B C P lt2 s p z f y g a)). Qed.
Lemma lem8124902 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term334 A B C P p lt2 s z f y g) = (term352 A B C P lt2 s p z f y g).
Proof. exact (fun_ext (fun a : P => @lem8124901 A B C P lt2 s p z f y g a)). Qed.
Lemma lem8124903 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8124904 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) (g : A -> B) : (term336 A B C P p lt2 s z f y g) = (term353 A B C P lt2 s p z f y g).
Proof. exact (MK_COMB (@lem8124903 P) (@lem8124902 A B C P lt2 s p z f y g)). Qed.
Lemma lem8124905 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term338 A B C P p lt2 s z f y) = (term354 A B C P lt2 s p z f y).
Proof. exact (fun_ext (fun g : A -> B => @lem8124904 A B C P lt2 s p z f y g)). Qed.
Lemma lem8124906 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124907 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (y : type564 A B C P) : (term339 A B C P p lt2 s z f y) = (term355 A B C P lt2 s p z f y).
Proof. exact (MK_COMB (@lem8124906 A B) (@lem8124905 A B C P lt2 s p z f y)). Qed.
Lemma lem8124908 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (y : type564 A B C P) : (term340 A B C P p lt2 s z y) = (term356 A B C P lt2 s p z y).
Proof. exact (fun_ext (fun f : A -> B => @lem8124907 A B C P lt2 s p z f y)). Qed.
Lemma lem8124909 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8124911 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (y : type564 A B C P) : (term341 A B C P p lt2 s z y) = (term357 A B C P lt2 s p z y).
Proof. exact (MK_COMB (@lem8124909 A B) (@lem8124908 A B C P lt2 s p z y)). Qed.
Lemma lem8124912 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term357 A B C P lt2 s p z y.
Proof. exact (EQ_MP (@lem8124911 A B C P lt2 s p z y) (@lem8124851 A B C P p lt2 s z y h1)). Qed.
Lemma lem8124928 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (z : A) : (term284 A B P lt2 s a f g' z) = (term284 A B P lt2 s a f g' z).
Proof. exact (eq_refl (term284 A B P lt2 s a f g' z)). Qed.
Lemma lem8124929 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term285 A B P lt2 s a f g') = (term285 A B P lt2 s a f g').
Proof. exact (fun_ext (fun z : A => @lem8124928 A B P lt2 s a f g' z)). Qed.
Lemma lem8124930 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8124932 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) : (term286 A B P lt2 s a f g') = (term286 A B P lt2 s a f g').
Proof. exact (MK_COMB (@lem8124930 A) (@lem8124929 A B P lt2 s a f g')). Qed.
Lemma lem8124933 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term286 A B P lt2 s a f g'.
Proof. exact (EQ_MP (@lem8124932 A B P lt2 s a f g') (@lem8124854 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8124934 {A B C P : Type'} (_107516 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term358 A B C P lt2 s p z y _107516.
Proof. exact (@lem8124912 A B C P p lt2 s z y h1 _107516). Qed.
Lemma lem8124935 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) : (term358 A B C P lt2 s p z y _107516) = (term355 A B C P lt2 s p z _107516 y).
Proof. exact (eq_refl (term358 A B C P lt2 s p z y _107516)). Qed.
Lemma lem8124936 {A B C P : Type'} (_107516 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term355 A B C P lt2 s p z _107516 y.
Proof. exact (EQ_MP (@lem8124935 A B C P lt2 s p z _107516 y) (@lem8124934 A B C P _107516 p lt2 s z y h1)). Qed.
Lemma lem8124937 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term359 A B C P lt2 s p z _107516 y _107517.
Proof. exact (@lem8124936 A B C P _107516 p lt2 s z y h1 _107517). Qed.
Lemma lem8124938 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) : (term359 A B C P lt2 s p z _107516 y _107517) = (term353 A B C P lt2 s p z _107516 y _107517).
Proof. exact (eq_refl (term359 A B C P lt2 s p z _107516 y _107517)). Qed.
Lemma lem8124939 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term353 A B C P lt2 s p z _107516 y _107517.
Proof. exact (EQ_MP (@lem8124938 A B C P lt2 s p z _107516 y _107517) (@lem8124937 A B C P _107516 _107517 p lt2 s z y h1)). Qed.
Lemma lem8124940 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term360 A B C P lt2 s p z _107516 y _107517 _107518.
Proof. exact (@lem8124939 A B C P _107516 _107517 p lt2 s z y h1 _107518). Qed.
Lemma lem8124941 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term360 A B C P lt2 s p z _107516 y _107517 _107518) = (term349 A B C P lt2 s p z _107516 y _107517 _107518).
Proof. exact (eq_refl (term360 A B C P lt2 s p z _107516 y _107517 _107518)). Qed.
Lemma lem8124942 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term349 A B C P lt2 s p z _107516 y _107517 _107518.
Proof. exact (EQ_MP (@lem8124941 A B C P lt2 s p z _107516 y _107517 _107518) (@lem8124940 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8124943 {A B P : Type'} (_107519 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term361 A B P lt2 s a f g' _107519.
Proof. exact (@lem8124933 A B P p lt2 s a f g' h1 _107519). Qed.
Lemma lem8124944 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (_107519 : A) : (term361 A B P lt2 s a f g' _107519) = (term284 A B P lt2 s a f g' _107519).
Proof. exact (eq_refl (term361 A B P lt2 s a f g' _107519)). Qed.
Lemma lem8124946 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term362 A B C P p z _107516 y _107517 _107518.
Proof. exact (proj2 (@lem8124942 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8124947 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term363 A B C P p lt2 z s _107516 y _107517 _107518.
Proof. exact (proj1 (@lem8124942 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8124949 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term116 A B C D P f g y g' a) : term296 A B C D P f g y g' a.
Proof. exact (EQ_MP (@lem8124633 A B C D P f g y g' a) (@lem8124469 A B C D P f g y g' a h1)). Qed.
Lemma lem8124959 {A B P : Type'} (_107519 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term284 A B P lt2 s a f g' _107519.
Proof. exact (EQ_MP (@lem8124944 A B P lt2 s a f g' _107519) (@lem8124943 A B P _107519 p lt2 s a f g' h1)). Qed.
Lemma lem8124963 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term363 A B C P p lt2 z s _107516 y _107517 _107518) = (term364 A B C P p lt2 z s _107516 y _107517 _107518).
Proof. exact (@lem8116294 (term323 A B P p _107516 _107518) (term345 A B P p lt2 z _107516 _107517 s _107518) ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8124970 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term365 A B C P p lt2 z s _107516 y _107517 _107518) = (term366 A B C P p lt2 z s _107516 y _107517 _107518).
Proof. exact (@lem8116294 (term323 A B P p _107517 _107518) (term318 A B P lt2 z _107516 _107517 s _107518) ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8124971 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term324 A B P p _107516 _107518) = (term324 A B P p _107516 _107518).
Proof. exact (eq_refl (term324 A B P p _107516 _107518)). Qed.
Lemma lem8124974 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term364 A B C P p lt2 z s _107516 y _107517 _107518) = (term367 A B C P p lt2 z s _107516 y _107517 _107518).
Proof. exact (MK_COMB (@lem8124971 A B P p _107516 _107518) (@lem8124970 A B C P p lt2 z s _107516 y _107517 _107518)). Qed.
Lemma lem8124976 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term363 A B C P p lt2 z s _107516 y _107517 _107518) = (term367 A B C P p lt2 z s _107516 y _107517 _107518).
Proof. exact (TRANS (@lem8124963 A B C P p lt2 z s _107516 y _107517 _107518) (@lem8124974 A B C P p lt2 z s _107516 y _107517 _107518)). Qed.
Lemma lem8124977 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term367 A B C P p lt2 z s _107516 y _107517 _107518.
Proof. exact (EQ_MP (@lem8124976 A B C P p lt2 z s _107516 y _107517 _107518) (@lem8124947 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8124981 {A B C P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term362 A B C P p z _107516 y _107517 _107518) = (term368 A B C P p z _107516 y _107517 _107518).
Proof. exact (@lem8116294 (term323 A B P p _107516 _107518) (term346 A B P p z _107516 _107517 _107518) ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8124988 {A B C P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term369 A B C P p z _107516 y _107517 _107518) = (term370 A B C P p z _107516 y _107517 _107518).
Proof. exact (@lem8116294 (term323 A B P p _107517 _107518) (term311 A B P z _107516 _107517 _107518) ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8124989 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term324 A B P p _107516 _107518) = (term324 A B P p _107516 _107518).
Proof. exact (eq_refl (term324 A B P p _107516 _107518)). Qed.
Lemma lem8124992 {A B C P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term368 A B C P p z _107516 y _107517 _107518) = (term371 A B C P p z _107516 y _107517 _107518).
Proof. exact (MK_COMB (@lem8124989 A B P p _107516 _107518) (@lem8124988 A B C P p z _107516 y _107517 _107518)). Qed.
Lemma lem8124994 {A B C P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term362 A B C P p z _107516 y _107517 _107518) = (term371 A B C P p z _107516 y _107517 _107518).
Proof. exact (TRANS (@lem8124981 A B C P p z _107516 y _107517 _107518) (@lem8124992 A B C P p z _107516 y _107517 _107518)). Qed.
Lemma lem8124995 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term371 A B C P p z _107516 y _107517 _107518.
Proof. exact (EQ_MP (@lem8124994 A B C P p z _107516 y _107517 _107518) (@lem8124946 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8125169 {C D : Type'} : (@I (C -> D)) = (@I (C -> D)).
Proof. exact (eq_refl (@I (C -> D))). Qed.
Lemma lem8125170 {C D : Type'} (_107564 : C -> D) (_107566 : C -> D) (h1 : _107564 = _107566) : _107564 = _107566.
Proof. exact (h1). Qed.
Lemma lem8125171 {C : Type'} (_107565 : C) (_107567 : C) (h1 : _107565 = _107567) : _107565 = _107567.
Proof. exact (h1). Qed.
Lemma lem8125172 {C D : Type'} (_107564 : C -> D) (_107566 : C -> D) (h1 : _107564 = _107566) : (@I (C -> D) _107564) = (@I (C -> D) _107566).
Proof. exact (MK_COMB (@lem8125169 C D) (@lem8125170 C D _107564 _107566 h1)). Qed.
Lemma lem8125173 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) (h1 : _107565 = _107567) (h2 : _107564 = _107566) : (@I (C -> D) _107564 _107565) = (@I (C -> D) _107566 _107567).
Proof. exact (MK_COMB (@lem8125172 C D _107564 _107566 h2) (@lem8125171 C _107565 _107567 h1)). Qed.
Lemma lem8125174 {C D : Type'} (_107564 : C -> D) (_107566 : C -> D) (_107565 : C) (_107567 : C) (h1 : _107565 = _107567) : term372 C D _107564 _107565 _107566 _107567.
Proof. exact (fun h0 : _107564 = _107566 => @lem8125173 C D _107565 _107567 _107564 _107566 h1 h0). Qed.
Lemma lem8125176 (a : Prop) (b : Prop) : (a -> b) = (term373 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem8125177 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : (term372 C D _107564 _107565 _107566 _107567) = (term374 C D _107564 _107565 _107566 _107567).
Proof. exact (@lem8125176 (_107564 = _107566) ((@I (C -> D) _107564 _107565) = (@I (C -> D) _107566 _107567))). Qed.
Lemma lem8125178 {C D : Type'} (_107564 : C -> D) (_107566 : C -> D) (_107565 : C) (_107567 : C) (h1 : _107565 = _107567) : term374 C D _107564 _107565 _107566 _107567.
Proof. exact (EQ_MP (@lem8125177 C D _107564 _107565 _107566 _107567) (@lem8125174 C D _107564 _107566 _107565 _107567 h1)). Qed.
Lemma lem8125179 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : term375 C D _107564 _107565 _107566 _107567.
Proof. exact (fun h0 : _107565 = _107567 => @lem8125178 C D _107564 _107566 _107565 _107567 h0). Qed.
Lemma lem8125181 (a : Prop) (b : Prop) : (a -> b) = (term373 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem8125182 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : (term375 C D _107564 _107565 _107566 _107567) = (term376 C D _107564 _107565 _107566 _107567).
Proof. exact (@lem8125181 (_107565 = _107567) (term374 C D _107564 _107565 _107566 _107567)). Qed.
Lemma lem8125183 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : term376 C D _107564 _107565 _107566 _107567.
Proof. exact (EQ_MP (@lem8125182 C D _107564 _107565 _107566 _107567) (@lem8125179 C D _107564 _107565 _107566 _107567)). Qed.
Lemma lem8125219 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term287 A B P p f a.
Proof. exact (proj1 (@lem8124562 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8125220 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term377 A B P p f a.
Proof. exact (fun h0 : term323 A B P p f a => @lem8125219 A B P p lt2 s a f g' h1). Qed.
Lemma lem8125222 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125223 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term377 A B P p f a) = (term287 A B P p f a).
Proof. exact (@lem8125222 (term287 A B P p f a)). Qed.
Lemma lem8125224 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term287 A B P p f a.
Proof. exact (EQ_MP (@lem8125223 A B P p f a) (@lem8125220 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8125226 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term287 A B P p g' a.
Proof. exact (proj1 (@lem8124852 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8125227 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term377 A B P p g' a.
Proof. exact (fun h0 : term323 A B P p g' a => @lem8125226 A B P p lt2 s a f g' h1). Qed.
Lemma lem8125229 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125230 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term377 A B P p g' a) = (term287 A B P p g' a).
Proof. exact (@lem8125229 (term287 A B P p g' a)). Qed.
Lemma lem8125231 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term287 A B P p g' a.
Proof. exact (EQ_MP (@lem8125230 A B P p g' a) (@lem8125227 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8125233 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term287 A B P p f a.
Proof. exact (proj1 (@lem8124562 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8125234 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term377 A B P p f a.
Proof. exact (fun h0 : term323 A B P p f a => @lem8125233 A B P p lt2 s a f g' h1). Qed.
Lemma lem8125236 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125237 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term377 A B P p f a) = (term287 A B P p f a).
Proof. exact (@lem8125236 (term287 A B P p f a)). Qed.
Lemma lem8125238 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term287 A B P p f a.
Proof. exact (EQ_MP (@lem8125237 A B P p f a) (@lem8125234 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8125240 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term287 A B P p g' a.
Proof. exact (proj1 (@lem8124852 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8125241 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term377 A B P p g' a.
Proof. exact (fun h0 : term323 A B P p g' a => @lem8125240 A B P p lt2 s a f g' h1). Qed.
Lemma lem8125243 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125244 {A B P : Type'} (p : type560 A B P) (g' : A -> B) (a : P) : (term377 A B P p g' a) = (term287 A B P p g' a).
Proof. exact (@lem8125243 (term287 A B P p g' a)). Qed.
Lemma lem8125245 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term287 A B P p g' a.
Proof. exact (EQ_MP (@lem8125244 A B P p g' a) (@lem8125241 A B P p lt2 s a f g' h1)). Qed.
Lemma lem8125248 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term379 A B C P f y g' a) : term379 A B C P f y g' a.
Proof. exact (h1). Qed.
Lemma lem8125249 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term379 A B C P f y g' a) : term380 A B C P f y g' a.
Proof. exact (fun h0 : (term291 A B C P y f a) = (term291 A B C P y g' a) => @lem8125248 A B C P f y g' a h1). Qed.
Lemma lem8125251 (p : Prop) : (term381 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8125252 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) : (term380 A B C P f y g' a) = (term379 A B C P f y g' a).
Proof. exact (@lem8125251 ((term291 A B C P y f a) = (term291 A B C P y g' a))). Qed.
Lemma lem8125253 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term379 A B C P f y g' a) : term379 A B C P f y g' a.
Proof. exact (EQ_MP (@lem8125252 A B C P f y g' a) (@lem8125249 A B C P f y g' a h1)). Qed.
Lemma lem8125269 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125270 {A B C P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term366 A B C P p lt2 z s _107516 y _107517 _107518) = (term382 A B C P lt2 z s p _107516 y _107517 _107518).
Proof. exact (@lem8125269 (term318 A B P lt2 z _107516 _107517 s _107518) (term323 A B P p _107517 _107518) ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8125284 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8125285 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term383 A B C P p _107516 y _107517 _107518) = (term384 A B C P _107516 y p _107517 _107518).
Proof. exact (@lem8125284 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125293 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (s : P -> A) (_107518 : P) : (term385 A B P lt2 z _107516 _107517 s _107518) = (term385 A B P lt2 z _107516 _107517 s _107518).
Proof. exact (eq_refl (term385 A B P lt2 z _107516 _107517 s _107518)). Qed.
Lemma lem8125294 {A B C P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term382 A B C P lt2 z s p _107516 y _107517 _107518) = (term386 A B C P lt2 z s _107516 y p _107517 _107518).
Proof. exact (MK_COMB (@lem8125293 A B P lt2 z _107516 _107517 s _107518) (@lem8125285 A B C P _107516 y p _107517 _107518)). Qed.
Lemma lem8125298 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125299 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (s : P -> A) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term386 A B C P lt2 z s _107516 y p _107517 _107518) = (term387 A B C P y lt2 z _107516 s p _107517 _107518).
Proof. exact (@lem8125298 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term318 A B P lt2 z _107516 _107517 s _107518) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125317 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (s : P -> A) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term382 A B C P lt2 z s p _107516 y _107517 _107518) = (term387 A B C P y lt2 z _107516 s p _107517 _107518).
Proof. exact (TRANS (@lem8125294 A B C P lt2 z s _107516 y p _107517 _107518) (@lem8125299 A B C P y lt2 z _107516 s p _107517 _107518)). Qed.
Lemma lem8125318 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (s : P -> A) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term366 A B C P p lt2 z s _107516 y _107517 _107518) = (term387 A B C P y lt2 z _107516 s p _107517 _107518).
Proof. exact (TRANS (@lem8125270 A B C P lt2 z s p _107516 y _107517 _107518) (@lem8125317 A B C P y lt2 z _107516 s p _107517 _107518)). Qed.
Lemma lem8125319 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term324 A B P p _107516 _107518) = (term324 A B P p _107516 _107518).
Proof. exact (eq_refl (term324 A B P p _107516 _107518)). Qed.
Lemma lem8125320 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (s : P -> A) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term367 A B C P p lt2 z s _107516 y _107517 _107518) = (term388 A B C P y lt2 z _107516 s p _107517 _107518).
Proof. exact (MK_COMB (@lem8125319 A B P p _107516 _107518) (@lem8125318 A B C P y lt2 z _107516 s p _107517 _107518)). Qed.
Lemma lem8125324 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125325 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (s : P -> A) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term388 A B C P y lt2 z _107516 s p _107517 _107518) = (term389 A B C P y lt2 z _107516 s p _107517 _107518).
Proof. exact (@lem8125324 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term323 A B P p _107516 _107518) (term390 A B P lt2 z _107516 s p _107517 _107518)). Qed.
Lemma lem8125341 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125342 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term391 A B P lt2 z _107516 s p _107517 _107518) = (term392 A B P lt2 z s _107516 p _107517 _107518).
Proof. exact (@lem8125341 (term318 A B P lt2 z _107516 _107517 s _107518) (term323 A B P p _107516 _107518) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125358 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term393 A B C P _107516 y _107517 _107518) = (term393 A B C P _107516 y _107517 _107518).
Proof. exact (eq_refl (term393 A B C P _107516 y _107517 _107518)). Qed.
Lemma lem8125359 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term389 A B C P y lt2 z _107516 s p _107517 _107518) = (term394 A B C P y lt2 z s _107516 p _107517 _107518).
Proof. exact (MK_COMB (@lem8125358 A B C P _107516 y _107517 _107518) (@lem8125342 A B P lt2 z s _107516 p _107517 _107518)). Qed.
Lemma lem8125370 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term388 A B C P y lt2 z _107516 s p _107517 _107518) = (term394 A B C P y lt2 z s _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125325 A B C P y lt2 z _107516 s p _107517 _107518) (@lem8125359 A B C P y lt2 z s _107516 p _107517 _107518)). Qed.
Lemma lem8125371 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term367 A B C P p lt2 z s _107516 y _107517 _107518) = (term394 A B C P y lt2 z s _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125320 A B C P y lt2 z _107516 s p _107517 _107518) (@lem8125370 A B C P y lt2 z s _107516 p _107517 _107518)). Qed.
Lemma lem8125372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8125373 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term395 A B C P p lt2 z s _107516 y _107517 _107518) = (term396 A B C P y lt2 z s _107516 p _107517 _107518).
Proof. exact (MK_COMB (@lem8125372) (@lem8125371 A B C P y lt2 z s _107516 p _107517 _107518)). Qed.
Lemma lem8125397 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8125398 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term383 A B C P p _107516 y _107517 _107518) = (term384 A B C P _107516 y p _107517 _107518).
Proof. exact (@lem8125397 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125406 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term324 A B P p _107516 _107518) = (term324 A B P p _107516 _107518).
Proof. exact (eq_refl (term324 A B P p _107516 _107518)). Qed.
Lemma lem8125407 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term397 A B C P p _107516 y _107517 _107518) = (term398 A B C P _107516 y p _107517 _107518).
Proof. exact (MK_COMB (@lem8125406 A B P p _107516 _107518) (@lem8125398 A B C P _107516 y p _107517 _107518)). Qed.
Lemma lem8125411 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125412 {A B C P : Type'} (y : type564 A B C P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term398 A B C P _107516 y p _107517 _107518) = (term399 A B C P y _107516 p _107517 _107518).
Proof. exact (@lem8125411 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term323 A B P p _107516 _107518) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125430 {A B C P : Type'} (y : type564 A B C P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term397 A B C P p _107516 y _107517 _107518) = (term399 A B C P y _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125407 A B C P _107516 y p _107517 _107518) (@lem8125412 A B C P y _107516 p _107517 _107518)). Qed.
Lemma lem8125431 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (s : P -> A) (_107518 : P) : (term385 A B P lt2 z _107516 _107517 s _107518) = (term385 A B P lt2 z _107516 _107517 s _107518).
Proof. exact (eq_refl (term385 A B P lt2 z _107516 _107517 s _107518)). Qed.
Lemma lem8125432 {A B C P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (y : type564 A B C P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term400 A B C P lt2 z s p _107516 y _107517 _107518) = (term401 A B C P lt2 z s y _107516 p _107517 _107518).
Proof. exact (MK_COMB (@lem8125431 A B P lt2 z _107516 _107517 s _107518) (@lem8125430 A B C P y _107516 p _107517 _107518)). Qed.
Lemma lem8125436 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125437 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term401 A B C P lt2 z s y _107516 p _107517 _107518) = (term394 A B C P y lt2 z s _107516 p _107517 _107518).
Proof. exact (@lem8125436 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term318 A B P lt2 z _107516 _107517 s _107518) (term402 A B P _107516 p _107517 _107518)). Qed.
Lemma lem8125465 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term400 A B C P lt2 z s p _107516 y _107517 _107518) = (term394 A B C P y lt2 z s _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125432 A B C P lt2 z s y _107516 p _107517 _107518) (@lem8125437 A B C P y lt2 z s _107516 p _107517 _107518)). Qed.
Lemma lem8125466 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : ((term367 A B C P p lt2 z s _107516 y _107517 _107518) = (term400 A B C P lt2 z s p _107516 y _107517 _107518)) = ((term394 A B C P y lt2 z s _107516 p _107517 _107518) = (term394 A B C P y lt2 z s _107516 p _107517 _107518)).
Proof. exact (MK_COMB (@lem8125373 A B C P y lt2 z s _107516 p _107517 _107518) (@lem8125465 A B C P y lt2 z s _107516 p _107517 _107518)). Qed.
Lemma lem8125468 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8125469 (x : Prop) : (x = x) = True.
Proof. exact (@lem8125468 Prop x). Qed.
Lemma lem8125470 {A B C P : Type'} (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : ((term394 A B C P y lt2 z s _107516 p _107517 _107518) = (term394 A B C P y lt2 z s _107516 p _107517 _107518)) = True.
Proof. exact (@lem8125469 (term394 A B C P y lt2 z s _107516 p _107517 _107518)). Qed.
Lemma lem8125471 {A B C P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : ((term367 A B C P p lt2 z s _107516 y _107517 _107518) = (term400 A B C P lt2 z s p _107516 y _107517 _107518)) = True.
Proof. exact (TRANS (@lem8125466 A B C P y lt2 z s _107516 p _107517 _107518) (@lem8125470 A B C P y lt2 z s _107516 p _107517 _107518)). Qed.
Lemma lem8125472 {A B C P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : True = ((term367 A B C P p lt2 z s _107516 y _107517 _107518) = (term400 A B C P lt2 z s p _107516 y _107517 _107518)).
Proof. exact (SYM (@lem8125471 A B C P lt2 z s p _107516 y _107517 _107518)). Qed.
Lemma lem8125473 {A B C P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term367 A B C P p lt2 z s _107516 y _107517 _107518) = (term400 A B C P lt2 z s p _107516 y _107517 _107518).
Proof. exact (EQ_MP (@lem8125472 A B C P lt2 z s p _107516 y _107517 _107518) (@lem0)). Qed.
Lemma lem8125474 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term400 A B C P lt2 z s p _107516 y _107517 _107518.
Proof. exact (EQ_MP (@lem8125473 A B C P lt2 z s p _107516 y _107517 _107518) (@lem8124977 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8125476 (b : Prop) (a : Prop) : (a \/ b) = (term403 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8125477 {A B C P : Type'} (p : type560 A B P) (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (s : P -> A) (_107518 : P) : (term400 A B C P lt2 z s p _107516 y _107517 _107518) = (term404 A B C P p y lt2 z _107516 _107517 s _107518).
Proof. exact (@lem8125476 (term397 A B C P p _107516 y _107517 _107518) (term318 A B P lt2 z _107516 _107517 s _107518)). Qed.
Lemma lem8125479 (a : Prop) (b : Prop) : (term405 a b) = (term406 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8125480 {A B C P : Type'} (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term407 A B C P p _107516 y _107517 _107518) = (term408 A B C P p _107516 y _107517 _107518).
Proof. exact (@lem8125479 (term323 A B P p _107516 _107518) (term383 A B C P p _107516 y _107517 _107518)). Qed.
Lemma lem8125482 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8125483 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term409 A B P p _107516 _107518) = (term287 A B P p _107516 _107518).
Proof. exact (@lem8125482 (term287 A B P p _107516 _107518)). Qed.
Lemma lem8125484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8125485 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term410 A B P p _107516 _107518) = (term288 A B P p _107516 _107518).
Proof. exact (MK_COMB (@lem8125484) (@lem8125483 A B P p _107516 _107518)). Qed.
Lemma lem8125487 (a : Prop) (b : Prop) : (term405 a b) = (term406 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8125488 {A B C P : Type'} (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term411 A B C P p _107516 y _107517 _107518) = (term412 A B C P p _107516 y _107517 _107518).
Proof. exact (@lem8125487 (term323 A B P p _107517 _107518) ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8125490 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8125491 {A B P : Type'} (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term409 A B P p _107517 _107518) = (term287 A B P p _107517 _107518).
Proof. exact (@lem8125490 (term287 A B P p _107517 _107518)). Qed.
Lemma lem8125492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8125493 {A B P : Type'} (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term410 A B P p _107517 _107518) = (term288 A B P p _107517 _107518).
Proof. exact (MK_COMB (@lem8125492) (@lem8125491 A B P p _107517 _107518)). Qed.
Lemma lem8125494 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term379 A B C P _107516 y _107517 _107518) = (term379 A B C P _107516 y _107517 _107518).
Proof. exact (eq_refl (term379 A B C P _107516 y _107517 _107518)). Qed.
Lemma lem8125495 {A B C P : Type'} (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term412 A B C P p _107516 y _107517 _107518) = (term413 A B C P p _107516 y _107517 _107518).
Proof. exact (MK_COMB (@lem8125493 A B P p _107517 _107518) (@lem8125494 A B C P _107516 y _107517 _107518)). Qed.
Lemma lem8125496 {A B C P : Type'} (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term411 A B C P p _107516 y _107517 _107518) = (term413 A B C P p _107516 y _107517 _107518).
Proof. exact (TRANS (@lem8125488 A B C P p _107516 y _107517 _107518) (@lem8125495 A B C P p _107516 y _107517 _107518)). Qed.
Lemma lem8125497 {A B C P : Type'} (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term408 A B C P p _107516 y _107517 _107518) = (term414 A B C P p _107516 y _107517 _107518).
Proof. exact (MK_COMB (@lem8125485 A B P p _107516 _107518) (@lem8125496 A B C P p _107516 y _107517 _107518)). Qed.
Lemma lem8125498 {A B C P : Type'} (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term407 A B C P p _107516 y _107517 _107518) = (term414 A B C P p _107516 y _107517 _107518).
Proof. exact (TRANS (@lem8125480 A B C P p _107516 y _107517 _107518) (@lem8125497 A B C P p _107516 y _107517 _107518)). Qed.
Lemma lem8125499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8125500 {A B C P : Type'} (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term415 A B C P p _107516 y _107517 _107518) = (term416 A B C P p _107516 y _107517 _107518).
Proof. exact (MK_COMB (@lem8125499) (@lem8125498 A B C P p _107516 y _107517 _107518)). Qed.
Lemma lem8125501 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (s : P -> A) (_107518 : P) : (term318 A B P lt2 z _107516 _107517 s _107518) = (term318 A B P lt2 z _107516 _107517 s _107518).
Proof. exact (eq_refl (term318 A B P lt2 z _107516 _107517 s _107518)). Qed.
Lemma lem8125502 {A B C P : Type'} (p : type560 A B P) (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (s : P -> A) (_107518 : P) : (term404 A B C P p y lt2 z _107516 _107517 s _107518) = (term417 A B C P p y lt2 z _107516 _107517 s _107518).
Proof. exact (MK_COMB (@lem8125500 A B C P p _107516 y _107517 _107518) (@lem8125501 A B P lt2 z _107516 _107517 s _107518)). Qed.
Lemma lem8125503 {A B C P : Type'} (p : type560 A B P) (y : type564 A B C P) (lt2 : type1402 A) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (s : P -> A) (_107518 : P) : (term400 A B C P lt2 z s p _107516 y _107517 _107518) = (term417 A B C P p y lt2 z _107516 _107517 s _107518).
Proof. exact (TRANS (@lem8125477 A B C P p y lt2 z _107516 _107517 s _107518) (@lem8125502 A B C P p y lt2 z _107516 _107517 s _107518)). Qed.
Lemma lem8125505 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term379 A B C P f y g' a) (h2 : term30 A B P p lt2 s a f g') : term413 A B C P p f y g' a.
Proof. exact (conj (@lem8125245 A B P p lt2 s a f g' h2) (@lem8125253 A B C P f y g' a h1)). Qed.
Lemma lem8125506 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term379 A B C P f y g' a) (h2 : term30 A B P p lt2 s a f g') : term414 A B C P p f y g' a.
Proof. exact (conj (@lem8125238 A B P p lt2 s a f g' h2) (@lem8125505 A B C P y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8125508 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term417 A B C P p y lt2 z _107516 _107517 s _107518.
Proof. exact (EQ_MP (@lem8125503 A B C P p y lt2 z _107516 _107517 s _107518) (@lem8125474 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8125509 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term417 A B C P p y lt2 z _107516 _107517 s _107518.
Proof. exact (@lem8125508 A B C P _107516 _107517 _107518 p lt2 s z y h1). Qed.
Lemma lem8125510 {A B C P : Type'} (f : A -> B) (g' : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term417 A B C P p y lt2 z f g' s a.
Proof. exact (@lem8125509 A B C P f g' a p lt2 s z y h1). Qed.
Lemma lem8125513 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : term318 A B P lt2 z f g' s a.
Proof. exact (@lem8125510 A B C P f g' a p lt2 s z y h1 (@lem8125506 A B C P y p lt2 s a f g' h2 h3)). Qed.
Lemma lem8125514 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : term418 A B P lt2 z f g' s a.
Proof. exact (fun h0 : term419 A B P lt2 z f g' s a => @lem8125513 A B C P z y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8125516 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125517 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g' : A -> B) (s : P -> A) (a : P) : (term418 A B P lt2 z f g' s a) = (term318 A B P lt2 z f g' s a).
Proof. exact (@lem8125516 (term318 A B P lt2 z f g' s a)). Qed.
Lemma lem8125518 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : term318 A B P lt2 z f g' s a.
Proof. exact (EQ_MP (@lem8125517 A B P lt2 z f g' s a) (@lem8125514 A B C P z y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8125524 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8125525 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : (term284 A B P lt2 s a f g' _107519) = (term420 A B P f g' lt2 _107519 s a).
Proof. exact (@lem8125524 ((@I (A -> B) f _107519) = (@I (A -> B) g' _107519)) (term281 A P lt2 _107519 s a)). Qed.
Lemma lem8125533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8125534 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : (term421 A B P lt2 s a f g' _107519) = (term422 A B P f g' lt2 _107519 s a).
Proof. exact (MK_COMB (@lem8125533) (@lem8125525 A B P f g' lt2 _107519 s a)). Qed.
Lemma lem8125542 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : (term420 A B P f g' lt2 _107519 s a) = (term420 A B P f g' lt2 _107519 s a).
Proof. exact (eq_refl (term420 A B P f g' lt2 _107519 s a)). Qed.
Lemma lem8125543 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : ((term284 A B P lt2 s a f g' _107519) = (term420 A B P f g' lt2 _107519 s a)) = ((term420 A B P f g' lt2 _107519 s a) = (term420 A B P f g' lt2 _107519 s a)).
Proof. exact (MK_COMB (@lem8125534 A B P f g' lt2 _107519 s a) (@lem8125542 A B P f g' lt2 _107519 s a)). Qed.
Lemma lem8125545 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8125546 (x : Prop) : (x = x) = True.
Proof. exact (@lem8125545 Prop x). Qed.
Lemma lem8125547 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : ((term420 A B P f g' lt2 _107519 s a) = (term420 A B P f g' lt2 _107519 s a)) = True.
Proof. exact (@lem8125546 (term420 A B P f g' lt2 _107519 s a)). Qed.
Lemma lem8125548 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : ((term284 A B P lt2 s a f g' _107519) = (term420 A B P f g' lt2 _107519 s a)) = True.
Proof. exact (TRANS (@lem8125543 A B P f g' lt2 _107519 s a) (@lem8125547 A B P f g' lt2 _107519 s a)). Qed.
Lemma lem8125549 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : True = ((term284 A B P lt2 s a f g' _107519) = (term420 A B P f g' lt2 _107519 s a)).
Proof. exact (SYM (@lem8125548 A B P f g' lt2 _107519 s a)). Qed.
Lemma lem8125550 {A B P : Type'} (f : A -> B) (g' : A -> B) (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : (term284 A B P lt2 s a f g' _107519) = (term420 A B P f g' lt2 _107519 s a).
Proof. exact (EQ_MP (@lem8125549 A B P f g' lt2 _107519 s a) (@lem0)). Qed.
Lemma lem8125551 {A B P : Type'} (_107519 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term420 A B P f g' lt2 _107519 s a.
Proof. exact (EQ_MP (@lem8125550 A B P f g' lt2 _107519 s a) (@lem8124959 A B P _107519 p lt2 s a f g' h1)). Qed.
Lemma lem8125553 (b : Prop) (a : Prop) : (a \/ b) = (term403 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8125554 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (_107519 : A) : (term420 A B P f g' lt2 _107519 s a) = (term423 A B P lt2 s a f g' _107519).
Proof. exact (@lem8125553 (term281 A P lt2 _107519 s a) ((@I (A -> B) f _107519) = (@I (A -> B) g' _107519))). Qed.
Lemma lem8125556 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8125557 {A P : Type'} (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : (term424 A P lt2 _107519 s a) = (term279 A P lt2 _107519 s a).
Proof. exact (@lem8125556 (term279 A P lt2 _107519 s a)). Qed.
Lemma lem8125558 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8125559 {A P : Type'} (lt2 : type1402 A) (_107519 : A) (s : P -> A) (a : P) : (term425 A P lt2 _107519 s a) = (term426 A P lt2 _107519 s a).
Proof. exact (MK_COMB (@lem8125558) (@lem8125557 A P lt2 _107519 s a)). Qed.
Lemma lem8125560 {A B : Type'} (f : A -> B) (g' : A -> B) (_107519 : A) : ((@I (A -> B) f _107519) = (@I (A -> B) g' _107519)) = ((@I (A -> B) f _107519) = (@I (A -> B) g' _107519)).
Proof. exact (eq_refl ((@I (A -> B) f _107519) = (@I (A -> B) g' _107519))). Qed.
Lemma lem8125561 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (_107519 : A) : (term423 A B P lt2 s a f g' _107519) = (term427 A B P lt2 s a f g' _107519).
Proof. exact (MK_COMB (@lem8125559 A P lt2 _107519 s a) (@lem8125560 A B f g' _107519)). Qed.
Lemma lem8125562 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (_107519 : A) : (term420 A B P f g' lt2 _107519 s a) = (term427 A B P lt2 s a f g' _107519).
Proof. exact (TRANS (@lem8125554 A B P lt2 s a f g' _107519) (@lem8125561 A B P lt2 s a f g' _107519)). Qed.
Lemma lem8125565 {A B P : Type'} (_107519 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term427 A B P lt2 s a f g' _107519.
Proof. exact (EQ_MP (@lem8125562 A B P lt2 s a f g' _107519) (@lem8125551 A B P _107519 p lt2 s a f g' h1)). Qed.
Lemma lem8125566 {A B P : Type'} (_107519 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term427 A B P lt2 s a f g' _107519.
Proof. exact (@lem8125565 A B P _107519 p lt2 s a f g' h1). Qed.
Lemma lem8125567 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term30 A B P p lt2 s a f g') : term428 A B P lt2 s z f g' a.
Proof. exact (@lem8125566 A B P (term301 A B P z f g' a) p lt2 s a f g' h1). Qed.
Lemma lem8125570 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : (term304 A B P z f g' a) = (term307 A B P z f g' a).
Proof. exact (@lem8125567 A B P z p lt2 s a f g' h3 (@lem8125518 A B C P z y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8125571 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : term429 A B P z f g' a.
Proof. exact (fun h0 : term311 A B P z f g' a => @lem8125570 A B C P z y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8125573 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125574 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g' : A -> B) (a : P) : (term429 A B P z f g' a) = ((term304 A B P z f g' a) = (term307 A B P z f g' a)).
Proof. exact (@lem8125573 ((term304 A B P z f g' a) = (term307 A B P z f g' a))). Qed.
Lemma lem8125575 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : (term304 A B P z f g' a) = (term307 A B P z f g' a).
Proof. exact (EQ_MP (@lem8125574 A B P z f g' a) (@lem8125571 A B C P z y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8125591 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125592 {A B C P : Type'} (z : type518 A B P) (p : type560 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term370 A B C P p z _107516 y _107517 _107518) = (term430 A B C P z p _107516 y _107517 _107518).
Proof. exact (@lem8125591 (term311 A B P z _107516 _107517 _107518) (term323 A B P p _107517 _107518) ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8125608 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8125609 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term383 A B C P p _107516 y _107517 _107518) = (term384 A B C P _107516 y p _107517 _107518).
Proof. exact (@lem8125608 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125617 {A B P : Type'} (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term431 A B P z _107516 _107517 _107518) = (term431 A B P z _107516 _107517 _107518).
Proof. exact (eq_refl (term431 A B P z _107516 _107517 _107518)). Qed.
Lemma lem8125618 {A B C P : Type'} (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term430 A B C P z p _107516 y _107517 _107518) = (term432 A B C P z _107516 y p _107517 _107518).
Proof. exact (MK_COMB (@lem8125617 A B P z _107516 _107517 _107518) (@lem8125609 A B C P _107516 y p _107517 _107518)). Qed.
Lemma lem8125622 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125623 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term432 A B C P z _107516 y p _107517 _107518) = (term433 A B C P y z _107516 p _107517 _107518).
Proof. exact (@lem8125622 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term311 A B P z _107516 _107517 _107518) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125643 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term430 A B C P z p _107516 y _107517 _107518) = (term433 A B C P y z _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125618 A B C P z _107516 y p _107517 _107518) (@lem8125623 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125644 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term370 A B C P p z _107516 y _107517 _107518) = (term433 A B C P y z _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125592 A B C P z p _107516 y _107517 _107518) (@lem8125643 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125645 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term324 A B P p _107516 _107518) = (term324 A B P p _107516 _107518).
Proof. exact (eq_refl (term324 A B P p _107516 _107518)). Qed.
Lemma lem8125646 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term371 A B C P p z _107516 y _107517 _107518) = (term434 A B C P y z _107516 p _107517 _107518).
Proof. exact (MK_COMB (@lem8125645 A B P p _107516 _107518) (@lem8125644 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125650 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125651 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term434 A B C P y z _107516 p _107517 _107518) = (term435 A B C P y z _107516 p _107517 _107518).
Proof. exact (@lem8125650 ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) (term323 A B P p _107516 _107518) (term436 A B P z _107516 p _107517 _107518)). Qed.
Lemma lem8125667 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125668 {A B P : Type'} (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term437 A B P z _107516 p _107517 _107518) = (term438 A B P z _107516 p _107517 _107518).
Proof. exact (@lem8125667 (term311 A B P z _107516 _107517 _107518) (term323 A B P p _107516 _107518) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125686 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term393 A B C P _107516 y _107517 _107518) = (term393 A B C P _107516 y _107517 _107518).
Proof. exact (eq_refl (term393 A B C P _107516 y _107517 _107518)). Qed.
Lemma lem8125687 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term435 A B C P y z _107516 p _107517 _107518) = (term439 A B C P y z _107516 p _107517 _107518).
Proof. exact (MK_COMB (@lem8125686 A B C P _107516 y _107517 _107518) (@lem8125668 A B P z _107516 p _107517 _107518)). Qed.
Lemma lem8125698 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term434 A B C P y z _107516 p _107517 _107518) = (term439 A B C P y z _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125651 A B C P y z _107516 p _107517 _107518) (@lem8125687 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125699 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term371 A B C P p z _107516 y _107517 _107518) = (term439 A B C P y z _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125646 A B C P y z _107516 p _107517 _107518) (@lem8125698 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8125701 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term440 A B C P p z _107516 y _107517 _107518) = (term441 A B C P y z _107516 p _107517 _107518).
Proof. exact (MK_COMB (@lem8125700) (@lem8125699 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125727 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8125728 {A B P : Type'} (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term346 A B P p z _107516 _107517 _107518) = (term436 A B P z _107516 p _107517 _107518).
Proof. exact (@lem8125727 (term311 A B P z _107516 _107517 _107518) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125736 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term324 A B P p _107516 _107518) = (term324 A B P p _107516 _107518).
Proof. exact (eq_refl (term324 A B P p _107516 _107518)). Qed.
Lemma lem8125737 {A B P : Type'} (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term351 A B P p z _107516 _107517 _107518) = (term437 A B P z _107516 p _107517 _107518).
Proof. exact (MK_COMB (@lem8125736 A B P p _107516 _107518) (@lem8125728 A B P z _107516 p _107517 _107518)). Qed.
Lemma lem8125741 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125742 {A B P : Type'} (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term437 A B P z _107516 p _107517 _107518) = (term438 A B P z _107516 p _107517 _107518).
Proof. exact (@lem8125741 (term311 A B P z _107516 _107517 _107518) (term323 A B P p _107516 _107518) (term323 A B P p _107517 _107518)). Qed.
Lemma lem8125760 {A B P : Type'} (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term351 A B P p z _107516 _107517 _107518) = (term438 A B P z _107516 p _107517 _107518).
Proof. exact (TRANS (@lem8125737 A B P z _107516 p _107517 _107518) (@lem8125742 A B P z _107516 p _107517 _107518)). Qed.
Lemma lem8125761 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term393 A B C P _107516 y _107517 _107518) = (term393 A B C P _107516 y _107517 _107518).
Proof. exact (eq_refl (term393 A B C P _107516 y _107517 _107518)). Qed.
Lemma lem8125762 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term442 A B C P y p z _107516 _107517 _107518) = (term439 A B C P y z _107516 p _107517 _107518).
Proof. exact (MK_COMB (@lem8125761 A B C P _107516 y _107517 _107518) (@lem8125760 A B P z _107516 p _107517 _107518)). Qed.
Lemma lem8125773 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : ((term371 A B C P p z _107516 y _107517 _107518) = (term442 A B C P y p z _107516 _107517 _107518)) = ((term439 A B C P y z _107516 p _107517 _107518) = (term439 A B C P y z _107516 p _107517 _107518)).
Proof. exact (MK_COMB (@lem8125701 A B C P y z _107516 p _107517 _107518) (@lem8125762 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125775 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8125776 (x : Prop) : (x = x) = True.
Proof. exact (@lem8125775 Prop x). Qed.
Lemma lem8125777 {A B C P : Type'} (y : type564 A B C P) (z : type518 A B P) (_107516 : A -> B) (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : ((term439 A B C P y z _107516 p _107517 _107518) = (term439 A B C P y z _107516 p _107517 _107518)) = True.
Proof. exact (@lem8125776 (term439 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125778 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : ((term371 A B C P p z _107516 y _107517 _107518) = (term442 A B C P y p z _107516 _107517 _107518)) = True.
Proof. exact (TRANS (@lem8125773 A B C P y z _107516 p _107517 _107518) (@lem8125777 A B C P y z _107516 p _107517 _107518)). Qed.
Lemma lem8125779 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : True = ((term371 A B C P p z _107516 y _107517 _107518) = (term442 A B C P y p z _107516 _107517 _107518)).
Proof. exact (SYM (@lem8125778 A B C P y p z _107516 _107517 _107518)). Qed.
Lemma lem8125780 {A B C P : Type'} (y : type564 A B C P) (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term371 A B C P p z _107516 y _107517 _107518) = (term442 A B C P y p z _107516 _107517 _107518).
Proof. exact (EQ_MP (@lem8125779 A B C P y p z _107516 _107517 _107518) (@lem0)). Qed.
Lemma lem8125781 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term442 A B C P y p z _107516 _107517 _107518.
Proof. exact (EQ_MP (@lem8125780 A B C P y p z _107516 _107517 _107518) (@lem8124995 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8125783 (b : Prop) (a : Prop) : (a \/ b) = (term403 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8125784 {A B C P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term442 A B C P y p z _107516 _107517 _107518) = (term443 A B C P p z _107516 y _107517 _107518).
Proof. exact (@lem8125783 (term351 A B P p z _107516 _107517 _107518) ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8125786 (a : Prop) (b : Prop) : (term405 a b) = (term406 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8125787 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term444 A B P p z _107516 _107517 _107518) = (term445 A B P p z _107516 _107517 _107518).
Proof. exact (@lem8125786 (term323 A B P p _107516 _107518) (term346 A B P p z _107516 _107517 _107518)). Qed.
Lemma lem8125789 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8125790 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term409 A B P p _107516 _107518) = (term287 A B P p _107516 _107518).
Proof. exact (@lem8125789 (term287 A B P p _107516 _107518)). Qed.
Lemma lem8125791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8125792 {A B P : Type'} (p : type560 A B P) (_107516 : A -> B) (_107518 : P) : (term410 A B P p _107516 _107518) = (term288 A B P p _107516 _107518).
Proof. exact (MK_COMB (@lem8125791) (@lem8125790 A B P p _107516 _107518)). Qed.
Lemma lem8125794 (a : Prop) (b : Prop) : (term405 a b) = (term406 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8125795 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term446 A B P p z _107516 _107517 _107518) = (term447 A B P p z _107516 _107517 _107518).
Proof. exact (@lem8125794 (term323 A B P p _107517 _107518) (term311 A B P z _107516 _107517 _107518)). Qed.
Lemma lem8125797 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8125798 {A B P : Type'} (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term409 A B P p _107517 _107518) = (term287 A B P p _107517 _107518).
Proof. exact (@lem8125797 (term287 A B P p _107517 _107518)). Qed.
Lemma lem8125799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8125800 {A B P : Type'} (p : type560 A B P) (_107517 : A -> B) (_107518 : P) : (term410 A B P p _107517 _107518) = (term288 A B P p _107517 _107518).
Proof. exact (MK_COMB (@lem8125799) (@lem8125798 A B P p _107517 _107518)). Qed.
Lemma lem8125802 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8125803 {A B P : Type'} (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term448 A B P z _107516 _107517 _107518) = ((term304 A B P z _107516 _107517 _107518) = (term307 A B P z _107516 _107517 _107518)).
Proof. exact (@lem8125802 ((term304 A B P z _107516 _107517 _107518) = (term307 A B P z _107516 _107517 _107518))). Qed.
Lemma lem8125804 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term447 A B P p z _107516 _107517 _107518) = (term449 A B P p z _107516 _107517 _107518).
Proof. exact (MK_COMB (@lem8125800 A B P p _107517 _107518) (@lem8125803 A B P z _107516 _107517 _107518)). Qed.
Lemma lem8125805 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term446 A B P p z _107516 _107517 _107518) = (term449 A B P p z _107516 _107517 _107518).
Proof. exact (TRANS (@lem8125795 A B P p z _107516 _107517 _107518) (@lem8125804 A B P p z _107516 _107517 _107518)). Qed.
Lemma lem8125806 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term445 A B P p z _107516 _107517 _107518) = (term450 A B P p z _107516 _107517 _107518).
Proof. exact (MK_COMB (@lem8125792 A B P p _107516 _107518) (@lem8125805 A B P p z _107516 _107517 _107518)). Qed.
Lemma lem8125807 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term444 A B P p z _107516 _107517 _107518) = (term450 A B P p z _107516 _107517 _107518).
Proof. exact (TRANS (@lem8125787 A B P p z _107516 _107517 _107518) (@lem8125806 A B P p z _107516 _107517 _107518)). Qed.
Lemma lem8125808 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8125809 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) : (term451 A B P p z _107516 _107517 _107518) = (term452 A B P p z _107516 _107517 _107518).
Proof. exact (MK_COMB (@lem8125808) (@lem8125807 A B P p z _107516 _107517 _107518)). Qed.
Lemma lem8125810 {A B C P : Type'} (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)) = ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518)).
Proof. exact (eq_refl ((term291 A B C P y _107516 _107518) = (term291 A B C P y _107517 _107518))). Qed.
Lemma lem8125811 {A B C P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term443 A B C P p z _107516 y _107517 _107518) = (term453 A B C P p z _107516 y _107517 _107518).
Proof. exact (MK_COMB (@lem8125809 A B P p z _107516 _107517 _107518) (@lem8125810 A B C P _107516 y _107517 _107518)). Qed.
Lemma lem8125812 {A B C P : Type'} (p : type560 A B P) (z : type518 A B P) (_107516 : A -> B) (y : type564 A B C P) (_107517 : A -> B) (_107518 : P) : (term442 A B C P y p z _107516 _107517 _107518) = (term453 A B C P p z _107516 y _107517 _107518).
Proof. exact (TRANS (@lem8125784 A B C P p z _107516 y _107517 _107518) (@lem8125811 A B C P p z _107516 y _107517 _107518)). Qed.
Lemma lem8125814 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : term449 A B P p z f g' a.
Proof. exact (conj (@lem8125231 A B P p lt2 s a f g' h3) (@lem8125575 A B C P z y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8125815 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : term450 A B P p z f g' a.
Proof. exact (conj (@lem8125224 A B P p lt2 s a f g' h3) (@lem8125814 A B C P z y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8125817 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term453 A B C P p z _107516 y _107517 _107518.
Proof. exact (EQ_MP (@lem8125812 A B C P p z _107516 y _107517 _107518) (@lem8125781 A B C P _107516 _107517 _107518 p lt2 s z y h1)). Qed.
Lemma lem8125818 {A B C P : Type'} (_107516 : A -> B) (_107517 : A -> B) (_107518 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term453 A B C P p z _107516 y _107517 _107518.
Proof. exact (@lem8125817 A B C P _107516 _107517 _107518 p lt2 s z y h1). Qed.
Lemma lem8125819 {A B C P : Type'} (f : A -> B) (g' : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (y : type564 A B C P) (h1 : term266 A B C P p lt2 s z y) : term453 A B C P p z f y g' a.
Proof. exact (@lem8125818 A B C P f g' a p lt2 s z y h1). Qed.
Lemma lem8125822 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term379 A B C P f y g' a) (h3 : term30 A B P p lt2 s a f g') : (term291 A B C P y f a) = (term291 A B C P y g' a).
Proof. exact (@lem8125819 A B C P f g' a p lt2 s z y h1 (@lem8125815 A B C P z y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8125823 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term30 A B P p lt2 s a f g') : term454 A B C P f y g' a.
Proof. exact (fun h0 : term379 A B C P f y g' a => @lem8125822 A B C P z y p lt2 s a f g' h1 h0 h2). Qed.
Lemma lem8125825 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125826 {A B C P : Type'} (f : A -> B) (y : type564 A B C P) (g' : A -> B) (a : P) : (term454 A B C P f y g' a) = ((term291 A B C P y f a) = (term291 A B C P y g' a)).
Proof. exact (@lem8125825 ((term291 A B C P y f a) = (term291 A B C P y g' a))). Qed.
Lemma lem8125827 {A B C P : Type'} (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term30 A B P p lt2 s a f g') : (term291 A B C P y f a) = (term291 A B C P y g' a).
Proof. exact (EQ_MP (@lem8125826 A B C P f y g' a) (@lem8125823 A B C P z y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8125829 {C D : Type'} (x : C -> D) : x = x.
Proof. exact (@lem21386 (C -> D) x). Qed.
Lemma lem8125830 {C D : Type'} (x : C -> D) : x = x.
Proof. exact (@lem8125829 C D x). Qed.
Lemma lem8125831 {C D P : Type'} (g : type1514 C D P) (a : P) : (@I (P -> C -> D) g a) = (@I (P -> C -> D) g a).
Proof. exact (@lem8125830 C D (@I (P -> C -> D) g a)). Qed.
Lemma lem8125832 {C D P : Type'} (g : type1514 C D P) (a : P) : term455 C D P g a.
Proof. exact (fun h0 : term456 C D P g a => @lem8125831 C D P g a). Qed.
Lemma lem8125834 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125835 {C D P : Type'} (g : type1514 C D P) (a : P) : (term455 C D P g a) = ((@I (P -> C -> D) g a) = (@I (P -> C -> D) g a)).
Proof. exact (@lem8125834 ((@I (P -> C -> D) g a) = (@I (P -> C -> D) g a))). Qed.
Lemma lem8125836 {C D P : Type'} (g : type1514 C D P) (a : P) : (@I (P -> C -> D) g a) = (@I (P -> C -> D) g a).
Proof. exact (EQ_MP (@lem8125835 C D P g a) (@lem8125832 C D P g a)). Qed.
Lemma lem8125854 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8125855 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term374 C D _107564 _107565 _107566 _107567) = (term457 C D _107565 _107567 _107564 _107566).
Proof. exact (@lem8125854 ((@I (C -> D) _107564 _107565) = (@I (C -> D) _107566 _107567)) (term458 C D _107564 _107566)). Qed.
Lemma lem8125865 {C : Type'} (_107565 : C) (_107567 : C) : (term459 C _107565 _107567) = (term459 C _107565 _107567).
Proof. exact (eq_refl (term459 C _107565 _107567)). Qed.
Lemma lem8125866 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term376 C D _107564 _107565 _107566 _107567) = (term460 C D _107565 _107567 _107564 _107566).
Proof. exact (MK_COMB (@lem8125865 C _107565 _107567) (@lem8125855 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125870 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8125871 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term460 C D _107565 _107567 _107564 _107566) = (term461 C D _107565 _107567 _107564 _107566).
Proof. exact (@lem8125870 ((@I (C -> D) _107564 _107565) = (@I (C -> D) _107566 _107567)) (term462 C _107565 _107567) (term458 C D _107564 _107566)). Qed.
Lemma lem8125893 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term376 C D _107564 _107565 _107566 _107567) = (term461 C D _107565 _107567 _107564 _107566).
Proof. exact (TRANS (@lem8125866 C D _107565 _107567 _107564 _107566) (@lem8125871 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8125895 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term463 C D _107564 _107565 _107566 _107567) = (term464 C D _107565 _107567 _107564 _107566).
Proof. exact (MK_COMB (@lem8125894) (@lem8125893 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125917 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term461 C D _107565 _107567 _107564 _107566) = (term461 C D _107565 _107567 _107564 _107566).
Proof. exact (eq_refl (term461 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125918 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : ((term376 C D _107564 _107565 _107566 _107567) = (term461 C D _107565 _107567 _107564 _107566)) = ((term461 C D _107565 _107567 _107564 _107566) = (term461 C D _107565 _107567 _107564 _107566)).
Proof. exact (MK_COMB (@lem8125895 C D _107565 _107567 _107564 _107566) (@lem8125917 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125920 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8125921 (x : Prop) : (x = x) = True.
Proof. exact (@lem8125920 Prop x). Qed.
Lemma lem8125922 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : ((term461 C D _107565 _107567 _107564 _107566) = (term461 C D _107565 _107567 _107564 _107566)) = True.
Proof. exact (@lem8125921 (term461 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125923 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : ((term376 C D _107564 _107565 _107566 _107567) = (term461 C D _107565 _107567 _107564 _107566)) = True.
Proof. exact (TRANS (@lem8125918 C D _107565 _107567 _107564 _107566) (@lem8125922 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125924 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : True = ((term376 C D _107564 _107565 _107566 _107567) = (term461 C D _107565 _107567 _107564 _107566)).
Proof. exact (SYM (@lem8125923 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125925 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term376 C D _107564 _107565 _107566 _107567) = (term461 C D _107565 _107567 _107564 _107566).
Proof. exact (EQ_MP (@lem8125924 C D _107565 _107567 _107564 _107566) (@lem0)). Qed.
Lemma lem8125926 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : term461 C D _107565 _107567 _107564 _107566.
Proof. exact (EQ_MP (@lem8125925 C D _107565 _107567 _107564 _107566) (@lem8125183 C D _107564 _107565 _107566 _107567)). Qed.
Lemma lem8125928 (b : Prop) (a : Prop) : (a \/ b) = (term403 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8125929 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : (term461 C D _107565 _107567 _107564 _107566) = (term465 C D _107564 _107565 _107566 _107567).
Proof. exact (@lem8125928 (term466 C D _107565 _107567 _107564 _107566) ((@I (C -> D) _107564 _107565) = (@I (C -> D) _107566 _107567))). Qed.
Lemma lem8125931 (a : Prop) (b : Prop) : (term405 a b) = (term406 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8125932 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term467 C D _107565 _107567 _107564 _107566) = (term468 C D _107565 _107567 _107564 _107566).
Proof. exact (@lem8125931 (term462 C _107565 _107567) (term458 C D _107564 _107566)). Qed.
Lemma lem8125934 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8125935 {C : Type'} (_107565 : C) (_107567 : C) : (term469 C _107565 _107567) = (_107565 = _107567).
Proof. exact (@lem8125934 (_107565 = _107567)). Qed.
Lemma lem8125936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8125937 {C : Type'} (_107565 : C) (_107567 : C) : (term470 C _107565 _107567) = (term471 C _107565 _107567).
Proof. exact (MK_COMB (@lem8125936) (@lem8125935 C _107565 _107567)). Qed.
Lemma lem8125939 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8125940 {C D : Type'} (_107564 : C -> D) (_107566 : C -> D) : (term472 C D _107564 _107566) = (_107564 = _107566).
Proof. exact (@lem8125939 (_107564 = _107566)). Qed.
Lemma lem8125941 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term468 C D _107565 _107567 _107564 _107566) = (term473 C D _107565 _107567 _107564 _107566).
Proof. exact (MK_COMB (@lem8125937 C _107565 _107567) (@lem8125940 C D _107564 _107566)). Qed.
Lemma lem8125942 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term467 C D _107565 _107567 _107564 _107566) = (term473 C D _107565 _107567 _107564 _107566).
Proof. exact (TRANS (@lem8125932 C D _107565 _107567 _107564 _107566) (@lem8125941 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125943 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8125944 {C D : Type'} (_107565 : C) (_107567 : C) (_107564 : C -> D) (_107566 : C -> D) : (term474 C D _107565 _107567 _107564 _107566) = (term475 C D _107565 _107567 _107564 _107566).
Proof. exact (MK_COMB (@lem8125943) (@lem8125942 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125945 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : ((@I (C -> D) _107564 _107565) = (@I (C -> D) _107566 _107567)) = ((@I (C -> D) _107564 _107565) = (@I (C -> D) _107566 _107567)).
Proof. exact (eq_refl ((@I (C -> D) _107564 _107565) = (@I (C -> D) _107566 _107567))). Qed.
Lemma lem8125946 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : (term465 C D _107564 _107565 _107566 _107567) = (term476 C D _107564 _107565 _107566 _107567).
Proof. exact (MK_COMB (@lem8125944 C D _107565 _107567 _107564 _107566) (@lem8125945 C D _107564 _107565 _107566 _107567)). Qed.
Lemma lem8125947 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : (term461 C D _107565 _107567 _107564 _107566) = (term476 C D _107564 _107565 _107566 _107567).
Proof. exact (TRANS (@lem8125929 C D _107564 _107565 _107566 _107567) (@lem8125946 C D _107564 _107565 _107566 _107567)). Qed.
Lemma lem8125949 {A B C D P : Type'} (g : type1514 C D P) (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term30 A B P p lt2 s a f g') : term477 A B C D P f y g' g a.
Proof. exact (conj (@lem8125827 A B C P z y p lt2 s a f g' h1 h2) (@lem8125836 C D P g a)). Qed.
Lemma lem8125951 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : term476 C D _107564 _107565 _107566 _107567.
Proof. exact (EQ_MP (@lem8125947 C D _107564 _107565 _107566 _107567) (@lem8125926 C D _107565 _107567 _107564 _107566)). Qed.
Lemma lem8125952 {C D : Type'} (_107564 : C -> D) (_107565 : C) (_107566 : C -> D) (_107567 : C) : term476 C D _107564 _107565 _107566 _107567.
Proof. exact (@lem8125951 C D _107564 _107565 _107566 _107567). Qed.
Lemma lem8125953 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : term478 A B C D P f g y g' a.
Proof. exact (@lem8125952 C D (@I (P -> C -> D) g a) (term291 A B C P y f a) (@I (P -> C -> D) g a) (term291 A B C P y g' a)). Qed.
Lemma lem8125956 {A B C D P : Type'} (g : type1514 C D P) (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term30 A B P p lt2 s a f g') : (term294 A B C D P g y f a) = (term294 A B C D P g y g' a).
Proof. exact (@lem8125953 A B C D P f g y g' a (@lem8125949 A B C D P g z y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8125957 {A B C D P : Type'} (g : type1514 C D P) (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term30 A B P p lt2 s a f g') : (term294 A B C D P g y f a) = (term294 A B C D P g y g' a).
Proof. exact (@lem8125956 A B C D P g z y p lt2 s a f g' h1 h2). Qed.
Lemma lem8125958 {A B C D P : Type'} (g : type1514 C D P) (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term30 A B P p lt2 s a f g') : term479 A B C D P f g y g' a.
Proof. exact (fun h0 : term296 A B C D P f g y g' a => @lem8125957 A B C D P g z y p lt2 s a f g' h1 h2). Qed.
Lemma lem8125960 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125961 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term479 A B C D P f g y g' a) = ((term294 A B C D P g y f a) = (term294 A B C D P g y g' a)).
Proof. exact (@lem8125960 ((term294 A B C D P g y f a) = (term294 A B C D P g y g' a))). Qed.
Lemma lem8125962 {A B C D P : Type'} (g : type1514 C D P) (z : type518 A B P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term30 A B P p lt2 s a f g') : (term294 A B C D P g y f a) = (term294 A B C D P g y g' a).
Proof. exact (EQ_MP (@lem8125961 A B C D P f g y g' a) (@lem8125958 A B C D P g z y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8125965 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8125967 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) : (term296 A B C D P f g y g' a) = (term480 A B C D P f g y g' a).
Proof. exact (@lem8125965 ((term294 A B C D P g y f a) = (term294 A B C D P g y g' a))). Qed.
Lemma lem8125970 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (y : type564 A B C P) (g' : A -> B) (a : P) (h1 : term116 A B C D P f g y g' a) : term480 A B C D P f g y g' a.
Proof. exact (EQ_MP (@lem8125967 A B C D P f g y g' a) (@lem8124949 A B C D P f g y g' a h1)). Qed.
Lemma lem8125973 {A B C D P : Type'} (z : type518 A B P) (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term116 A B C D P f g y g' a) (h3 : term30 A B P p lt2 s a f g') : False.
Proof. exact (@lem8125970 A B C D P f g y g' a h2 (@lem8125962 A B C D P g z y p lt2 s a f g' h1 h3)). Qed.
Lemma lem8125974 {A B C D P : Type'} (z : type518 A B P) (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term116 A B C D P f g y g' a) (h3 : term30 A B P p lt2 s a f g') : term481.
Proof. exact (fun h0 : ~ False => @lem8125973 A B C D P z g y p lt2 s a f g' h1 h2 h3). Qed.
Lemma lem8125976 (p : Prop) : (term378 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8125977 : term481 = False.
Proof. exact (@lem8125976 False). Qed.
Lemma lem8125978 {A B C D P : Type'} (z : type518 A B P) (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term266 A B C P p lt2 s z y) (h2 : term116 A B C D P f g y g' a) (h3 : term30 A B P p lt2 s a f g') : False.
Proof. exact (EQ_MP (@lem8125977) (@lem8125974 A B C D P z g y p lt2 s a f g' h1 h2 h3)). Qed.
Lemma lem8125979 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term24 A B C P p lt2 s y) (h2 : term116 A B C D P f g y g' a) (h3 : term30 A B P p lt2 s a f g') : False.
Proof. exact (ex_elim (@lem8124392 A B C P p lt2 s y h1) (fun z : type518 A B P => fun h0 : term268 A B C P p lt2 s y z => @lem8125978 A B C D P z g y p lt2 s a f g' h0 h2 h3)). Qed.
Lemma lem8125980 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term24 A B C P p lt2 s y) (h2 : term116 A B C D P f g y g' a) (h3 : term30 A B P p lt2 s a f g') : (term116 A B C D P f g y g' a) = False.
Proof. exact (prop_ext (fun h4 : term116 A B C D P f g y g' a => @lem8125979 A B C D P g y p lt2 s a f g' h1 h2 h3) (fun h4 : False => @lem8124469 A B C D P f g y g' a h2)). Qed.
Lemma lem8125981 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term24 A B C P p lt2 s y) (h2 : term116 A B C D P f g y g' a) (h3 : term30 A B P p lt2 s a f g') : False.
Proof. exact (EQ_MP (@lem8125980 A B C D P g y p lt2 s a f g' h1 h2 h3) (@lem8124469 A B C D P f g y g' a h2)). Qed.
Lemma lem8125982 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term24 A B C P p lt2 s y) (h2 : term116 A B C D P f g y g' a) (h3 : term30 A B P p lt2 s a f g') : (term116 A B C D P f g y g' a) = False.
Proof. exact (prop_ext (fun h4 : term116 A B C D P f g y g' a => @lem8125981 A B C D P g y p lt2 s a f g' h1 h2 h3) (fun h4 : False => @lem8124066 A B C D P f g y g' a h2)). Qed.
Lemma lem8125983 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term24 A B C P p lt2 s y) (h2 : term116 A B C D P f g y g' a) (h3 : term30 A B P p lt2 s a f g') : False.
Proof. exact (EQ_MP (@lem8125982 A B C D P g y p lt2 s a f g' h1 h2 h3) (@lem8124066 A B C D P f g y g' a h2)). Qed.
Lemma lem8125984 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term24 A B C P p lt2 s y) (h2 : term30 A B P p lt2 s a f g') : term115 A B C D P f g y g' a.
Proof. exact (fun h0 : term116 A B C D P f g y g' a => @lem8125983 A B C D P g y p lt2 s a f g' h1 h0 h2). Qed.
Lemma lem8125985 {A B C D P : Type'} (g : type1514 C D P) (y : type564 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g' : A -> B) (h1 : term24 A B C P p lt2 s y) (h2 : term30 A B P p lt2 s a f g') : (term49 A B C D P g y f a) = (term49 A B C D P g y g' a).
Proof. exact (EQ_MP (@lem8124065 A B C D P f g y g' a) (@lem8125984 A B C D P g y p lt2 s a f g' h1 h2)). Qed.
Lemma lem8125986 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (g' : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term24 A B C P p lt2 s y) : term58 A B C D P p lt2 s f g y g' a.
Proof. exact (fun h0 : term30 A B P p lt2 s a f g' => @lem8125985 A B C D P g y p lt2 s a f g' h1 h0). Qed.
Lemma lem8125991 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (g' : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term24 A B C P p lt2 s y) : term62 A B C D P p lt2 s f g y g'.
Proof. exact (fun a : P => @lem8125986 A B C D P f g g' a p lt2 s y h1). Qed.
Lemma lem8125996 {A B C D P : Type'} (f : A -> B) (g : type1514 C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term24 A B C P p lt2 s y) : term66 A B C D P p lt2 s f g y.
Proof. exact (fun g' : A -> B => @lem8125991 A B C D P f g g' p lt2 s y h1). Qed.
Lemma lem8126001 {A B C D P : Type'} (g : type1514 C D P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (y : type564 A B C P) (h1 : term24 A B C P p lt2 s y) : term69 A B C D P p lt2 s g y.
Proof. exact (fun f : A -> B => @lem8125996 A B C D P f g p lt2 s y h1). Qed.
Lemma lem8126002 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) (y : type564 A B C P) : term73 A B C D P p lt2 s g y.
Proof. exact (fun h0 : term24 A B C P p lt2 s y => @lem8126001 A B C D P g p lt2 s y h0). Qed.
Lemma lem8126007 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (g : type1514 C D P) : term77 A B C D P p lt2 s g.
Proof. exact (fun y : type564 A B C P => @lem8126002 A B C D P p lt2 s g y). Qed.
Lemma lem8126012 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : term81 A B C D P p lt2 s.
Proof. exact (fun g : type1514 C D P => @lem8126007 A B C D P p lt2 s g). Qed.
Lemma lem8126017 {A B C D P : Type'} (p : type560 A B P) (lt2 : type1402 A) : term85 A B C D P p lt2.
Proof. exact (fun s : P -> A => @lem8126012 A B C D P p lt2 s). Qed.
Lemma lem8126022 {A B C D P : Type'} (lt2 : type1402 A) : term89 A B C D P lt2.
Proof. exact (fun p : type560 A B P => @lem8126017 A B C D P p lt2). Qed.
Lemma lem8126027 {A B C D P : Type'} : term93 A B C D P.
Proof. exact (fun lt2 : type1402 A => @lem8126022 A B C D P lt2). Qed.
Lemma lem8126028 {A B C D P : Type'} : term95 A B C D P.
Proof. exact (EQ_MP (@lem8124059 A B C D P) (@lem8126027 A B C D P)). Qed.
Lemma lem8126030 {A B C D P : Type'} : term95 A B C D P.
Proof. exact (@lem8123802 A B C D P (@lem8126028 A B C D P)). Qed.
Lemma lem8126031 {A B C D P : Type'} (h1 : term96 A B C D P) : False.
Proof. exact (@lem8126030 A B C D P (@lem8123786 A B C D P h1)). Qed.
Lemma lem8126032 {A B C D P : Type'} (h1 : term96 A B C D P) : (term96 A B C D P) = False.
Proof. exact (prop_ext (fun h2 : term96 A B C D P => @lem8126031 A B C D P h1) (fun h2 : False => @lem8123786 A B C D P h1)). Qed.
Lemma lem8126033 {A B C D P : Type'} (h1 : term96 A B C D P) : False.
Proof. exact (EQ_MP (@lem8126032 A B C D P h1) (@lem8123786 A B C D P h1)). Qed.
Lemma lem8126034 {A B C D P : Type'} : term95 A B C D P.
Proof. exact (fun h0 : term96 A B C D P => @lem8126033 A B C D P h0). Qed.
Lemma lem8126035 {A B C D P : Type'} : term93 A B C D P.
Proof. exact (EQ_MP (@lem8123785 A B C D P) (@lem8126034 A B C D P)). Qed.
Lemma lem8126036 {A B C D P : Type'} : term92 A B C D P.
Proof. exact (EQ_MP (@lem8123781 A B C D P) (@lem8126035 A B C D P)). Qed.
