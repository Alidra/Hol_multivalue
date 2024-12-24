Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_MAXIMAL_SETS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_IN_GSPEC_spec.
Require Import FINITE_RESTRICT_spec.
Require Import FINITE_TRANSITIVITY_CHAIN_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IMP_spec.
Require Import PSUBSET_spec.
Require Import PSUBSET_TRANS_spec.
Require Import SUBSET_ANTISYM_EQ_spec.
Require Import SUBSET_PSUBSET_TRANS_spec.
Require Import SUBSET_RESTRICT_spec.
Require Import SUBSET_UNIONS_spec.
Require Import UNIONS_MONO_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem3743382 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3743383 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3743384 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3743383 t1) (@lem3743382 t1)). Qed.
Lemma lem3743385 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3743384 t1 t2). Qed.
Lemma lem3743386 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3743387 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3743386 t1 t2) (@lem3743385 t1 t2)). Qed.
Lemma lem3743388 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3743387 t1 t2 t3). Qed.
Lemma lem3743389 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3743390 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3743389 t1 t2 t3) (@lem3743388 t1 t2 t3)). Qed.
Lemma lem3743391 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3743390 t1 t2 t3)). Qed.
Lemma lem3743412 {A : Type'} : term7 A.
Proof. exact (@lem3743381 (A -> Prop)). Qed.
Lemma lem3743413 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem3743412 A (term9 A s)). Qed.
Lemma lem3743414 {A : Type'} (s : A -> Prop) : (term8 A s) = (term10 A s).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem3743415 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem3743414 A s) (@lem3743413 A s)). Qed.
Lemma lem3743416 {A : Type'} (f : type686 A) (s : A -> Prop) : term11 A f s.
Proof. exact (@lem3743415 A s (term12 A f s)). Qed.
Lemma lem3743417 {A : Type'} (f : type686 A) (s : A -> Prop) : (term11 A f s) = (term13 A f s).
Proof. exact (eq_refl (term11 A f s)). Qed.
Lemma lem3743418 {A : Type'} (f : type686 A) (s : A -> Prop) : term13 A f s.
Proof. exact (EQ_MP (@lem3743417 A f s) (@lem3743416 A f s)). Qed.
Lemma lem3743422 (t : Prop) : (term14 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3743423 (p : Prop) : (term14 p) = p.
Proof. exact (@lem3743422 p). Qed.
Lemma lem3743424 (p : Prop) : (@eq Prop p) = (@eq Prop p).
Proof. exact (eq_refl (@eq Prop p)). Qed.
Lemma lem3743425 (p : Prop) : (p = (term14 p)) = (p = p).
Proof. exact (MK_COMB (@lem3743424 p) (@lem3743423 p)). Qed.
Lemma lem3743427 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3743428 (x : Prop) : (x = x) = True.
Proof. exact (@lem3743427 Prop x). Qed.
Lemma lem3743429 (p : Prop) : (p = p) = True.
Proof. exact (@lem3743428 p). Qed.
Lemma lem3743430 (p : Prop) : (p = (term14 p)) = True.
Proof. exact (TRANS (@lem3743425 p) (@lem3743429 p)). Qed.
Lemma lem3743431 (p : Prop) : True = (p = (term14 p)).
Proof. exact (SYM (@lem3743430 p)). Qed.
Lemma lem3743456 {_89156 _89357 : Type'} (Q : _89357 -> Prop) : term15 _89156 _89357 Q.
Proof. exact (proj1 (@lem3449335 _89156 Prop Prop Prop Prop Prop _89357 Prop Prop Prop Prop Q)). Qed.
Lemma lem3743457 {_89156 _89357 : Type'} (Q : _89357 -> Prop) (P : _89156 -> Prop) : term16 _89156 _89357 Q P.
Proof. exact (@lem3743456 _89156 _89357 Q P). Qed.
Lemma lem3743458 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) : (term16 _89156 _89357 Q P) = (term17 _89156 _89357 P Q).
Proof. exact (eq_refl (term16 _89156 _89357 Q P)). Qed.
Lemma lem3743459 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) : term17 _89156 _89357 P Q.
Proof. exact (EQ_MP (@lem3743458 _89156 _89357 P Q) (@lem3743457 _89156 _89357 Q P)). Qed.
Lemma lem3743460 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : term18 _89156 _89357 P Q f.
Proof. exact (@lem3743459 _89156 _89357 P Q f). Qed.
Lemma lem3743461 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : (term18 _89156 _89357 P Q f) = ((term19 _89156 _89357 P f Q) = (term20 _89156 _89357 P Q f)).
Proof. exact (eq_refl (term18 _89156 _89357 P Q f)). Qed.
Lemma lem3743463 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term21 _87154 s t) : term21 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3743464 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term22 _87154 s t) : term22 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3743465 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term22 _87154 s t) (h2 : term21 _87154 s t) : term23 _87154 s t.
Proof. exact (@lem3743463 _87154 s t h2 (@lem3743464 _87154 s t h1)). Qed.
Lemma lem3743466 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term22 _87154 s t) : term24 _87154 s t.
Proof. exact (fun h0 : term21 _87154 s t => @lem3743465 _87154 s t h1 h0). Qed.
Lemma lem3743467 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term21 _87154 s t) : term21 _87154 s t.
Proof. exact (h1). Qed.
Lemma lem3743468 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term22 _87154 s t) (h2 : term21 _87154 s t) : term23 _87154 s t.
Proof. exact (@lem3743466 _87154 s t h1 (@lem3743467 _87154 s t h2)). Qed.
Lemma lem3743469 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) (h1 : term21 _87154 s t) : term21 _87154 s t.
Proof. exact (fun h0 : term22 _87154 s t => @lem3743468 _87154 s t h0 h1). Qed.
Lemma lem3743470 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term25 _87154 s t.
Proof. exact (fun h0 : term21 _87154 s t => @lem3743469 _87154 s t h0). Qed.
Lemma lem3743474 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term26 A t s) = (s = t)) : (term26 A t s) = (s = t).
Proof. exact (h1). Qed.
Lemma lem3743475 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term26 A t s) = (s = t)) : (s = t) = (term26 A t s).
Proof. exact (SYM (@lem3743474 A s t h1)). Qed.
Lemma lem3743476 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term26 A t s)) : (s = t) = (term26 A t s).
Proof. exact (h1). Qed.
Lemma lem3743477 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term26 A t s)) : (term26 A t s) = (s = t).
Proof. exact (SYM (@lem3743476 A t s h1)). Qed.
Lemma lem3743478 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term26 A t s) = (s = t)) = ((s = t) = (term26 A t s)).
Proof. exact (prop_ext (fun h1 : (term26 A t s) = (s = t) => @lem3743475 A s t h1) (fun h1 : (s = t) = (term26 A t s) => @lem3743477 A t s h1)). Qed.
Lemma lem3743479 {A : Type'} (s : A -> Prop) : (term27 A s) = (term28 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3743478 A t s)). Qed.
Lemma lem3743480 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3743481 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem3743480 A) (@lem3743479 A s)). Qed.
Lemma lem3743482 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3743481 A s)). Qed.
Lemma lem3743483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3743484 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (MK_COMB (@lem3743483 A) (@lem3743482 A)). Qed.
Lemma lem3743485 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem3743484 A) (@lem3219910 A)). Qed.
Lemma lem3743486 {_84465 : Type'} (s : _84465 -> Prop) : term35 _84465 s.
Proof. exact (@lem3221162 _84465 s). Qed.
Lemma lem3743487 {_84465 : Type'} (s : _84465 -> Prop) : (term35 _84465 s) = (term36 _84465 s).
Proof. exact (eq_refl (term35 _84465 s)). Qed.
Lemma lem3743488 {_84465 : Type'} (s : _84465 -> Prop) : term36 _84465 s.
Proof. exact (EQ_MP (@lem3743487 _84465 s) (@lem3743486 _84465 s)). Qed.
Lemma lem3743489 {_84465 : Type'} (s : _84465 -> Prop) (P : _84465 -> Prop) : term37 _84465 s P.
Proof. exact (@lem3743488 _84465 s P). Qed.
Lemma lem3743490 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term37 _84465 s P) = (term38 _84465 P s).
Proof. exact (eq_refl (term37 _84465 s P)). Qed.
Lemma lem3743491 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : term38 _84465 P s.
Proof. exact (EQ_MP (@lem3743490 _84465 P s) (@lem3743489 _84465 s P)). Qed.
Lemma lem3743492 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term38 _84465 P s) = ((term38 _84465 P s) = True).
Proof. exact (@lem7 (term38 _84465 P s)). Qed.
Lemma lem3743494 {_87075 : Type'} (f : type686 _87075) : term39 _87075 f.
Proof. exact (@lem3343813 _87075 f). Qed.
Lemma lem3743495 {_87075 : Type'} (f : type686 _87075) : (term39 _87075 f) = (term40 _87075 f).
Proof. exact (eq_refl (term39 _87075 f)). Qed.
Lemma lem3743496 {_87075 : Type'} (f : type686 _87075) : term40 _87075 f.
Proof. exact (EQ_MP (@lem3743495 _87075 f) (@lem3743494 _87075 f)). Qed.
Lemma lem3743497 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : term41 _87075 f g.
Proof. exact (@lem3743496 _87075 f g). Qed.
Lemma lem3743498 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term41 _87075 f g) = (term42 _87075 f g).
Proof. exact (eq_refl (term41 _87075 f g)). Qed.
Lemma lem3743499 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : term42 _87075 f g.
Proof. exact (EQ_MP (@lem3743498 _87075 f g) (@lem3743497 _87075 f g)). Qed.
Lemma lem3743500 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (h1 : @SUBSET (_87075 -> Prop) f g) : @SUBSET (_87075 -> Prop) f g.
Proof. exact (h1). Qed.
Lemma lem3743501 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (h1 : @SUBSET (_87075 -> Prop) f g) : term23 _87075 f g.
Proof. exact (@lem3743499 _87075 f g (@lem3743500 _87075 f g h1)). Qed.
Lemma lem3743502 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : (term23 _87075 f g) = ((term23 _87075 f g) = True).
Proof. exact (@lem7 (term23 _87075 f g)). Qed.
Lemma lem3743503 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) (h1 : @SUBSET (_87075 -> Prop) f g) : (term23 _87075 f g) = True.
Proof. exact (EQ_MP (@lem3743502 _87075 f g) (@lem3743501 _87075 f g h1)). Qed.
Lemma lem3743509 {A : Type'} (s : A -> Prop) : term43 A s.
Proof. exact (@lem3743485 A s). Qed.
Lemma lem3743510 {A : Type'} (s : A -> Prop) : (term43 A s) = (term30 A s).
Proof. exact (eq_refl (term43 A s)). Qed.
Lemma lem3743511 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (EQ_MP (@lem3743510 A s) (@lem3743509 A s)). Qed.
Lemma lem3743512 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term44 A s t.
Proof. exact (@lem3743511 A s t). Qed.
Lemma lem3743513 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A s t) = ((s = t) = (term26 A t s)).
Proof. exact (eq_refl (term44 A s t)). Qed.
Lemma lem3743522 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term45 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3743523 (p : Prop) (q : Prop) (p' : Prop) : term46 p q p'.
Proof. exact (fun q' : Prop => @lem3743522 p q p' q'). Qed.
Lemma lem3743524 (p : Prop) (q : Prop) : term47 p q.
Proof. exact (fun p' : Prop => @lem3743523 p q p'). Qed.
Lemma lem3743525 {A : Type'} (f : type686 A) : term48 A f.
Proof. exact (@lem3743524 (@FINITE (A -> Prop) f) ((term49 A f) = (@UNIONS A f))). Qed.
Lemma lem3743526 {A : Type'} (f : type686 A) (p' : Prop) : term50 A f p'.
Proof. exact (@lem3743525 A f p'). Qed.
Lemma lem3743527 {A : Type'} (f : type686 A) (p' : Prop) : (term50 A f p') = (term51 A f p').
Proof. exact (eq_refl (term50 A f p')). Qed.
Lemma lem3743528 {A : Type'} (f : type686 A) (p' : Prop) : term51 A f p'.
Proof. exact (EQ_MP (@lem3743527 A f p') (@lem3743526 A f p')). Qed.
Lemma lem3743529 {A : Type'} (f : type686 A) (p' : Prop) (q' : Prop) : term52 A f p' q'.
Proof. exact (@lem3743528 A f p' q'). Qed.
Lemma lem3743530 {A : Type'} (f : type686 A) (p' : Prop) (q' : Prop) : (term52 A f p' q') = (term53 A f p' q').
Proof. exact (eq_refl (term52 A f p' q')). Qed.
Lemma lem3743531 {A : Type'} (f : type686 A) (p' : Prop) (q' : Prop) : term53 A f p' q'.
Proof. exact (EQ_MP (@lem3743530 A f p' q') (@lem3743529 A f p' q')). Qed.
Lemma lem3743532 {A : Type'} (f : type686 A) : (@FINITE (A -> Prop) f) = (@FINITE (A -> Prop) f).
Proof. exact (eq_refl (@FINITE (A -> Prop) f)). Qed.
Lemma lem3743533 {A : Type'} (f : type686 A) (q' : Prop) : term54 A f q'.
Proof. exact (@lem3743531 A f (@FINITE (A -> Prop) f) q'). Qed.
Lemma lem3743534 {A : Type'} (f : type686 A) (q' : Prop) : term55 A f q'.
Proof. exact (@lem3743533 A f q' (@lem3743532 A f)). Qed.
Lemma lem3743541 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term26 A t s).
Proof. exact (EQ_MP (@lem3743513 A t s) (@lem3743512 A s t)). Qed.
Lemma lem3743542 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term26 A t s).
Proof. exact (@lem3743541 A t s). Qed.
Lemma lem3743543 {A : Type'} (f : type686 A) : ((term49 A f) = (@UNIONS A f)) = (term56 A f).
Proof. exact (@lem3743542 A (@UNIONS A f) (term49 A f)). Qed.
Lemma lem3743547 {_87075 : Type'} (f : type686 _87075) (g : type686 _87075) : term57 _87075 f g.
Proof. exact (fun h0 : @SUBSET (_87075 -> Prop) f g => @lem3743503 _87075 f g h0). Qed.
Lemma lem3743548 {A : Type'} (f : type686 A) (g : type686 A) : term57 A f g.
Proof. exact (@lem3743547 A f g). Qed.
Lemma lem3743549 {A : Type'} (f : type686 A) : term58 A f.
Proof. exact (@lem3743548 A (term59 A f) f). Qed.
Lemma lem3743551 {_84465 : Type'} (P : _84465 -> Prop) (s : _84465 -> Prop) : (term38 _84465 P s) = True.
Proof. exact (EQ_MP (@lem3743492 _84465 P s) (@lem3743491 _84465 P s)). Qed.
Lemma lem3743552 {A : Type'} (P : type686 A) (s : type686 A) : (term60 A P s) = True.
Proof. exact (@lem3743551 (A -> Prop) P s). Qed.
Lemma lem3743553 {A : Type'} (f : type686 A) : (term61 A f) = True.
Proof. exact (@lem3743552 A (term62 A f) f). Qed.
Lemma lem3743554 {A : Type'} (f : type686 A) (t : A -> Prop) : (term63 A f t) = (term64 A f t).
Proof. exact (eq_refl (term63 A f t)). Qed.
Lemma lem3743555 {A : Type'} (t : A -> Prop) (f : type686 A) : (term65 A t f) = (term65 A t f).
Proof. exact (eq_refl (term65 A t f)). Qed.
Lemma lem3743556 {A : Type'} (f : type686 A) (t : A -> Prop) : (term66 A f t) = (term67 A f t).
Proof. exact (MK_COMB (@lem3743555 A t f) (@lem3743554 A f t)). Qed.
Lemma lem3743557 {A : Type'} (GEN_PVAR_104 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_104) = (@SETSPEC (A -> Prop) GEN_PVAR_104).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_104)). Qed.
Lemma lem3743558 {A : Type'} (GEN_PVAR_104 : A -> Prop) (f : type686 A) (t : A -> Prop) : (term68 A GEN_PVAR_104 f t) = (term69 A GEN_PVAR_104 f t).
Proof. exact (MK_COMB (@lem3743557 A GEN_PVAR_104) (@lem3743556 A f t)). Qed.
Lemma lem3743559 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3743560 {A : Type'} (GEN_PVAR_104 : A -> Prop) (f : type686 A) (t : A -> Prop) : (term70 A GEN_PVAR_104 f t) = (term71 A GEN_PVAR_104 f t).
Proof. exact (MK_COMB (@lem3743558 A GEN_PVAR_104 f t) (@lem3743559 A t)). Qed.
Lemma lem3743561 {A : Type'} (GEN_PVAR_104 : A -> Prop) (f : type686 A) : (term72 A GEN_PVAR_104 f) = (term73 A GEN_PVAR_104 f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3743560 A GEN_PVAR_104 f t)). Qed.
Lemma lem3743562 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3743563 {A : Type'} (GEN_PVAR_104 : A -> Prop) (f : type686 A) : (term74 A GEN_PVAR_104 f) = (term75 A GEN_PVAR_104 f).
Proof. exact (MK_COMB (@lem3743562 A) (@lem3743561 A GEN_PVAR_104 f)). Qed.
Lemma lem3743564 {A : Type'} (f : type686 A) : (term76 A f) = (term77 A f).
Proof. exact (fun_ext (fun GEN_PVAR_104 : A -> Prop => @lem3743563 A GEN_PVAR_104 f)). Qed.
Lemma lem3743565 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3743566 {A : Type'} (f : type686 A) : (term78 A f) = (term59 A f).
Proof. exact (MK_COMB (@lem3743565 A) (@lem3743564 A f)). Qed.
Lemma lem3743567 {A : Type'} : (@SUBSET (A -> Prop)) = (@SUBSET (A -> Prop)).
Proof. exact (eq_refl (@SUBSET (A -> Prop))). Qed.
Lemma lem3743568 {A : Type'} (f : type686 A) : (term79 A f) = (term80 A f).
Proof. exact (MK_COMB (@lem3743567 A) (@lem3743566 A f)). Qed.
Lemma lem3743569 {A : Type'} (f : type686 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3743570 {A : Type'} (f : type686 A) : (term61 A f) = (term81 A f).
Proof. exact (MK_COMB (@lem3743568 A f) (@lem3743569 A f)). Qed.
Lemma lem3743571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3743572 {A : Type'} (f : type686 A) : (term82 A f) = (term83 A f).
Proof. exact (MK_COMB (@lem3743571) (@lem3743570 A f)). Qed.
Lemma lem3743573 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem3743574 {A : Type'} (f : type686 A) : ((term61 A f) = True) = ((term81 A f) = True).
Proof. exact (MK_COMB (@lem3743572 A f) (@lem3743573)). Qed.
Lemma lem3743575 {A : Type'} (f : type686 A) : (term81 A f) = True.
Proof. exact (EQ_MP (@lem3743574 A f) (@lem3743553 A f)). Qed.
Lemma lem3743576 {A : Type'} (f : type686 A) : True = (term81 A f).
Proof. exact (SYM (@lem3743575 A f)). Qed.
Lemma lem3743577 {A : Type'} (f : type686 A) : term81 A f.
Proof. exact (EQ_MP (@lem3743576 A f) (@lem0)). Qed.
Lemma lem3743578 {A : Type'} (f : type686 A) : (term84 A f) = True.
Proof. exact (@lem3743549 A f (@lem3743577 A f)). Qed.
Lemma lem3743579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3743580 {A : Type'} (f : type686 A) : (term85 A f) = (and True).
Proof. exact (MK_COMB (@lem3743579) (@lem3743578 A f)). Qed.
Lemma lem3743653 {A : Type'} (f : type686 A) : (term86 A f) = (term86 A f).
Proof. exact (eq_refl (term86 A f)). Qed.
Lemma lem3743654 {A : Type'} (f : type686 A) : (term56 A f) = (term87 A f).
Proof. exact (MK_COMB (@lem3743580 A f) (@lem3743653 A f)). Qed.
Lemma lem3743656 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3743657 {A : Type'} (f : type686 A) : (term87 A f) = (term86 A f).
Proof. exact (@lem3743656 (term86 A f)). Qed.
Lemma lem3743730 {A : Type'} (f : type686 A) : (term56 A f) = (term86 A f).
Proof. exact (TRANS (@lem3743654 A f) (@lem3743657 A f)). Qed.
Lemma lem3743731 {A : Type'} (f : type686 A) : ((term49 A f) = (@UNIONS A f)) = (term86 A f).
Proof. exact (TRANS (@lem3743543 A f) (@lem3743730 A f)). Qed.
Lemma lem3743732 {A : Type'} (f : type686 A) : term88 A f.
Proof. exact (fun h0 : @FINITE (A -> Prop) f => @lem3743731 A f). Qed.
Lemma lem3743733 {A : Type'} (f : type686 A) : term89 A f.
Proof. exact (@lem3743534 A f (term86 A f)). Qed.
Lemma lem3743734 {A : Type'} (f : type686 A) : (term90 A f) = (term91 A f).
Proof. exact (@lem3743733 A f (@lem3743732 A f)). Qed.
Lemma lem3743902 {A : Type'} : (term92 A) = (term93 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3743734 A f)). Qed.
Lemma lem3744070 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3744071 {A : Type'} : (term94 A) = (term95 A).
Proof. exact (MK_COMB (@lem3744070 A) (@lem3743902 A)). Qed.
Lemma lem3744243 {A : Type'} : (term95 A) = (term94 A).
Proof. exact (SYM (@lem3744071 A)). Qed.
Lemma lem3744244 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : @FINITE (A -> Prop) f.
Proof. exact (h1). Qed.
Lemma lem3744246 {_87154 : Type'} (s : type686 _87154) (t : type686 _87154) : term21 _87154 s t.
Proof. exact (@lem3743470 _87154 s t (@lem3348272 _87154 s t)). Qed.
Lemma lem3744247 {A : Type'} (s : type686 A) (t : type686 A) : term21 A s t.
Proof. exact (@lem3744246 A s t). Qed.
Lemma lem3744248 {A : Type'} (f : type686 A) : term96 A f.
Proof. exact (@lem3744247 A f (term59 A f)). Qed.
Lemma lem3744249 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) s f) : @IN (A -> Prop) s f.
Proof. exact (h1). Qed.
Lemma lem3744251 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : (term19 _89156 _89357 P f Q) = (term20 _89156 _89357 P Q f).
Proof. exact (EQ_MP (@lem3743461 _89156 _89357 P Q f) (@lem3743460 _89156 _89357 P Q f)). Qed.
Lemma lem3744252 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term97 A P f Q) = (term98 A P Q f).
Proof. exact (@lem3744251 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem3744253 {A : Type'} (f : type686 A) (s : A -> Prop) : (term99 A f s) = (term100 A f s).
Proof. exact (@lem3744252 A (term101 A f) (term102 A s) (term103 A)). Qed.
Lemma lem3744254 {A : Type'} (f : type686 A) (t : A -> Prop) : (term104 A f t) = (term67 A f t).
Proof. exact (eq_refl (term104 A f t)). Qed.
Lemma lem3744255 {A : Type'} (GEN_PVAR_104 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_104) = (@SETSPEC (A -> Prop) GEN_PVAR_104).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_104)). Qed.
Lemma lem3744256 {A : Type'} (GEN_PVAR_104 : A -> Prop) (f : type686 A) (t : A -> Prop) : (term105 A GEN_PVAR_104 f t) = (term69 A GEN_PVAR_104 f t).
Proof. exact (MK_COMB (@lem3744255 A GEN_PVAR_104) (@lem3744254 A f t)). Qed.
Lemma lem3744257 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3744258 {A : Type'} (GEN_PVAR_104 : A -> Prop) (f : type686 A) (t : A -> Prop) : (term107 A GEN_PVAR_104 f t) = (term71 A GEN_PVAR_104 f t).
Proof. exact (MK_COMB (@lem3744256 A GEN_PVAR_104 f t) (@lem3744257 A t)). Qed.
Lemma lem3744259 {A : Type'} (GEN_PVAR_104 : A -> Prop) (f : type686 A) : (term108 A GEN_PVAR_104 f) = (term73 A GEN_PVAR_104 f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744258 A GEN_PVAR_104 f t)). Qed.
Lemma lem3744260 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3744261 {A : Type'} (GEN_PVAR_104 : A -> Prop) (f : type686 A) : (term109 A GEN_PVAR_104 f) = (term75 A GEN_PVAR_104 f).
Proof. exact (MK_COMB (@lem3744260 A) (@lem3744259 A GEN_PVAR_104 f)). Qed.
Lemma lem3744262 {A : Type'} (f : type686 A) : (term110 A f) = (term77 A f).
Proof. exact (fun_ext (fun GEN_PVAR_104 : A -> Prop => @lem3744261 A GEN_PVAR_104 f)). Qed.
Lemma lem3744263 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3744264 {A : Type'} (f : type686 A) : (term111 A f) = (term59 A f).
Proof. exact (MK_COMB (@lem3744263 A) (@lem3744262 A f)). Qed.
Lemma lem3744265 {A : Type'} (y : A -> Prop) : (@IN (A -> Prop) y) = (@IN (A -> Prop) y).
Proof. exact (eq_refl (@IN (A -> Prop) y)). Qed.
Lemma lem3744266 {A : Type'} (y : A -> Prop) (f : type686 A) : (term112 A y f) = (term113 A y f).
Proof. exact (MK_COMB (@lem3744265 A y) (@lem3744264 A f)). Qed.
Lemma lem3744267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3744268 {A : Type'} (y : A -> Prop) (f : type686 A) : (term114 A y f) = (term115 A y f).
Proof. exact (MK_COMB (@lem3744267) (@lem3744266 A y f)). Qed.
Lemma lem3744269 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term116 A s y) = (@SUBSET A s y).
Proof. exact (eq_refl (term116 A s y)). Qed.
Lemma lem3744270 {A : Type'} (f : type686 A) (s : A -> Prop) (y : A -> Prop) : (term117 A f s y) = (term118 A f s y).
Proof. exact (MK_COMB (@lem3744268 A y f) (@lem3744269 A s y)). Qed.
Lemma lem3744271 {A : Type'} (f : type686 A) (s : A -> Prop) : (term119 A f s) = (term120 A f s).
Proof. exact (fun_ext (fun y : A -> Prop => @lem3744270 A f s y)). Qed.
Lemma lem3744272 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3744273 {A : Type'} (f : type686 A) (s : A -> Prop) : (term99 A f s) = (term121 A f s).
Proof. exact (MK_COMB (@lem3744272 A) (@lem3744271 A f s)). Qed.
Lemma lem3744274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3744275 {A : Type'} (f : type686 A) (s : A -> Prop) : (term122 A f s) = (term123 A f s).
Proof. exact (MK_COMB (@lem3744274) (@lem3744273 A f s)). Qed.
Lemma lem3744276 {A : Type'} (f : type686 A) (t : A -> Prop) : (term104 A f t) = (term67 A f t).
Proof. exact (eq_refl (term104 A f t)). Qed.
Lemma lem3744277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3744278 {A : Type'} (f : type686 A) (t : A -> Prop) : (term124 A f t) = (term125 A f t).
Proof. exact (MK_COMB (@lem3744277) (@lem3744276 A f t)). Qed.
Lemma lem3744279 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term127 A s t).
Proof. exact (eq_refl (term126 A s t)). Qed.
Lemma lem3744280 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term128 A f s t) = (term129 A f s t).
Proof. exact (MK_COMB (@lem3744278 A f t) (@lem3744279 A s t)). Qed.
Lemma lem3744281 {A : Type'} (f : type686 A) (s : A -> Prop) : (term130 A f s) = (term131 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744280 A f s t)). Qed.
Lemma lem3744282 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3744283 {A : Type'} (f : type686 A) (s : A -> Prop) : (term100 A f s) = (term132 A f s).
Proof. exact (MK_COMB (@lem3744282 A) (@lem3744281 A f s)). Qed.
Lemma lem3744284 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term99 A f s) = (term100 A f s)) = ((term121 A f s) = (term132 A f s)).
Proof. exact (MK_COMB (@lem3744275 A f s) (@lem3744283 A f s)). Qed.
Lemma lem3744285 {A : Type'} (f : type686 A) (s : A -> Prop) : (term121 A f s) = (term132 A f s).
Proof. exact (EQ_MP (@lem3744284 A f s) (@lem3744253 A f s)). Qed.
Lemma lem3744301 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744302 {A : Type'} (f : type672 A) (y : A -> Prop) : (term134 A f y) = (f y).
Proof. exact (@lem3744301 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem3744303 {A : Type'} (t : A -> Prop) : (term135 A t) = (term106 A t).
Proof. exact (@lem3744302 A (term103 A) t). Qed.
Lemma lem3744304 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3744305 {A : Type'} : (term136 A) = (term103 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744304 A t)). Qed.
Lemma lem3744306 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3744307 {A : Type'} (t : A -> Prop) : (term135 A t) = (term106 A t).
Proof. exact (MK_COMB (@lem3744305 A) (@lem3744306 A t)). Qed.
Lemma lem3744308 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3744309 {A : Type'} (t : A -> Prop) : (term137 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem3744308 A) (@lem3744307 A t)). Qed.
Lemma lem3744310 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3744311 {A : Type'} (t : A -> Prop) : ((term135 A t) = (term106 A t)) = ((term106 A t) = t).
Proof. exact (MK_COMB (@lem3744309 A t) (@lem3744310 A t)). Qed.
Lemma lem3744312 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem3744311 A t) (@lem3744303 A t)). Qed.
Lemma lem3744313 {A : Type'} (s : A -> Prop) : (@SUBSET A s) = (@SUBSET A s).
Proof. exact (eq_refl (@SUBSET A s)). Qed.
Lemma lem3744314 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term127 A s t) = (@SUBSET A s t).
Proof. exact (MK_COMB (@lem3744313 A s) (@lem3744312 A t)). Qed.
Lemma lem3744315 {A : Type'} (f : type686 A) (t : A -> Prop) : (term125 A f t) = (term125 A f t).
Proof. exact (eq_refl (term125 A f t)). Qed.
Lemma lem3744316 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term129 A f s t) = (term139 A f s t).
Proof. exact (MK_COMB (@lem3744315 A f t) (@lem3744314 A s t)). Qed.
Lemma lem3744319 {A : Type'} (f : type686 A) (s : A -> Prop) : (term131 A f s) = (term140 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744316 A f s t)). Qed.
Lemma lem3744320 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3744321 {A : Type'} (f : type686 A) (s : A -> Prop) : (term132 A f s) = (term141 A f s).
Proof. exact (MK_COMB (@lem3744320 A) (@lem3744319 A f s)). Qed.
Lemma lem3744326 {A : Type'} (f : type686 A) (s : A -> Prop) : (term121 A f s) = (term141 A f s).
Proof. exact (TRANS (@lem3744285 A f s) (@lem3744321 A f s)). Qed.
Lemma lem3744327 {A : Type'} (f : type686 A) (s : A -> Prop) : (term141 A f s) = (term121 A f s).
Proof. exact (SYM (@lem3744326 A f s)). Qed.
Lemma lem3744329 (p : Prop) : p = (term14 p).
Proof. exact (EQ_MP (@lem3743431 p) (@lem0)). Qed.
Lemma lem3744330 {A : Type'} (f : type686 A) (s : A -> Prop) : (term141 A f s) = (term142 A f s).
Proof. exact (@lem3744329 (term141 A f s)). Qed.
Lemma lem3744331 {A : Type'} (f : type686 A) (s : A -> Prop) : (term142 A f s) = (term141 A f s).
Proof. exact (SYM (@lem3744330 A f s)). Qed.
Lemma lem3744332 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term143 A f s) : term143 A f s.
Proof. exact (h1). Qed.
Lemma lem3744356 {_89156 _89357 : Type'} (Q : _89357 -> Prop) : term15 _89156 _89357 Q.
Proof. exact (proj1 (@lem3449335 _89156 Prop Prop Prop Prop Prop _89357 Prop Prop Prop Prop Q)). Qed.
Lemma lem3744357 {_89156 _89357 : Type'} (Q : _89357 -> Prop) (P : _89156 -> Prop) : term16 _89156 _89357 Q P.
Proof. exact (@lem3744356 _89156 _89357 Q P). Qed.
Lemma lem3744358 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) : (term16 _89156 _89357 Q P) = (term17 _89156 _89357 P Q).
Proof. exact (eq_refl (term16 _89156 _89357 Q P)). Qed.
Lemma lem3744359 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) : term17 _89156 _89357 P Q.
Proof. exact (EQ_MP (@lem3744358 _89156 _89357 P Q) (@lem3744357 _89156 _89357 Q P)). Qed.
Lemma lem3744360 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : term18 _89156 _89357 P Q f.
Proof. exact (@lem3744359 _89156 _89357 P Q f). Qed.
Lemma lem3744361 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : (term18 _89156 _89357 P Q f) = ((term19 _89156 _89357 P f Q) = (term20 _89156 _89357 P Q f)).
Proof. exact (eq_refl (term18 _89156 _89357 P Q f)). Qed.
Lemma lem3744386 {_88905 _89106 : Type'} (Q : _89106 -> Prop) : term144 _88905 _89106 Q.
Proof. exact (proj1 (@lem3435744 _88905 Prop Prop Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem3744387 {_88905 _89106 : Type'} (Q : _89106 -> Prop) (P : _88905 -> Prop) : term145 _88905 _89106 Q P.
Proof. exact (@lem3744386 _88905 _89106 Q P). Qed.
Lemma lem3744388 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : (term145 _88905 _89106 Q P) = (term146 _88905 _89106 P Q).
Proof. exact (eq_refl (term145 _88905 _89106 Q P)). Qed.
Lemma lem3744389 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : term146 _88905 _89106 P Q.
Proof. exact (EQ_MP (@lem3744388 _88905 _89106 P Q) (@lem3744387 _88905 _89106 Q P)). Qed.
Lemma lem3744390 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : term147 _88905 _89106 P Q f.
Proof. exact (@lem3744389 _88905 _89106 P Q f). Qed.
Lemma lem3744391 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term147 _88905 _89106 P Q f) = ((term148 _88905 _89106 P f Q) = (term149 _88905 _89106 P Q f)).
Proof. exact (eq_refl (term147 _88905 _89106 P Q f)). Qed.
Lemma lem3744393 {A : Type'} (s : A -> Prop) : term150 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem3744394 {A : Type'} (s : A -> Prop) : (term150 A s) = (term151 A s).
Proof. exact (eq_refl (term150 A s)). Qed.
Lemma lem3744395 {A : Type'} (s : A -> Prop) : term151 A s.
Proof. exact (EQ_MP (@lem3744394 A s) (@lem3744393 A s)). Qed.
Lemma lem3744396 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term152 A s P.
Proof. exact (@lem3744395 A s P). Qed.
Lemma lem3744397 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term152 A s P) = (term153 A s P).
Proof. exact (eq_refl (term152 A s P)). Qed.
Lemma lem3744398 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term153 A s P.
Proof. exact (EQ_MP (@lem3744397 A s P) (@lem3744396 A s P)). Qed.
Lemma lem3744399 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3744400 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term154 A s P.
Proof. exact (@lem3744398 A s P (@lem3744399 A s h1)). Qed.
Lemma lem3744401 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term154 A s P) = ((term154 A s P) = True).
Proof. exact (@lem7 (term154 A s P)). Qed.
Lemma lem3744402 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term154 A s P) = True.
Proof. exact (EQ_MP (@lem3744401 A s P) (@lem3744400 A P s h1)). Qed.
Lemma lem3744408 (t1 : Prop) : term155 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem3744409 (t1 : Prop) : (term155 t1) = (term156 t1).
Proof. exact (eq_refl (term155 t1)). Qed.
Lemma lem3744410 (t1 : Prop) : term156 t1.
Proof. exact (EQ_MP (@lem3744409 t1) (@lem3744408 t1)). Qed.
Lemma lem3744411 (t1 : Prop) (t2 : Prop) : term157 t1 t2.
Proof. exact (@lem3744410 t1 t2). Qed.
Lemma lem3744412 (t1 : Prop) (t2 : Prop) : (term157 t1 t2) = ((term158 t1 t2) = (term159 t1 t2)).
Proof. exact (eq_refl (term157 t1 t2)). Qed.
Lemma lem3744414 {A : Type'} (f : type686 A) : (@FINITE (A -> Prop) f) = ((@FINITE (A -> Prop) f) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) f)). Qed.
Lemma lem3744421 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem3744422 {A : Type'} (f : type686 A) (s : A -> Prop) : (term160 A f s) = (term161 A f s).
Proof. exact (@lem3744421 (term13 A f s)). Qed.
Lemma lem3744424 (t1 : Prop) (t2 : Prop) : (term158 t1 t2) = (term159 t1 t2).
Proof. exact (EQ_MP (@lem3744412 t1 t2) (@lem3744411 t1 t2)). Qed.
Lemma lem3744425 {A : Type'} (f : type686 A) (s : A -> Prop) : (term161 A f s) = (term162 A f s).
Proof. exact (@lem3744424 (term163 A f s) ((term12 A f s) = (@EMPTY (A -> Prop)))). Qed.
Lemma lem3744431 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term164 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem3744402 A P s h0). Qed.
Lemma lem3744432 {A : Type'} (s : type686 A) (P : type686 A) : term165 A s P.
Proof. exact (@lem3744431 (A -> Prop) s P). Qed.
Lemma lem3744433 {A : Type'} (f : type686 A) (s : A -> Prop) : term166 A f s.
Proof. exact (@lem3744432 A f (term102 A s)). Qed.
Lemma lem3744434 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (@SUBSET A s t).
Proof. exact (eq_refl (term116 A s t)). Qed.
Lemma lem3744435 {A : Type'} (t : A -> Prop) (f : type686 A) : (term65 A t f) = (term65 A t f).
Proof. exact (eq_refl (term65 A t f)). Qed.
Lemma lem3744436 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term167 A f s t) = (term168 A f s t).
Proof. exact (MK_COMB (@lem3744435 A t f) (@lem3744434 A s t)). Qed.
Lemma lem3744437 {A : Type'} (GEN_PVAR_103 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_103) = (@SETSPEC (A -> Prop) GEN_PVAR_103).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_103)). Qed.
Lemma lem3744438 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term169 A GEN_PVAR_103 f s t) = (term170 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3744437 A GEN_PVAR_103) (@lem3744436 A f s t)). Qed.
Lemma lem3744439 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3744440 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term171 A GEN_PVAR_103 f s t) = (term172 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3744438 A GEN_PVAR_103 f s t) (@lem3744439 A t)). Qed.
Lemma lem3744441 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term173 A GEN_PVAR_103 f s) = (term174 A GEN_PVAR_103 f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744440 A GEN_PVAR_103 f s t)). Qed.
Lemma lem3744442 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3744443 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term175 A GEN_PVAR_103 f s) = (term176 A GEN_PVAR_103 f s).
Proof. exact (MK_COMB (@lem3744442 A) (@lem3744441 A GEN_PVAR_103 f s)). Qed.
Lemma lem3744444 {A : Type'} (f : type686 A) (s : A -> Prop) : (term177 A f s) = (term178 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_103 : A -> Prop => @lem3744443 A GEN_PVAR_103 f s)). Qed.
Lemma lem3744445 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3744446 {A : Type'} (f : type686 A) (s : A -> Prop) : (term179 A f s) = (term12 A f s).
Proof. exact (MK_COMB (@lem3744445 A) (@lem3744444 A f s)). Qed.
Lemma lem3744447 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem3744448 {A : Type'} (f : type686 A) (s : A -> Prop) : (term180 A f s) = (term181 A f s).
Proof. exact (MK_COMB (@lem3744447 A) (@lem3744446 A f s)). Qed.
Lemma lem3744449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3744450 {A : Type'} (f : type686 A) (s : A -> Prop) : (term182 A f s) = (term183 A f s).
Proof. exact (MK_COMB (@lem3744449) (@lem3744448 A f s)). Qed.
Lemma lem3744451 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem3744452 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term180 A f s) = True) = ((term181 A f s) = True).
Proof. exact (MK_COMB (@lem3744450 A f s) (@lem3744451)). Qed.
Lemma lem3744453 {A : Type'} (f : type686 A) : (term184 A f) = (term184 A f).
Proof. exact (eq_refl (term184 A f)). Qed.
Lemma lem3744454 {A : Type'} (f : type686 A) (s : A -> Prop) : (term166 A f s) = (term185 A f s).
Proof. exact (MK_COMB (@lem3744453 A f) (@lem3744452 A f s)). Qed.
Lemma lem3744455 {A : Type'} (f : type686 A) (s : A -> Prop) : term185 A f s.
Proof. exact (EQ_MP (@lem3744454 A f s) (@lem3744433 A f s)). Qed.
Lemma lem3744457 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (@FINITE (A -> Prop) f) = True.
Proof. exact (EQ_MP (@lem3744414 A f) (@lem3744244 A f h1)). Qed.
Lemma lem3744458 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : True = (@FINITE (A -> Prop) f).
Proof. exact (SYM (@lem3744457 A f h1)). Qed.
Lemma lem3744459 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : @FINITE (A -> Prop) f.
Proof. exact (EQ_MP (@lem3744458 A f h1) (@lem0)). Qed.
Lemma lem3744460 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term181 A f s) = True.
Proof. exact (@lem3744455 A f s (@lem3744459 A f h1)). Qed.
Lemma lem3744461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3744462 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term186 A f s) = (and True).
Proof. exact (MK_COMB (@lem3744461) (@lem3744460 A s f h1)). Qed.
Lemma lem3744470 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744471 {A : Type'} (f : type639 A) (y : A -> Prop) : (term187 A f y) = (f y).
Proof. exact (@lem3744470 (A -> Prop) (type686 A) f y). Qed.
Lemma lem3744472 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term188 A s x) = (term189 A s x).
Proof. exact (@lem3744471 A (term9 A s) x). Qed.
Lemma lem3744473 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term190 A s t).
Proof. exact (eq_refl (term189 A s t)). Qed.
Lemma lem3744474 {A : Type'} (s : A -> Prop) : (term191 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744473 A s t)). Qed.
Lemma lem3744475 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3744476 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term188 A s x) = (term189 A s x).
Proof. exact (MK_COMB (@lem3744474 A s) (@lem3744475 A x)). Qed.
Lemma lem3744477 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem3744478 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term192 A s x) = (term193 A s x).
Proof. exact (MK_COMB (@lem3744477 A) (@lem3744476 A s x)). Qed.
Lemma lem3744479 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term189 A s x) = (term190 A s x).
Proof. exact (eq_refl (term189 A s x)). Qed.
Lemma lem3744480 {A : Type'} (s : A -> Prop) (x : A -> Prop) : ((term188 A s x) = (term189 A s x)) = ((term189 A s x) = (term190 A s x)).
Proof. exact (MK_COMB (@lem3744478 A s x) (@lem3744479 A s x)). Qed.
Lemma lem3744481 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term189 A s x) = (term190 A s x).
Proof. exact (EQ_MP (@lem3744480 A s x) (@lem3744472 A s x)). Qed.
Lemma lem3744484 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3744485 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term194 A s x) = (term195 A s x).
Proof. exact (MK_COMB (@lem3744481 A s x) (@lem3744484 A x)). Qed.
Lemma lem3744487 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744488 {A : Type'} (f : type686 A) (y : A -> Prop) : (term196 A f y) = (f y).
Proof. exact (@lem3744487 (A -> Prop) Prop f y). Qed.
Lemma lem3744489 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term197 A s x) = (term195 A s x).
Proof. exact (@lem3744488 A (term190 A s x) x). Qed.
Lemma lem3744490 {A : Type'} (s : A -> Prop) (x : A -> Prop) (u : A -> Prop) : (term198 A s x u) = (term199 A s x u).
Proof. exact (eq_refl (term198 A s x u)). Qed.
Lemma lem3744491 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term200 A s x) = (term190 A s x).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3744490 A s x u)). Qed.
Lemma lem3744492 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3744493 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term197 A s x) = (term195 A s x).
Proof. exact (MK_COMB (@lem3744491 A s x) (@lem3744492 A x)). Qed.
Lemma lem3744494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3744495 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term201 A s x) = (term202 A s x).
Proof. exact (MK_COMB (@lem3744494) (@lem3744493 A s x)). Qed.
Lemma lem3744496 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term195 A s x) = (term203 A s x).
Proof. exact (eq_refl (term195 A s x)). Qed.
Lemma lem3744497 {A : Type'} (s : A -> Prop) (x : A -> Prop) : ((term197 A s x) = (term195 A s x)) = ((term195 A s x) = (term203 A s x)).
Proof. exact (MK_COMB (@lem3744495 A s x) (@lem3744496 A s x)). Qed.
Lemma lem3744498 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term195 A s x) = (term203 A s x).
Proof. exact (EQ_MP (@lem3744497 A s x) (@lem3744489 A s x)). Qed.
Lemma lem3744501 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term194 A s x) = (term203 A s x).
Proof. exact (TRANS (@lem3744485 A s x) (@lem3744498 A s x)). Qed.
Lemma lem3744502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3744503 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term204 A s x) = (term205 A s x).
Proof. exact (MK_COMB (@lem3744502) (@lem3744501 A s x)). Qed.
Lemma lem3744506 {A : Type'} (s : A -> Prop) : (term206 A s) = (term207 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3744503 A s x)). Qed.
Lemma lem3744509 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3744510 {A : Type'} (s : A -> Prop) : (term208 A s) = (term209 A s).
Proof. exact (MK_COMB (@lem3744509 A) (@lem3744506 A s)). Qed.
Lemma lem3744517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3744518 {A : Type'} (s : A -> Prop) : (term210 A s) = (term211 A s).
Proof. exact (MK_COMB (@lem3744517) (@lem3744510 A s)). Qed.
Lemma lem3744542 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term45 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3744543 (p : Prop) (q : Prop) (p' : Prop) : term46 p q p'.
Proof. exact (fun q' : Prop => @lem3744542 p q p' q'). Qed.
Lemma lem3744544 (p : Prop) (q : Prop) : term47 p q.
Proof. exact (fun p' : Prop => @lem3744543 p q p'). Qed.
Lemma lem3744545 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term212 A y s x z.
Proof. exact (@lem3744544 (term213 A x s y z) (term214 A s x z)). Qed.
Lemma lem3744546 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) : term215 A y s x z p'.
Proof. exact (@lem3744545 A y s x z p'). Qed.
Lemma lem3744547 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) : (term215 A y s x z p') = (term216 A y s x z p').
Proof. exact (eq_refl (term215 A y s x z p')). Qed.
Lemma lem3744548 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) : term216 A y s x z p'.
Proof. exact (EQ_MP (@lem3744547 A y s x z p') (@lem3744546 A y s x z p')). Qed.
Lemma lem3744549 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) (q' : Prop) : term217 A y s x z p' q'.
Proof. exact (@lem3744548 A y s x z p' q'). Qed.
Lemma lem3744550 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) (q' : Prop) : (term217 A y s x z p' q') = (term218 A y s x z p' q').
Proof. exact (eq_refl (term217 A y s x z p' q')). Qed.
Lemma lem3744551 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) (q' : Prop) : term218 A y s x z p' q'.
Proof. exact (EQ_MP (@lem3744550 A y s x z p' q') (@lem3744549 A y s x z p' q')). Qed.
Lemma lem3744555 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744556 {A : Type'} (f : type639 A) (y : A -> Prop) : (term187 A f y) = (f y).
Proof. exact (@lem3744555 (A -> Prop) (type686 A) f y). Qed.
Lemma lem3744557 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term188 A s x) = (term189 A s x).
Proof. exact (@lem3744556 A (term9 A s) x). Qed.
Lemma lem3744558 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term190 A s t).
Proof. exact (eq_refl (term189 A s t)). Qed.
Lemma lem3744559 {A : Type'} (s : A -> Prop) : (term191 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744558 A s t)). Qed.
Lemma lem3744560 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3744561 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term188 A s x) = (term189 A s x).
Proof. exact (MK_COMB (@lem3744559 A s) (@lem3744560 A x)). Qed.
Lemma lem3744562 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem3744563 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term192 A s x) = (term193 A s x).
Proof. exact (MK_COMB (@lem3744562 A) (@lem3744561 A s x)). Qed.
Lemma lem3744564 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term189 A s x) = (term190 A s x).
Proof. exact (eq_refl (term189 A s x)). Qed.
Lemma lem3744565 {A : Type'} (s : A -> Prop) (x : A -> Prop) : ((term188 A s x) = (term189 A s x)) = ((term189 A s x) = (term190 A s x)).
Proof. exact (MK_COMB (@lem3744563 A s x) (@lem3744564 A s x)). Qed.
Lemma lem3744566 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term189 A s x) = (term190 A s x).
Proof. exact (EQ_MP (@lem3744565 A s x) (@lem3744557 A s x)). Qed.
Lemma lem3744569 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3744570 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term214 A s x y) = (term198 A s x y).
Proof. exact (MK_COMB (@lem3744566 A s x) (@lem3744569 A y)). Qed.
Lemma lem3744572 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744573 {A : Type'} (f : type686 A) (y : A -> Prop) : (term196 A f y) = (f y).
Proof. exact (@lem3744572 (A -> Prop) Prop f y). Qed.
Lemma lem3744574 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term219 A s x y) = (term198 A s x y).
Proof. exact (@lem3744573 A (term190 A s x) y). Qed.
Lemma lem3744575 {A : Type'} (s : A -> Prop) (x : A -> Prop) (u : A -> Prop) : (term198 A s x u) = (term199 A s x u).
Proof. exact (eq_refl (term198 A s x u)). Qed.
Lemma lem3744576 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term200 A s x) = (term190 A s x).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3744575 A s x u)). Qed.
Lemma lem3744577 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3744578 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term219 A s x y) = (term198 A s x y).
Proof. exact (MK_COMB (@lem3744576 A s x) (@lem3744577 A y)). Qed.
Lemma lem3744579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3744580 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term220 A s x y) = (term221 A s x y).
Proof. exact (MK_COMB (@lem3744579) (@lem3744578 A s x y)). Qed.
Lemma lem3744581 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term198 A s x y) = (term199 A s x y).
Proof. exact (eq_refl (term198 A s x y)). Qed.
Lemma lem3744582 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : ((term219 A s x y) = (term198 A s x y)) = ((term198 A s x y) = (term199 A s x y)).
Proof. exact (MK_COMB (@lem3744580 A s x y) (@lem3744581 A s x y)). Qed.
Lemma lem3744583 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term198 A s x y) = (term199 A s x y).
Proof. exact (EQ_MP (@lem3744582 A s x y) (@lem3744574 A s x y)). Qed.
Lemma lem3744586 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term214 A s x y) = (term199 A s x y).
Proof. exact (TRANS (@lem3744570 A s x y) (@lem3744583 A s x y)). Qed.
Lemma lem3744587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3744588 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term222 A s x y) = (term223 A s x y).
Proof. exact (MK_COMB (@lem3744587) (@lem3744586 A s x y)). Qed.
Lemma lem3744592 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744593 {A : Type'} (f : type639 A) (y : A -> Prop) : (term187 A f y) = (f y).
Proof. exact (@lem3744592 (A -> Prop) (type686 A) f y). Qed.
Lemma lem3744594 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term188 A s y) = (term189 A s y).
Proof. exact (@lem3744593 A (term9 A s) y). Qed.
Lemma lem3744595 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term190 A s t).
Proof. exact (eq_refl (term189 A s t)). Qed.
Lemma lem3744596 {A : Type'} (s : A -> Prop) : (term191 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744595 A s t)). Qed.
Lemma lem3744597 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3744598 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term188 A s y) = (term189 A s y).
Proof. exact (MK_COMB (@lem3744596 A s) (@lem3744597 A y)). Qed.
Lemma lem3744599 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem3744600 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term192 A s y) = (term193 A s y).
Proof. exact (MK_COMB (@lem3744599 A) (@lem3744598 A s y)). Qed.
Lemma lem3744601 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term189 A s y) = (term190 A s y).
Proof. exact (eq_refl (term189 A s y)). Qed.
Lemma lem3744602 {A : Type'} (s : A -> Prop) (y : A -> Prop) : ((term188 A s y) = (term189 A s y)) = ((term189 A s y) = (term190 A s y)).
Proof. exact (MK_COMB (@lem3744600 A s y) (@lem3744601 A s y)). Qed.
Lemma lem3744603 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term189 A s y) = (term190 A s y).
Proof. exact (EQ_MP (@lem3744602 A s y) (@lem3744594 A s y)). Qed.
Lemma lem3744606 {A : Type'} (z : A -> Prop) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem3744607 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term214 A s y z) = (term198 A s y z).
Proof. exact (MK_COMB (@lem3744603 A s y) (@lem3744606 A z)). Qed.
Lemma lem3744609 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744610 {A : Type'} (f : type686 A) (y : A -> Prop) : (term196 A f y) = (f y).
Proof. exact (@lem3744609 (A -> Prop) Prop f y). Qed.
Lemma lem3744611 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term219 A s y z) = (term198 A s y z).
Proof. exact (@lem3744610 A (term190 A s y) z). Qed.
Lemma lem3744612 {A : Type'} (s : A -> Prop) (y : A -> Prop) (u : A -> Prop) : (term198 A s y u) = (term199 A s y u).
Proof. exact (eq_refl (term198 A s y u)). Qed.
Lemma lem3744613 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term200 A s y) = (term190 A s y).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3744612 A s y u)). Qed.
Lemma lem3744614 {A : Type'} (z : A -> Prop) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem3744615 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term219 A s y z) = (term198 A s y z).
Proof. exact (MK_COMB (@lem3744613 A s y) (@lem3744614 A z)). Qed.
Lemma lem3744616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3744617 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term220 A s y z) = (term221 A s y z).
Proof. exact (MK_COMB (@lem3744616) (@lem3744615 A s y z)). Qed.
Lemma lem3744618 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term198 A s y z) = (term199 A s y z).
Proof. exact (eq_refl (term198 A s y z)). Qed.
Lemma lem3744619 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : ((term219 A s y z) = (term198 A s y z)) = ((term198 A s y z) = (term199 A s y z)).
Proof. exact (MK_COMB (@lem3744617 A s y z) (@lem3744618 A s y z)). Qed.
Lemma lem3744620 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term198 A s y z) = (term199 A s y z).
Proof. exact (EQ_MP (@lem3744619 A s y z) (@lem3744611 A s y z)). Qed.
Lemma lem3744623 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term214 A s y z) = (term199 A s y z).
Proof. exact (TRANS (@lem3744607 A s y z) (@lem3744620 A s y z)). Qed.
Lemma lem3744624 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term213 A x s y z) = (term224 A x s y z).
Proof. exact (MK_COMB (@lem3744588 A s x y) (@lem3744623 A s y z)). Qed.
Lemma lem3744631 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (q' : Prop) : term225 A x s y z q'.
Proof. exact (@lem3744551 A y s x z (term224 A x s y z) q'). Qed.
Lemma lem3744632 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (q' : Prop) : term226 A x s y z q'.
Proof. exact (@lem3744631 A x s y z q' (@lem3744624 A x s y z)). Qed.
Lemma lem3744633 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : term224 A x s y z.
Proof. exact (h1). Qed.
Lemma lem3744641 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : term199 A s x y.
Proof. exact (proj1 (@lem3744633 A x s y z h1)). Qed.
Lemma lem3744645 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : @SUBSET A s x.
Proof. exact (proj1 (@lem3744641 A x s y z h1)). Qed.
Lemma lem3744646 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (@SUBSET A s x) = ((@SUBSET A s x) = True).
Proof. exact (@lem7 (@SUBSET A s x)). Qed.
Lemma lem3744649 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744650 {A : Type'} (f : type639 A) (y : A -> Prop) : (term187 A f y) = (f y).
Proof. exact (@lem3744649 (A -> Prop) (type686 A) f y). Qed.
Lemma lem3744651 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term188 A s x) = (term189 A s x).
Proof. exact (@lem3744650 A (term9 A s) x). Qed.
Lemma lem3744652 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term190 A s t).
Proof. exact (eq_refl (term189 A s t)). Qed.
Lemma lem3744653 {A : Type'} (s : A -> Prop) : (term191 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3744652 A s t)). Qed.
Lemma lem3744654 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3744655 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term188 A s x) = (term189 A s x).
Proof. exact (MK_COMB (@lem3744653 A s) (@lem3744654 A x)). Qed.
Lemma lem3744656 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem3744657 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term192 A s x) = (term193 A s x).
Proof. exact (MK_COMB (@lem3744656 A) (@lem3744655 A s x)). Qed.
Lemma lem3744658 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term189 A s x) = (term190 A s x).
Proof. exact (eq_refl (term189 A s x)). Qed.
Lemma lem3744659 {A : Type'} (s : A -> Prop) (x : A -> Prop) : ((term188 A s x) = (term189 A s x)) = ((term189 A s x) = (term190 A s x)).
Proof. exact (MK_COMB (@lem3744657 A s x) (@lem3744658 A s x)). Qed.
Lemma lem3744660 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term189 A s x) = (term190 A s x).
Proof. exact (EQ_MP (@lem3744659 A s x) (@lem3744651 A s x)). Qed.
Lemma lem3744664 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : (@SUBSET A s x) = True.
Proof. exact (EQ_MP (@lem3744646 A s x) (@lem3744645 A x s y z h1)). Qed.
Lemma lem3744665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3744666 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : (term227 A s x) = (and True).
Proof. exact (MK_COMB (@lem3744665) (@lem3744664 A x s y z h1)). Qed.
Lemma lem3744667 {A : Type'} (x : A -> Prop) (u : A -> Prop) : (@PSUBSET A x u) = (@PSUBSET A x u).
Proof. exact (eq_refl (@PSUBSET A x u)). Qed.
Lemma lem3744668 {A : Type'} (u : A -> Prop) (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : (term199 A s x u) = (term228 A x u).
Proof. exact (MK_COMB (@lem3744666 A x s y z h1) (@lem3744667 A x u)). Qed.
Lemma lem3744670 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3744671 {A : Type'} (x : A -> Prop) (u : A -> Prop) : (term228 A x u) = (@PSUBSET A x u).
Proof. exact (@lem3744670 (@PSUBSET A x u)). Qed.
Lemma lem3744672 {A : Type'} (u : A -> Prop) (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : (term199 A s x u) = (@PSUBSET A x u).
Proof. exact (TRANS (@lem3744668 A u x s y z h1) (@lem3744671 A x u)). Qed.
Lemma lem3744673 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : (term190 A s x) = (term229 A x).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3744672 A u x s y z h1)). Qed.
Lemma lem3744674 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : (term189 A s x) = (term229 A x).
Proof. exact (TRANS (@lem3744660 A s x) (@lem3744673 A x s y z h1)). Qed.
Lemma lem3744675 {A : Type'} (z : A -> Prop) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem3744676 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : (term214 A s x z) = (term230 A x z).
Proof. exact (MK_COMB (@lem3744674 A x s y z h1) (@lem3744675 A z)). Qed.
Lemma lem3744678 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3744679 {A : Type'} (f : type686 A) (y : A -> Prop) : (term196 A f y) = (f y).
Proof. exact (@lem3744678 (A -> Prop) Prop f y). Qed.
Lemma lem3744680 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term231 A x z) = (term230 A x z).
Proof. exact (@lem3744679 A (term229 A x) z). Qed.
Lemma lem3744681 {A : Type'} (x : A -> Prop) (u : A -> Prop) : (term230 A x u) = (@PSUBSET A x u).
Proof. exact (eq_refl (term230 A x u)). Qed.
Lemma lem3744682 {A : Type'} (x : A -> Prop) : (term232 A x) = (term229 A x).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3744681 A x u)). Qed.
Lemma lem3744683 {A : Type'} (z : A -> Prop) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem3744684 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term231 A x z) = (term230 A x z).
Proof. exact (MK_COMB (@lem3744682 A x) (@lem3744683 A z)). Qed.
Lemma lem3744685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3744686 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term233 A x z) = (term234 A x z).
Proof. exact (MK_COMB (@lem3744685) (@lem3744684 A x z)). Qed.
Lemma lem3744687 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term230 A x z) = (@PSUBSET A x z).
Proof. exact (eq_refl (term230 A x z)). Qed.
Lemma lem3744688 {A : Type'} (x : A -> Prop) (z : A -> Prop) : ((term231 A x z) = (term230 A x z)) = ((term230 A x z) = (@PSUBSET A x z)).
Proof. exact (MK_COMB (@lem3744686 A x z) (@lem3744687 A x z)). Qed.
Lemma lem3744689 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term230 A x z) = (@PSUBSET A x z).
Proof. exact (EQ_MP (@lem3744688 A x z) (@lem3744680 A x z)). Qed.
Lemma lem3744690 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term224 A x s y z) : (term214 A s x z) = (@PSUBSET A x z).
Proof. exact (TRANS (@lem3744676 A x s y z h1) (@lem3744689 A x z)). Qed.
Lemma lem3744691 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term235 A y s x z.
Proof. exact (fun h0 : term224 A x s y z => @lem3744690 A x s y z h0). Qed.
Lemma lem3744692 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term236 A s y x z.
Proof. exact (@lem3744632 A x s y z (@PSUBSET A x z)). Qed.
Lemma lem3744693 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term237 A y s x z) = (term238 A s y x z).
Proof. exact (@lem3744692 A s y x z (@lem3744691 A y s x z)). Qed.
Lemma lem3744741 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : (term239 A y s x) = (term240 A s y x).
Proof. exact (fun_ext (fun z : A -> Prop => @lem3744693 A s y x z)). Qed.
Lemma lem3744789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3744790 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : (term241 A y s x) = (term242 A s y x).
Proof. exact (MK_COMB (@lem3744789 A) (@lem3744741 A s y x)). Qed.
Lemma lem3744842 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term243 A s x) = (term244 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem3744790 A s y x)). Qed.
Lemma lem3744894 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3744895 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term245 A s x) = (term246 A s x).
Proof. exact (MK_COMB (@lem3744894 A) (@lem3744842 A s x)). Qed.
Lemma lem3744951 {A : Type'} (s : A -> Prop) : (term247 A s) = (term248 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3744895 A s x)). Qed.
Lemma lem3745007 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3745008 {A : Type'} (s : A -> Prop) : (term249 A s) = (term250 A s).
Proof. exact (MK_COMB (@lem3745007 A) (@lem3744951 A s)). Qed.
Lemma lem3745068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3745069 {A : Type'} (s : A -> Prop) : (term251 A s) = (term252 A s).
Proof. exact (MK_COMB (@lem3745068) (@lem3745008 A s)). Qed.
Lemma lem3745130 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term148 _88905 _89106 P f Q) = (term149 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem3744391 _88905 _89106 P Q f) (@lem3744390 _88905 _89106 P Q f)). Qed.
Lemma lem3745131 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term253 A P f Q) = (term254 A P Q f).
Proof. exact (@lem3745130 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem3745132 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term256 A f s).
Proof. exact (@lem3745131 A (term257 A f s) (term258 A f s) (term103 A)). Qed.
Lemma lem3745133 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term259 A f s t) = (term168 A f s t).
Proof. exact (eq_refl (term259 A f s t)). Qed.
Lemma lem3745134 {A : Type'} (GEN_PVAR_103 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_103) = (@SETSPEC (A -> Prop) GEN_PVAR_103).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_103)). Qed.
Lemma lem3745135 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term260 A GEN_PVAR_103 f s t) = (term170 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3745134 A GEN_PVAR_103) (@lem3745133 A f s t)). Qed.
Lemma lem3745136 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3745137 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term261 A GEN_PVAR_103 f s t) = (term172 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3745135 A GEN_PVAR_103 f s t) (@lem3745136 A t)). Qed.
Lemma lem3745138 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term262 A GEN_PVAR_103 f s) = (term174 A GEN_PVAR_103 f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3745137 A GEN_PVAR_103 f s t)). Qed.
Lemma lem3745139 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3745140 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term263 A GEN_PVAR_103 f s) = (term176 A GEN_PVAR_103 f s).
Proof. exact (MK_COMB (@lem3745139 A) (@lem3745138 A GEN_PVAR_103 f s)). Qed.
Lemma lem3745141 {A : Type'} (f : type686 A) (s : A -> Prop) : (term264 A f s) = (term178 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_103 : A -> Prop => @lem3745140 A GEN_PVAR_103 f s)). Qed.
Lemma lem3745142 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3745143 {A : Type'} (f : type686 A) (s : A -> Prop) : (term265 A f s) = (term12 A f s).
Proof. exact (MK_COMB (@lem3745142 A) (@lem3745141 A f s)). Qed.
Lemma lem3745144 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem3745145 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term266 A x f s) = (term267 A x f s).
Proof. exact (MK_COMB (@lem3745144 A x) (@lem3745143 A f s)). Qed.
Lemma lem3745146 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3745147 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term268 A x f s) = (term269 A x f s).
Proof. exact (MK_COMB (@lem3745146) (@lem3745145 A x f s)). Qed.
Lemma lem3745148 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term270 A f s x) = (term271 A f s x).
Proof. exact (eq_refl (term270 A f s x)). Qed.
Lemma lem3745149 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term272 A f s x) = (term273 A f s x).
Proof. exact (MK_COMB (@lem3745147 A x f s) (@lem3745148 A f s x)). Qed.
Lemma lem3745150 {A : Type'} (f : type686 A) (s : A -> Prop) : (term274 A f s) = (term275 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3745149 A f s x)). Qed.
Lemma lem3745151 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3745152 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term276 A f s).
Proof. exact (MK_COMB (@lem3745151 A) (@lem3745150 A f s)). Qed.
Lemma lem3745153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3745154 {A : Type'} (f : type686 A) (s : A -> Prop) : (term277 A f s) = (term278 A f s).
Proof. exact (MK_COMB (@lem3745153) (@lem3745152 A f s)). Qed.
Lemma lem3745155 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term259 A f s t) = (term168 A f s t).
Proof. exact (eq_refl (term259 A f s t)). Qed.
Lemma lem3745156 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3745157 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term279 A f s t) = (term280 A f s t).
Proof. exact (MK_COMB (@lem3745156) (@lem3745155 A f s t)). Qed.
Lemma lem3745158 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term281 A f s t) = (term282 A f s t).
Proof. exact (eq_refl (term281 A f s t)). Qed.
Lemma lem3745159 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term283 A f s t) = (term284 A f s t).
Proof. exact (MK_COMB (@lem3745157 A f s t) (@lem3745158 A f s t)). Qed.
Lemma lem3745160 {A : Type'} (f : type686 A) (s : A -> Prop) : (term285 A f s) = (term286 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3745159 A f s t)). Qed.
Lemma lem3745161 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3745162 {A : Type'} (f : type686 A) (s : A -> Prop) : (term256 A f s) = (term287 A f s).
Proof. exact (MK_COMB (@lem3745161 A) (@lem3745160 A f s)). Qed.
Lemma lem3745163 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term255 A f s) = (term256 A f s)) = ((term276 A f s) = (term287 A f s)).
Proof. exact (MK_COMB (@lem3745154 A f s) (@lem3745162 A f s)). Qed.
Lemma lem3745164 {A : Type'} (f : type686 A) (s : A -> Prop) : (term276 A f s) = (term287 A f s).
Proof. exact (EQ_MP (@lem3745163 A f s) (@lem3745132 A f s)). Qed.
Lemma lem3745172 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term45 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3745173 (p : Prop) (q : Prop) (p' : Prop) : term46 p q p'.
Proof. exact (fun q' : Prop => @lem3745172 p q p' q'). Qed.
Lemma lem3745174 (p : Prop) (q : Prop) : term47 p q.
Proof. exact (fun p' : Prop => @lem3745173 p q p'). Qed.
Lemma lem3745175 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : term288 A f s t.
Proof. exact (@lem3745174 (term168 A f s t) (term282 A f s t)). Qed.
Lemma lem3745176 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (p' : Prop) : term289 A f s t p'.
Proof. exact (@lem3745175 A f s t p'). Qed.
Lemma lem3745177 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (p' : Prop) : (term289 A f s t p') = (term290 A f s t p').
Proof. exact (eq_refl (term289 A f s t p')). Qed.
Lemma lem3745178 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (p' : Prop) : term290 A f s t p'.
Proof. exact (EQ_MP (@lem3745177 A f s t p') (@lem3745176 A f s t p')). Qed.
Lemma lem3745179 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (p' : Prop) (q' : Prop) : term291 A f s t p' q'.
Proof. exact (@lem3745178 A f s t p' q'). Qed.
Lemma lem3745180 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (p' : Prop) (q' : Prop) : (term291 A f s t p' q') = (term292 A f s t p' q').
Proof. exact (eq_refl (term291 A f s t p' q')). Qed.
Lemma lem3745181 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (p' : Prop) (q' : Prop) : term292 A f s t p' q'.
Proof. exact (EQ_MP (@lem3745180 A f s t p' q') (@lem3745179 A f s t p' q')). Qed.
Lemma lem3745184 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term168 A f s t) = (term168 A f s t).
Proof. exact (eq_refl (term168 A f s t)). Qed.
Lemma lem3745185 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (q' : Prop) : term293 A f s t q'.
Proof. exact (@lem3745181 A f s t (term168 A f s t) q'). Qed.
Lemma lem3745186 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (q' : Prop) : term294 A f s t q'.
Proof. exact (@lem3745185 A f s t q' (@lem3745184 A f s t)). Qed.
Lemma lem3745187 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : term168 A f s t.
Proof. exact (h1). Qed.
Lemma lem3745188 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : @SUBSET A s t.
Proof. exact (proj2 (@lem3745187 A f s t h1)). Qed.
Lemma lem3745189 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = ((@SUBSET A s t) = True).
Proof. exact (@lem7 (@SUBSET A s t)). Qed.
Lemma lem3745195 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : (term19 _89156 _89357 P f Q) = (term20 _89156 _89357 P Q f).
Proof. exact (EQ_MP (@lem3744361 _89156 _89357 P Q f) (@lem3744360 _89156 _89357 P Q f)). Qed.
Lemma lem3745196 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term97 A P f Q) = (term98 A P Q f).
Proof. exact (@lem3745195 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem3745197 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term295 A f s t) = (term296 A f s t).
Proof. exact (@lem3745196 A (term257 A f s) (term297 A s t) (term103 A)). Qed.
Lemma lem3745198 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term259 A f s t) = (term168 A f s t).
Proof. exact (eq_refl (term259 A f s t)). Qed.
Lemma lem3745199 {A : Type'} (GEN_PVAR_103 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_103) = (@SETSPEC (A -> Prop) GEN_PVAR_103).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_103)). Qed.
Lemma lem3745200 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term260 A GEN_PVAR_103 f s t) = (term170 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3745199 A GEN_PVAR_103) (@lem3745198 A f s t)). Qed.
Lemma lem3745201 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3745202 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term261 A GEN_PVAR_103 f s t) = (term172 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3745200 A GEN_PVAR_103 f s t) (@lem3745201 A t)). Qed.
Lemma lem3745203 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term262 A GEN_PVAR_103 f s) = (term174 A GEN_PVAR_103 f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3745202 A GEN_PVAR_103 f s t)). Qed.
Lemma lem3745204 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3745205 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term263 A GEN_PVAR_103 f s) = (term176 A GEN_PVAR_103 f s).
Proof. exact (MK_COMB (@lem3745204 A) (@lem3745203 A GEN_PVAR_103 f s)). Qed.
Lemma lem3745206 {A : Type'} (f : type686 A) (s : A -> Prop) : (term264 A f s) = (term178 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_103 : A -> Prop => @lem3745205 A GEN_PVAR_103 f s)). Qed.
Lemma lem3745207 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3745208 {A : Type'} (f : type686 A) (s : A -> Prop) : (term265 A f s) = (term12 A f s).
Proof. exact (MK_COMB (@lem3745207 A) (@lem3745206 A f s)). Qed.
Lemma lem3745209 {A : Type'} (y : A -> Prop) : (@IN (A -> Prop) y) = (@IN (A -> Prop) y).
Proof. exact (eq_refl (@IN (A -> Prop) y)). Qed.
Lemma lem3745210 {A : Type'} (y : A -> Prop) (f : type686 A) (s : A -> Prop) : (term266 A y f s) = (term267 A y f s).
Proof. exact (MK_COMB (@lem3745209 A y) (@lem3745208 A f s)). Qed.
Lemma lem3745211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3745212 {A : Type'} (y : A -> Prop) (f : type686 A) (s : A -> Prop) : (term298 A y f s) = (term299 A y f s).
Proof. exact (MK_COMB (@lem3745211) (@lem3745210 A y f s)). Qed.
Lemma lem3745213 {A : Type'} (s : A -> Prop) (t : A -> Prop) (y : A -> Prop) : (term300 A s t y) = (term301 A s t y).
Proof. exact (eq_refl (term300 A s t y)). Qed.
Lemma lem3745214 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (y : A -> Prop) : (term302 A f s t y) = (term303 A f s t y).
Proof. exact (MK_COMB (@lem3745212 A y f s) (@lem3745213 A s t y)). Qed.
Lemma lem3745215 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term304 A f s t) = (term305 A f s t).
Proof. exact (fun_ext (fun y : A -> Prop => @lem3745214 A f s t y)). Qed.
Lemma lem3745216 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3745217 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term295 A f s t) = (term282 A f s t).
Proof. exact (MK_COMB (@lem3745216 A) (@lem3745215 A f s t)). Qed.
Lemma lem3745218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3745219 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term306 A f s t) = (term307 A f s t).
Proof. exact (MK_COMB (@lem3745218) (@lem3745217 A f s t)). Qed.
Lemma lem3745220 {A : Type'} (f : type686 A) (s : A -> Prop) (t' : A -> Prop) : (term259 A f s t') = (term168 A f s t').
Proof. exact (eq_refl (term259 A f s t')). Qed.
Lemma lem3745221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3745222 {A : Type'} (f : type686 A) (s : A -> Prop) (t' : A -> Prop) : (term308 A f s t') = (term309 A f s t').
Proof. exact (MK_COMB (@lem3745221) (@lem3745220 A f s t')). Qed.
Lemma lem3745223 {A : Type'} (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term310 A s t t') = (term311 A s t t').
Proof. exact (eq_refl (term310 A s t t')). Qed.
Lemma lem3745224 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term312 A f s t t') = (term313 A f s t t').
Proof. exact (MK_COMB (@lem3745222 A f s t') (@lem3745223 A s t t')). Qed.
Lemma lem3745225 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term314 A f s t) = (term315 A f s t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3745224 A f s t t')). Qed.
Lemma lem3745226 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3745227 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term296 A f s t) = (term316 A f s t).
Proof. exact (MK_COMB (@lem3745226 A) (@lem3745225 A f s t)). Qed.
Lemma lem3745228 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : ((term295 A f s t) = (term296 A f s t)) = ((term282 A f s t) = (term316 A f s t)).
Proof. exact (MK_COMB (@lem3745219 A f s t) (@lem3745227 A f s t)). Qed.
Lemma lem3745229 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term282 A f s t) = (term316 A f s t).
Proof. exact (EQ_MP (@lem3745228 A f s t) (@lem3745197 A f s t)). Qed.
Lemma lem3745239 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3745240 {A : Type'} (f : type639 A) (y : A -> Prop) : (term187 A f y) = (f y).
Proof. exact (@lem3745239 (A -> Prop) (type686 A) f y). Qed.
Lemma lem3745241 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term317 A s t) = (term318 A s t).
Proof. exact (@lem3745240 A (term9 A s) (term106 A t)). Qed.
Lemma lem3745242 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term190 A s t).
Proof. exact (eq_refl (term189 A s t)). Qed.
Lemma lem3745243 {A : Type'} (s : A -> Prop) : (term191 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3745242 A s t)). Qed.
Lemma lem3745244 {A : Type'} (t : A -> Prop) : (term106 A t) = (term106 A t).
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3745245 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term317 A s t) = (term318 A s t).
Proof. exact (MK_COMB (@lem3745243 A s) (@lem3745244 A t)). Qed.
Lemma lem3745246 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem3745247 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term319 A s t) = (term320 A s t).
Proof. exact (MK_COMB (@lem3745246 A) (@lem3745245 A s t)). Qed.
Lemma lem3745248 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (term321 A s t).
Proof. exact (eq_refl (term318 A s t)). Qed.
Lemma lem3745249 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term317 A s t) = (term318 A s t)) = ((term318 A s t) = (term321 A s t)).
Proof. exact (MK_COMB (@lem3745247 A s t) (@lem3745248 A s t)). Qed.
Lemma lem3745250 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (term321 A s t).
Proof. exact (EQ_MP (@lem3745249 A s t) (@lem3745241 A s t)). Qed.
Lemma lem3745254 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3745255 {A : Type'} (f : type672 A) (y : A -> Prop) : (term134 A f y) = (f y).
Proof. exact (@lem3745254 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem3745256 {A : Type'} (t : A -> Prop) : (term135 A t) = (term106 A t).
Proof. exact (@lem3745255 A (term103 A) t). Qed.
Lemma lem3745257 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3745258 {A : Type'} : (term136 A) = (term103 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3745257 A t)). Qed.
Lemma lem3745259 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3745260 {A : Type'} (t : A -> Prop) : (term135 A t) = (term106 A t).
Proof. exact (MK_COMB (@lem3745258 A) (@lem3745259 A t)). Qed.
Lemma lem3745261 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3745262 {A : Type'} (t : A -> Prop) : (term137 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem3745261 A) (@lem3745260 A t)). Qed.
Lemma lem3745263 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3745264 {A : Type'} (t : A -> Prop) : ((term135 A t) = (term106 A t)) = ((term106 A t) = t).
Proof. exact (MK_COMB (@lem3745262 A t) (@lem3745263 A t)). Qed.
Lemma lem3745265 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem3745264 A t) (@lem3745256 A t)). Qed.
Lemma lem3745266 {A : Type'} (s : A -> Prop) : (@SUBSET A s) = (@SUBSET A s).
Proof. exact (eq_refl (@SUBSET A s)). Qed.
Lemma lem3745267 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term127 A s t) = (@SUBSET A s t).
Proof. exact (MK_COMB (@lem3745266 A s) (@lem3745265 A t)). Qed.
Lemma lem3745269 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (@SUBSET A s t) = True.
Proof. exact (EQ_MP (@lem3745189 A s t) (@lem3745188 A f s t h1)). Qed.
Lemma lem3745270 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term127 A s t) = True.
Proof. exact (TRANS (@lem3745267 A s t) (@lem3745269 A f s t h1)). Qed.
Lemma lem3745271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3745272 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term322 A s t) = (and True).
Proof. exact (MK_COMB (@lem3745271) (@lem3745270 A f s t h1)). Qed.
Lemma lem3745274 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3745275 {A : Type'} (f : type672 A) (y : A -> Prop) : (term134 A f y) = (f y).
Proof. exact (@lem3745274 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem3745276 {A : Type'} (t : A -> Prop) : (term135 A t) = (term106 A t).
Proof. exact (@lem3745275 A (term103 A) t). Qed.
Lemma lem3745277 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3745278 {A : Type'} : (term136 A) = (term103 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3745277 A t)). Qed.
Lemma lem3745279 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3745280 {A : Type'} (t : A -> Prop) : (term135 A t) = (term106 A t).
Proof. exact (MK_COMB (@lem3745278 A) (@lem3745279 A t)). Qed.
Lemma lem3745281 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3745282 {A : Type'} (t : A -> Prop) : (term137 A t) = (term138 A t).
Proof. exact (MK_COMB (@lem3745281 A) (@lem3745280 A t)). Qed.
Lemma lem3745283 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3745284 {A : Type'} (t : A -> Prop) : ((term135 A t) = (term106 A t)) = ((term106 A t) = t).
Proof. exact (MK_COMB (@lem3745282 A t) (@lem3745283 A t)). Qed.
Lemma lem3745285 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem3745284 A t) (@lem3745276 A t)). Qed.
Lemma lem3745286 {A : Type'} : (@PSUBSET A) = (@PSUBSET A).
Proof. exact (eq_refl (@PSUBSET A)). Qed.
Lemma lem3745287 {A : Type'} (t : A -> Prop) : (term323 A t) = (@PSUBSET A t).
Proof. exact (MK_COMB (@lem3745286 A) (@lem3745285 A t)). Qed.
Lemma lem3745288 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem3745289 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term324 A t u) = (@PSUBSET A t u).
Proof. exact (MK_COMB (@lem3745287 A t) (@lem3745288 A u)). Qed.
Lemma lem3745290 {A : Type'} (u : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term325 A s t u) = (term228 A t u).
Proof. exact (MK_COMB (@lem3745272 A f s t h1) (@lem3745289 A t u)). Qed.
Lemma lem3745292 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3745293 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term228 A t u) = (@PSUBSET A t u).
Proof. exact (@lem3745292 (@PSUBSET A t u)). Qed.
Lemma lem3745294 {A : Type'} (u : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term325 A s t u) = (@PSUBSET A t u).
Proof. exact (TRANS (@lem3745290 A u f s t h1) (@lem3745293 A t u)). Qed.
Lemma lem3745295 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term321 A s t) = (term229 A t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3745294 A u f s t h1)). Qed.
Lemma lem3745296 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term318 A s t) = (term229 A t).
Proof. exact (TRANS (@lem3745250 A s t) (@lem3745295 A f s t h1)). Qed.
Lemma lem3745298 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3745299 {A : Type'} (f : type672 A) (y : A -> Prop) : (term134 A f y) = (f y).
Proof. exact (@lem3745298 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem3745300 {A : Type'} (t' : A -> Prop) : (term135 A t') = (term106 A t').
Proof. exact (@lem3745299 A (term103 A) t'). Qed.
Lemma lem3745301 {A : Type'} (t : A -> Prop) : (term106 A t) = t.
Proof. exact (eq_refl (term106 A t)). Qed.
Lemma lem3745302 {A : Type'} : (term136 A) = (term103 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3745301 A t)). Qed.
Lemma lem3745303 {A : Type'} (t' : A -> Prop) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem3745304 {A : Type'} (t' : A -> Prop) : (term135 A t') = (term106 A t').
Proof. exact (MK_COMB (@lem3745302 A) (@lem3745303 A t')). Qed.
Lemma lem3745305 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3745306 {A : Type'} (t' : A -> Prop) : (term137 A t') = (term138 A t').
Proof. exact (MK_COMB (@lem3745305 A) (@lem3745304 A t')). Qed.
Lemma lem3745307 {A : Type'} (t' : A -> Prop) : (term106 A t') = t'.
Proof. exact (eq_refl (term106 A t')). Qed.
Lemma lem3745308 {A : Type'} (t' : A -> Prop) : ((term135 A t') = (term106 A t')) = ((term106 A t') = t').
Proof. exact (MK_COMB (@lem3745306 A t') (@lem3745307 A t')). Qed.
Lemma lem3745309 {A : Type'} (t' : A -> Prop) : (term106 A t') = t'.
Proof. exact (EQ_MP (@lem3745308 A t') (@lem3745300 A t')). Qed.
Lemma lem3745310 {A : Type'} (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term311 A s t t') = (term230 A t t').
Proof. exact (MK_COMB (@lem3745296 A f s t h1) (@lem3745309 A t')). Qed.
Lemma lem3745312 {A B : Type'} (f : A -> B) (y : A) : (term133 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3745313 {A : Type'} (f : type686 A) (y : A -> Prop) : (term196 A f y) = (f y).
Proof. exact (@lem3745312 (A -> Prop) Prop f y). Qed.
Lemma lem3745314 {A : Type'} (t : A -> Prop) (t' : A -> Prop) : (term231 A t t') = (term230 A t t').
Proof. exact (@lem3745313 A (term229 A t) t'). Qed.
Lemma lem3745315 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term230 A t u) = (@PSUBSET A t u).
Proof. exact (eq_refl (term230 A t u)). Qed.
Lemma lem3745316 {A : Type'} (t : A -> Prop) : (term232 A t) = (term229 A t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3745315 A t u)). Qed.
Lemma lem3745317 {A : Type'} (t' : A -> Prop) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem3745318 {A : Type'} (t : A -> Prop) (t' : A -> Prop) : (term231 A t t') = (term230 A t t').
Proof. exact (MK_COMB (@lem3745316 A t) (@lem3745317 A t')). Qed.
Lemma lem3745319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3745320 {A : Type'} (t : A -> Prop) (t' : A -> Prop) : (term233 A t t') = (term234 A t t').
Proof. exact (MK_COMB (@lem3745319) (@lem3745318 A t t')). Qed.
Lemma lem3745321 {A : Type'} (t : A -> Prop) (t' : A -> Prop) : (term230 A t t') = (@PSUBSET A t t').
Proof. exact (eq_refl (term230 A t t')). Qed.
Lemma lem3745322 {A : Type'} (t : A -> Prop) (t' : A -> Prop) : ((term231 A t t') = (term230 A t t')) = ((term230 A t t') = (@PSUBSET A t t')).
Proof. exact (MK_COMB (@lem3745320 A t t') (@lem3745321 A t t')). Qed.
Lemma lem3745323 {A : Type'} (t : A -> Prop) (t' : A -> Prop) : (term230 A t t') = (@PSUBSET A t t').
Proof. exact (EQ_MP (@lem3745322 A t t') (@lem3745314 A t t')). Qed.
Lemma lem3745324 {A : Type'} (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term311 A s t t') = (@PSUBSET A t t').
Proof. exact (TRANS (@lem3745310 A t' f s t h1) (@lem3745323 A t t')). Qed.
Lemma lem3745325 {A : Type'} (f : type686 A) (s : A -> Prop) (t' : A -> Prop) : (term309 A f s t') = (term309 A f s t').
Proof. exact (eq_refl (term309 A f s t')). Qed.
Lemma lem3745326 {A : Type'} (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term313 A f s t t') = (term326 A f s t t').
Proof. exact (MK_COMB (@lem3745325 A f s t') (@lem3745324 A t' f s t h1)). Qed.
Lemma lem3745331 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term315 A f s t) = (term327 A f s t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3745326 A t' f s t h1)). Qed.
Lemma lem3745336 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3745337 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term316 A f s t) = (term328 A f s t).
Proof. exact (MK_COMB (@lem3745336 A) (@lem3745331 A f s t h1)). Qed.
Lemma lem3745346 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term168 A f s t) : (term282 A f s t) = (term328 A f s t).
Proof. exact (TRANS (@lem3745229 A f s t) (@lem3745337 A f s t h1)). Qed.
Lemma lem3745347 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : term329 A f s t.
Proof. exact (fun h0 : term168 A f s t => @lem3745346 A f s t h0). Qed.
Lemma lem3745348 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : term330 A f s t.
Proof. exact (@lem3745186 A f s t (term328 A f s t)). Qed.
Lemma lem3745349 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term284 A f s t) = (term331 A f s t).
Proof. exact (@lem3745348 A f s t (@lem3745347 A f s t)). Qed.
Lemma lem3745397 {A : Type'} (f : type686 A) (s : A -> Prop) : (term286 A f s) = (term332 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3745349 A f s t)). Qed.
Lemma lem3745445 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3745446 {A : Type'} (f : type686 A) (s : A -> Prop) : (term287 A f s) = (term333 A f s).
Proof. exact (MK_COMB (@lem3745445 A) (@lem3745397 A f s)). Qed.
Lemma lem3745498 {A : Type'} (f : type686 A) (s : A -> Prop) : (term276 A f s) = (term333 A f s).
Proof. exact (TRANS (@lem3745164 A f s) (@lem3745446 A f s)). Qed.
Lemma lem3745499 {A : Type'} (f : type686 A) (s : A -> Prop) : (term334 A f s) = (term335 A f s).
Proof. exact (MK_COMB (@lem3745069 A s) (@lem3745498 A f s)). Qed.
Lemma lem3745612 {A : Type'} (f : type686 A) (s : A -> Prop) : (term336 A f s) = (term337 A f s).
Proof. exact (MK_COMB (@lem3744518 A s) (@lem3745499 A f s)). Qed.
Lemma lem3745733 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term163 A f s) = (term338 A f s).
Proof. exact (MK_COMB (@lem3744462 A s f h1) (@lem3745612 A f s)). Qed.
Lemma lem3745735 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3745736 {A : Type'} (f : type686 A) (s : A -> Prop) : (term338 A f s) = (term337 A f s).
Proof. exact (@lem3745735 (term337 A f s)). Qed.
Lemma lem3745857 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term163 A f s) = (term337 A f s).
Proof. exact (TRANS (@lem3745733 A s f h1) (@lem3745736 A f s)). Qed.
Lemma lem3745858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3745859 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term339 A f s) = (term340 A f s).
Proof. exact (MK_COMB (@lem3745858) (@lem3745857 A s f h1)). Qed.
Lemma lem3745988 {A : Type'} (f : type686 A) (s : A -> Prop) : (term341 A f s) = (term341 A f s).
Proof. exact (eq_refl (term341 A f s)). Qed.
Lemma lem3745989 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term162 A f s) = (term342 A f s).
Proof. exact (MK_COMB (@lem3745859 A s f h1) (@lem3745988 A f s)). Qed.
Lemma lem3746120 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term161 A f s) = (term342 A f s).
Proof. exact (TRANS (@lem3744425 A f s) (@lem3745989 A s f h1)). Qed.
Lemma lem3746121 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term160 A f s) = (term342 A f s).
Proof. exact (TRANS (@lem3744422 A f s) (@lem3746120 A s f h1)). Qed.
Lemma lem3746122 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term342 A f s) = (term160 A f s).
Proof. exact (SYM (@lem3746121 A s f h1)). Qed.
Lemma lem3746130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3746131 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3746130 A s t). Qed.
Lemma lem3746132 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (@SUBSET A s x) = (term343 A s x).
Proof. exact (@lem3746131 A s x). Qed.
Lemma lem3746139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746140 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term227 A s x) = (term344 A s x).
Proof. exact (MK_COMB (@lem3746139) (@lem3746132 A s x)). Qed.
Lemma lem3746142 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3746143 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (@lem3746142 A s t). Qed.
Lemma lem3746144 {A : Type'} (x : A -> Prop) : (@PSUBSET A x x) = (term346 A x).
Proof. exact (@lem3746143 A x x). Qed.
Lemma lem3746148 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3746149 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3746148 A s t). Qed.
Lemma lem3746150 {A : Type'} (x : A -> Prop) : (@SUBSET A x x) = (term347 A x).
Proof. exact (@lem3746149 A x x). Qed.
Lemma lem3746156 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3746157 {A : Type'} (x : A) (x' : A -> Prop) : (term348 A x x') = True.
Proof. exact (@lem3746156 (@IN A x x')). Qed.
Lemma lem3746158 {A : Type'} (x : A -> Prop) : (term349 A x) = (term350 A).
Proof. exact (fun_ext (fun x' : A => @lem3746157 A x' x)). Qed.
Lemma lem3746159 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746160 {A : Type'} (x : A -> Prop) : (term347 A x) = (term351 A).
Proof. exact (MK_COMB (@lem3746159 A) (@lem3746158 A x)). Qed.
Lemma lem3746162 {A : Type'} (t : Prop) : (term352 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3746163 {A : Type'} (t : Prop) : (term352 A t) = t.
Proof. exact (@lem3746162 A t). Qed.
Lemma lem3746164 {A : Type'} : (term351 A) = True.
Proof. exact (@lem3746163 A True). Qed.
Lemma lem3746165 {A : Type'} (x : A -> Prop) : (term347 A x) = True.
Proof. exact (TRANS (@lem3746160 A x) (@lem3746164 A)). Qed.
Lemma lem3746166 {A : Type'} (x : A -> Prop) : (@SUBSET A x x) = True.
Proof. exact (TRANS (@lem3746150 A x) (@lem3746165 A x)). Qed.
Lemma lem3746167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746168 {A : Type'} (x : A -> Prop) : (term353 A x) = (and True).
Proof. exact (MK_COMB (@lem3746167) (@lem3746166 A x)). Qed.
Lemma lem3746170 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3746171 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3746170 (A -> Prop) x). Qed.
Lemma lem3746172 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746173 {A : Type'} (x : A -> Prop) : (term354 A x) = (~ True).
Proof. exact (MK_COMB (@lem3746172) (@lem3746171 A x)). Qed.
Lemma lem3746175 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3746176 {A : Type'} (x : A -> Prop) : (term354 A x) = False.
Proof. exact (TRANS (@lem3746173 A x) (@lem3746175)). Qed.
Lemma lem3746177 {A : Type'} (x : A -> Prop) : (term346 A x) = (True /\ False).
Proof. exact (MK_COMB (@lem3746168 A x) (@lem3746176 A x)). Qed.
Lemma lem3746179 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3746180 : (True /\ False) = False.
Proof. exact (@lem3746179 False). Qed.
Lemma lem3746181 {A : Type'} (x : A -> Prop) : (term346 A x) = False.
Proof. exact (TRANS (@lem3746177 A x) (@lem3746180)). Qed.
Lemma lem3746182 {A : Type'} (x : A -> Prop) : (@PSUBSET A x x) = False.
Proof. exact (TRANS (@lem3746144 A x) (@lem3746181 A x)). Qed.
Lemma lem3746183 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term203 A s x) = (term355 A s x).
Proof. exact (MK_COMB (@lem3746140 A s x) (@lem3746182 A x)). Qed.
Lemma lem3746185 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem3746186 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term355 A s x) = False.
Proof. exact (@lem3746185 (term343 A s x)). Qed.
Lemma lem3746187 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term203 A s x) = False.
Proof. exact (TRANS (@lem3746183 A s x) (@lem3746186 A s x)). Qed.
Lemma lem3746188 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746189 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term205 A s x) = (~ False).
Proof. exact (MK_COMB (@lem3746188) (@lem3746187 A s x)). Qed.
Lemma lem3746191 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3746192 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term205 A s x) = True.
Proof. exact (TRANS (@lem3746189 A s x) (@lem3746191)). Qed.
Lemma lem3746193 {A : Type'} (s : A -> Prop) : (term207 A s) = (term356 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3746192 A s x)). Qed.
Lemma lem3746194 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746195 {A : Type'} (s : A -> Prop) : (term209 A s) = (term357 A).
Proof. exact (MK_COMB (@lem3746194 A) (@lem3746193 A s)). Qed.
Lemma lem3746197 {A : Type'} (t : Prop) : (term352 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3746198 {A : Type'} (t : Prop) : (term358 A t) = t.
Proof. exact (@lem3746197 (A -> Prop) t). Qed.
Lemma lem3746199 {A : Type'} : (term357 A) = True.
Proof. exact (@lem3746198 A True). Qed.
Lemma lem3746200 {A : Type'} (s : A -> Prop) : (term209 A s) = True.
Proof. exact (TRANS (@lem3746195 A s) (@lem3746199 A)). Qed.
Lemma lem3746201 {A : Type'} (s : A -> Prop) : True = (term209 A s).
Proof. exact (SYM (@lem3746200 A s)). Qed.
Lemma lem3746202 {A : Type'} (s : A -> Prop) : term209 A s.
Proof. exact (EQ_MP (@lem3746201 A s) (@lem0)). Qed.
Lemma lem3746222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3746223 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3746222 A s t). Qed.
Lemma lem3746224 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (@SUBSET A s x) = (term343 A s x).
Proof. exact (@lem3746223 A s x). Qed.
Lemma lem3746231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746232 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term227 A s x) = (term344 A s x).
Proof. exact (MK_COMB (@lem3746231) (@lem3746224 A s x)). Qed.
Lemma lem3746234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3746235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (@lem3746234 A s t). Qed.
Lemma lem3746236 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (@PSUBSET A x y) = (term345 A x y).
Proof. exact (@lem3746235 A x y). Qed.
Lemma lem3746240 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3746241 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3746240 A s t). Qed.
Lemma lem3746242 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (@SUBSET A x y) = (term343 A x y).
Proof. exact (@lem3746241 A x y). Qed.
Lemma lem3746249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746250 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term227 A x y) = (term344 A x y).
Proof. exact (MK_COMB (@lem3746249) (@lem3746242 A x y)). Qed.
Lemma lem3746254 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3746255 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (@lem3746254 A s t). Qed.
Lemma lem3746256 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (x = y) = (term359 A x y).
Proof. exact (@lem3746255 A x y). Qed.
Lemma lem3746265 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746266 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term360 A x y) = (term361 A x y).
Proof. exact (MK_COMB (@lem3746265) (@lem3746256 A x y)). Qed.
Lemma lem3746267 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term345 A x y) = (term362 A x y).
Proof. exact (MK_COMB (@lem3746250 A x y) (@lem3746266 A x y)). Qed.
Lemma lem3746270 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (@PSUBSET A x y) = (term362 A x y).
Proof. exact (TRANS (@lem3746236 A x y) (@lem3746267 A x y)). Qed.
Lemma lem3746271 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term199 A s x y) = (term363 A s x y).
Proof. exact (MK_COMB (@lem3746232 A s x) (@lem3746270 A x y)). Qed.
Lemma lem3746274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746275 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term223 A s x y) = (term364 A s x y).
Proof. exact (MK_COMB (@lem3746274) (@lem3746271 A s x y)). Qed.
Lemma lem3746279 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3746280 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3746279 A s t). Qed.
Lemma lem3746281 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (@SUBSET A s y) = (term343 A s y).
Proof. exact (@lem3746280 A s y). Qed.
Lemma lem3746288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746289 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term227 A s y) = (term344 A s y).
Proof. exact (MK_COMB (@lem3746288) (@lem3746281 A s y)). Qed.
Lemma lem3746291 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3746292 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (@lem3746291 A s t). Qed.
Lemma lem3746293 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (@PSUBSET A y z) = (term345 A y z).
Proof. exact (@lem3746292 A y z). Qed.
Lemma lem3746297 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3746298 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3746297 A s t). Qed.
Lemma lem3746299 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (@SUBSET A y z) = (term343 A y z).
Proof. exact (@lem3746298 A y z). Qed.
Lemma lem3746306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746307 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term227 A y z) = (term344 A y z).
Proof. exact (MK_COMB (@lem3746306) (@lem3746299 A y z)). Qed.
Lemma lem3746311 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3746312 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (@lem3746311 A s t). Qed.
Lemma lem3746313 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (y = z) = (term359 A y z).
Proof. exact (@lem3746312 A y z). Qed.
Lemma lem3746322 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746323 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term360 A y z) = (term361 A y z).
Proof. exact (MK_COMB (@lem3746322) (@lem3746313 A y z)). Qed.
Lemma lem3746324 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term345 A y z) = (term362 A y z).
Proof. exact (MK_COMB (@lem3746307 A y z) (@lem3746323 A y z)). Qed.
Lemma lem3746327 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (@PSUBSET A y z) = (term362 A y z).
Proof. exact (TRANS (@lem3746293 A y z) (@lem3746324 A y z)). Qed.
Lemma lem3746328 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term199 A s y z) = (term363 A s y z).
Proof. exact (MK_COMB (@lem3746289 A s y) (@lem3746327 A y z)). Qed.
Lemma lem3746331 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term224 A x s y z) = (term365 A x s y z).
Proof. exact (MK_COMB (@lem3746275 A s x y) (@lem3746328 A s y z)). Qed.
Lemma lem3746334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3746335 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term366 A x s y z) = (term367 A x s y z).
Proof. exact (MK_COMB (@lem3746334) (@lem3746331 A x s y z)). Qed.
Lemma lem3746337 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3746338 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (@lem3746337 A s t). Qed.
Lemma lem3746339 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (@PSUBSET A x z) = (term345 A x z).
Proof. exact (@lem3746338 A x z). Qed.
Lemma lem3746343 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3746344 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3746343 A s t). Qed.
Lemma lem3746345 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (@SUBSET A x z) = (term343 A x z).
Proof. exact (@lem3746344 A x z). Qed.
Lemma lem3746352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746353 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term227 A x z) = (term344 A x z).
Proof. exact (MK_COMB (@lem3746352) (@lem3746345 A x z)). Qed.
Lemma lem3746357 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3746358 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (@lem3746357 A s t). Qed.
Lemma lem3746359 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (x = z) = (term359 A x z).
Proof. exact (@lem3746358 A x z). Qed.
Lemma lem3746368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746369 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term360 A x z) = (term361 A x z).
Proof. exact (MK_COMB (@lem3746368) (@lem3746359 A x z)). Qed.
Lemma lem3746370 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term345 A x z) = (term362 A x z).
Proof. exact (MK_COMB (@lem3746353 A x z) (@lem3746369 A x z)). Qed.
Lemma lem3746373 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (@PSUBSET A x z) = (term362 A x z).
Proof. exact (TRANS (@lem3746339 A x z) (@lem3746370 A x z)). Qed.
Lemma lem3746374 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term238 A s y x z) = (term368 A s y x z).
Proof. exact (MK_COMB (@lem3746335 A x s y z) (@lem3746373 A x z)). Qed.
Lemma lem3746377 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : (term240 A s y x) = (term369 A s y x).
Proof. exact (fun_ext (fun z : A -> Prop => @lem3746374 A s y x z)). Qed.
Lemma lem3746378 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746379 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : (term242 A s y x) = (term370 A s y x).
Proof. exact (MK_COMB (@lem3746378 A) (@lem3746377 A s y x)). Qed.
Lemma lem3746384 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term244 A s x) = (term371 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem3746379 A s y x)). Qed.
Lemma lem3746385 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746386 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term246 A s x) = (term372 A s x).
Proof. exact (MK_COMB (@lem3746385 A) (@lem3746384 A s x)). Qed.
Lemma lem3746391 {A : Type'} (s : A -> Prop) : (term248 A s) = (term373 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3746386 A s x)). Qed.
Lemma lem3746392 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746393 {A : Type'} (s : A -> Prop) : (term250 A s) = (term374 A s).
Proof. exact (MK_COMB (@lem3746392 A) (@lem3746391 A s)). Qed.
Lemma lem3746398 {A : Type'} (s : A -> Prop) : (term374 A s) = (term250 A s).
Proof. exact (SYM (@lem3746393 A s)). Qed.
Lemma lem3746424 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746425 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746424 A P x). Qed.
Lemma lem3746426 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3746425 A s x). Qed.
Lemma lem3746427 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3746428 {A : Type'} (s : A -> Prop) (x : A) : (term375 A x s) = (term376 A s x).
Proof. exact (MK_COMB (@lem3746427) (@lem3746426 A s x)). Qed.
Lemma lem3746430 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746431 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746430 A P x). Qed.
Lemma lem3746432 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem3746431 A x x'). Qed.
Lemma lem3746433 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term377 A s x' x) = (term378 A s x x').
Proof. exact (MK_COMB (@lem3746428 A s x') (@lem3746432 A x x')). Qed.
Lemma lem3746436 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term379 A s x) = (term380 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3746433 A s x x')). Qed.
Lemma lem3746437 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746438 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term343 A s x) = (term381 A s x).
Proof. exact (MK_COMB (@lem3746437 A) (@lem3746436 A s x)). Qed.
Lemma lem3746443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746444 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term344 A s x) = (term382 A s x).
Proof. exact (MK_COMB (@lem3746443) (@lem3746438 A s x)). Qed.
Lemma lem3746454 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746455 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746454 A P x). Qed.
Lemma lem3746456 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem3746455 A x x'). Qed.
Lemma lem3746457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3746458 {A : Type'} (x : A -> Prop) (x' : A) : (term375 A x' x) = (term376 A x x').
Proof. exact (MK_COMB (@lem3746457) (@lem3746456 A x x')). Qed.
Lemma lem3746460 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746461 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746460 A P x). Qed.
Lemma lem3746462 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem3746461 A y x). Qed.
Lemma lem3746463 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term377 A x x' y) = (term378 A x y x').
Proof. exact (MK_COMB (@lem3746458 A x x') (@lem3746462 A y x')). Qed.
Lemma lem3746466 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term379 A x y) = (term380 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3746463 A x y x')). Qed.
Lemma lem3746467 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746468 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term343 A x y) = (term381 A x y).
Proof. exact (MK_COMB (@lem3746467 A) (@lem3746466 A x y)). Qed.
Lemma lem3746473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746474 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term344 A x y) = (term382 A x y).
Proof. exact (MK_COMB (@lem3746473) (@lem3746468 A x y)). Qed.
Lemma lem3746482 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746483 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746482 A P x). Qed.
Lemma lem3746484 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem3746483 A x x'). Qed.
Lemma lem3746485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3746486 {A : Type'} (x : A -> Prop) (x' : A) : (term383 A x' x) = (term384 A x x').
Proof. exact (MK_COMB (@lem3746485) (@lem3746484 A x x')). Qed.
Lemma lem3746488 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746489 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746488 A P x). Qed.
Lemma lem3746490 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem3746489 A y x). Qed.
Lemma lem3746491 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : ((@IN A x' x) = (@IN A x' y)) = ((x x') = (y x')).
Proof. exact (MK_COMB (@lem3746486 A x x') (@lem3746490 A y x')). Qed.
Lemma lem3746494 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term385 A x y) = (term386 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3746491 A x y x')). Qed.
Lemma lem3746495 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746496 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term359 A x y) = (term387 A x y).
Proof. exact (MK_COMB (@lem3746495 A) (@lem3746494 A x y)). Qed.
Lemma lem3746501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746502 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term361 A x y) = (term388 A x y).
Proof. exact (MK_COMB (@lem3746501) (@lem3746496 A x y)). Qed.
Lemma lem3746503 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term362 A x y) = (term389 A x y).
Proof. exact (MK_COMB (@lem3746474 A x y) (@lem3746502 A x y)). Qed.
Lemma lem3746506 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term363 A s x y) = (term390 A s x y).
Proof. exact (MK_COMB (@lem3746444 A s x) (@lem3746503 A x y)). Qed.
Lemma lem3746509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746510 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term364 A s x y) = (term391 A s x y).
Proof. exact (MK_COMB (@lem3746509) (@lem3746506 A s x y)). Qed.
Lemma lem3746520 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746521 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746520 A P x). Qed.
Lemma lem3746522 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3746521 A s x). Qed.
Lemma lem3746523 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3746524 {A : Type'} (s : A -> Prop) (x : A) : (term375 A x s) = (term376 A s x).
Proof. exact (MK_COMB (@lem3746523) (@lem3746522 A s x)). Qed.
Lemma lem3746526 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746527 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746526 A P x). Qed.
Lemma lem3746528 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem3746527 A y x). Qed.
Lemma lem3746529 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A) : (term377 A s x y) = (term378 A s y x).
Proof. exact (MK_COMB (@lem3746524 A s x) (@lem3746528 A y x)). Qed.
Lemma lem3746532 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term379 A s y) = (term380 A s y).
Proof. exact (fun_ext (fun x : A => @lem3746529 A s y x)). Qed.
Lemma lem3746533 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746534 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term343 A s y) = (term381 A s y).
Proof. exact (MK_COMB (@lem3746533 A) (@lem3746532 A s y)). Qed.
Lemma lem3746539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746540 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term344 A s y) = (term382 A s y).
Proof. exact (MK_COMB (@lem3746539) (@lem3746534 A s y)). Qed.
Lemma lem3746550 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746551 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746550 A P x). Qed.
Lemma lem3746552 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem3746551 A y x). Qed.
Lemma lem3746553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3746554 {A : Type'} (y : A -> Prop) (x : A) : (term375 A x y) = (term376 A y x).
Proof. exact (MK_COMB (@lem3746553) (@lem3746552 A y x)). Qed.
Lemma lem3746556 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746557 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746556 A P x). Qed.
Lemma lem3746558 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem3746557 A z x). Qed.
Lemma lem3746559 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term377 A y x z) = (term378 A y z x).
Proof. exact (MK_COMB (@lem3746554 A y x) (@lem3746558 A z x)). Qed.
Lemma lem3746562 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term379 A y z) = (term380 A y z).
Proof. exact (fun_ext (fun x : A => @lem3746559 A y z x)). Qed.
Lemma lem3746563 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746564 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term343 A y z) = (term381 A y z).
Proof. exact (MK_COMB (@lem3746563 A) (@lem3746562 A y z)). Qed.
Lemma lem3746569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746570 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term344 A y z) = (term382 A y z).
Proof. exact (MK_COMB (@lem3746569) (@lem3746564 A y z)). Qed.
Lemma lem3746578 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746579 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746578 A P x). Qed.
Lemma lem3746580 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem3746579 A y x). Qed.
Lemma lem3746581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3746582 {A : Type'} (y : A -> Prop) (x : A) : (term383 A x y) = (term384 A y x).
Proof. exact (MK_COMB (@lem3746581) (@lem3746580 A y x)). Qed.
Lemma lem3746584 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746585 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746584 A P x). Qed.
Lemma lem3746586 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem3746585 A z x). Qed.
Lemma lem3746587 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : ((@IN A x y) = (@IN A x z)) = ((y x) = (z x)).
Proof. exact (MK_COMB (@lem3746582 A y x) (@lem3746586 A z x)). Qed.
Lemma lem3746590 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term385 A y z) = (term386 A y z).
Proof. exact (fun_ext (fun x : A => @lem3746587 A y z x)). Qed.
Lemma lem3746591 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746592 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term359 A y z) = (term387 A y z).
Proof. exact (MK_COMB (@lem3746591 A) (@lem3746590 A y z)). Qed.
Lemma lem3746597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746598 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term361 A y z) = (term388 A y z).
Proof. exact (MK_COMB (@lem3746597) (@lem3746592 A y z)). Qed.
Lemma lem3746599 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term362 A y z) = (term389 A y z).
Proof. exact (MK_COMB (@lem3746570 A y z) (@lem3746598 A y z)). Qed.
Lemma lem3746602 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term363 A s y z) = (term390 A s y z).
Proof. exact (MK_COMB (@lem3746540 A s y) (@lem3746599 A y z)). Qed.
Lemma lem3746605 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term365 A x s y z) = (term392 A x s y z).
Proof. exact (MK_COMB (@lem3746510 A s x y) (@lem3746602 A s y z)). Qed.
Lemma lem3746608 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3746609 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term367 A x s y z) = (term393 A x s y z).
Proof. exact (MK_COMB (@lem3746608) (@lem3746605 A x s y z)). Qed.
Lemma lem3746619 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746620 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746619 A P x). Qed.
Lemma lem3746621 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem3746620 A x x'). Qed.
Lemma lem3746622 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3746623 {A : Type'} (x : A -> Prop) (x' : A) : (term375 A x' x) = (term376 A x x').
Proof. exact (MK_COMB (@lem3746622) (@lem3746621 A x x')). Qed.
Lemma lem3746625 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746626 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746625 A P x). Qed.
Lemma lem3746627 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem3746626 A z x). Qed.
Lemma lem3746628 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term377 A x x' z) = (term378 A x z x').
Proof. exact (MK_COMB (@lem3746623 A x x') (@lem3746627 A z x')). Qed.
Lemma lem3746631 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term379 A x z) = (term380 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3746628 A x z x')). Qed.
Lemma lem3746632 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746633 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term343 A x z) = (term381 A x z).
Proof. exact (MK_COMB (@lem3746632 A) (@lem3746631 A x z)). Qed.
Lemma lem3746638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746639 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term344 A x z) = (term382 A x z).
Proof. exact (MK_COMB (@lem3746638) (@lem3746633 A x z)). Qed.
Lemma lem3746647 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746648 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746647 A P x). Qed.
Lemma lem3746649 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem3746648 A x x'). Qed.
Lemma lem3746650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3746651 {A : Type'} (x : A -> Prop) (x' : A) : (term383 A x' x) = (term384 A x x').
Proof. exact (MK_COMB (@lem3746650) (@lem3746649 A x x')). Qed.
Lemma lem3746653 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3746654 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3746653 A P x). Qed.
Lemma lem3746655 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem3746654 A z x). Qed.
Lemma lem3746656 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : ((@IN A x' x) = (@IN A x' z)) = ((x x') = (z x')).
Proof. exact (MK_COMB (@lem3746651 A x x') (@lem3746655 A z x')). Qed.
Lemma lem3746659 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term385 A x z) = (term386 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3746656 A x z x')). Qed.
Lemma lem3746660 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746661 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term359 A x z) = (term387 A x z).
Proof. exact (MK_COMB (@lem3746660 A) (@lem3746659 A x z)). Qed.
Lemma lem3746666 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746667 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term361 A x z) = (term388 A x z).
Proof. exact (MK_COMB (@lem3746666) (@lem3746661 A x z)). Qed.
Lemma lem3746668 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term362 A x z) = (term389 A x z).
Proof. exact (MK_COMB (@lem3746639 A x z) (@lem3746667 A x z)). Qed.
Lemma lem3746671 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term368 A s y x z) = (term394 A s y x z).
Proof. exact (MK_COMB (@lem3746609 A x s y z) (@lem3746668 A x z)). Qed.
Lemma lem3746674 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : (term369 A s y x) = (term395 A s y x).
Proof. exact (fun_ext (fun z : A -> Prop => @lem3746671 A s y x z)). Qed.
Lemma lem3746675 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746676 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : (term370 A s y x) = (term396 A s y x).
Proof. exact (MK_COMB (@lem3746675 A) (@lem3746674 A s y x)). Qed.
Lemma lem3746681 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term371 A s x) = (term397 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem3746676 A s y x)). Qed.
Lemma lem3746682 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746683 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term372 A s x) = (term398 A s x).
Proof. exact (MK_COMB (@lem3746682 A) (@lem3746681 A s x)). Qed.
Lemma lem3746688 {A : Type'} (s : A -> Prop) : (term373 A s) = (term399 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3746683 A s x)). Qed.
Lemma lem3746689 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746690 {A : Type'} (s : A -> Prop) : (term374 A s) = (term400 A s).
Proof. exact (MK_COMB (@lem3746689 A) (@lem3746688 A s)). Qed.
Lemma lem3746695 {A : Type'} (s : A -> Prop) : (term400 A s) = (term374 A s).
Proof. exact (SYM (@lem3746690 A s)). Qed.
Lemma lem3746697 (p : Prop) : p = (term401 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3746698 {A : Type'} (s : A -> Prop) : (term400 A s) = (term402 A s).
Proof. exact (@lem3746697 (term400 A s)). Qed.
Lemma lem3746699 {A : Type'} (s : A -> Prop) : (term402 A s) = (term400 A s).
Proof. exact (SYM (@lem3746698 A s)). Qed.
Lemma lem3746700 {A : Type'} (s : A -> Prop) (h1 : term403 A s) : term403 A s.
Proof. exact (h1). Qed.
Lemma lem3746703 {A : Type'} (s : A -> Prop) (h1 : term402 A s) : term402 A s.
Proof. exact (h1). Qed.
Lemma lem3746704 {A : Type'} (s : A -> Prop) : term404 A s.
Proof. exact (fun h0 : term402 A s => @lem3746703 A s h0). Qed.
Lemma lem3746705 {A : Type'} (s : A -> Prop) (h1 : term404 A s) : term404 A s.
Proof. exact (h1). Qed.
Lemma lem3746706 {A : Type'} (s : A -> Prop) (h1 : term402 A s) : term402 A s.
Proof. exact (h1). Qed.
Lemma lem3746707 {A : Type'} (s : A -> Prop) (h1 : term402 A s) (h2 : term404 A s) : term402 A s.
Proof. exact (@lem3746705 A s h2 (@lem3746706 A s h1)). Qed.
Lemma lem3746708 {A : Type'} (s : A -> Prop) (h1 : term402 A s) : term405 A s.
Proof. exact (fun h0 : term404 A s => @lem3746707 A s h1 h0). Qed.
Lemma lem3746709 {A : Type'} (s : A -> Prop) (h1 : term404 A s) : term404 A s.
Proof. exact (h1). Qed.
Lemma lem3746710 {A : Type'} (s : A -> Prop) (h1 : term402 A s) (h2 : term404 A s) : term402 A s.
Proof. exact (@lem3746708 A s h1 (@lem3746709 A s h2)). Qed.
Lemma lem3746711 {A : Type'} (s : A -> Prop) (h1 : term404 A s) : term404 A s.
Proof. exact (fun h0 : term402 A s => @lem3746710 A s h0 h1). Qed.
Lemma lem3746712 {A : Type'} (s : A -> Prop) : term406 A s.
Proof. exact (fun h0 : term404 A s => @lem3746711 A s h0). Qed.
Lemma lem3746715 {A : Type'} (s : A -> Prop) : term404 A s.
Proof. exact (@lem3746712 A s (@lem3746704 A s)). Qed.
Lemma lem3746716 {A : Type'} (s : A -> Prop) : term404 A s.
Proof. exact (@lem3746715 A s). Qed.
Lemma lem3746722 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3746723 {A : Type'} (s : A -> Prop) : (term402 A s) = (term407 A s).
Proof. exact (@lem3746722 (term403 A s)). Qed.
Lemma lem3746725 (t : Prop) : (term14 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3746726 {A : Type'} (s : A -> Prop) : (term407 A s) = (term400 A s).
Proof. exact (@lem3746725 (term400 A s)). Qed.
Lemma lem3746731 {A : Type'} (s : A -> Prop) : (term402 A s) = (term400 A s).
Proof. exact (TRANS (@lem3746723 A s) (@lem3746726 A s)). Qed.
Lemma lem3746796 {A : Type'} : (term408 A) = (term409 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3746731 A s)). Qed.
Lemma lem3746797 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746806 {A : Type'} : (term410 A) = (term411 A).
Proof. exact (MK_COMB (@lem3746797 A) (@lem3746796 A)). Qed.
Lemma lem3746811 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : ((x x') = (z x')) = ((x x') = (z x')).
Proof. exact (eq_refl ((x x') = (z x'))). Qed.
Lemma lem3746812 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term386 A x z) = (term386 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3746811 A x z x')). Qed.
Lemma lem3746813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746814 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term387 A x z) = (term387 A x z).
Proof. exact (MK_COMB (@lem3746813 A) (@lem3746812 A x z)). Qed.
Lemma lem3746815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746816 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term388 A x z) = (term388 A x z).
Proof. exact (MK_COMB (@lem3746815) (@lem3746814 A x z)). Qed.
Lemma lem3746821 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term378 A x z x') = (term378 A x z x').
Proof. exact (eq_refl (term378 A x z x')). Qed.
Lemma lem3746822 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term380 A x z) = (term380 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3746821 A x z x')). Qed.
Lemma lem3746823 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746824 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term381 A x z) = (term381 A x z).
Proof. exact (MK_COMB (@lem3746823 A) (@lem3746822 A x z)). Qed.
Lemma lem3746825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746826 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term382 A x z) = (term382 A x z).
Proof. exact (MK_COMB (@lem3746825) (@lem3746824 A x z)). Qed.
Lemma lem3746827 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term389 A x z) = (term389 A x z).
Proof. exact (MK_COMB (@lem3746826 A x z) (@lem3746816 A x z)). Qed.
Lemma lem3746832 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : ((y x) = (z x)) = ((y x) = (z x)).
Proof. exact (eq_refl ((y x) = (z x))). Qed.
Lemma lem3746833 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term386 A y z) = (term386 A y z).
Proof. exact (fun_ext (fun x : A => @lem3746832 A y z x)). Qed.
Lemma lem3746834 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746835 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term387 A y z) = (term387 A y z).
Proof. exact (MK_COMB (@lem3746834 A) (@lem3746833 A y z)). Qed.
Lemma lem3746836 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746837 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term388 A y z) = (term388 A y z).
Proof. exact (MK_COMB (@lem3746836) (@lem3746835 A y z)). Qed.
Lemma lem3746842 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term378 A y z x) = (term378 A y z x).
Proof. exact (eq_refl (term378 A y z x)). Qed.
Lemma lem3746843 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term380 A y z) = (term380 A y z).
Proof. exact (fun_ext (fun x : A => @lem3746842 A y z x)). Qed.
Lemma lem3746844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746845 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term381 A y z) = (term381 A y z).
Proof. exact (MK_COMB (@lem3746844 A) (@lem3746843 A y z)). Qed.
Lemma lem3746846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746847 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term382 A y z) = (term382 A y z).
Proof. exact (MK_COMB (@lem3746846) (@lem3746845 A y z)). Qed.
Lemma lem3746848 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term389 A y z) = (term389 A y z).
Proof. exact (MK_COMB (@lem3746847 A y z) (@lem3746837 A y z)). Qed.
Lemma lem3746853 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A) : (term378 A s y x) = (term378 A s y x).
Proof. exact (eq_refl (term378 A s y x)). Qed.
Lemma lem3746854 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term380 A s y) = (term380 A s y).
Proof. exact (fun_ext (fun x : A => @lem3746853 A s y x)). Qed.
Lemma lem3746855 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746856 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term381 A s y) = (term381 A s y).
Proof. exact (MK_COMB (@lem3746855 A) (@lem3746854 A s y)). Qed.
Lemma lem3746857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746858 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term382 A s y) = (term382 A s y).
Proof. exact (MK_COMB (@lem3746857) (@lem3746856 A s y)). Qed.
Lemma lem3746859 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term390 A s y z) = (term390 A s y z).
Proof. exact (MK_COMB (@lem3746858 A s y) (@lem3746848 A y z)). Qed.
Lemma lem3746864 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : ((x x') = (y x')) = ((x x') = (y x')).
Proof. exact (eq_refl ((x x') = (y x'))). Qed.
Lemma lem3746865 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term386 A x y) = (term386 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3746864 A x y x')). Qed.
Lemma lem3746866 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746867 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term387 A x y) = (term387 A x y).
Proof. exact (MK_COMB (@lem3746866 A) (@lem3746865 A x y)). Qed.
Lemma lem3746868 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3746869 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term388 A x y) = (term388 A x y).
Proof. exact (MK_COMB (@lem3746868) (@lem3746867 A x y)). Qed.
Lemma lem3746874 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term378 A x y x') = (term378 A x y x').
Proof. exact (eq_refl (term378 A x y x')). Qed.
Lemma lem3746875 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term380 A x y) = (term380 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3746874 A x y x')). Qed.
Lemma lem3746876 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746877 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term381 A x y) = (term381 A x y).
Proof. exact (MK_COMB (@lem3746876 A) (@lem3746875 A x y)). Qed.
Lemma lem3746878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746879 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term382 A x y) = (term382 A x y).
Proof. exact (MK_COMB (@lem3746878) (@lem3746877 A x y)). Qed.
Lemma lem3746880 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term389 A x y) = (term389 A x y).
Proof. exact (MK_COMB (@lem3746879 A x y) (@lem3746869 A x y)). Qed.
Lemma lem3746885 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term378 A s x x') = (term378 A s x x').
Proof. exact (eq_refl (term378 A s x x')). Qed.
Lemma lem3746886 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term380 A s x) = (term380 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3746885 A s x x')). Qed.
Lemma lem3746887 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3746888 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term381 A s x) = (term381 A s x).
Proof. exact (MK_COMB (@lem3746887 A) (@lem3746886 A s x)). Qed.
Lemma lem3746889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746890 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term382 A s x) = (term382 A s x).
Proof. exact (MK_COMB (@lem3746889) (@lem3746888 A s x)). Qed.
Lemma lem3746891 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term390 A s x y) = (term390 A s x y).
Proof. exact (MK_COMB (@lem3746890 A s x) (@lem3746880 A x y)). Qed.
Lemma lem3746892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3746893 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term391 A s x y) = (term391 A s x y).
Proof. exact (MK_COMB (@lem3746892) (@lem3746891 A s x y)). Qed.
Lemma lem3746894 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term392 A x s y z) = (term392 A x s y z).
Proof. exact (MK_COMB (@lem3746893 A s x y) (@lem3746859 A s y z)). Qed.
Lemma lem3746895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3746896 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term393 A x s y z) = (term393 A x s y z).
Proof. exact (MK_COMB (@lem3746895) (@lem3746894 A x s y z)). Qed.
Lemma lem3746897 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term394 A s y x z) = (term394 A s y x z).
Proof. exact (MK_COMB (@lem3746896 A x s y z) (@lem3746827 A x z)). Qed.
Lemma lem3746898 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : (term395 A s y x) = (term395 A s y x).
Proof. exact (fun_ext (fun z : A -> Prop => @lem3746897 A s y x z)). Qed.
Lemma lem3746899 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746900 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : (term396 A s y x) = (term396 A s y x).
Proof. exact (MK_COMB (@lem3746899 A) (@lem3746898 A s y x)). Qed.
Lemma lem3746901 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term397 A s x) = (term397 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem3746900 A s y x)). Qed.
Lemma lem3746902 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746903 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term398 A s x) = (term398 A s x).
Proof. exact (MK_COMB (@lem3746902 A) (@lem3746901 A s x)). Qed.
Lemma lem3746904 {A : Type'} (s : A -> Prop) : (term399 A s) = (term399 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3746903 A s x)). Qed.
Lemma lem3746905 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746906 {A : Type'} (s : A -> Prop) : (term400 A s) = (term400 A s).
Proof. exact (MK_COMB (@lem3746905 A) (@lem3746904 A s)). Qed.
Lemma lem3746907 {A : Type'} : (term409 A) = (term409 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3746906 A s)). Qed.
Lemma lem3746908 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3746909 {A : Type'} : (term411 A) = (term411 A).
Proof. exact (MK_COMB (@lem3746908 A) (@lem3746907 A)). Qed.
Lemma lem3747008 {A : Type'} : (term410 A) = (term411 A).
Proof. exact (TRANS (@lem3746806 A) (@lem3746909 A)). Qed.
Lemma lem3747009 {A : Type'} : (term411 A) = (term410 A).
Proof. exact (SYM (@lem3747008 A)). Qed.
Lemma lem3747010 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term392 A x s y z) : term392 A x s y z.
Proof. exact (h1). Qed.
Lemma lem3747012 (p : Prop) : p = (term401 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3747013 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term389 A x z) = (term412 A x z).
Proof. exact (@lem3747012 (term389 A x z)). Qed.
Lemma lem3747014 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term412 A x z) = (term389 A x z).
Proof. exact (SYM (@lem3747013 A x z)). Qed.
Lemma lem3747015 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term413 A x z) : term413 A x z.
Proof. exact (h1). Qed.
Lemma lem3747022 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term378 A s x x') = (term414 A s x x').
Proof. exact (@lem17265 (s x') (x x')). Qed.
Lemma lem3747023 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term380 A s x) = (term415 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3747022 A s x x')). Qed.
Lemma lem3747024 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747025 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term381 A s x) = (term416 A s x).
Proof. exact (MK_COMB (@lem3747024 A) (@lem3747023 A s x)). Qed.
Lemma lem3747032 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term378 A x y x') = (term414 A x y x').
Proof. exact (@lem17265 (x x') (y x')). Qed.
Lemma lem3747033 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term380 A x y) = (term415 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747032 A x y x')). Qed.
Lemma lem3747034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747035 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term381 A x y) = (term416 A x y).
Proof. exact (MK_COMB (@lem3747034 A) (@lem3747033 A x y)). Qed.
Lemma lem3747050 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term417 A x y x') = (term418 A x y x').
Proof. exact (@lem17646 (x x') (y x')). Qed.
Lemma lem3747051 {A : Type'} (P : A -> Prop) : (term419 A P) = (term420 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3747052 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term388 A x y) = (term421 A x y).
Proof. exact (@lem3747051 A (term386 A x y)). Qed.
Lemma lem3747053 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term422 A x y x') = ((x x') = (y x')).
Proof. exact (eq_refl (term422 A x y x')). Qed.
Lemma lem3747054 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3747055 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term423 A x y x') = (term417 A x y x').
Proof. exact (MK_COMB (@lem3747054) (@lem3747053 A x y x')). Qed.
Lemma lem3747056 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term423 A x y x') = (term418 A x y x').
Proof. exact (TRANS (@lem3747055 A x y x') (@lem3747050 A x y x')). Qed.
Lemma lem3747057 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term424 A x y) = (term425 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747056 A x y x')). Qed.
Lemma lem3747058 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747059 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term421 A x y) = (term426 A x y).
Proof. exact (MK_COMB (@lem3747058 A) (@lem3747057 A x y)). Qed.
Lemma lem3747060 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term388 A x y) = (term426 A x y).
Proof. exact (TRANS (@lem3747052 A x y) (@lem3747059 A x y)). Qed.
Lemma lem3747061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747062 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term382 A x y) = (term427 A x y).
Proof. exact (MK_COMB (@lem3747061) (@lem3747035 A x y)). Qed.
Lemma lem3747063 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term389 A x y) = (term428 A x y).
Proof. exact (MK_COMB (@lem3747062 A x y) (@lem3747060 A x y)). Qed.
Lemma lem3747064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747065 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term382 A s x) = (term427 A s x).
Proof. exact (MK_COMB (@lem3747064) (@lem3747025 A s x)). Qed.
Lemma lem3747066 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term390 A s x y) = (term429 A s x y).
Proof. exact (MK_COMB (@lem3747065 A s x) (@lem3747063 A x y)). Qed.
Lemma lem3747073 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A) : (term378 A s y x) = (term414 A s y x).
Proof. exact (@lem17265 (s x) (y x)). Qed.
Lemma lem3747074 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term380 A s y) = (term415 A s y).
Proof. exact (fun_ext (fun x : A => @lem3747073 A s y x)). Qed.
Lemma lem3747075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747076 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term381 A s y) = (term416 A s y).
Proof. exact (MK_COMB (@lem3747075 A) (@lem3747074 A s y)). Qed.
Lemma lem3747083 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term378 A y z x) = (term414 A y z x).
Proof. exact (@lem17265 (y x) (z x)). Qed.
Lemma lem3747084 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term380 A y z) = (term415 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747083 A y z x)). Qed.
Lemma lem3747085 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747086 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term381 A y z) = (term416 A y z).
Proof. exact (MK_COMB (@lem3747085 A) (@lem3747084 A y z)). Qed.
Lemma lem3747101 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term417 A y z x) = (term418 A y z x).
Proof. exact (@lem17646 (y x) (z x)). Qed.
Lemma lem3747102 {A : Type'} (P : A -> Prop) : (term419 A P) = (term420 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3747103 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term388 A y z) = (term421 A y z).
Proof. exact (@lem3747102 A (term386 A y z)). Qed.
Lemma lem3747104 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term422 A y z x) = ((y x) = (z x)).
Proof. exact (eq_refl (term422 A y z x)). Qed.
Lemma lem3747105 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3747106 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term423 A y z x) = (term417 A y z x).
Proof. exact (MK_COMB (@lem3747105) (@lem3747104 A y z x)). Qed.
Lemma lem3747107 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term423 A y z x) = (term418 A y z x).
Proof. exact (TRANS (@lem3747106 A y z x) (@lem3747101 A y z x)). Qed.
Lemma lem3747108 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term424 A y z) = (term425 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747107 A y z x)). Qed.
Lemma lem3747109 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747110 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term421 A y z) = (term426 A y z).
Proof. exact (MK_COMB (@lem3747109 A) (@lem3747108 A y z)). Qed.
Lemma lem3747111 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term388 A y z) = (term426 A y z).
Proof. exact (TRANS (@lem3747103 A y z) (@lem3747110 A y z)). Qed.
Lemma lem3747112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747113 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term382 A y z) = (term427 A y z).
Proof. exact (MK_COMB (@lem3747112) (@lem3747086 A y z)). Qed.
Lemma lem3747114 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term389 A y z) = (term428 A y z).
Proof. exact (MK_COMB (@lem3747113 A y z) (@lem3747111 A y z)). Qed.
Lemma lem3747115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747116 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term382 A s y) = (term427 A s y).
Proof. exact (MK_COMB (@lem3747115) (@lem3747076 A s y)). Qed.
Lemma lem3747117 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term390 A s y z) = (term429 A s y z).
Proof. exact (MK_COMB (@lem3747116 A s y) (@lem3747114 A y z)). Qed.
Lemma lem3747118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747119 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term391 A s x y) = (term430 A s x y).
Proof. exact (MK_COMB (@lem3747118) (@lem3747066 A s x y)). Qed.
Lemma lem3747120 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term392 A x s y z) = (term431 A x s y z).
Proof. exact (MK_COMB (@lem3747119 A s x y) (@lem3747117 A s y z)). Qed.
Lemma lem3747186 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3747187 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (@lem3747186 A P Q). Qed.
Lemma lem3747188 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term434 A x y) = (term435 A x y).
Proof. exact (@lem3747187 A (term436 A x y) (term437 A x y)). Qed.
Lemma lem3747189 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term438 A x y x') = (term439 A x y x').
Proof. exact (eq_refl (term438 A x y x')). Qed.
Lemma lem3747190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747191 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term440 A x y x') = (term441 A x y x').
Proof. exact (MK_COMB (@lem3747190) (@lem3747189 A x y x')). Qed.
Lemma lem3747192 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term442 A x y x') = (term443 A x y x').
Proof. exact (eq_refl (term442 A x y x')). Qed.
Lemma lem3747193 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term444 A x y x') = (term418 A x y x').
Proof. exact (MK_COMB (@lem3747191 A x y x') (@lem3747192 A x y x')). Qed.
Lemma lem3747194 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term445 A x y) = (term425 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747193 A x y x')). Qed.
Lemma lem3747195 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747196 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term434 A x y) = (term426 A x y).
Proof. exact (MK_COMB (@lem3747195 A) (@lem3747194 A x y)). Qed.
Lemma lem3747197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747198 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term446 A x y) = (term447 A x y).
Proof. exact (MK_COMB (@lem3747197) (@lem3747196 A x y)). Qed.
Lemma lem3747199 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term438 A x y x') = (term439 A x y x').
Proof. exact (eq_refl (term438 A x y x')). Qed.
Lemma lem3747200 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term448 A x y) = (term436 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747199 A x y x')). Qed.
Lemma lem3747201 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747202 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term449 A x y) = (term450 A x y).
Proof. exact (MK_COMB (@lem3747201 A) (@lem3747200 A x y)). Qed.
Lemma lem3747203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747204 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term451 A x y) = (term452 A x y).
Proof. exact (MK_COMB (@lem3747203) (@lem3747202 A x y)). Qed.
Lemma lem3747205 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term442 A x y x') = (term443 A x y x').
Proof. exact (eq_refl (term442 A x y x')). Qed.
Lemma lem3747206 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term453 A x y) = (term437 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747205 A x y x')). Qed.
Lemma lem3747207 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747208 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term454 A x y) = (term455 A x y).
Proof. exact (MK_COMB (@lem3747207 A) (@lem3747206 A x y)). Qed.
Lemma lem3747209 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term435 A x y) = (term456 A x y).
Proof. exact (MK_COMB (@lem3747204 A x y) (@lem3747208 A x y)). Qed.
Lemma lem3747210 {A : Type'} (x : A -> Prop) (y : A -> Prop) : ((term434 A x y) = (term435 A x y)) = ((term426 A x y) = (term456 A x y)).
Proof. exact (MK_COMB (@lem3747198 A x y) (@lem3747209 A x y)). Qed.
Lemma lem3747211 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term426 A x y) = (term456 A x y).
Proof. exact (EQ_MP (@lem3747210 A x y) (@lem3747188 A x y)). Qed.
Lemma lem3747272 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term427 A x y) = (term427 A x y).
Proof. exact (eq_refl (term427 A x y)). Qed.
Lemma lem3747273 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term428 A x y) = (term457 A x y).
Proof. exact (MK_COMB (@lem3747272 A x y) (@lem3747211 A x y)). Qed.
Lemma lem3747274 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term427 A s x) = (term427 A s x).
Proof. exact (eq_refl (term427 A s x)). Qed.
Lemma lem3747275 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term429 A s x y) = (term458 A s x y).
Proof. exact (MK_COMB (@lem3747274 A s x) (@lem3747273 A x y)). Qed.
Lemma lem3747276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747277 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term430 A s x y) = (term459 A s x y).
Proof. exact (MK_COMB (@lem3747276) (@lem3747275 A s x y)). Qed.
Lemma lem3747343 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3747344 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (@lem3747343 A P Q). Qed.
Lemma lem3747345 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term434 A y z) = (term435 A y z).
Proof. exact (@lem3747344 A (term436 A y z) (term437 A y z)). Qed.
Lemma lem3747346 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term438 A y z x) = (term439 A y z x).
Proof. exact (eq_refl (term438 A y z x)). Qed.
Lemma lem3747347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747348 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term440 A y z x) = (term441 A y z x).
Proof. exact (MK_COMB (@lem3747347) (@lem3747346 A y z x)). Qed.
Lemma lem3747349 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term442 A y z x) = (term443 A y z x).
Proof. exact (eq_refl (term442 A y z x)). Qed.
Lemma lem3747350 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term444 A y z x) = (term418 A y z x).
Proof. exact (MK_COMB (@lem3747348 A y z x) (@lem3747349 A y z x)). Qed.
Lemma lem3747351 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term445 A y z) = (term425 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747350 A y z x)). Qed.
Lemma lem3747352 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747353 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term434 A y z) = (term426 A y z).
Proof. exact (MK_COMB (@lem3747352 A) (@lem3747351 A y z)). Qed.
Lemma lem3747354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747355 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term446 A y z) = (term447 A y z).
Proof. exact (MK_COMB (@lem3747354) (@lem3747353 A y z)). Qed.
Lemma lem3747356 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term438 A y z x) = (term439 A y z x).
Proof. exact (eq_refl (term438 A y z x)). Qed.
Lemma lem3747357 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term448 A y z) = (term436 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747356 A y z x)). Qed.
Lemma lem3747358 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747359 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term449 A y z) = (term450 A y z).
Proof. exact (MK_COMB (@lem3747358 A) (@lem3747357 A y z)). Qed.
Lemma lem3747360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747361 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term451 A y z) = (term452 A y z).
Proof. exact (MK_COMB (@lem3747360) (@lem3747359 A y z)). Qed.
Lemma lem3747362 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term442 A y z x) = (term443 A y z x).
Proof. exact (eq_refl (term442 A y z x)). Qed.
Lemma lem3747363 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term453 A y z) = (term437 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747362 A y z x)). Qed.
Lemma lem3747364 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747365 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term454 A y z) = (term455 A y z).
Proof. exact (MK_COMB (@lem3747364 A) (@lem3747363 A y z)). Qed.
Lemma lem3747366 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term435 A y z) = (term456 A y z).
Proof. exact (MK_COMB (@lem3747361 A y z) (@lem3747365 A y z)). Qed.
Lemma lem3747367 {A : Type'} (y : A -> Prop) (z : A -> Prop) : ((term434 A y z) = (term435 A y z)) = ((term426 A y z) = (term456 A y z)).
Proof. exact (MK_COMB (@lem3747355 A y z) (@lem3747366 A y z)). Qed.
Lemma lem3747368 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term426 A y z) = (term456 A y z).
Proof. exact (EQ_MP (@lem3747367 A y z) (@lem3747345 A y z)). Qed.
Lemma lem3747429 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term427 A y z) = (term427 A y z).
Proof. exact (eq_refl (term427 A y z)). Qed.
Lemma lem3747430 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term428 A y z) = (term457 A y z).
Proof. exact (MK_COMB (@lem3747429 A y z) (@lem3747368 A y z)). Qed.
Lemma lem3747431 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term427 A s y) = (term427 A s y).
Proof. exact (eq_refl (term427 A s y)). Qed.
Lemma lem3747432 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term429 A s y z) = (term458 A s y z).
Proof. exact (MK_COMB (@lem3747431 A s y) (@lem3747430 A y z)). Qed.
Lemma lem3747433 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term431 A x s y z) = (term460 A x s y z).
Proof. exact (MK_COMB (@lem3747277 A s x y) (@lem3747432 A s y z)). Qed.
Lemma lem3747435 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term433 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3747436 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term433 A P Q) = (term432 A P Q).
Proof. exact (@lem3747435 A P Q). Qed.
Lemma lem3747437 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term435 A x y) = (term434 A x y).
Proof. exact (@lem3747436 A (term436 A x y) (term437 A x y)). Qed.
Lemma lem3747438 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term438 A x y x') = (term439 A x y x').
Proof. exact (eq_refl (term438 A x y x')). Qed.
Lemma lem3747439 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term448 A x y) = (term436 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747438 A x y x')). Qed.
Lemma lem3747440 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747441 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term449 A x y) = (term450 A x y).
Proof. exact (MK_COMB (@lem3747440 A) (@lem3747439 A x y)). Qed.
Lemma lem3747442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747443 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term451 A x y) = (term452 A x y).
Proof. exact (MK_COMB (@lem3747442) (@lem3747441 A x y)). Qed.
Lemma lem3747444 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term442 A x y x') = (term443 A x y x').
Proof. exact (eq_refl (term442 A x y x')). Qed.
Lemma lem3747445 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term453 A x y) = (term437 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747444 A x y x')). Qed.
Lemma lem3747446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747447 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term454 A x y) = (term455 A x y).
Proof. exact (MK_COMB (@lem3747446 A) (@lem3747445 A x y)). Qed.
Lemma lem3747448 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term435 A x y) = (term456 A x y).
Proof. exact (MK_COMB (@lem3747443 A x y) (@lem3747447 A x y)). Qed.
Lemma lem3747449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747450 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term461 A x y) = (term462 A x y).
Proof. exact (MK_COMB (@lem3747449) (@lem3747448 A x y)). Qed.
Lemma lem3747451 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term438 A x y x') = (term439 A x y x').
Proof. exact (eq_refl (term438 A x y x')). Qed.
Lemma lem3747452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747453 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term440 A x y x') = (term441 A x y x').
Proof. exact (MK_COMB (@lem3747452) (@lem3747451 A x y x')). Qed.
Lemma lem3747454 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term442 A x y x') = (term443 A x y x').
Proof. exact (eq_refl (term442 A x y x')). Qed.
Lemma lem3747455 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term444 A x y x') = (term418 A x y x').
Proof. exact (MK_COMB (@lem3747453 A x y x') (@lem3747454 A x y x')). Qed.
Lemma lem3747456 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term445 A x y) = (term425 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747455 A x y x')). Qed.
Lemma lem3747457 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747458 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term434 A x y) = (term426 A x y).
Proof. exact (MK_COMB (@lem3747457 A) (@lem3747456 A x y)). Qed.
Lemma lem3747459 {A : Type'} (x : A -> Prop) (y : A -> Prop) : ((term435 A x y) = (term434 A x y)) = ((term456 A x y) = (term426 A x y)).
Proof. exact (MK_COMB (@lem3747450 A x y) (@lem3747458 A x y)). Qed.
Lemma lem3747460 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term456 A x y) = (term426 A x y).
Proof. exact (EQ_MP (@lem3747459 A x y) (@lem3747437 A x y)). Qed.
Lemma lem3747461 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term427 A x y) = (term427 A x y).
Proof. exact (eq_refl (term427 A x y)). Qed.
Lemma lem3747462 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term457 A x y) = (term428 A x y).
Proof. exact (MK_COMB (@lem3747461 A x y) (@lem3747460 A x y)). Qed.
Lemma lem3747464 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3747465 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (@lem3747464 A P Q). Qed.
Lemma lem3747466 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term465 A x y) = (term466 A x y).
Proof. exact (@lem3747465 A (term416 A x y) (term425 A x y)). Qed.
Lemma lem3747467 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term467 A x y x') = (term418 A x y x').
Proof. exact (eq_refl (term467 A x y x')). Qed.
Lemma lem3747468 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term468 A x y) = (term425 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747467 A x y x')). Qed.
Lemma lem3747469 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747470 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term469 A x y) = (term426 A x y).
Proof. exact (MK_COMB (@lem3747469 A) (@lem3747468 A x y)). Qed.
Lemma lem3747471 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term427 A x y) = (term427 A x y).
Proof. exact (eq_refl (term427 A x y)). Qed.
Lemma lem3747472 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term465 A x y) = (term428 A x y).
Proof. exact (MK_COMB (@lem3747471 A x y) (@lem3747470 A x y)). Qed.
Lemma lem3747473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747474 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term470 A x y) = (term471 A x y).
Proof. exact (MK_COMB (@lem3747473) (@lem3747472 A x y)). Qed.
Lemma lem3747475 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term467 A x y x') = (term418 A x y x').
Proof. exact (eq_refl (term467 A x y x')). Qed.
Lemma lem3747476 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term427 A x y) = (term427 A x y).
Proof. exact (eq_refl (term427 A x y)). Qed.
Lemma lem3747477 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term472 A x y x') = (term473 A x y x').
Proof. exact (MK_COMB (@lem3747476 A x y) (@lem3747475 A x y x')). Qed.
Lemma lem3747478 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term474 A x y) = (term475 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747477 A x y x')). Qed.
Lemma lem3747479 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747480 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term466 A x y) = (term476 A x y).
Proof. exact (MK_COMB (@lem3747479 A) (@lem3747478 A x y)). Qed.
Lemma lem3747481 {A : Type'} (x : A -> Prop) (y : A -> Prop) : ((term465 A x y) = (term466 A x y)) = ((term428 A x y) = (term476 A x y)).
Proof. exact (MK_COMB (@lem3747474 A x y) (@lem3747480 A x y)). Qed.
Lemma lem3747482 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term428 A x y) = (term476 A x y).
Proof. exact (EQ_MP (@lem3747481 A x y) (@lem3747466 A x y)). Qed.
Lemma lem3747483 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term457 A x y) = (term476 A x y).
Proof. exact (TRANS (@lem3747462 A x y) (@lem3747482 A x y)). Qed.
Lemma lem3747484 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term427 A s x) = (term427 A s x).
Proof. exact (eq_refl (term427 A s x)). Qed.
Lemma lem3747485 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term458 A s x y) = (term477 A s x y).
Proof. exact (MK_COMB (@lem3747484 A s x) (@lem3747483 A x y)). Qed.
Lemma lem3747487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3747488 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (@lem3747487 A P Q). Qed.
Lemma lem3747489 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term478 A s x y) = (term479 A s x y).
Proof. exact (@lem3747488 A (term416 A s x) (term475 A x y)). Qed.
Lemma lem3747490 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term480 A x y x') = (term473 A x y x').
Proof. exact (eq_refl (term480 A x y x')). Qed.
Lemma lem3747491 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term481 A x y) = (term475 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747490 A x y x')). Qed.
Lemma lem3747492 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747493 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term482 A x y) = (term476 A x y).
Proof. exact (MK_COMB (@lem3747492 A) (@lem3747491 A x y)). Qed.
Lemma lem3747494 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term427 A s x) = (term427 A s x).
Proof. exact (eq_refl (term427 A s x)). Qed.
Lemma lem3747495 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term478 A s x y) = (term477 A s x y).
Proof. exact (MK_COMB (@lem3747494 A s x) (@lem3747493 A x y)). Qed.
Lemma lem3747496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747497 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term483 A s x y) = (term484 A s x y).
Proof. exact (MK_COMB (@lem3747496) (@lem3747495 A s x y)). Qed.
Lemma lem3747498 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term480 A x y x') = (term473 A x y x').
Proof. exact (eq_refl (term480 A x y x')). Qed.
Lemma lem3747499 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term427 A s x) = (term427 A s x).
Proof. exact (eq_refl (term427 A s x)). Qed.
Lemma lem3747500 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) (x' : A) : (term485 A s x y x') = (term486 A s x y x').
Proof. exact (MK_COMB (@lem3747499 A s x) (@lem3747498 A x y x')). Qed.
Lemma lem3747501 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term487 A s x y) = (term488 A s x y).
Proof. exact (fun_ext (fun x' : A => @lem3747500 A s x y x')). Qed.
Lemma lem3747502 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747503 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term479 A s x y) = (term489 A s x y).
Proof. exact (MK_COMB (@lem3747502 A) (@lem3747501 A s x y)). Qed.
Lemma lem3747504 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : ((term478 A s x y) = (term479 A s x y)) = ((term477 A s x y) = (term489 A s x y)).
Proof. exact (MK_COMB (@lem3747497 A s x y) (@lem3747503 A s x y)). Qed.
Lemma lem3747505 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term477 A s x y) = (term489 A s x y).
Proof. exact (EQ_MP (@lem3747504 A s x y) (@lem3747489 A s x y)). Qed.
Lemma lem3747506 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term458 A s x y) = (term489 A s x y).
Proof. exact (TRANS (@lem3747485 A s x y) (@lem3747505 A s x y)). Qed.
Lemma lem3747507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747508 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term459 A s x y) = (term490 A s x y).
Proof. exact (MK_COMB (@lem3747507) (@lem3747506 A s x y)). Qed.
Lemma lem3747510 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term433 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3747511 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term433 A P Q) = (term432 A P Q).
Proof. exact (@lem3747510 A P Q). Qed.
Lemma lem3747512 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term435 A y z) = (term434 A y z).
Proof. exact (@lem3747511 A (term436 A y z) (term437 A y z)). Qed.
Lemma lem3747513 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term438 A y z x) = (term439 A y z x).
Proof. exact (eq_refl (term438 A y z x)). Qed.
Lemma lem3747514 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term448 A y z) = (term436 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747513 A y z x)). Qed.
Lemma lem3747515 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747516 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term449 A y z) = (term450 A y z).
Proof. exact (MK_COMB (@lem3747515 A) (@lem3747514 A y z)). Qed.
Lemma lem3747517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747518 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term451 A y z) = (term452 A y z).
Proof. exact (MK_COMB (@lem3747517) (@lem3747516 A y z)). Qed.
Lemma lem3747519 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term442 A y z x) = (term443 A y z x).
Proof. exact (eq_refl (term442 A y z x)). Qed.
Lemma lem3747520 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term453 A y z) = (term437 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747519 A y z x)). Qed.
Lemma lem3747521 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747522 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term454 A y z) = (term455 A y z).
Proof. exact (MK_COMB (@lem3747521 A) (@lem3747520 A y z)). Qed.
Lemma lem3747523 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term435 A y z) = (term456 A y z).
Proof. exact (MK_COMB (@lem3747518 A y z) (@lem3747522 A y z)). Qed.
Lemma lem3747524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747525 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term461 A y z) = (term462 A y z).
Proof. exact (MK_COMB (@lem3747524) (@lem3747523 A y z)). Qed.
Lemma lem3747526 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term438 A y z x) = (term439 A y z x).
Proof. exact (eq_refl (term438 A y z x)). Qed.
Lemma lem3747527 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747528 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term440 A y z x) = (term441 A y z x).
Proof. exact (MK_COMB (@lem3747527) (@lem3747526 A y z x)). Qed.
Lemma lem3747529 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term442 A y z x) = (term443 A y z x).
Proof. exact (eq_refl (term442 A y z x)). Qed.
Lemma lem3747530 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term444 A y z x) = (term418 A y z x).
Proof. exact (MK_COMB (@lem3747528 A y z x) (@lem3747529 A y z x)). Qed.
Lemma lem3747531 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term445 A y z) = (term425 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747530 A y z x)). Qed.
Lemma lem3747532 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747533 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term434 A y z) = (term426 A y z).
Proof. exact (MK_COMB (@lem3747532 A) (@lem3747531 A y z)). Qed.
Lemma lem3747534 {A : Type'} (y : A -> Prop) (z : A -> Prop) : ((term435 A y z) = (term434 A y z)) = ((term456 A y z) = (term426 A y z)).
Proof. exact (MK_COMB (@lem3747525 A y z) (@lem3747533 A y z)). Qed.
Lemma lem3747535 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term456 A y z) = (term426 A y z).
Proof. exact (EQ_MP (@lem3747534 A y z) (@lem3747512 A y z)). Qed.
Lemma lem3747536 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term427 A y z) = (term427 A y z).
Proof. exact (eq_refl (term427 A y z)). Qed.
Lemma lem3747537 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term457 A y z) = (term428 A y z).
Proof. exact (MK_COMB (@lem3747536 A y z) (@lem3747535 A y z)). Qed.
Lemma lem3747539 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3747540 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (@lem3747539 A P Q). Qed.
Lemma lem3747541 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term465 A y z) = (term466 A y z).
Proof. exact (@lem3747540 A (term416 A y z) (term425 A y z)). Qed.
Lemma lem3747542 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term467 A y z x) = (term418 A y z x).
Proof. exact (eq_refl (term467 A y z x)). Qed.
Lemma lem3747543 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term468 A y z) = (term425 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747542 A y z x)). Qed.
Lemma lem3747544 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747545 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term469 A y z) = (term426 A y z).
Proof. exact (MK_COMB (@lem3747544 A) (@lem3747543 A y z)). Qed.
Lemma lem3747546 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term427 A y z) = (term427 A y z).
Proof. exact (eq_refl (term427 A y z)). Qed.
Lemma lem3747547 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term465 A y z) = (term428 A y z).
Proof. exact (MK_COMB (@lem3747546 A y z) (@lem3747545 A y z)). Qed.
Lemma lem3747548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747549 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term470 A y z) = (term471 A y z).
Proof. exact (MK_COMB (@lem3747548) (@lem3747547 A y z)). Qed.
Lemma lem3747550 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term467 A y z x) = (term418 A y z x).
Proof. exact (eq_refl (term467 A y z x)). Qed.
Lemma lem3747551 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term427 A y z) = (term427 A y z).
Proof. exact (eq_refl (term427 A y z)). Qed.
Lemma lem3747552 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term472 A y z x) = (term473 A y z x).
Proof. exact (MK_COMB (@lem3747551 A y z) (@lem3747550 A y z x)). Qed.
Lemma lem3747553 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term474 A y z) = (term475 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747552 A y z x)). Qed.
Lemma lem3747554 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747555 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term466 A y z) = (term476 A y z).
Proof. exact (MK_COMB (@lem3747554 A) (@lem3747553 A y z)). Qed.
Lemma lem3747556 {A : Type'} (y : A -> Prop) (z : A -> Prop) : ((term465 A y z) = (term466 A y z)) = ((term428 A y z) = (term476 A y z)).
Proof. exact (MK_COMB (@lem3747549 A y z) (@lem3747555 A y z)). Qed.
Lemma lem3747557 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term428 A y z) = (term476 A y z).
Proof. exact (EQ_MP (@lem3747556 A y z) (@lem3747541 A y z)). Qed.
Lemma lem3747558 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term457 A y z) = (term476 A y z).
Proof. exact (TRANS (@lem3747537 A y z) (@lem3747557 A y z)). Qed.
Lemma lem3747559 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term427 A s y) = (term427 A s y).
Proof. exact (eq_refl (term427 A s y)). Qed.
Lemma lem3747560 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term458 A s y z) = (term477 A s y z).
Proof. exact (MK_COMB (@lem3747559 A s y) (@lem3747558 A y z)). Qed.
Lemma lem3747562 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3747563 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (@lem3747562 A P Q). Qed.
Lemma lem3747564 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term478 A s y z) = (term479 A s y z).
Proof. exact (@lem3747563 A (term416 A s y) (term475 A y z)). Qed.
Lemma lem3747565 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term480 A y z x) = (term473 A y z x).
Proof. exact (eq_refl (term480 A y z x)). Qed.
Lemma lem3747566 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term481 A y z) = (term475 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747565 A y z x)). Qed.
Lemma lem3747567 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747568 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term482 A y z) = (term476 A y z).
Proof. exact (MK_COMB (@lem3747567 A) (@lem3747566 A y z)). Qed.
Lemma lem3747569 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term427 A s y) = (term427 A s y).
Proof. exact (eq_refl (term427 A s y)). Qed.
Lemma lem3747570 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term478 A s y z) = (term477 A s y z).
Proof. exact (MK_COMB (@lem3747569 A s y) (@lem3747568 A y z)). Qed.
Lemma lem3747571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747572 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term483 A s y z) = (term484 A s y z).
Proof. exact (MK_COMB (@lem3747571) (@lem3747570 A s y z)). Qed.
Lemma lem3747573 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term480 A y z x) = (term473 A y z x).
Proof. exact (eq_refl (term480 A y z x)). Qed.
Lemma lem3747574 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term427 A s y) = (term427 A s y).
Proof. exact (eq_refl (term427 A s y)). Qed.
Lemma lem3747575 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x : A) : (term485 A s y z x) = (term486 A s y z x).
Proof. exact (MK_COMB (@lem3747574 A s y) (@lem3747573 A y z x)). Qed.
Lemma lem3747576 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term487 A s y z) = (term488 A s y z).
Proof. exact (fun_ext (fun x : A => @lem3747575 A s y z x)). Qed.
Lemma lem3747577 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747578 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term479 A s y z) = (term489 A s y z).
Proof. exact (MK_COMB (@lem3747577 A) (@lem3747576 A s y z)). Qed.
Lemma lem3747579 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : ((term478 A s y z) = (term479 A s y z)) = ((term477 A s y z) = (term489 A s y z)).
Proof. exact (MK_COMB (@lem3747572 A s y z) (@lem3747578 A s y z)). Qed.
Lemma lem3747580 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term477 A s y z) = (term489 A s y z).
Proof. exact (EQ_MP (@lem3747579 A s y z) (@lem3747564 A s y z)). Qed.
Lemma lem3747581 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term458 A s y z) = (term489 A s y z).
Proof. exact (TRANS (@lem3747560 A s y z) (@lem3747580 A s y z)). Qed.
Lemma lem3747582 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term460 A x s y z) = (term491 A x s y z).
Proof. exact (MK_COMB (@lem3747508 A s x y) (@lem3747581 A s y z)). Qed.
Lemma lem3747584 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3747585 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (@lem3747584 A P Q). Qed.
Lemma lem3747586 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term494 A x s y z) = (term495 A x s y z).
Proof. exact (@lem3747585 A (term488 A s x y) (term489 A s y z)). Qed.
Lemma lem3747587 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) (x' : A) : (term496 A s x y x') = (term486 A s x y x').
Proof. exact (eq_refl (term496 A s x y x')). Qed.
Lemma lem3747588 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term497 A s x y) = (term488 A s x y).
Proof. exact (fun_ext (fun x' : A => @lem3747587 A s x y x')). Qed.
Lemma lem3747589 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747590 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term498 A s x y) = (term489 A s x y).
Proof. exact (MK_COMB (@lem3747589 A) (@lem3747588 A s x y)). Qed.
Lemma lem3747591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747592 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term499 A s x y) = (term490 A s x y).
Proof. exact (MK_COMB (@lem3747591) (@lem3747590 A s x y)). Qed.
Lemma lem3747593 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term489 A s y z) = (term489 A s y z).
Proof. exact (eq_refl (term489 A s y z)). Qed.
Lemma lem3747594 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term494 A x s y z) = (term491 A x s y z).
Proof. exact (MK_COMB (@lem3747592 A s x y) (@lem3747593 A s y z)). Qed.
Lemma lem3747595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747596 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term500 A x s y z) = (term501 A x s y z).
Proof. exact (MK_COMB (@lem3747595) (@lem3747594 A x s y z)). Qed.
Lemma lem3747597 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) (x' : A) : (term496 A s x y x') = (term486 A s x y x').
Proof. exact (eq_refl (term496 A s x y x')). Qed.
Lemma lem3747598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747599 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) (x' : A) : (term502 A s x y x') = (term503 A s x y x').
Proof. exact (MK_COMB (@lem3747598) (@lem3747597 A s x y x')). Qed.
Lemma lem3747600 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term489 A s y z) = (term489 A s y z).
Proof. exact (eq_refl (term489 A s y z)). Qed.
Lemma lem3747601 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term504 A x x' s y z) = (term505 A x x' s y z).
Proof. exact (MK_COMB (@lem3747599 A s x y x') (@lem3747600 A s y z)). Qed.
Lemma lem3747602 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term506 A x s y z) = (term507 A x s y z).
Proof. exact (fun_ext (fun x' : A => @lem3747601 A x x' s y z)). Qed.
Lemma lem3747603 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747604 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term495 A x s y z) = (term508 A x s y z).
Proof. exact (MK_COMB (@lem3747603 A) (@lem3747602 A x s y z)). Qed.
Lemma lem3747605 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : ((term494 A x s y z) = (term495 A x s y z)) = ((term491 A x s y z) = (term508 A x s y z)).
Proof. exact (MK_COMB (@lem3747596 A x s y z) (@lem3747604 A x s y z)). Qed.
Lemma lem3747606 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term491 A x s y z) = (term508 A x s y z).
Proof. exact (EQ_MP (@lem3747605 A x s y z) (@lem3747586 A x s y z)). Qed.
Lemma lem3747608 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3747609 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (@lem3747608 A P Q). Qed.
Lemma lem3747610 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term509 A x x' s y z) = (term510 A x x' s y z).
Proof. exact (@lem3747609 A (term486 A s x y x') (term488 A s y z)). Qed.
Lemma lem3747611 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x : A) : (term496 A s y z x) = (term486 A s y z x).
Proof. exact (eq_refl (term496 A s y z x)). Qed.
Lemma lem3747612 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term497 A s y z) = (term488 A s y z).
Proof. exact (fun_ext (fun x : A => @lem3747611 A s y z x)). Qed.
Lemma lem3747613 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747614 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term498 A s y z) = (term489 A s y z).
Proof. exact (MK_COMB (@lem3747613 A) (@lem3747612 A s y z)). Qed.
Lemma lem3747615 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) (x' : A) : (term503 A s x y x') = (term503 A s x y x').
Proof. exact (eq_refl (term503 A s x y x')). Qed.
Lemma lem3747616 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term509 A x x' s y z) = (term505 A x x' s y z).
Proof. exact (MK_COMB (@lem3747615 A s x y x') (@lem3747614 A s y z)). Qed.
Lemma lem3747617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747618 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term511 A x x' s y z) = (term512 A x x' s y z).
Proof. exact (MK_COMB (@lem3747617) (@lem3747616 A x x' s y z)). Qed.
Lemma lem3747619 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x' : A) : (term496 A s y z x') = (term486 A s y z x').
Proof. exact (eq_refl (term496 A s y z x')). Qed.
Lemma lem3747620 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) (x' : A) : (term503 A s x y x') = (term503 A s x y x').
Proof. exact (eq_refl (term503 A s x y x')). Qed.
Lemma lem3747621 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x'' : A) : (term513 A x x' s y z x'') = (term514 A x x' s y z x'').
Proof. exact (MK_COMB (@lem3747620 A s x y x') (@lem3747619 A s y z x'')). Qed.
Lemma lem3747622 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term515 A x x' s y z) = (term516 A x x' s y z).
Proof. exact (fun_ext (fun x'' : A => @lem3747621 A x x' s y z x'')). Qed.
Lemma lem3747623 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747624 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term510 A x x' s y z) = (term517 A x x' s y z).
Proof. exact (MK_COMB (@lem3747623 A) (@lem3747622 A x x' s y z)). Qed.
Lemma lem3747625 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : ((term509 A x x' s y z) = (term510 A x x' s y z)) = ((term505 A x x' s y z) = (term517 A x x' s y z)).
Proof. exact (MK_COMB (@lem3747618 A x x' s y z) (@lem3747624 A x x' s y z)). Qed.
Lemma lem3747626 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term505 A x x' s y z) = (term517 A x x' s y z).
Proof. exact (EQ_MP (@lem3747625 A x x' s y z) (@lem3747610 A x x' s y z)). Qed.
Lemma lem3747627 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term507 A x s y z) = (term518 A x s y z).
Proof. exact (fun_ext (fun x' : A => @lem3747626 A x x' s y z)). Qed.
Lemma lem3747628 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747629 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term508 A x s y z) = (term519 A x s y z).
Proof. exact (MK_COMB (@lem3747628 A) (@lem3747627 A x s y z)). Qed.
Lemma lem3747630 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term491 A x s y z) = (term519 A x s y z).
Proof. exact (TRANS (@lem3747606 A x s y z) (@lem3747629 A x s y z)). Qed.
Lemma lem3747631 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term460 A x s y z) = (term519 A x s y z).
Proof. exact (TRANS (@lem3747582 A x s y z) (@lem3747630 A x s y z)). Qed.
Lemma lem3747632 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term431 A x s y z) = (term519 A x s y z).
Proof. exact (TRANS (@lem3747433 A x s y z) (@lem3747631 A x s y z)). Qed.
Lemma lem3747633 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term392 A x s y z) = (term519 A x s y z).
Proof. exact (TRANS (@lem3747120 A x s y z) (@lem3747632 A x s y z)). Qed.
Lemma lem3747634 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term392 A x s y z) : term519 A x s y z.
Proof. exact (EQ_MP (@lem3747633 A x s y z) (@lem3747010 A x s y z h1)). Qed.
Lemma lem3747641 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term520 A x z x') = (term439 A x z x').
Proof. exact (@lem17362 (x x') (z x')). Qed.
Lemma lem3747642 {A : Type'} (P : A -> Prop) : (term419 A P) = (term420 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3747643 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term521 A x z) = (term522 A x z).
Proof. exact (@lem3747642 A (term380 A x z)). Qed.
Lemma lem3747644 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term523 A x z x') = (term378 A x z x').
Proof. exact (eq_refl (term523 A x z x')). Qed.
Lemma lem3747645 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3747646 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term524 A x z x') = (term520 A x z x').
Proof. exact (MK_COMB (@lem3747645) (@lem3747644 A x z x')). Qed.
Lemma lem3747647 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term524 A x z x') = (term439 A x z x').
Proof. exact (TRANS (@lem3747646 A x z x') (@lem3747641 A x z x')). Qed.
Lemma lem3747648 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term525 A x z) = (term436 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747647 A x z x')). Qed.
Lemma lem3747649 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747650 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term522 A x z) = (term450 A x z).
Proof. exact (MK_COMB (@lem3747649 A) (@lem3747648 A x z)). Qed.
Lemma lem3747651 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term521 A x z) = (term450 A x z).
Proof. exact (TRANS (@lem3747643 A x z) (@lem3747650 A x z)). Qed.
Lemma lem3747666 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : ((x x') = (z x')) = (term526 A x z x').
Proof. exact (@lem17784 (x x') (z x')). Qed.
Lemma lem3747667 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term386 A x z) = (term527 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747666 A x z x')). Qed.
Lemma lem3747668 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747669 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term387 A x z) = (term528 A x z).
Proof. exact (MK_COMB (@lem3747668 A) (@lem3747667 A x z)). Qed.
Lemma lem3747670 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term529 A x z) = (term387 A x z).
Proof. exact (@lem16933 (term387 A x z)). Qed.
Lemma lem3747671 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term529 A x z) = (term528 A x z).
Proof. exact (TRANS (@lem3747670 A x z) (@lem3747669 A x z)). Qed.
Lemma lem3747672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747673 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term530 A x z) = (term452 A x z).
Proof. exact (MK_COMB (@lem3747672) (@lem3747651 A x z)). Qed.
Lemma lem3747674 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term531 A x z) = (term532 A x z).
Proof. exact (MK_COMB (@lem3747673 A x z) (@lem3747671 A x z)). Qed.
Lemma lem3747675 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term413 A x z) = (term531 A x z).
Proof. exact (@lem17045 (term381 A x z) (term388 A x z)). Qed.
Lemma lem3747676 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term413 A x z) = (term532 A x z).
Proof. exact (TRANS (@lem3747675 A x z) (@lem3747674 A x z)). Qed.
Lemma lem3747706 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term533 A P Q) = (term534 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3747707 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term533 A P Q) = (term534 A P Q).
Proof. exact (@lem3747706 A P Q). Qed.
Lemma lem3747708 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term535 A x z) = (term536 A x z).
Proof. exact (@lem3747707 A (term537 A x z) (term415 A x z)). Qed.
Lemma lem3747709 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term538 A x z x') = (term539 A x z x').
Proof. exact (eq_refl (term538 A x z x')). Qed.
Lemma lem3747710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747711 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term540 A x z x') = (term541 A x z x').
Proof. exact (MK_COMB (@lem3747710) (@lem3747709 A x z x')). Qed.
Lemma lem3747712 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term542 A x z x') = (term414 A x z x').
Proof. exact (eq_refl (term542 A x z x')). Qed.
Lemma lem3747713 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term543 A x z x') = (term526 A x z x').
Proof. exact (MK_COMB (@lem3747711 A x z x') (@lem3747712 A x z x')). Qed.
Lemma lem3747714 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term544 A x z) = (term527 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747713 A x z x')). Qed.
Lemma lem3747715 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747716 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term535 A x z) = (term528 A x z).
Proof. exact (MK_COMB (@lem3747715 A) (@lem3747714 A x z)). Qed.
Lemma lem3747717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747718 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term545 A x z) = (term546 A x z).
Proof. exact (MK_COMB (@lem3747717) (@lem3747716 A x z)). Qed.
Lemma lem3747719 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term538 A x z x') = (term539 A x z x').
Proof. exact (eq_refl (term538 A x z x')). Qed.
Lemma lem3747720 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term547 A x z) = (term537 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747719 A x z x')). Qed.
Lemma lem3747721 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747722 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term548 A x z) = (term549 A x z).
Proof. exact (MK_COMB (@lem3747721 A) (@lem3747720 A x z)). Qed.
Lemma lem3747723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747724 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term550 A x z) = (term551 A x z).
Proof. exact (MK_COMB (@lem3747723) (@lem3747722 A x z)). Qed.
Lemma lem3747725 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term542 A x z x') = (term414 A x z x').
Proof. exact (eq_refl (term542 A x z x')). Qed.
Lemma lem3747726 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term552 A x z) = (term415 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747725 A x z x')). Qed.
Lemma lem3747727 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747728 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term553 A x z) = (term416 A x z).
Proof. exact (MK_COMB (@lem3747727 A) (@lem3747726 A x z)). Qed.
Lemma lem3747729 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term536 A x z) = (term554 A x z).
Proof. exact (MK_COMB (@lem3747724 A x z) (@lem3747728 A x z)). Qed.
Lemma lem3747730 {A : Type'} (x : A -> Prop) (z : A -> Prop) : ((term535 A x z) = (term536 A x z)) = ((term528 A x z) = (term554 A x z)).
Proof. exact (MK_COMB (@lem3747718 A x z) (@lem3747729 A x z)). Qed.
Lemma lem3747731 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term528 A x z) = (term554 A x z).
Proof. exact (EQ_MP (@lem3747730 A x z) (@lem3747708 A x z)). Qed.
Lemma lem3747792 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term452 A x z) = (term452 A x z).
Proof. exact (eq_refl (term452 A x z)). Qed.
Lemma lem3747793 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term532 A x z) = (term555 A x z).
Proof. exact (MK_COMB (@lem3747792 A x z) (@lem3747731 A x z)). Qed.
Lemma lem3747795 {A : Type'} (P : A -> Prop) (Q : Prop) : (term556 A P Q) = (term557 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3747796 {A : Type'} (P : A -> Prop) (Q : Prop) : (term556 A P Q) = (term557 A P Q).
Proof. exact (@lem3747795 A P Q). Qed.
Lemma lem3747797 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term558 A x z) = (term559 A x z).
Proof. exact (@lem3747796 A (term436 A x z) (term554 A x z)). Qed.
Lemma lem3747798 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term438 A x z x') = (term439 A x z x').
Proof. exact (eq_refl (term438 A x z x')). Qed.
Lemma lem3747799 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term448 A x z) = (term436 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747798 A x z x')). Qed.
Lemma lem3747800 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747801 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term449 A x z) = (term450 A x z).
Proof. exact (MK_COMB (@lem3747800 A) (@lem3747799 A x z)). Qed.
Lemma lem3747802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747803 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term451 A x z) = (term452 A x z).
Proof. exact (MK_COMB (@lem3747802) (@lem3747801 A x z)). Qed.
Lemma lem3747804 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term554 A x z) = (term554 A x z).
Proof. exact (eq_refl (term554 A x z)). Qed.
Lemma lem3747805 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term558 A x z) = (term555 A x z).
Proof. exact (MK_COMB (@lem3747803 A x z) (@lem3747804 A x z)). Qed.
Lemma lem3747806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3747807 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term560 A x z) = (term561 A x z).
Proof. exact (MK_COMB (@lem3747806) (@lem3747805 A x z)). Qed.
Lemma lem3747808 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term438 A x z x') = (term439 A x z x').
Proof. exact (eq_refl (term438 A x z x')). Qed.
Lemma lem3747809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3747810 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term440 A x z x') = (term441 A x z x').
Proof. exact (MK_COMB (@lem3747809) (@lem3747808 A x z x')). Qed.
Lemma lem3747811 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term554 A x z) = (term554 A x z).
Proof. exact (eq_refl (term554 A x z)). Qed.
Lemma lem3747812 {A : Type'} (x : A) (x' : A -> Prop) (z : A -> Prop) : (term562 A x x' z) = (term563 A x x' z).
Proof. exact (MK_COMB (@lem3747810 A x' z x) (@lem3747811 A x' z)). Qed.
Lemma lem3747813 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term564 A x z) = (term565 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747812 A x' x z)). Qed.
Lemma lem3747814 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3747815 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term559 A x z) = (term566 A x z).
Proof. exact (MK_COMB (@lem3747814 A) (@lem3747813 A x z)). Qed.
Lemma lem3747816 {A : Type'} (x : A -> Prop) (z : A -> Prop) : ((term558 A x z) = (term559 A x z)) = ((term555 A x z) = (term566 A x z)).
Proof. exact (MK_COMB (@lem3747807 A x z) (@lem3747815 A x z)). Qed.
Lemma lem3747817 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term555 A x z) = (term566 A x z).
Proof. exact (EQ_MP (@lem3747816 A x z) (@lem3747797 A x z)). Qed.
Lemma lem3747818 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term532 A x z) = (term566 A x z).
Proof. exact (TRANS (@lem3747793 A x z) (@lem3747817 A x z)). Qed.
Lemma lem3747819 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term413 A x z) = (term566 A x z).
Proof. exact (TRANS (@lem3747676 A x z) (@lem3747818 A x z)). Qed.
Lemma lem3747820 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term413 A x z) : term566 A x z.
Proof. exact (EQ_MP (@lem3747819 A x z) (@lem3747015 A x z h1)). Qed.
Lemma lem3747821 {A : Type'} (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term563 A x' x z) : term563 A x' x z.
Proof. exact (h1). Qed.
Lemma lem3747822 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term517 A x x'' s y z) : term517 A x x'' s y z.
Proof. exact (h1). Qed.
Lemma lem3747823 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term514 A x x'' s y z x'''.
Proof. exact (h1). Qed.
Lemma lem3747834 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term414 A x z x') = (term414 A x z x').
Proof. exact (eq_refl (term414 A x z x')). Qed.
Lemma lem3747835 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term415 A x z) = (term415 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747834 A x z x')). Qed.
Lemma lem3747836 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747837 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term416 A x z) = (term416 A x z).
Proof. exact (MK_COMB (@lem3747836 A) (@lem3747835 A x z)). Qed.
Lemma lem3747848 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term539 A x z x') = (term539 A x z x').
Proof. exact (eq_refl (term539 A x z x')). Qed.
Lemma lem3747849 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term537 A x z) = (term537 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3747848 A x z x')). Qed.
Lemma lem3747850 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747851 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term549 A x z) = (term549 A x z).
Proof. exact (MK_COMB (@lem3747850 A) (@lem3747849 A x z)). Qed.
Lemma lem3747852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747853 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term551 A x z) = (term551 A x z).
Proof. exact (MK_COMB (@lem3747852) (@lem3747851 A x z)). Qed.
Lemma lem3747854 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term554 A x z) = (term554 A x z).
Proof. exact (MK_COMB (@lem3747853 A x z) (@lem3747837 A x z)). Qed.
Lemma lem3747867 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term441 A x z x') = (term441 A x z x').
Proof. exact (eq_refl (term441 A x z x')). Qed.
Lemma lem3747868 {A : Type'} (x' : A) (x : A -> Prop) (z : A -> Prop) : (term563 A x' x z) = (term563 A x' x z).
Proof. exact (MK_COMB (@lem3747867 A x z x') (@lem3747854 A x z)). Qed.
Lemma lem3747869 {A : Type'} (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term563 A x' x z) : term563 A x' x z.
Proof. exact (EQ_MP (@lem3747868 A x' x z) (@lem3747821 A x' x z h1)). Qed.
Lemma lem3747894 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) : (term418 A y z x''') = (term418 A y z x''').
Proof. exact (eq_refl (term418 A y z x''')). Qed.
Lemma lem3747905 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term414 A y z x) = (term414 A y z x).
Proof. exact (eq_refl (term414 A y z x)). Qed.
Lemma lem3747906 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term415 A y z) = (term415 A y z).
Proof. exact (fun_ext (fun x : A => @lem3747905 A y z x)). Qed.
Lemma lem3747907 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747908 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term416 A y z) = (term416 A y z).
Proof. exact (MK_COMB (@lem3747907 A) (@lem3747906 A y z)). Qed.
Lemma lem3747909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747910 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term427 A y z) = (term427 A y z).
Proof. exact (MK_COMB (@lem3747909) (@lem3747908 A y z)). Qed.
Lemma lem3747911 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) : (term473 A y z x''') = (term473 A y z x''').
Proof. exact (MK_COMB (@lem3747910 A y z) (@lem3747894 A y z x''')). Qed.
Lemma lem3747922 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A) : (term414 A s y x) = (term414 A s y x).
Proof. exact (eq_refl (term414 A s y x)). Qed.
Lemma lem3747923 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term415 A s y) = (term415 A s y).
Proof. exact (fun_ext (fun x : A => @lem3747922 A s y x)). Qed.
Lemma lem3747924 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747925 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term416 A s y) = (term416 A s y).
Proof. exact (MK_COMB (@lem3747924 A) (@lem3747923 A s y)). Qed.
Lemma lem3747926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747927 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term427 A s y) = (term427 A s y).
Proof. exact (MK_COMB (@lem3747926) (@lem3747925 A s y)). Qed.
Lemma lem3747928 {A : Type'} (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) : (term486 A s y z x''') = (term486 A s y z x''').
Proof. exact (MK_COMB (@lem3747927 A s y) (@lem3747911 A y z x''')). Qed.
Lemma lem3747953 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) : (term418 A x y x'') = (term418 A x y x'').
Proof. exact (eq_refl (term418 A x y x'')). Qed.
Lemma lem3747964 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term414 A x y x') = (term414 A x y x').
Proof. exact (eq_refl (term414 A x y x')). Qed.
Lemma lem3747965 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term415 A x y) = (term415 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3747964 A x y x')). Qed.
Lemma lem3747966 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747967 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term416 A x y) = (term416 A x y).
Proof. exact (MK_COMB (@lem3747966 A) (@lem3747965 A x y)). Qed.
Lemma lem3747968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747969 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term427 A x y) = (term427 A x y).
Proof. exact (MK_COMB (@lem3747968) (@lem3747967 A x y)). Qed.
Lemma lem3747970 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) : (term473 A x y x'') = (term473 A x y x'').
Proof. exact (MK_COMB (@lem3747969 A x y) (@lem3747953 A x y x'')). Qed.
Lemma lem3747981 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term414 A s x x') = (term414 A s x x').
Proof. exact (eq_refl (term414 A s x x')). Qed.
Lemma lem3747982 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term415 A s x) = (term415 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3747981 A s x x')). Qed.
Lemma lem3747983 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3747984 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term416 A s x) = (term416 A s x).
Proof. exact (MK_COMB (@lem3747983 A) (@lem3747982 A s x)). Qed.
Lemma lem3747985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747986 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term427 A s x) = (term427 A s x).
Proof. exact (MK_COMB (@lem3747985) (@lem3747984 A s x)). Qed.
Lemma lem3747987 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) (x'' : A) : (term486 A s x y x'') = (term486 A s x y x'').
Proof. exact (MK_COMB (@lem3747986 A s x) (@lem3747970 A x y x'')). Qed.
Lemma lem3747988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3747989 {A : Type'} (s : A -> Prop) (x : A -> Prop) (y : A -> Prop) (x'' : A) : (term503 A s x y x'') = (term503 A s x y x'').
Proof. exact (MK_COMB (@lem3747988) (@lem3747987 A s x y x'')). Qed.
Lemma lem3747990 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) : (term514 A x x'' s y z x''') = (term514 A x x'' s y z x''').
Proof. exact (MK_COMB (@lem3747989 A s x y x'') (@lem3747928 A s y z x''')). Qed.
Lemma lem3747991 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term514 A x x'' s y z x'''.
Proof. exact (EQ_MP (@lem3747990 A x x'' s y z x''') (@lem3747823 A x x'' s y z x''' h1)). Qed.
Lemma lem3747992 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term486 A s y z x'''.
Proof. exact (proj2 (@lem3747991 A x x'' s y z x''' h1)). Qed.
Lemma lem3747993 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term486 A s x y x''.
Proof. exact (proj1 (@lem3747991 A x x'' s y z x''' h1)). Qed.
Lemma lem3747994 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term473 A y z x'''.
Proof. exact (proj2 (@lem3747992 A x x'' s y z x''' h1)). Qed.
Lemma lem3747996 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term418 A y z x'''.
Proof. exact (proj2 (@lem3747994 A x x'' s y z x''' h1)). Qed.
Lemma lem3747997 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A y z.
Proof. exact (proj1 (@lem3747994 A x x'' s y z x''' h1)). Qed.
Lemma lem3747998 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term473 A x y x''.
Proof. exact (proj2 (@lem3747993 A x x'' s y z x''' h1)). Qed.
Lemma lem3748000 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term418 A x y x''.
Proof. exact (proj2 (@lem3747998 A x x'' s y z x''' h1)). Qed.
Lemma lem3748001 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A x y.
Proof. exact (proj1 (@lem3747998 A x x'' s y z x''' h1)). Qed.
Lemma lem3748002 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : term439 A x y x''.
Proof. exact (h1). Qed.
Lemma lem3748006 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term439 A y z x'''.
Proof. exact (h1). Qed.
Lemma lem3748026 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term439 A y z x'''.
Proof. exact (h1). Qed.
Lemma lem3748027 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term443 A y z x''') : term443 A y z x'''.
Proof. exact (h1). Qed.
Lemma lem3748038 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term439 A x z x') : term439 A x z x'.
Proof. exact (h1). Qed.
Lemma lem3748039 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term554 A x z) : term554 A x z.
Proof. exact (h1). Qed.
Lemma lem3748043 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term554 A x z) : term549 A x z.
Proof. exact (proj1 (@lem3748039 A x z h1)). Qed.
Lemma lem3748064 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term414 A y z x) = (term414 A y z x).
Proof. exact (eq_refl (term414 A y z x)). Qed.
Lemma lem3748065 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term415 A y z) = (term415 A y z).
Proof. exact (fun_ext (fun x : A => @lem3748064 A y z x)). Qed.
Lemma lem3748066 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748068 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term416 A y z) = (term416 A y z).
Proof. exact (MK_COMB (@lem3748066 A) (@lem3748065 A y z)). Qed.
Lemma lem3748069 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A y z.
Proof. exact (EQ_MP (@lem3748068 A y z) (@lem3747997 A x x'' s y z x''' h1)). Qed.
Lemma lem3748140 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term414 A y z x) = (term414 A y z x).
Proof. exact (eq_refl (term414 A y z x)). Qed.
Lemma lem3748141 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term415 A y z) = (term415 A y z).
Proof. exact (fun_ext (fun x : A => @lem3748140 A y z x)). Qed.
Lemma lem3748142 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748144 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term416 A y z) = (term416 A y z).
Proof. exact (MK_COMB (@lem3748142 A) (@lem3748141 A y z)). Qed.
Lemma lem3748145 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A y z.
Proof. exact (EQ_MP (@lem3748144 A y z) (@lem3747997 A x x'' s y z x''' h1)). Qed.
Lemma lem3748260 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term414 A x y x') = (term414 A x y x').
Proof. exact (eq_refl (term414 A x y x')). Qed.
Lemma lem3748261 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term415 A x y) = (term415 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3748260 A x y x')). Qed.
Lemma lem3748262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748264 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term416 A x y) = (term416 A x y).
Proof. exact (MK_COMB (@lem3748262 A) (@lem3748261 A x y)). Qed.
Lemma lem3748265 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A x y.
Proof. exact (EQ_MP (@lem3748264 A x y) (@lem3748001 A x x'' s y z x''' h1)). Qed.
Lemma lem3748336 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term414 A x y x') = (term414 A x y x').
Proof. exact (eq_refl (term414 A x y x')). Qed.
Lemma lem3748337 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term415 A x y) = (term415 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3748336 A x y x')). Qed.
Lemma lem3748338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748340 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term416 A x y) = (term416 A x y).
Proof. exact (MK_COMB (@lem3748338 A) (@lem3748337 A x y)). Qed.
Lemma lem3748341 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A x y.
Proof. exact (EQ_MP (@lem3748340 A x y) (@lem3748001 A x x'' s y z x''' h1)). Qed.
Lemma lem3748404 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term414 A y z x) = (term414 A y z x).
Proof. exact (eq_refl (term414 A y z x)). Qed.
Lemma lem3748405 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term415 A y z) = (term415 A y z).
Proof. exact (fun_ext (fun x : A => @lem3748404 A y z x)). Qed.
Lemma lem3748406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748408 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term416 A y z) = (term416 A y z).
Proof. exact (MK_COMB (@lem3748406 A) (@lem3748405 A y z)). Qed.
Lemma lem3748409 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A y z.
Proof. exact (EQ_MP (@lem3748408 A y z) (@lem3747997 A x x'' s y z x''' h1)). Qed.
Lemma lem3748480 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term414 A y z x) = (term414 A y z x).
Proof. exact (eq_refl (term414 A y z x)). Qed.
Lemma lem3748481 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term415 A y z) = (term415 A y z).
Proof. exact (fun_ext (fun x : A => @lem3748480 A y z x)). Qed.
Lemma lem3748482 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748484 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term416 A y z) = (term416 A y z).
Proof. exact (MK_COMB (@lem3748482 A) (@lem3748481 A y z)). Qed.
Lemma lem3748485 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A y z.
Proof. exact (EQ_MP (@lem3748484 A y z) (@lem3747997 A x x'' s y z x''' h1)). Qed.
Lemma lem3748574 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term414 A y z x) = (term414 A y z x).
Proof. exact (eq_refl (term414 A y z x)). Qed.
Lemma lem3748575 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term415 A y z) = (term415 A y z).
Proof. exact (fun_ext (fun x : A => @lem3748574 A y z x)). Qed.
Lemma lem3748576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748578 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term416 A y z) = (term416 A y z).
Proof. exact (MK_COMB (@lem3748576 A) (@lem3748575 A y z)). Qed.
Lemma lem3748579 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A y z.
Proof. exact (EQ_MP (@lem3748578 A y z) (@lem3747997 A x x'' s y z x''' h1)). Qed.
Lemma lem3748600 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term414 A x y x') = (term414 A x y x').
Proof. exact (eq_refl (term414 A x y x')). Qed.
Lemma lem3748601 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term415 A x y) = (term415 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3748600 A x y x')). Qed.
Lemma lem3748602 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748604 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term416 A x y) = (term416 A x y).
Proof. exact (MK_COMB (@lem3748602 A) (@lem3748601 A x y)). Qed.
Lemma lem3748605 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A x y.
Proof. exact (EQ_MP (@lem3748604 A x y) (@lem3748001 A x x'' s y z x''' h1)). Qed.
Lemma lem3748676 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term414 A x y x') = (term414 A x y x').
Proof. exact (eq_refl (term414 A x y x')). Qed.
Lemma lem3748677 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term415 A x y) = (term415 A x y).
Proof. exact (fun_ext (fun x' : A => @lem3748676 A x y x')). Qed.
Lemma lem3748678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748680 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term416 A x y) = (term416 A x y).
Proof. exact (MK_COMB (@lem3748678 A) (@lem3748677 A x y)). Qed.
Lemma lem3748681 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term416 A x y.
Proof. exact (EQ_MP (@lem3748680 A x y) (@lem3748001 A x x'' s y z x''' h1)). Qed.
Lemma lem3748705 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term539 A x z x') = (term539 A x z x').
Proof. exact (eq_refl (term539 A x z x')). Qed.
Lemma lem3748706 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term537 A x z) = (term537 A x z).
Proof. exact (fun_ext (fun x' : A => @lem3748705 A x z x')). Qed.
Lemma lem3748707 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3748709 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term549 A x z) = (term549 A x z).
Proof. exact (MK_COMB (@lem3748707 A) (@lem3748706 A x z)). Qed.
Lemma lem3748710 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term554 A x z) : term549 A x z.
Proof. exact (EQ_MP (@lem3748709 A x z) (@lem3748043 A x z h1)). Qed.
Lemma lem3748727 {A : Type'} (_43118 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A y z _43118.
Proof. exact (@lem3748069 A x x'' s y z x''' h1 _43118). Qed.
Lemma lem3748728 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43118 : A) : (term542 A y z _43118) = (term414 A y z _43118).
Proof. exact (eq_refl (term542 A y z _43118)). Qed.
Lemma lem3748739 {A : Type'} (_43122 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A y z _43122.
Proof. exact (@lem3748145 A x x'' s y z x''' h1 _43122). Qed.
Lemma lem3748740 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43122 : A) : (term542 A y z _43122) = (term414 A y z _43122).
Proof. exact (eq_refl (term542 A y z _43122)). Qed.
Lemma lem3748763 {A : Type'} (_43130 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A x y _43130.
Proof. exact (@lem3748265 A x x'' s y z x''' h1 _43130). Qed.
Lemma lem3748764 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43130 : A) : (term542 A x y _43130) = (term414 A x y _43130).
Proof. exact (eq_refl (term542 A x y _43130)). Qed.
Lemma lem3748775 {A : Type'} (_43134 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A x y _43134.
Proof. exact (@lem3748341 A x x'' s y z x''' h1 _43134). Qed.
Lemma lem3748776 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43134 : A) : (term542 A x y _43134) = (term414 A x y _43134).
Proof. exact (eq_refl (term542 A x y _43134)). Qed.
Lemma lem3748787 {A : Type'} (_43138 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A y z _43138.
Proof. exact (@lem3748409 A x x'' s y z x''' h1 _43138). Qed.
Lemma lem3748788 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43138 : A) : (term542 A y z _43138) = (term414 A y z _43138).
Proof. exact (eq_refl (term542 A y z _43138)). Qed.
Lemma lem3748799 {A : Type'} (_43142 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A y z _43142.
Proof. exact (@lem3748485 A x x'' s y z x''' h1 _43142). Qed.
Lemma lem3748800 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43142 : A) : (term542 A y z _43142) = (term414 A y z _43142).
Proof. exact (eq_refl (term542 A y z _43142)). Qed.
Lemma lem3748817 {A : Type'} (_43148 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A y z _43148.
Proof. exact (@lem3748579 A x x'' s y z x''' h1 _43148). Qed.
Lemma lem3748818 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43148 : A) : (term542 A y z _43148) = (term414 A y z _43148).
Proof. exact (eq_refl (term542 A y z _43148)). Qed.
Lemma lem3748823 {A : Type'} (_43150 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A x y _43150.
Proof. exact (@lem3748605 A x x'' s y z x''' h1 _43150). Qed.
Lemma lem3748824 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43150 : A) : (term542 A x y _43150) = (term414 A x y _43150).
Proof. exact (eq_refl (term542 A x y _43150)). Qed.
Lemma lem3748835 {A : Type'} (_43154 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term542 A x y _43154.
Proof. exact (@lem3748681 A x x'' s y z x''' h1 _43154). Qed.
Lemma lem3748836 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43154 : A) : (term542 A x y _43154) = (term414 A x y _43154).
Proof. exact (eq_refl (term542 A x y _43154)). Qed.
Lemma lem3748838 {A : Type'} (_43155 : A) (x : A -> Prop) (z : A -> Prop) (h1 : term554 A x z) : term538 A x z _43155.
Proof. exact (@lem3748710 A x z h1 _43155). Qed.
Lemma lem3748839 {A : Type'} (x : A -> Prop) (z : A -> Prop) (_43155 : A) : (term538 A x z _43155) = (term539 A x z _43155).
Proof. exact (eq_refl (term538 A x z _43155)). Qed.
Lemma lem3748855 {A : Type'} (_43118 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A y z _43118.
Proof. exact (EQ_MP (@lem3748728 A y z _43118) (@lem3748727 A _43118 x x'' s y z x''' h1)). Qed.
Lemma lem3748875 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term567 A z x'''.
Proof. exact (proj2 (@lem3748006 A y z x''' h1)). Qed.
Lemma lem3748891 {A : Type'} (_43122 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A y z _43122.
Proof. exact (EQ_MP (@lem3748740 A y z _43122) (@lem3748739 A _43122 x x'' s y z x''' h1)). Qed.
Lemma lem3748911 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term567 A z x'''.
Proof. exact (proj2 (@lem3748006 A y z x''' h1)). Qed.
Lemma lem3748947 {A : Type'} (_43130 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A x y _43130.
Proof. exact (EQ_MP (@lem3748764 A x y _43130) (@lem3748763 A _43130 x x'' s y z x''' h1)). Qed.
Lemma lem3748951 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : term567 A y x''.
Proof. exact (proj2 (@lem3748002 A x y x'' h1)). Qed.
Lemma lem3748983 {A : Type'} (_43134 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A x y _43134.
Proof. exact (EQ_MP (@lem3748776 A x y _43134) (@lem3748775 A _43134 x x'' s y z x''' h1)). Qed.
Lemma lem3748987 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : term567 A y x''.
Proof. exact (proj2 (@lem3748002 A x y x'' h1)). Qed.
Lemma lem3749015 {A : Type'} (_43138 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A y z _43138.
Proof. exact (EQ_MP (@lem3748788 A y z _43138) (@lem3748787 A _43138 x x'' s y z x''' h1)). Qed.
Lemma lem3749035 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term567 A z x'''.
Proof. exact (proj2 (@lem3748026 A y z x''' h1)). Qed.
Lemma lem3749051 {A : Type'} (_43142 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A y z _43142.
Proof. exact (EQ_MP (@lem3748800 A y z _43142) (@lem3748799 A _43142 x x'' s y z x''' h1)). Qed.
Lemma lem3749071 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term567 A z x'''.
Proof. exact (proj2 (@lem3748026 A y z x''' h1)). Qed.
Lemma lem3749095 {A : Type'} (_43148 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A y z _43148.
Proof. exact (EQ_MP (@lem3748818 A y z _43148) (@lem3748817 A _43148 x x'' s y z x''' h1)). Qed.
Lemma lem3749107 {A : Type'} (_43150 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A x y _43150.
Proof. exact (EQ_MP (@lem3748824 A x y _43150) (@lem3748823 A _43150 x x'' s y z x''' h1)). Qed.
Lemma lem3749119 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term439 A x z x') : term567 A z x'.
Proof. exact (proj2 (@lem3748038 A x z x' h1)). Qed.
Lemma lem3749143 {A : Type'} (_43154 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term414 A x y _43154.
Proof. exact (EQ_MP (@lem3748836 A x y _43154) (@lem3748835 A _43154 x x'' s y z x''' h1)). Qed.
Lemma lem3749149 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term443 A y z x''') : term567 A y x'''.
Proof. exact (proj1 (@lem3748027 A y z x''' h1)). Qed.
Lemma lem3749157 {A : Type'} (_43155 : A) (x : A -> Prop) (z : A -> Prop) (h1 : term554 A x z) : term539 A x z _43155.
Proof. exact (EQ_MP (@lem3748839 A x z _43155) (@lem3748838 A _43155 x z h1)). Qed.
Lemma lem3749165 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : y x'''.
Proof. exact (proj1 (@lem3748006 A y z x''' h1)). Qed.
Lemma lem3749166 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term568 A y x'''.
Proof. exact (fun h0 : term567 A y x''' => @lem3749165 A y z x''' h1). Qed.
Lemma lem3749168 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749169 {A : Type'} (y : A -> Prop) (x''' : A) : (term568 A y x''') = (y x''').
Proof. exact (@lem3749168 (y x''')). Qed.
Lemma lem3749170 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : y x'''.
Proof. exact (EQ_MP (@lem3749169 A y x''') (@lem3749166 A y z x''' h1)). Qed.
Lemma lem3749176 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749177 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43118 : A) : (term414 A y z _43118) = (term539 A z y _43118).
Proof. exact (@lem3749176 (z _43118) (term567 A y _43118)). Qed.
Lemma lem3749183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749184 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43118 : A) : (term570 A y z _43118) = (term571 A z y _43118).
Proof. exact (MK_COMB (@lem3749183) (@lem3749177 A z y _43118)). Qed.
Lemma lem3749190 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43118 : A) : (term539 A z y _43118) = (term539 A z y _43118).
Proof. exact (eq_refl (term539 A z y _43118)). Qed.
Lemma lem3749191 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43118 : A) : ((term414 A y z _43118) = (term539 A z y _43118)) = ((term539 A z y _43118) = (term539 A z y _43118)).
Proof. exact (MK_COMB (@lem3749184 A z y _43118) (@lem3749190 A z y _43118)). Qed.
Lemma lem3749193 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749194 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749193 Prop x). Qed.
Lemma lem3749195 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43118 : A) : ((term539 A z y _43118) = (term539 A z y _43118)) = True.
Proof. exact (@lem3749194 (term539 A z y _43118)). Qed.
Lemma lem3749196 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43118 : A) : ((term414 A y z _43118) = (term539 A z y _43118)) = True.
Proof. exact (TRANS (@lem3749191 A z y _43118) (@lem3749195 A z y _43118)). Qed.
Lemma lem3749197 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43118 : A) : True = ((term414 A y z _43118) = (term539 A z y _43118)).
Proof. exact (SYM (@lem3749196 A z y _43118)). Qed.
Lemma lem3749198 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43118 : A) : (term414 A y z _43118) = (term539 A z y _43118).
Proof. exact (EQ_MP (@lem3749197 A z y _43118) (@lem0)). Qed.
Lemma lem3749199 {A : Type'} (_43118 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A z y _43118.
Proof. exact (EQ_MP (@lem3749198 A z y _43118) (@lem3748855 A _43118 x x'' s y z x''' h1)). Qed.
Lemma lem3749201 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749202 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43118 : A) : (term539 A z y _43118) = (term573 A y z _43118).
Proof. exact (@lem3749201 (term567 A y _43118) (z _43118)). Qed.
Lemma lem3749204 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749205 {A : Type'} (y : A -> Prop) (_43118 : A) : (term574 A y _43118) = (y _43118).
Proof. exact (@lem3749204 (y _43118)). Qed.
Lemma lem3749206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749207 {A : Type'} (y : A -> Prop) (_43118 : A) : (term575 A y _43118) = (term376 A y _43118).
Proof. exact (MK_COMB (@lem3749206) (@lem3749205 A y _43118)). Qed.
Lemma lem3749208 {A : Type'} (z : A -> Prop) (_43118 : A) : (z _43118) = (z _43118).
Proof. exact (eq_refl (z _43118)). Qed.
Lemma lem3749209 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43118 : A) : (term573 A y z _43118) = (term378 A y z _43118).
Proof. exact (MK_COMB (@lem3749207 A y _43118) (@lem3749208 A z _43118)). Qed.
Lemma lem3749210 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43118 : A) : (term539 A z y _43118) = (term378 A y z _43118).
Proof. exact (TRANS (@lem3749202 A y z _43118) (@lem3749209 A y z _43118)). Qed.
Lemma lem3749213 {A : Type'} (_43118 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43118.
Proof. exact (EQ_MP (@lem3749210 A y z _43118) (@lem3749199 A _43118 x x'' s y z x''' h1)). Qed.
Lemma lem3749214 {A : Type'} (_43118 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43118.
Proof. exact (@lem3749213 A _43118 x x'' s y z x''' h1). Qed.
Lemma lem3749215 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z x'''.
Proof. exact (@lem3749214 A x''' x x'' s y z x''' h1). Qed.
Lemma lem3749218 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : z x'''.
Proof. exact (@lem3749215 A x x'' s y z x''' h2 (@lem3749170 A y z x''' h1)). Qed.
Lemma lem3749219 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : term568 A z x'''.
Proof. exact (fun h0 : term567 A z x''' => @lem3749218 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749221 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749222 {A : Type'} (z : A -> Prop) (x''' : A) : (term568 A z x''') = (z x''').
Proof. exact (@lem3749221 (z x''')). Qed.
Lemma lem3749223 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : z x'''.
Proof. exact (EQ_MP (@lem3749222 A z x''') (@lem3749219 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749226 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3749228 {A : Type'} (z : A -> Prop) (x''' : A) : (term567 A z x''') = (term576 A z x''').
Proof. exact (@lem3749226 (z x''')). Qed.
Lemma lem3749231 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term576 A z x'''.
Proof. exact (EQ_MP (@lem3749228 A z x''') (@lem3748875 A y z x''' h1)). Qed.
Lemma lem3749234 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (@lem3749231 A y z x''' h1 (@lem3749223 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749235 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : term577.
Proof. exact (fun h0 : ~ False => @lem3749234 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749237 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749238 : term577 = False.
Proof. exact (@lem3749237 False). Qed.
Lemma lem3749239 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (EQ_MP (@lem3749238) (@lem3749235 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749241 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : y x'''.
Proof. exact (proj1 (@lem3748006 A y z x''' h1)). Qed.
Lemma lem3749242 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term568 A y x'''.
Proof. exact (fun h0 : term567 A y x''' => @lem3749241 A y z x''' h1). Qed.
Lemma lem3749244 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749245 {A : Type'} (y : A -> Prop) (x''' : A) : (term568 A y x''') = (y x''').
Proof. exact (@lem3749244 (y x''')). Qed.
Lemma lem3749246 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : y x'''.
Proof. exact (EQ_MP (@lem3749245 A y x''') (@lem3749242 A y z x''' h1)). Qed.
Lemma lem3749252 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749253 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43122 : A) : (term414 A y z _43122) = (term539 A z y _43122).
Proof. exact (@lem3749252 (z _43122) (term567 A y _43122)). Qed.
Lemma lem3749259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749260 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43122 : A) : (term570 A y z _43122) = (term571 A z y _43122).
Proof. exact (MK_COMB (@lem3749259) (@lem3749253 A z y _43122)). Qed.
Lemma lem3749266 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43122 : A) : (term539 A z y _43122) = (term539 A z y _43122).
Proof. exact (eq_refl (term539 A z y _43122)). Qed.
Lemma lem3749267 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43122 : A) : ((term414 A y z _43122) = (term539 A z y _43122)) = ((term539 A z y _43122) = (term539 A z y _43122)).
Proof. exact (MK_COMB (@lem3749260 A z y _43122) (@lem3749266 A z y _43122)). Qed.
Lemma lem3749269 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749270 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749269 Prop x). Qed.
Lemma lem3749271 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43122 : A) : ((term539 A z y _43122) = (term539 A z y _43122)) = True.
Proof. exact (@lem3749270 (term539 A z y _43122)). Qed.
Lemma lem3749272 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43122 : A) : ((term414 A y z _43122) = (term539 A z y _43122)) = True.
Proof. exact (TRANS (@lem3749267 A z y _43122) (@lem3749271 A z y _43122)). Qed.
Lemma lem3749273 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43122 : A) : True = ((term414 A y z _43122) = (term539 A z y _43122)).
Proof. exact (SYM (@lem3749272 A z y _43122)). Qed.
Lemma lem3749274 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43122 : A) : (term414 A y z _43122) = (term539 A z y _43122).
Proof. exact (EQ_MP (@lem3749273 A z y _43122) (@lem0)). Qed.
Lemma lem3749275 {A : Type'} (_43122 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A z y _43122.
Proof. exact (EQ_MP (@lem3749274 A z y _43122) (@lem3748891 A _43122 x x'' s y z x''' h1)). Qed.
Lemma lem3749277 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749278 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43122 : A) : (term539 A z y _43122) = (term573 A y z _43122).
Proof. exact (@lem3749277 (term567 A y _43122) (z _43122)). Qed.
Lemma lem3749280 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749281 {A : Type'} (y : A -> Prop) (_43122 : A) : (term574 A y _43122) = (y _43122).
Proof. exact (@lem3749280 (y _43122)). Qed.
Lemma lem3749282 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749283 {A : Type'} (y : A -> Prop) (_43122 : A) : (term575 A y _43122) = (term376 A y _43122).
Proof. exact (MK_COMB (@lem3749282) (@lem3749281 A y _43122)). Qed.
Lemma lem3749284 {A : Type'} (z : A -> Prop) (_43122 : A) : (z _43122) = (z _43122).
Proof. exact (eq_refl (z _43122)). Qed.
Lemma lem3749285 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43122 : A) : (term573 A y z _43122) = (term378 A y z _43122).
Proof. exact (MK_COMB (@lem3749283 A y _43122) (@lem3749284 A z _43122)). Qed.
Lemma lem3749286 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43122 : A) : (term539 A z y _43122) = (term378 A y z _43122).
Proof. exact (TRANS (@lem3749278 A y z _43122) (@lem3749285 A y z _43122)). Qed.
Lemma lem3749289 {A : Type'} (_43122 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43122.
Proof. exact (EQ_MP (@lem3749286 A y z _43122) (@lem3749275 A _43122 x x'' s y z x''' h1)). Qed.
Lemma lem3749290 {A : Type'} (_43122 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43122.
Proof. exact (@lem3749289 A _43122 x x'' s y z x''' h1). Qed.
Lemma lem3749291 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z x'''.
Proof. exact (@lem3749290 A x''' x x'' s y z x''' h1). Qed.
Lemma lem3749294 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : z x'''.
Proof. exact (@lem3749291 A x x'' s y z x''' h2 (@lem3749246 A y z x''' h1)). Qed.
Lemma lem3749295 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : term568 A z x'''.
Proof. exact (fun h0 : term567 A z x''' => @lem3749294 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749297 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749298 {A : Type'} (z : A -> Prop) (x''' : A) : (term568 A z x''') = (z x''').
Proof. exact (@lem3749297 (z x''')). Qed.
Lemma lem3749299 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : z x'''.
Proof. exact (EQ_MP (@lem3749298 A z x''') (@lem3749295 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749302 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3749304 {A : Type'} (z : A -> Prop) (x''' : A) : (term567 A z x''') = (term576 A z x''').
Proof. exact (@lem3749302 (z x''')). Qed.
Lemma lem3749307 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term576 A z x'''.
Proof. exact (EQ_MP (@lem3749304 A z x''') (@lem3748911 A y z x''' h1)). Qed.
Lemma lem3749310 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (@lem3749307 A y z x''' h1 (@lem3749299 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749311 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : term577.
Proof. exact (fun h0 : ~ False => @lem3749310 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749313 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749314 : term577 = False.
Proof. exact (@lem3749313 False). Qed.
Lemma lem3749315 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (EQ_MP (@lem3749314) (@lem3749311 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749317 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : x x''.
Proof. exact (proj1 (@lem3748002 A x y x'' h1)). Qed.
Lemma lem3749318 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : term568 A x x''.
Proof. exact (fun h0 : term567 A x x'' => @lem3749317 A x y x'' h1). Qed.
Lemma lem3749320 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749321 {A : Type'} (x : A -> Prop) (x'' : A) : (term568 A x x'') = (x x'').
Proof. exact (@lem3749320 (x x'')). Qed.
Lemma lem3749322 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : x x''.
Proof. exact (EQ_MP (@lem3749321 A x x'') (@lem3749318 A x y x'' h1)). Qed.
Lemma lem3749328 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749329 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43130 : A) : (term414 A x y _43130) = (term539 A y x _43130).
Proof. exact (@lem3749328 (y _43130) (term567 A x _43130)). Qed.
Lemma lem3749335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749336 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43130 : A) : (term570 A x y _43130) = (term571 A y x _43130).
Proof. exact (MK_COMB (@lem3749335) (@lem3749329 A y x _43130)). Qed.
Lemma lem3749342 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43130 : A) : (term539 A y x _43130) = (term539 A y x _43130).
Proof. exact (eq_refl (term539 A y x _43130)). Qed.
Lemma lem3749343 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43130 : A) : ((term414 A x y _43130) = (term539 A y x _43130)) = ((term539 A y x _43130) = (term539 A y x _43130)).
Proof. exact (MK_COMB (@lem3749336 A y x _43130) (@lem3749342 A y x _43130)). Qed.
Lemma lem3749345 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749346 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749345 Prop x). Qed.
Lemma lem3749347 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43130 : A) : ((term539 A y x _43130) = (term539 A y x _43130)) = True.
Proof. exact (@lem3749346 (term539 A y x _43130)). Qed.
Lemma lem3749348 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43130 : A) : ((term414 A x y _43130) = (term539 A y x _43130)) = True.
Proof. exact (TRANS (@lem3749343 A y x _43130) (@lem3749347 A y x _43130)). Qed.
Lemma lem3749349 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43130 : A) : True = ((term414 A x y _43130) = (term539 A y x _43130)).
Proof. exact (SYM (@lem3749348 A y x _43130)). Qed.
Lemma lem3749350 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43130 : A) : (term414 A x y _43130) = (term539 A y x _43130).
Proof. exact (EQ_MP (@lem3749349 A y x _43130) (@lem0)). Qed.
Lemma lem3749351 {A : Type'} (_43130 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A y x _43130.
Proof. exact (EQ_MP (@lem3749350 A y x _43130) (@lem3748947 A _43130 x x'' s y z x''' h1)). Qed.
Lemma lem3749353 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749354 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43130 : A) : (term539 A y x _43130) = (term573 A x y _43130).
Proof. exact (@lem3749353 (term567 A x _43130) (y _43130)). Qed.
Lemma lem3749356 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749357 {A : Type'} (x : A -> Prop) (_43130 : A) : (term574 A x _43130) = (x _43130).
Proof. exact (@lem3749356 (x _43130)). Qed.
Lemma lem3749358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749359 {A : Type'} (x : A -> Prop) (_43130 : A) : (term575 A x _43130) = (term376 A x _43130).
Proof. exact (MK_COMB (@lem3749358) (@lem3749357 A x _43130)). Qed.
Lemma lem3749360 {A : Type'} (y : A -> Prop) (_43130 : A) : (y _43130) = (y _43130).
Proof. exact (eq_refl (y _43130)). Qed.
Lemma lem3749361 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43130 : A) : (term573 A x y _43130) = (term378 A x y _43130).
Proof. exact (MK_COMB (@lem3749359 A x _43130) (@lem3749360 A y _43130)). Qed.
Lemma lem3749362 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43130 : A) : (term539 A y x _43130) = (term378 A x y _43130).
Proof. exact (TRANS (@lem3749354 A x y _43130) (@lem3749361 A x y _43130)). Qed.
Lemma lem3749365 {A : Type'} (_43130 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y _43130.
Proof. exact (EQ_MP (@lem3749362 A x y _43130) (@lem3749351 A _43130 x x'' s y z x''' h1)). Qed.
Lemma lem3749366 {A : Type'} (_43130 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y _43130.
Proof. exact (@lem3749365 A _43130 x x'' s y z x''' h1). Qed.
Lemma lem3749367 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y x''.
Proof. exact (@lem3749366 A x'' x x'' s y z x''' h1). Qed.
Lemma lem3749370 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : y x''.
Proof. exact (@lem3749367 A x x'' s y z x''' h2 (@lem3749322 A x y x'' h1)). Qed.
Lemma lem3749371 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : term568 A y x''.
Proof. exact (fun h0 : term567 A y x'' => @lem3749370 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749373 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749374 {A : Type'} (y : A -> Prop) (x'' : A) : (term568 A y x'') = (y x'').
Proof. exact (@lem3749373 (y x'')). Qed.
Lemma lem3749375 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : y x''.
Proof. exact (EQ_MP (@lem3749374 A y x'') (@lem3749371 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749378 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3749380 {A : Type'} (y : A -> Prop) (x'' : A) : (term567 A y x'') = (term576 A y x'').
Proof. exact (@lem3749378 (y x'')). Qed.
Lemma lem3749383 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : term576 A y x''.
Proof. exact (EQ_MP (@lem3749380 A y x'') (@lem3748951 A x y x'' h1)). Qed.
Lemma lem3749386 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (@lem3749383 A x y x'' h1 (@lem3749375 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749387 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : term577.
Proof. exact (fun h0 : ~ False => @lem3749386 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749389 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749390 : term577 = False.
Proof. exact (@lem3749389 False). Qed.
Lemma lem3749391 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (EQ_MP (@lem3749390) (@lem3749387 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749393 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : x x''.
Proof. exact (proj1 (@lem3748002 A x y x'' h1)). Qed.
Lemma lem3749394 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : term568 A x x''.
Proof. exact (fun h0 : term567 A x x'' => @lem3749393 A x y x'' h1). Qed.
Lemma lem3749396 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749397 {A : Type'} (x : A -> Prop) (x'' : A) : (term568 A x x'') = (x x'').
Proof. exact (@lem3749396 (x x'')). Qed.
Lemma lem3749398 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : x x''.
Proof. exact (EQ_MP (@lem3749397 A x x'') (@lem3749394 A x y x'' h1)). Qed.
Lemma lem3749404 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749405 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43134 : A) : (term414 A x y _43134) = (term539 A y x _43134).
Proof. exact (@lem3749404 (y _43134) (term567 A x _43134)). Qed.
Lemma lem3749411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749412 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43134 : A) : (term570 A x y _43134) = (term571 A y x _43134).
Proof. exact (MK_COMB (@lem3749411) (@lem3749405 A y x _43134)). Qed.
Lemma lem3749418 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43134 : A) : (term539 A y x _43134) = (term539 A y x _43134).
Proof. exact (eq_refl (term539 A y x _43134)). Qed.
Lemma lem3749419 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43134 : A) : ((term414 A x y _43134) = (term539 A y x _43134)) = ((term539 A y x _43134) = (term539 A y x _43134)).
Proof. exact (MK_COMB (@lem3749412 A y x _43134) (@lem3749418 A y x _43134)). Qed.
Lemma lem3749421 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749422 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749421 Prop x). Qed.
Lemma lem3749423 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43134 : A) : ((term539 A y x _43134) = (term539 A y x _43134)) = True.
Proof. exact (@lem3749422 (term539 A y x _43134)). Qed.
Lemma lem3749424 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43134 : A) : ((term414 A x y _43134) = (term539 A y x _43134)) = True.
Proof. exact (TRANS (@lem3749419 A y x _43134) (@lem3749423 A y x _43134)). Qed.
Lemma lem3749425 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43134 : A) : True = ((term414 A x y _43134) = (term539 A y x _43134)).
Proof. exact (SYM (@lem3749424 A y x _43134)). Qed.
Lemma lem3749426 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43134 : A) : (term414 A x y _43134) = (term539 A y x _43134).
Proof. exact (EQ_MP (@lem3749425 A y x _43134) (@lem0)). Qed.
Lemma lem3749427 {A : Type'} (_43134 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A y x _43134.
Proof. exact (EQ_MP (@lem3749426 A y x _43134) (@lem3748983 A _43134 x x'' s y z x''' h1)). Qed.
Lemma lem3749429 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749430 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43134 : A) : (term539 A y x _43134) = (term573 A x y _43134).
Proof. exact (@lem3749429 (term567 A x _43134) (y _43134)). Qed.
Lemma lem3749432 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749433 {A : Type'} (x : A -> Prop) (_43134 : A) : (term574 A x _43134) = (x _43134).
Proof. exact (@lem3749432 (x _43134)). Qed.
Lemma lem3749434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749435 {A : Type'} (x : A -> Prop) (_43134 : A) : (term575 A x _43134) = (term376 A x _43134).
Proof. exact (MK_COMB (@lem3749434) (@lem3749433 A x _43134)). Qed.
Lemma lem3749436 {A : Type'} (y : A -> Prop) (_43134 : A) : (y _43134) = (y _43134).
Proof. exact (eq_refl (y _43134)). Qed.
Lemma lem3749437 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43134 : A) : (term573 A x y _43134) = (term378 A x y _43134).
Proof. exact (MK_COMB (@lem3749435 A x _43134) (@lem3749436 A y _43134)). Qed.
Lemma lem3749438 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43134 : A) : (term539 A y x _43134) = (term378 A x y _43134).
Proof. exact (TRANS (@lem3749430 A x y _43134) (@lem3749437 A x y _43134)). Qed.
Lemma lem3749441 {A : Type'} (_43134 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y _43134.
Proof. exact (EQ_MP (@lem3749438 A x y _43134) (@lem3749427 A _43134 x x'' s y z x''' h1)). Qed.
Lemma lem3749442 {A : Type'} (_43134 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y _43134.
Proof. exact (@lem3749441 A _43134 x x'' s y z x''' h1). Qed.
Lemma lem3749443 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y x''.
Proof. exact (@lem3749442 A x'' x x'' s y z x''' h1). Qed.
Lemma lem3749446 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : y x''.
Proof. exact (@lem3749443 A x x'' s y z x''' h2 (@lem3749398 A x y x'' h1)). Qed.
Lemma lem3749447 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : term568 A y x''.
Proof. exact (fun h0 : term567 A y x'' => @lem3749446 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749449 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749450 {A : Type'} (y : A -> Prop) (x'' : A) : (term568 A y x'') = (y x'').
Proof. exact (@lem3749449 (y x'')). Qed.
Lemma lem3749451 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : y x''.
Proof. exact (EQ_MP (@lem3749450 A y x'') (@lem3749447 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749454 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3749456 {A : Type'} (y : A -> Prop) (x'' : A) : (term567 A y x'') = (term576 A y x'').
Proof. exact (@lem3749454 (y x'')). Qed.
Lemma lem3749459 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term439 A x y x'') : term576 A y x''.
Proof. exact (EQ_MP (@lem3749456 A y x'') (@lem3748987 A x y x'' h1)). Qed.
Lemma lem3749462 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (@lem3749459 A x y x'' h1 (@lem3749451 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749463 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : term577.
Proof. exact (fun h0 : ~ False => @lem3749462 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749465 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749466 : term577 = False.
Proof. exact (@lem3749465 False). Qed.
Lemma lem3749467 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (EQ_MP (@lem3749466) (@lem3749463 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749469 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : y x'''.
Proof. exact (proj1 (@lem3748026 A y z x''' h1)). Qed.
Lemma lem3749470 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term568 A y x'''.
Proof. exact (fun h0 : term567 A y x''' => @lem3749469 A y z x''' h1). Qed.
Lemma lem3749472 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749473 {A : Type'} (y : A -> Prop) (x''' : A) : (term568 A y x''') = (y x''').
Proof. exact (@lem3749472 (y x''')). Qed.
Lemma lem3749474 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : y x'''.
Proof. exact (EQ_MP (@lem3749473 A y x''') (@lem3749470 A y z x''' h1)). Qed.
Lemma lem3749480 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749481 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43138 : A) : (term414 A y z _43138) = (term539 A z y _43138).
Proof. exact (@lem3749480 (z _43138) (term567 A y _43138)). Qed.
Lemma lem3749487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749488 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43138 : A) : (term570 A y z _43138) = (term571 A z y _43138).
Proof. exact (MK_COMB (@lem3749487) (@lem3749481 A z y _43138)). Qed.
Lemma lem3749494 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43138 : A) : (term539 A z y _43138) = (term539 A z y _43138).
Proof. exact (eq_refl (term539 A z y _43138)). Qed.
Lemma lem3749495 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43138 : A) : ((term414 A y z _43138) = (term539 A z y _43138)) = ((term539 A z y _43138) = (term539 A z y _43138)).
Proof. exact (MK_COMB (@lem3749488 A z y _43138) (@lem3749494 A z y _43138)). Qed.
Lemma lem3749497 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749498 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749497 Prop x). Qed.
Lemma lem3749499 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43138 : A) : ((term539 A z y _43138) = (term539 A z y _43138)) = True.
Proof. exact (@lem3749498 (term539 A z y _43138)). Qed.
Lemma lem3749500 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43138 : A) : ((term414 A y z _43138) = (term539 A z y _43138)) = True.
Proof. exact (TRANS (@lem3749495 A z y _43138) (@lem3749499 A z y _43138)). Qed.
Lemma lem3749501 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43138 : A) : True = ((term414 A y z _43138) = (term539 A z y _43138)).
Proof. exact (SYM (@lem3749500 A z y _43138)). Qed.
Lemma lem3749502 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43138 : A) : (term414 A y z _43138) = (term539 A z y _43138).
Proof. exact (EQ_MP (@lem3749501 A z y _43138) (@lem0)). Qed.
Lemma lem3749503 {A : Type'} (_43138 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A z y _43138.
Proof. exact (EQ_MP (@lem3749502 A z y _43138) (@lem3749015 A _43138 x x'' s y z x''' h1)). Qed.
Lemma lem3749505 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749506 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43138 : A) : (term539 A z y _43138) = (term573 A y z _43138).
Proof. exact (@lem3749505 (term567 A y _43138) (z _43138)). Qed.
Lemma lem3749508 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749509 {A : Type'} (y : A -> Prop) (_43138 : A) : (term574 A y _43138) = (y _43138).
Proof. exact (@lem3749508 (y _43138)). Qed.
Lemma lem3749510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749511 {A : Type'} (y : A -> Prop) (_43138 : A) : (term575 A y _43138) = (term376 A y _43138).
Proof. exact (MK_COMB (@lem3749510) (@lem3749509 A y _43138)). Qed.
Lemma lem3749512 {A : Type'} (z : A -> Prop) (_43138 : A) : (z _43138) = (z _43138).
Proof. exact (eq_refl (z _43138)). Qed.
Lemma lem3749513 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43138 : A) : (term573 A y z _43138) = (term378 A y z _43138).
Proof. exact (MK_COMB (@lem3749511 A y _43138) (@lem3749512 A z _43138)). Qed.
Lemma lem3749514 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43138 : A) : (term539 A z y _43138) = (term378 A y z _43138).
Proof. exact (TRANS (@lem3749506 A y z _43138) (@lem3749513 A y z _43138)). Qed.
Lemma lem3749517 {A : Type'} (_43138 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43138.
Proof. exact (EQ_MP (@lem3749514 A y z _43138) (@lem3749503 A _43138 x x'' s y z x''' h1)). Qed.
Lemma lem3749518 {A : Type'} (_43138 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43138.
Proof. exact (@lem3749517 A _43138 x x'' s y z x''' h1). Qed.
Lemma lem3749519 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z x'''.
Proof. exact (@lem3749518 A x''' x x'' s y z x''' h1). Qed.
Lemma lem3749522 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : z x'''.
Proof. exact (@lem3749519 A x x'' s y z x''' h2 (@lem3749474 A y z x''' h1)). Qed.
Lemma lem3749523 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : term568 A z x'''.
Proof. exact (fun h0 : term567 A z x''' => @lem3749522 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749525 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749526 {A : Type'} (z : A -> Prop) (x''' : A) : (term568 A z x''') = (z x''').
Proof. exact (@lem3749525 (z x''')). Qed.
Lemma lem3749527 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : z x'''.
Proof. exact (EQ_MP (@lem3749526 A z x''') (@lem3749523 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749530 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3749532 {A : Type'} (z : A -> Prop) (x''' : A) : (term567 A z x''') = (term576 A z x''').
Proof. exact (@lem3749530 (z x''')). Qed.
Lemma lem3749535 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term576 A z x'''.
Proof. exact (EQ_MP (@lem3749532 A z x''') (@lem3749035 A y z x''' h1)). Qed.
Lemma lem3749538 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (@lem3749535 A y z x''' h1 (@lem3749527 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749539 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : term577.
Proof. exact (fun h0 : ~ False => @lem3749538 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749541 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749542 : term577 = False.
Proof. exact (@lem3749541 False). Qed.
Lemma lem3749543 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (EQ_MP (@lem3749542) (@lem3749539 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749545 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : y x'''.
Proof. exact (proj1 (@lem3748026 A y z x''' h1)). Qed.
Lemma lem3749546 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term568 A y x'''.
Proof. exact (fun h0 : term567 A y x''' => @lem3749545 A y z x''' h1). Qed.
Lemma lem3749548 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749549 {A : Type'} (y : A -> Prop) (x''' : A) : (term568 A y x''') = (y x''').
Proof. exact (@lem3749548 (y x''')). Qed.
Lemma lem3749550 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : y x'''.
Proof. exact (EQ_MP (@lem3749549 A y x''') (@lem3749546 A y z x''' h1)). Qed.
Lemma lem3749556 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749557 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43142 : A) : (term414 A y z _43142) = (term539 A z y _43142).
Proof. exact (@lem3749556 (z _43142) (term567 A y _43142)). Qed.
Lemma lem3749563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749564 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43142 : A) : (term570 A y z _43142) = (term571 A z y _43142).
Proof. exact (MK_COMB (@lem3749563) (@lem3749557 A z y _43142)). Qed.
Lemma lem3749570 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43142 : A) : (term539 A z y _43142) = (term539 A z y _43142).
Proof. exact (eq_refl (term539 A z y _43142)). Qed.
Lemma lem3749571 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43142 : A) : ((term414 A y z _43142) = (term539 A z y _43142)) = ((term539 A z y _43142) = (term539 A z y _43142)).
Proof. exact (MK_COMB (@lem3749564 A z y _43142) (@lem3749570 A z y _43142)). Qed.
Lemma lem3749573 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749574 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749573 Prop x). Qed.
Lemma lem3749575 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43142 : A) : ((term539 A z y _43142) = (term539 A z y _43142)) = True.
Proof. exact (@lem3749574 (term539 A z y _43142)). Qed.
Lemma lem3749576 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43142 : A) : ((term414 A y z _43142) = (term539 A z y _43142)) = True.
Proof. exact (TRANS (@lem3749571 A z y _43142) (@lem3749575 A z y _43142)). Qed.
Lemma lem3749577 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43142 : A) : True = ((term414 A y z _43142) = (term539 A z y _43142)).
Proof. exact (SYM (@lem3749576 A z y _43142)). Qed.
Lemma lem3749578 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43142 : A) : (term414 A y z _43142) = (term539 A z y _43142).
Proof. exact (EQ_MP (@lem3749577 A z y _43142) (@lem0)). Qed.
Lemma lem3749579 {A : Type'} (_43142 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A z y _43142.
Proof. exact (EQ_MP (@lem3749578 A z y _43142) (@lem3749051 A _43142 x x'' s y z x''' h1)). Qed.
Lemma lem3749581 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749582 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43142 : A) : (term539 A z y _43142) = (term573 A y z _43142).
Proof. exact (@lem3749581 (term567 A y _43142) (z _43142)). Qed.
Lemma lem3749584 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749585 {A : Type'} (y : A -> Prop) (_43142 : A) : (term574 A y _43142) = (y _43142).
Proof. exact (@lem3749584 (y _43142)). Qed.
Lemma lem3749586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749587 {A : Type'} (y : A -> Prop) (_43142 : A) : (term575 A y _43142) = (term376 A y _43142).
Proof. exact (MK_COMB (@lem3749586) (@lem3749585 A y _43142)). Qed.
Lemma lem3749588 {A : Type'} (z : A -> Prop) (_43142 : A) : (z _43142) = (z _43142).
Proof. exact (eq_refl (z _43142)). Qed.
Lemma lem3749589 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43142 : A) : (term573 A y z _43142) = (term378 A y z _43142).
Proof. exact (MK_COMB (@lem3749587 A y _43142) (@lem3749588 A z _43142)). Qed.
Lemma lem3749590 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43142 : A) : (term539 A z y _43142) = (term378 A y z _43142).
Proof. exact (TRANS (@lem3749582 A y z _43142) (@lem3749589 A y z _43142)). Qed.
Lemma lem3749593 {A : Type'} (_43142 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43142.
Proof. exact (EQ_MP (@lem3749590 A y z _43142) (@lem3749579 A _43142 x x'' s y z x''' h1)). Qed.
Lemma lem3749594 {A : Type'} (_43142 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43142.
Proof. exact (@lem3749593 A _43142 x x'' s y z x''' h1). Qed.
Lemma lem3749595 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z x'''.
Proof. exact (@lem3749594 A x''' x x'' s y z x''' h1). Qed.
Lemma lem3749598 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : z x'''.
Proof. exact (@lem3749595 A x x'' s y z x''' h2 (@lem3749550 A y z x''' h1)). Qed.
Lemma lem3749599 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : term568 A z x'''.
Proof. exact (fun h0 : term567 A z x''' => @lem3749598 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749601 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749602 {A : Type'} (z : A -> Prop) (x''' : A) : (term568 A z x''') = (z x''').
Proof. exact (@lem3749601 (z x''')). Qed.
Lemma lem3749603 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : z x'''.
Proof. exact (EQ_MP (@lem3749602 A z x''') (@lem3749599 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749606 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3749608 {A : Type'} (z : A -> Prop) (x''' : A) : (term567 A z x''') = (term576 A z x''').
Proof. exact (@lem3749606 (z x''')). Qed.
Lemma lem3749611 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') : term576 A z x'''.
Proof. exact (EQ_MP (@lem3749608 A z x''') (@lem3749071 A y z x''' h1)). Qed.
Lemma lem3749614 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (@lem3749611 A y z x''' h1 (@lem3749603 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749615 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : term577.
Proof. exact (fun h0 : ~ False => @lem3749614 A x x'' s y z x''' h1 h2). Qed.
Lemma lem3749617 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749618 : term577 = False.
Proof. exact (@lem3749617 False). Qed.
Lemma lem3749619 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (EQ_MP (@lem3749618) (@lem3749615 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749621 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term439 A x z x') : x x'.
Proof. exact (proj1 (@lem3748038 A x z x' h1)). Qed.
Lemma lem3749622 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term439 A x z x') : term568 A x x'.
Proof. exact (fun h0 : term567 A x x' => @lem3749621 A x z x' h1). Qed.
Lemma lem3749624 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749625 {A : Type'} (x : A -> Prop) (x' : A) : (term568 A x x') = (x x').
Proof. exact (@lem3749624 (x x')). Qed.
Lemma lem3749626 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term439 A x z x') : x x'.
Proof. exact (EQ_MP (@lem3749625 A x x') (@lem3749622 A x z x' h1)). Qed.
Lemma lem3749632 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749633 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43150 : A) : (term414 A x y _43150) = (term539 A y x _43150).
Proof. exact (@lem3749632 (y _43150) (term567 A x _43150)). Qed.
Lemma lem3749639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749640 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43150 : A) : (term570 A x y _43150) = (term571 A y x _43150).
Proof. exact (MK_COMB (@lem3749639) (@lem3749633 A y x _43150)). Qed.
Lemma lem3749646 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43150 : A) : (term539 A y x _43150) = (term539 A y x _43150).
Proof. exact (eq_refl (term539 A y x _43150)). Qed.
Lemma lem3749647 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43150 : A) : ((term414 A x y _43150) = (term539 A y x _43150)) = ((term539 A y x _43150) = (term539 A y x _43150)).
Proof. exact (MK_COMB (@lem3749640 A y x _43150) (@lem3749646 A y x _43150)). Qed.
Lemma lem3749649 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749650 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749649 Prop x). Qed.
Lemma lem3749651 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43150 : A) : ((term539 A y x _43150) = (term539 A y x _43150)) = True.
Proof. exact (@lem3749650 (term539 A y x _43150)). Qed.
Lemma lem3749652 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43150 : A) : ((term414 A x y _43150) = (term539 A y x _43150)) = True.
Proof. exact (TRANS (@lem3749647 A y x _43150) (@lem3749651 A y x _43150)). Qed.
Lemma lem3749653 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43150 : A) : True = ((term414 A x y _43150) = (term539 A y x _43150)).
Proof. exact (SYM (@lem3749652 A y x _43150)). Qed.
Lemma lem3749654 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43150 : A) : (term414 A x y _43150) = (term539 A y x _43150).
Proof. exact (EQ_MP (@lem3749653 A y x _43150) (@lem0)). Qed.
Lemma lem3749655 {A : Type'} (_43150 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A y x _43150.
Proof. exact (EQ_MP (@lem3749654 A y x _43150) (@lem3749107 A _43150 x x'' s y z x''' h1)). Qed.
Lemma lem3749657 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749658 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43150 : A) : (term539 A y x _43150) = (term573 A x y _43150).
Proof. exact (@lem3749657 (term567 A x _43150) (y _43150)). Qed.
Lemma lem3749660 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749661 {A : Type'} (x : A -> Prop) (_43150 : A) : (term574 A x _43150) = (x _43150).
Proof. exact (@lem3749660 (x _43150)). Qed.
Lemma lem3749662 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749663 {A : Type'} (x : A -> Prop) (_43150 : A) : (term575 A x _43150) = (term376 A x _43150).
Proof. exact (MK_COMB (@lem3749662) (@lem3749661 A x _43150)). Qed.
Lemma lem3749664 {A : Type'} (y : A -> Prop) (_43150 : A) : (y _43150) = (y _43150).
Proof. exact (eq_refl (y _43150)). Qed.
Lemma lem3749665 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43150 : A) : (term573 A x y _43150) = (term378 A x y _43150).
Proof. exact (MK_COMB (@lem3749663 A x _43150) (@lem3749664 A y _43150)). Qed.
Lemma lem3749666 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43150 : A) : (term539 A y x _43150) = (term378 A x y _43150).
Proof. exact (TRANS (@lem3749658 A x y _43150) (@lem3749665 A x y _43150)). Qed.
Lemma lem3749669 {A : Type'} (_43150 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y _43150.
Proof. exact (EQ_MP (@lem3749666 A x y _43150) (@lem3749655 A _43150 x x'' s y z x''' h1)). Qed.
Lemma lem3749670 {A : Type'} (_43150 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y _43150.
Proof. exact (@lem3749669 A _43150 x x'' s y z x''' h1). Qed.
Lemma lem3749671 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y x'.
Proof. exact (@lem3749670 A x' x x'' s y z x''' h1). Qed.
Lemma lem3749674 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : y x'.
Proof. exact (@lem3749671 A x' x x'' s y z x''' h2 (@lem3749626 A x z x' h1)). Qed.
Lemma lem3749675 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : term568 A y x'.
Proof. exact (fun h0 : term567 A y x' => @lem3749674 A x' x x'' s y z x''' h1 h2). Qed.
Lemma lem3749677 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749678 {A : Type'} (y : A -> Prop) (x' : A) : (term568 A y x') = (y x').
Proof. exact (@lem3749677 (y x')). Qed.
Lemma lem3749679 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : y x'.
Proof. exact (EQ_MP (@lem3749678 A y x') (@lem3749675 A x' x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749685 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749686 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43148 : A) : (term414 A y z _43148) = (term539 A z y _43148).
Proof. exact (@lem3749685 (z _43148) (term567 A y _43148)). Qed.
Lemma lem3749692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749693 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43148 : A) : (term570 A y z _43148) = (term571 A z y _43148).
Proof. exact (MK_COMB (@lem3749692) (@lem3749686 A z y _43148)). Qed.
Lemma lem3749699 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43148 : A) : (term539 A z y _43148) = (term539 A z y _43148).
Proof. exact (eq_refl (term539 A z y _43148)). Qed.
Lemma lem3749700 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43148 : A) : ((term414 A y z _43148) = (term539 A z y _43148)) = ((term539 A z y _43148) = (term539 A z y _43148)).
Proof. exact (MK_COMB (@lem3749693 A z y _43148) (@lem3749699 A z y _43148)). Qed.
Lemma lem3749702 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749703 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749702 Prop x). Qed.
Lemma lem3749704 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43148 : A) : ((term539 A z y _43148) = (term539 A z y _43148)) = True.
Proof. exact (@lem3749703 (term539 A z y _43148)). Qed.
Lemma lem3749705 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43148 : A) : ((term414 A y z _43148) = (term539 A z y _43148)) = True.
Proof. exact (TRANS (@lem3749700 A z y _43148) (@lem3749704 A z y _43148)). Qed.
Lemma lem3749706 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43148 : A) : True = ((term414 A y z _43148) = (term539 A z y _43148)).
Proof. exact (SYM (@lem3749705 A z y _43148)). Qed.
Lemma lem3749707 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_43148 : A) : (term414 A y z _43148) = (term539 A z y _43148).
Proof. exact (EQ_MP (@lem3749706 A z y _43148) (@lem0)). Qed.
Lemma lem3749708 {A : Type'} (_43148 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A z y _43148.
Proof. exact (EQ_MP (@lem3749707 A z y _43148) (@lem3749095 A _43148 x x'' s y z x''' h1)). Qed.
Lemma lem3749710 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749711 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43148 : A) : (term539 A z y _43148) = (term573 A y z _43148).
Proof. exact (@lem3749710 (term567 A y _43148) (z _43148)). Qed.
Lemma lem3749713 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749714 {A : Type'} (y : A -> Prop) (_43148 : A) : (term574 A y _43148) = (y _43148).
Proof. exact (@lem3749713 (y _43148)). Qed.
Lemma lem3749715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749716 {A : Type'} (y : A -> Prop) (_43148 : A) : (term575 A y _43148) = (term376 A y _43148).
Proof. exact (MK_COMB (@lem3749715) (@lem3749714 A y _43148)). Qed.
Lemma lem3749717 {A : Type'} (z : A -> Prop) (_43148 : A) : (z _43148) = (z _43148).
Proof. exact (eq_refl (z _43148)). Qed.
Lemma lem3749718 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43148 : A) : (term573 A y z _43148) = (term378 A y z _43148).
Proof. exact (MK_COMB (@lem3749716 A y _43148) (@lem3749717 A z _43148)). Qed.
Lemma lem3749719 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_43148 : A) : (term539 A z y _43148) = (term378 A y z _43148).
Proof. exact (TRANS (@lem3749711 A y z _43148) (@lem3749718 A y z _43148)). Qed.
Lemma lem3749722 {A : Type'} (_43148 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43148.
Proof. exact (EQ_MP (@lem3749719 A y z _43148) (@lem3749708 A _43148 x x'' s y z x''' h1)). Qed.
Lemma lem3749723 {A : Type'} (_43148 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z _43148.
Proof. exact (@lem3749722 A _43148 x x'' s y z x''' h1). Qed.
Lemma lem3749724 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A y z x'.
Proof. exact (@lem3749723 A x' x x'' s y z x''' h1). Qed.
Lemma lem3749727 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : z x'.
Proof. exact (@lem3749724 A x' x x'' s y z x''' h2 (@lem3749679 A x' x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749728 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : term568 A z x'.
Proof. exact (fun h0 : term567 A z x' => @lem3749727 A x' x x'' s y z x''' h1 h2). Qed.
Lemma lem3749730 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749731 {A : Type'} (z : A -> Prop) (x' : A) : (term568 A z x') = (z x').
Proof. exact (@lem3749730 (z x')). Qed.
Lemma lem3749732 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : z x'.
Proof. exact (EQ_MP (@lem3749731 A z x') (@lem3749728 A x' x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749735 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3749737 {A : Type'} (z : A -> Prop) (x' : A) : (term567 A z x') = (term576 A z x').
Proof. exact (@lem3749735 (z x')). Qed.
Lemma lem3749740 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term439 A x z x') : term576 A z x'.
Proof. exact (EQ_MP (@lem3749737 A z x') (@lem3749119 A x z x' h1)). Qed.
Lemma lem3749743 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (@lem3749740 A x z x' h1 (@lem3749732 A x' x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749744 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : term577.
Proof. exact (fun h0 : ~ False => @lem3749743 A x' x x'' s y z x''' h1 h2). Qed.
Lemma lem3749746 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749747 : term577 = False.
Proof. exact (@lem3749746 False). Qed.
Lemma lem3749748 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term439 A x z x') (h2 : term514 A x x'' s y z x''') : False.
Proof. exact (EQ_MP (@lem3749747) (@lem3749744 A x' x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749750 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term443 A y z x''') : z x'''.
Proof. exact (proj2 (@lem3748027 A y z x''' h1)). Qed.
Lemma lem3749751 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term443 A y z x''') : term568 A z x'''.
Proof. exact (fun h0 : term567 A z x''' => @lem3749750 A y z x''' h1). Qed.
Lemma lem3749753 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749754 {A : Type'} (z : A -> Prop) (x''' : A) : (term568 A z x''') = (z x''').
Proof. exact (@lem3749753 (z x''')). Qed.
Lemma lem3749755 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term443 A y z x''') : z x'''.
Proof. exact (EQ_MP (@lem3749754 A z x''') (@lem3749751 A y z x''' h1)). Qed.
Lemma lem3749757 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749758 {A : Type'} (z : A -> Prop) (x : A -> Prop) (_43155 : A) : (term539 A x z _43155) = (term573 A z x _43155).
Proof. exact (@lem3749757 (term567 A z _43155) (x _43155)). Qed.
Lemma lem3749760 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749761 {A : Type'} (z : A -> Prop) (_43155 : A) : (term574 A z _43155) = (z _43155).
Proof. exact (@lem3749760 (z _43155)). Qed.
Lemma lem3749762 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749763 {A : Type'} (z : A -> Prop) (_43155 : A) : (term575 A z _43155) = (term376 A z _43155).
Proof. exact (MK_COMB (@lem3749762) (@lem3749761 A z _43155)). Qed.
Lemma lem3749764 {A : Type'} (x : A -> Prop) (_43155 : A) : (x _43155) = (x _43155).
Proof. exact (eq_refl (x _43155)). Qed.
Lemma lem3749765 {A : Type'} (z : A -> Prop) (x : A -> Prop) (_43155 : A) : (term573 A z x _43155) = (term378 A z x _43155).
Proof. exact (MK_COMB (@lem3749763 A z _43155) (@lem3749764 A x _43155)). Qed.
Lemma lem3749766 {A : Type'} (z : A -> Prop) (x : A -> Prop) (_43155 : A) : (term539 A x z _43155) = (term378 A z x _43155).
Proof. exact (TRANS (@lem3749758 A z x _43155) (@lem3749765 A z x _43155)). Qed.
Lemma lem3749769 {A : Type'} (_43155 : A) (x : A -> Prop) (z : A -> Prop) (h1 : term554 A x z) : term378 A z x _43155.
Proof. exact (EQ_MP (@lem3749766 A z x _43155) (@lem3749157 A _43155 x z h1)). Qed.
Lemma lem3749770 {A : Type'} (_43155 : A) (x : A -> Prop) (z : A -> Prop) (h1 : term554 A x z) : term378 A z x _43155.
Proof. exact (@lem3749769 A _43155 x z h1). Qed.
Lemma lem3749771 {A : Type'} (x''' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term554 A x z) : term378 A z x x'''.
Proof. exact (@lem3749770 A x''' x z h1). Qed.
Lemma lem3749774 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') : x x'''.
Proof. exact (@lem3749771 A x''' x z h1 (@lem3749755 A y z x''' h2)). Qed.
Lemma lem3749775 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') : term568 A x x'''.
Proof. exact (fun h0 : term567 A x x''' => @lem3749774 A x y z x''' h1 h2). Qed.
Lemma lem3749777 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749778 {A : Type'} (x : A -> Prop) (x''' : A) : (term568 A x x''') = (x x''').
Proof. exact (@lem3749777 (x x''')). Qed.
Lemma lem3749779 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') : x x'''.
Proof. exact (EQ_MP (@lem3749778 A x x''') (@lem3749775 A x y z x''' h1 h2)). Qed.
Lemma lem3749785 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3749786 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43154 : A) : (term414 A x y _43154) = (term539 A y x _43154).
Proof. exact (@lem3749785 (y _43154) (term567 A x _43154)). Qed.
Lemma lem3749792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3749793 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43154 : A) : (term570 A x y _43154) = (term571 A y x _43154).
Proof. exact (MK_COMB (@lem3749792) (@lem3749786 A y x _43154)). Qed.
Lemma lem3749799 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43154 : A) : (term539 A y x _43154) = (term539 A y x _43154).
Proof. exact (eq_refl (term539 A y x _43154)). Qed.
Lemma lem3749800 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43154 : A) : ((term414 A x y _43154) = (term539 A y x _43154)) = ((term539 A y x _43154) = (term539 A y x _43154)).
Proof. exact (MK_COMB (@lem3749793 A y x _43154) (@lem3749799 A y x _43154)). Qed.
Lemma lem3749802 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3749803 (x : Prop) : (x = x) = True.
Proof. exact (@lem3749802 Prop x). Qed.
Lemma lem3749804 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43154 : A) : ((term539 A y x _43154) = (term539 A y x _43154)) = True.
Proof. exact (@lem3749803 (term539 A y x _43154)). Qed.
Lemma lem3749805 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43154 : A) : ((term414 A x y _43154) = (term539 A y x _43154)) = True.
Proof. exact (TRANS (@lem3749800 A y x _43154) (@lem3749804 A y x _43154)). Qed.
Lemma lem3749806 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43154 : A) : True = ((term414 A x y _43154) = (term539 A y x _43154)).
Proof. exact (SYM (@lem3749805 A y x _43154)). Qed.
Lemma lem3749807 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_43154 : A) : (term414 A x y _43154) = (term539 A y x _43154).
Proof. exact (EQ_MP (@lem3749806 A y x _43154) (@lem0)). Qed.
Lemma lem3749808 {A : Type'} (_43154 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term539 A y x _43154.
Proof. exact (EQ_MP (@lem3749807 A y x _43154) (@lem3749143 A _43154 x x'' s y z x''' h1)). Qed.
Lemma lem3749810 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3749811 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43154 : A) : (term539 A y x _43154) = (term573 A x y _43154).
Proof. exact (@lem3749810 (term567 A x _43154) (y _43154)). Qed.
Lemma lem3749813 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3749814 {A : Type'} (x : A -> Prop) (_43154 : A) : (term574 A x _43154) = (x _43154).
Proof. exact (@lem3749813 (x _43154)). Qed.
Lemma lem3749815 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3749816 {A : Type'} (x : A -> Prop) (_43154 : A) : (term575 A x _43154) = (term376 A x _43154).
Proof. exact (MK_COMB (@lem3749815) (@lem3749814 A x _43154)). Qed.
Lemma lem3749817 {A : Type'} (y : A -> Prop) (_43154 : A) : (y _43154) = (y _43154).
Proof. exact (eq_refl (y _43154)). Qed.
Lemma lem3749818 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43154 : A) : (term573 A x y _43154) = (term378 A x y _43154).
Proof. exact (MK_COMB (@lem3749816 A x _43154) (@lem3749817 A y _43154)). Qed.
Lemma lem3749819 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_43154 : A) : (term539 A y x _43154) = (term378 A x y _43154).
Proof. exact (TRANS (@lem3749811 A x y _43154) (@lem3749818 A x y _43154)). Qed.
Lemma lem3749822 {A : Type'} (_43154 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y _43154.
Proof. exact (EQ_MP (@lem3749819 A x y _43154) (@lem3749808 A _43154 x x'' s y z x''' h1)). Qed.
Lemma lem3749823 {A : Type'} (_43154 : A) (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y _43154.
Proof. exact (@lem3749822 A _43154 x x'' s y z x''' h1). Qed.
Lemma lem3749824 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term514 A x x'' s y z x''') : term378 A x y x'''.
Proof. exact (@lem3749823 A x''' x x'' s y z x''' h1). Qed.
Lemma lem3749827 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') (h3 : term514 A x x'' s y z x''') : y x'''.
Proof. exact (@lem3749824 A x x'' s y z x''' h3 (@lem3749779 A x y z x''' h1 h2)). Qed.
Lemma lem3749828 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') (h3 : term514 A x x'' s y z x''') : term568 A y x'''.
Proof. exact (fun h0 : term567 A y x''' => @lem3749827 A x x'' s y z x''' h1 h2 h3). Qed.
Lemma lem3749830 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749831 {A : Type'} (y : A -> Prop) (x''' : A) : (term568 A y x''') = (y x''').
Proof. exact (@lem3749830 (y x''')). Qed.
Lemma lem3749832 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') (h3 : term514 A x x'' s y z x''') : y x'''.
Proof. exact (EQ_MP (@lem3749831 A y x''') (@lem3749828 A x x'' s y z x''' h1 h2 h3)). Qed.
Lemma lem3749835 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3749837 {A : Type'} (y : A -> Prop) (x''' : A) : (term567 A y x''') = (term576 A y x''').
Proof. exact (@lem3749835 (y x''')). Qed.
Lemma lem3749840 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term443 A y z x''') : term576 A y x'''.
Proof. exact (EQ_MP (@lem3749837 A y x''') (@lem3749149 A y z x''' h1)). Qed.
Lemma lem3749843 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') (h3 : term514 A x x'' s y z x''') : False.
Proof. exact (@lem3749840 A y z x''' h2 (@lem3749832 A x x'' s y z x''' h1 h2 h3)). Qed.
Lemma lem3749844 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') (h3 : term514 A x x'' s y z x''') : term577.
Proof. exact (fun h0 : ~ False => @lem3749843 A x x'' s y z x''' h1 h2 h3). Qed.
Lemma lem3749846 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3749847 : term577 = False.
Proof. exact (@lem3749846 False). Qed.
Lemma lem3749848 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term554 A x z) (h2 : term443 A y z x''') (h3 : term514 A x x'' s y z x''') : False.
Proof. exact (EQ_MP (@lem3749847) (@lem3749844 A x x'' s y z x''' h1 h2 h3)). Qed.
Lemma lem3749849 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term443 A y z x''') (h2 : term514 A x x'' s y z x''') (h3 : term563 A x' x z) : False.
Proof. exact (or_elim (@lem3747869 A x' x z h3) (fun h0 : term439 A x z x' => @lem3749748 A x' x x'' s y z x''' h0 h2) (fun h0 : term554 A x z => @lem3749848 A x x'' s y z x''' h0 h1 h2)). Qed.
Lemma lem3749850 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') (h3 : term563 A x' x z) : False.
Proof. exact (or_elim (@lem3747869 A x' x z h3) (fun h0 : term439 A x z x' => @lem3749543 A x x'' s y z x''' h1 h2) (fun h0 : term554 A x z => @lem3749619 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749851 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term514 A x x'' s y z x''') (h2 : term563 A x' x z) : False.
Proof. exact (or_elim (@lem3747996 A x x'' s y z x''' h1) (fun h0 : term439 A y z x''' => @lem3749850 A x'' s y x''' x' x z h0 h1 h2) (fun h0 : term443 A y z x''' => @lem3749849 A x'' s y x''' x' x z h0 h1 h2)). Qed.
Lemma lem3749852 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') (h3 : term563 A x' x z) : False.
Proof. exact (or_elim (@lem3747869 A x' x z h3) (fun h0 : term439 A x z x' => @lem3749391 A x x'' s y z x''' h1 h2) (fun h0 : term554 A x z => @lem3749467 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749853 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term439 A y z x''') (h2 : term514 A x x'' s y z x''') (h3 : term563 A x' x z) : False.
Proof. exact (or_elim (@lem3747869 A x' x z h3) (fun h0 : term439 A x z x' => @lem3749239 A x x'' s y z x''' h1 h2) (fun h0 : term554 A x z => @lem3749315 A x x'' s y z x''' h1 h2)). Qed.
Lemma lem3749854 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term439 A x y x'') (h2 : term514 A x x'' s y z x''') (h3 : term563 A x' x z) : False.
Proof. exact (or_elim (@lem3747996 A x x'' s y z x''' h2) (fun h0 : term439 A y z x''' => @lem3749853 A x'' s y x''' x' x z h0 h2 h3) (fun h0 : term443 A y z x''' => @lem3749852 A x'' s y x''' x' x z h1 h2 h3)). Qed.
Lemma lem3749855 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term514 A x x'' s y z x''') (h2 : term563 A x' x z) : False.
Proof. exact (or_elim (@lem3748000 A x x'' s y z x''' h1) (fun h0 : term439 A x y x'' => @lem3749854 A x'' s y x''' x' x z h0 h1 h2) (fun h0 : term443 A x y x'' => @lem3749851 A x'' s y x''' x' x z h1 h2)). Qed.
Lemma lem3749856 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term514 A x x'' s y z x''') (h2 : term563 A x' x z) : (term514 A x x'' s y z x''') = False.
Proof. exact (prop_ext (fun h3 : term514 A x x'' s y z x''' => @lem3749855 A x'' s y x''' x' x z h1 h2) (fun h3 : False => @lem3747991 A x x'' s y z x''' h1)). Qed.
Lemma lem3749857 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term514 A x x'' s y z x''') (h2 : term563 A x' x z) : False.
Proof. exact (EQ_MP (@lem3749856 A x'' s y x''' x' x z h1 h2) (@lem3747991 A x x'' s y z x''' h1)). Qed.
Lemma lem3749858 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term514 A x x'' s y z x''') (h2 : term563 A x' x z) : (term563 A x' x z) = False.
Proof. exact (prop_ext (fun h3 : term563 A x' x z => @lem3749857 A x'' s y x''' x' x z h1 h2) (fun h3 : False => @lem3747869 A x' x z h2)). Qed.
Lemma lem3749859 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x''' : A) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term514 A x x'' s y z x''') (h2 : term563 A x' x z) : False.
Proof. exact (EQ_MP (@lem3749858 A x'' s y x''' x' x z h1 h2) (@lem3747869 A x' x z h2)). Qed.
Lemma lem3749860 {A : Type'} (x'' : A) (s : A -> Prop) (y : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term517 A x x'' s y z) (h2 : term563 A x' x z) : False.
Proof. exact (ex_elim (@lem3747822 A x x'' s y z h1) (fun x''' : A => fun h0 : term516 A x x'' s y z x''' => @lem3749859 A x'' s y x''' x' x z h0 h2)). Qed.
Lemma lem3749861 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term392 A x s y z) (h2 : term563 A x' x z) : False.
Proof. exact (ex_elim (@lem3747634 A x s y z h1) (fun x'' : A => fun h0 : term518 A x s y z x'' => @lem3749860 A x'' s y x' x z h0 h2)). Qed.
Lemma lem3749862 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term413 A x z) (h2 : term392 A x s y z) : False.
Proof. exact (ex_elim (@lem3747820 A x z h1) (fun x' : A => fun h0 : term565 A x z x' => @lem3749861 A s y x' x z h2 h0)). Qed.
Lemma lem3749863 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term413 A x z) (h2 : term392 A x s y z) : (term413 A x z) = False.
Proof. exact (prop_ext (fun h3 : term413 A x z => @lem3749862 A x s y z h1 h2) (fun h3 : False => @lem3747015 A x z h1)). Qed.
Lemma lem3749864 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term413 A x z) (h2 : term392 A x s y z) : False.
Proof. exact (EQ_MP (@lem3749863 A x s y z h1 h2) (@lem3747015 A x z h1)). Qed.
Lemma lem3749865 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term392 A x s y z) : term412 A x z.
Proof. exact (fun h0 : term413 A x z => @lem3749864 A x s y z h0 h1). Qed.
Lemma lem3749866 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (h1 : term392 A x s y z) : term389 A x z.
Proof. exact (EQ_MP (@lem3747014 A x z) (@lem3749865 A x s y z h1)). Qed.
Lemma lem3749867 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term394 A s y x z.
Proof. exact (fun h0 : term392 A x s y z => @lem3749866 A x s y z h0). Qed.
Lemma lem3749872 {A : Type'} (s : A -> Prop) (y : A -> Prop) (x : A -> Prop) : term396 A s y x.
Proof. exact (fun z : A -> Prop => @lem3749867 A s y x z). Qed.
Lemma lem3749877 {A : Type'} (s : A -> Prop) (x : A -> Prop) : term398 A s x.
Proof. exact (fun y : A -> Prop => @lem3749872 A s y x). Qed.
Lemma lem3749882 {A : Type'} (s : A -> Prop) : term400 A s.
Proof. exact (fun x : A -> Prop => @lem3749877 A s x). Qed.
Lemma lem3749887 {A : Type'} : term411 A.
Proof. exact (fun s : A -> Prop => @lem3749882 A s). Qed.
Lemma lem3749888 {A : Type'} : term410 A.
Proof. exact (EQ_MP (@lem3747009 A) (@lem3749887 A)). Qed.
Lemma lem3749889 {A : Type'} (s : A -> Prop) : term578 A s.
Proof. exact (@lem3749888 A s). Qed.
Lemma lem3749890 {A : Type'} (s : A -> Prop) : (term578 A s) = (term402 A s).
Proof. exact (eq_refl (term578 A s)). Qed.
Lemma lem3749891 {A : Type'} (s : A -> Prop) : term402 A s.
Proof. exact (EQ_MP (@lem3749890 A s) (@lem3749889 A s)). Qed.
Lemma lem3749893 {A : Type'} (s : A -> Prop) : term402 A s.
Proof. exact (@lem3746716 A s (@lem3749891 A s)). Qed.
Lemma lem3749894 {A : Type'} (s : A -> Prop) (h1 : term403 A s) : False.
Proof. exact (@lem3749893 A s (@lem3746700 A s h1)). Qed.
Lemma lem3749895 {A : Type'} (s : A -> Prop) (h1 : term403 A s) : (term403 A s) = False.
Proof. exact (prop_ext (fun h2 : term403 A s => @lem3749894 A s h1) (fun h2 : False => @lem3746700 A s h1)). Qed.
Lemma lem3749896 {A : Type'} (s : A -> Prop) (h1 : term403 A s) : False.
Proof. exact (EQ_MP (@lem3749895 A s h1) (@lem3746700 A s h1)). Qed.
Lemma lem3749897 {A : Type'} (s : A -> Prop) : term402 A s.
Proof. exact (fun h0 : term403 A s => @lem3749896 A s h0). Qed.
Lemma lem3749898 {A : Type'} (s : A -> Prop) : term400 A s.
Proof. exact (EQ_MP (@lem3746699 A s) (@lem3749897 A s)). Qed.
Lemma lem3749899 {A : Type'} (s : A -> Prop) : term374 A s.
Proof. exact (EQ_MP (@lem3746695 A s) (@lem3749898 A s)). Qed.
Lemma lem3749900 {A : Type'} (s : A -> Prop) : term250 A s.
Proof. exact (EQ_MP (@lem3746398 A s) (@lem3749899 A s)). Qed.
Lemma lem3749911 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : @IN (A -> Prop) s f) : term579 A s f.
Proof. exact (conj (@lem3744249 A s f h2) (@lem3744244 A f h1)). Qed.
Lemma lem3749912 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term580 A s f.
Proof. exact (conj (@lem3744332 A f s h2) (@lem3749911 A s f h1 h3)). Qed.
Lemma lem3749932 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3749933 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term345 A s t).
Proof. exact (@lem3749932 A s t). Qed.
Lemma lem3749934 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@PSUBSET A t u) = (term345 A t u).
Proof. exact (@lem3749933 A t u). Qed.
Lemma lem3749938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3749939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3749938 A s t). Qed.
Lemma lem3749940 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term343 A t u).
Proof. exact (@lem3749939 A t u). Qed.
Lemma lem3749947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3749948 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term227 A t u) = (term344 A t u).
Proof. exact (MK_COMB (@lem3749947) (@lem3749940 A t u)). Qed.
Lemma lem3749952 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3749953 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (@lem3749952 A s t). Qed.
Lemma lem3749954 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (t = u) = (term359 A t u).
Proof. exact (@lem3749953 A t u). Qed.
Lemma lem3749963 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3749964 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term360 A t u) = (term361 A t u).
Proof. exact (MK_COMB (@lem3749963) (@lem3749954 A t u)). Qed.
Lemma lem3749965 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term345 A t u) = (term362 A t u).
Proof. exact (MK_COMB (@lem3749948 A t u) (@lem3749964 A t u)). Qed.
Lemma lem3749968 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@PSUBSET A t u) = (term362 A t u).
Proof. exact (TRANS (@lem3749934 A t u) (@lem3749965 A t u)). Qed.
Lemma lem3749969 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3749970 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term581 A t u) = (term582 A t u).
Proof. exact (MK_COMB (@lem3749969) (@lem3749968 A t u)). Qed.
Lemma lem3749971 {A : Type'} (u : A -> Prop) (f : type686 A) : (term583 A u f) = (term583 A u f).
Proof. exact (eq_refl (term583 A u f)). Qed.
Lemma lem3749972 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term584 A f t u) = (term585 A f t u).
Proof. exact (MK_COMB (@lem3749971 A u f) (@lem3749970 A t u)). Qed.
Lemma lem3749975 {A : Type'} (f : type686 A) (t : A -> Prop) : (term586 A f t) = (term587 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3749972 A f t u)). Qed.
Lemma lem3749976 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3749977 {A : Type'} (f : type686 A) (t : A -> Prop) : (term64 A f t) = (term588 A f t).
Proof. exact (MK_COMB (@lem3749976 A) (@lem3749975 A f t)). Qed.
Lemma lem3749982 {A : Type'} (t : A -> Prop) (f : type686 A) : (term65 A t f) = (term65 A t f).
Proof. exact (eq_refl (term65 A t f)). Qed.
Lemma lem3749983 {A : Type'} (f : type686 A) (t : A -> Prop) : (term67 A f t) = (term589 A f t).
Proof. exact (MK_COMB (@lem3749982 A t f) (@lem3749977 A f t)). Qed.
Lemma lem3749986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3749987 {A : Type'} (f : type686 A) (t : A -> Prop) : (term125 A f t) = (term590 A f t).
Proof. exact (MK_COMB (@lem3749986) (@lem3749983 A f t)). Qed.
Lemma lem3749989 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3749990 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3749989 A s t). Qed.
Lemma lem3749997 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term139 A f s t) = (term591 A f s t).
Proof. exact (MK_COMB (@lem3749987 A f t) (@lem3749990 A s t)). Qed.
Lemma lem3750000 {A : Type'} (f : type686 A) (s : A -> Prop) : (term140 A f s) = (term592 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3749997 A f s t)). Qed.
Lemma lem3750001 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3750002 {A : Type'} (f : type686 A) (s : A -> Prop) : (term141 A f s) = (term593 A f s).
Proof. exact (MK_COMB (@lem3750001 A) (@lem3750000 A f s)). Qed.
Lemma lem3750007 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750008 {A : Type'} (f : type686 A) (s : A -> Prop) : (term143 A f s) = (term594 A f s).
Proof. exact (MK_COMB (@lem3750007) (@lem3750002 A f s)). Qed.
Lemma lem3750009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750010 {A : Type'} (f : type686 A) (s : A -> Prop) : (term595 A f s) = (term596 A f s).
Proof. exact (MK_COMB (@lem3750009) (@lem3750008 A f s)). Qed.
Lemma lem3750013 {A : Type'} (s : A -> Prop) (f : type686 A) : (term579 A s f) = (term579 A s f).
Proof. exact (eq_refl (term579 A s f)). Qed.
Lemma lem3750014 {A : Type'} (s : A -> Prop) (f : type686 A) : (term580 A s f) = (term597 A s f).
Proof. exact (MK_COMB (@lem3750010 A f s) (@lem3750013 A s f)). Qed.
Lemma lem3750017 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3750018 {A : Type'} (s : A -> Prop) (f : type686 A) : (term598 A s f) = (term599 A s f).
Proof. exact (MK_COMB (@lem3750017) (@lem3750014 A s f)). Qed.
Lemma lem3750022 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term359 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3750023 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term600 A s t).
Proof. exact (@lem3750022 (A -> Prop) s t). Qed.
Lemma lem3750024 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term12 A f s) = (@EMPTY (A -> Prop))) = (term601 A f s).
Proof. exact (@lem3750023 A (term12 A f s) (@EMPTY (A -> Prop))). Qed.
Lemma lem3750040 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3750041 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term343 A s t).
Proof. exact (@lem3750040 A s t). Qed.
Lemma lem3750048 {A : Type'} (t : A -> Prop) (f : type686 A) : (term65 A t f) = (term65 A t f).
Proof. exact (eq_refl (term65 A t f)). Qed.
Lemma lem3750049 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term168 A f s t) = (term602 A f s t).
Proof. exact (MK_COMB (@lem3750048 A t f) (@lem3750041 A s t)). Qed.
Lemma lem3750052 {A : Type'} (GEN_PVAR_103 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_103) = (@SETSPEC (A -> Prop) GEN_PVAR_103).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_103)). Qed.
Lemma lem3750053 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term170 A GEN_PVAR_103 f s t) = (term603 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3750052 A GEN_PVAR_103) (@lem3750049 A f s t)). Qed.
Lemma lem3750054 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3750055 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term172 A GEN_PVAR_103 f s t) = (term604 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3750053 A GEN_PVAR_103 f s t) (@lem3750054 A t)). Qed.
Lemma lem3750056 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term174 A GEN_PVAR_103 f s) = (term605 A GEN_PVAR_103 f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3750055 A GEN_PVAR_103 f s t)). Qed.
Lemma lem3750057 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3750058 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term176 A GEN_PVAR_103 f s) = (term606 A GEN_PVAR_103 f s).
Proof. exact (MK_COMB (@lem3750057 A) (@lem3750056 A GEN_PVAR_103 f s)). Qed.
Lemma lem3750063 {A : Type'} (f : type686 A) (s : A -> Prop) : (term178 A f s) = (term607 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_103 : A -> Prop => @lem3750058 A GEN_PVAR_103 f s)). Qed.
Lemma lem3750064 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3750065 {A : Type'} (f : type686 A) (s : A -> Prop) : (term12 A f s) = (term608 A f s).
Proof. exact (MK_COMB (@lem3750064 A) (@lem3750063 A f s)). Qed.
Lemma lem3750066 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem3750067 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term267 A x f s) = (term609 A x f s).
Proof. exact (MK_COMB (@lem3750066 A x) (@lem3750065 A f s)). Qed.
Lemma lem3750068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3750069 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term610 A x f s) = (term611 A x f s).
Proof. exact (MK_COMB (@lem3750068) (@lem3750067 A x f s)). Qed.
Lemma lem3750070 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = (@IN (A -> Prop) x (@EMPTY (A -> Prop))).
Proof. exact (eq_refl (@IN (A -> Prop) x (@EMPTY (A -> Prop)))). Qed.
Lemma lem3750071 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : ((term267 A x f s) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((term609 A x f s) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))).
Proof. exact (MK_COMB (@lem3750069 A x f s) (@lem3750070 A x)). Qed.
Lemma lem3750076 {A : Type'} (f : type686 A) (s : A -> Prop) : (term612 A f s) = (term613 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3750071 A f s x)). Qed.
Lemma lem3750077 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3750078 {A : Type'} (f : type686 A) (s : A -> Prop) : (term601 A f s) = (term614 A f s).
Proof. exact (MK_COMB (@lem3750077 A) (@lem3750076 A f s)). Qed.
Lemma lem3750083 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term12 A f s) = (@EMPTY (A -> Prop))) = (term614 A f s).
Proof. exact (TRANS (@lem3750024 A f s) (@lem3750078 A f s)). Qed.
Lemma lem3750084 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750085 {A : Type'} (f : type686 A) (s : A -> Prop) : (term341 A f s) = (term615 A f s).
Proof. exact (MK_COMB (@lem3750084) (@lem3750083 A f s)). Qed.
Lemma lem3750086 {A : Type'} (f : type686 A) (s : A -> Prop) : (term616 A f s) = (term617 A f s).
Proof. exact (MK_COMB (@lem3750018 A s f) (@lem3750085 A f s)). Qed.
Lemma lem3750089 {A : Type'} (f : type686 A) (s : A -> Prop) : (term617 A f s) = (term616 A f s).
Proof. exact (SYM (@lem3750086 A f s)). Qed.
Lemma lem3750103 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750104 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3750103 (A -> Prop) P x). Qed.
Lemma lem3750105 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3750104 A f t). Qed.
Lemma lem3750106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750107 {A : Type'} (f : type686 A) (t : A -> Prop) : (term65 A t f) = (term618 A f t).
Proof. exact (MK_COMB (@lem3750106) (@lem3750105 A f t)). Qed.
Lemma lem3750115 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750116 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3750115 (A -> Prop) P x). Qed.
Lemma lem3750117 {A : Type'} (f : type686 A) (u : A -> Prop) : (@IN (A -> Prop) u f) = (f u).
Proof. exact (@lem3750116 A f u). Qed.
Lemma lem3750118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3750119 {A : Type'} (f : type686 A) (u : A -> Prop) : (term583 A u f) = (term619 A f u).
Proof. exact (MK_COMB (@lem3750118) (@lem3750117 A f u)). Qed.
Lemma lem3750129 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750130 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3750129 A P x). Qed.
Lemma lem3750131 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3750130 A t x). Qed.
Lemma lem3750132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3750133 {A : Type'} (t : A -> Prop) (x : A) : (term375 A x t) = (term376 A t x).
Proof. exact (MK_COMB (@lem3750132) (@lem3750131 A t x)). Qed.
Lemma lem3750135 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750136 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3750135 A P x). Qed.
Lemma lem3750137 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3750136 A u x). Qed.
Lemma lem3750138 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term377 A t x u) = (term378 A t u x).
Proof. exact (MK_COMB (@lem3750133 A t x) (@lem3750137 A u x)). Qed.
Lemma lem3750141 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term379 A t u) = (term380 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750138 A t u x)). Qed.
Lemma lem3750142 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750143 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term343 A t u) = (term381 A t u).
Proof. exact (MK_COMB (@lem3750142 A) (@lem3750141 A t u)). Qed.
Lemma lem3750148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750149 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term344 A t u) = (term382 A t u).
Proof. exact (MK_COMB (@lem3750148) (@lem3750143 A t u)). Qed.
Lemma lem3750157 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750158 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3750157 A P x). Qed.
Lemma lem3750159 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3750158 A t x). Qed.
Lemma lem3750160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3750161 {A : Type'} (t : A -> Prop) (x : A) : (term383 A x t) = (term384 A t x).
Proof. exact (MK_COMB (@lem3750160) (@lem3750159 A t x)). Qed.
Lemma lem3750163 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750164 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3750163 A P x). Qed.
Lemma lem3750165 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3750164 A u x). Qed.
Lemma lem3750166 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((@IN A x t) = (@IN A x u)) = ((t x) = (u x)).
Proof. exact (MK_COMB (@lem3750161 A t x) (@lem3750165 A u x)). Qed.
Lemma lem3750169 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term385 A t u) = (term386 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750166 A t u x)). Qed.
Lemma lem3750170 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750171 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term359 A t u) = (term387 A t u).
Proof. exact (MK_COMB (@lem3750170 A) (@lem3750169 A t u)). Qed.
Lemma lem3750176 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750177 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term361 A t u) = (term388 A t u).
Proof. exact (MK_COMB (@lem3750176) (@lem3750171 A t u)). Qed.
Lemma lem3750178 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term362 A t u) = (term389 A t u).
Proof. exact (MK_COMB (@lem3750149 A t u) (@lem3750177 A t u)). Qed.
Lemma lem3750181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750182 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term582 A t u) = (term413 A t u).
Proof. exact (MK_COMB (@lem3750181) (@lem3750178 A t u)). Qed.
Lemma lem3750183 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term585 A f t u) = (term620 A f t u).
Proof. exact (MK_COMB (@lem3750119 A f u) (@lem3750182 A t u)). Qed.
Lemma lem3750186 {A : Type'} (f : type686 A) (t : A -> Prop) : (term587 A f t) = (term621 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3750183 A f t u)). Qed.
Lemma lem3750187 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3750188 {A : Type'} (f : type686 A) (t : A -> Prop) : (term588 A f t) = (term622 A f t).
Proof. exact (MK_COMB (@lem3750187 A) (@lem3750186 A f t)). Qed.
Lemma lem3750193 {A : Type'} (f : type686 A) (t : A -> Prop) : (term589 A f t) = (term623 A f t).
Proof. exact (MK_COMB (@lem3750107 A f t) (@lem3750188 A f t)). Qed.
Lemma lem3750196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750197 {A : Type'} (f : type686 A) (t : A -> Prop) : (term590 A f t) = (term624 A f t).
Proof. exact (MK_COMB (@lem3750196) (@lem3750193 A f t)). Qed.
Lemma lem3750205 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750206 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3750205 A P x). Qed.
Lemma lem3750207 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3750206 A s x). Qed.
Lemma lem3750208 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3750209 {A : Type'} (s : A -> Prop) (x : A) : (term375 A x s) = (term376 A s x).
Proof. exact (MK_COMB (@lem3750208) (@lem3750207 A s x)). Qed.
Lemma lem3750211 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750212 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3750211 A P x). Qed.
Lemma lem3750213 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3750212 A t x). Qed.
Lemma lem3750214 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term377 A s x t) = (term378 A s t x).
Proof. exact (MK_COMB (@lem3750209 A s x) (@lem3750213 A t x)). Qed.
Lemma lem3750217 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term379 A s t) = (term380 A s t).
Proof. exact (fun_ext (fun x : A => @lem3750214 A s t x)). Qed.
Lemma lem3750218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750219 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term343 A s t) = (term381 A s t).
Proof. exact (MK_COMB (@lem3750218 A) (@lem3750217 A s t)). Qed.
Lemma lem3750224 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term591 A f s t) = (term625 A f s t).
Proof. exact (MK_COMB (@lem3750197 A f t) (@lem3750219 A s t)). Qed.
Lemma lem3750227 {A : Type'} (f : type686 A) (s : A -> Prop) : (term592 A f s) = (term626 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3750224 A f s t)). Qed.
Lemma lem3750228 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3750229 {A : Type'} (f : type686 A) (s : A -> Prop) : (term593 A f s) = (term627 A f s).
Proof. exact (MK_COMB (@lem3750228 A) (@lem3750227 A f s)). Qed.
Lemma lem3750234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750235 {A : Type'} (f : type686 A) (s : A -> Prop) : (term594 A f s) = (term628 A f s).
Proof. exact (MK_COMB (@lem3750234) (@lem3750229 A f s)). Qed.
Lemma lem3750236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750237 {A : Type'} (f : type686 A) (s : A -> Prop) : (term596 A f s) = (term629 A f s).
Proof. exact (MK_COMB (@lem3750236) (@lem3750235 A f s)). Qed.
Lemma lem3750241 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750242 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3750241 (A -> Prop) P x). Qed.
Lemma lem3750243 {A : Type'} (f : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s f) = (f s).
Proof. exact (@lem3750242 A f s). Qed.
Lemma lem3750244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750245 {A : Type'} (f : type686 A) (s : A -> Prop) : (term65 A s f) = (term618 A f s).
Proof. exact (MK_COMB (@lem3750244) (@lem3750243 A f s)). Qed.
Lemma lem3750246 {A : Type'} (f : type686 A) : (@FINITE (A -> Prop) f) = (@FINITE (A -> Prop) f).
Proof. exact (eq_refl (@FINITE (A -> Prop) f)). Qed.
Lemma lem3750247 {A : Type'} (s : A -> Prop) (f : type686 A) : (term579 A s f) = (term630 A s f).
Proof. exact (MK_COMB (@lem3750245 A f s) (@lem3750246 A f)). Qed.
Lemma lem3750250 {A : Type'} (s : A -> Prop) (f : type686 A) : (term597 A s f) = (term631 A s f).
Proof. exact (MK_COMB (@lem3750237 A f s) (@lem3750247 A s f)). Qed.
Lemma lem3750253 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3750254 {A : Type'} (s : A -> Prop) (f : type686 A) : (term599 A s f) = (term632 A s f).
Proof. exact (MK_COMB (@lem3750253) (@lem3750250 A s f)). Qed.
Lemma lem3750262 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term633 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3750263 {A : Type'} (p : type686 A) (x : A -> Prop) : (term634 A x p) = (p x).
Proof. exact (@lem3750262 (A -> Prop) p x). Qed.
Lemma lem3750264 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term635 A x f s) = (term636 A f s x).
Proof. exact (@lem3750263 A (term637 A f s) x). Qed.
Lemma lem3750265 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term636 A f s t) = (term602 A f s t).
Proof. exact (eq_refl (term636 A f s t)). Qed.
Lemma lem3750266 {A : Type'} (GEN_PVAR_103 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_103) = (@SETSPEC (A -> Prop) GEN_PVAR_103).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_103)). Qed.
Lemma lem3750267 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term638 A GEN_PVAR_103 f s t) = (term603 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3750266 A GEN_PVAR_103) (@lem3750265 A f s t)). Qed.
Lemma lem3750268 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3750269 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term639 A GEN_PVAR_103 f s t) = (term604 A GEN_PVAR_103 f s t).
Proof. exact (MK_COMB (@lem3750267 A GEN_PVAR_103 f s t) (@lem3750268 A t)). Qed.
Lemma lem3750270 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term640 A GEN_PVAR_103 f s) = (term605 A GEN_PVAR_103 f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3750269 A GEN_PVAR_103 f s t)). Qed.
Lemma lem3750271 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3750272 {A : Type'} (GEN_PVAR_103 : A -> Prop) (f : type686 A) (s : A -> Prop) : (term641 A GEN_PVAR_103 f s) = (term606 A GEN_PVAR_103 f s).
Proof. exact (MK_COMB (@lem3750271 A) (@lem3750270 A GEN_PVAR_103 f s)). Qed.
Lemma lem3750273 {A : Type'} (f : type686 A) (s : A -> Prop) : (term642 A f s) = (term607 A f s).
Proof. exact (fun_ext (fun GEN_PVAR_103 : A -> Prop => @lem3750272 A GEN_PVAR_103 f s)). Qed.
Lemma lem3750274 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3750275 {A : Type'} (f : type686 A) (s : A -> Prop) : (term643 A f s) = (term608 A f s).
Proof. exact (MK_COMB (@lem3750274 A) (@lem3750273 A f s)). Qed.
Lemma lem3750276 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem3750277 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term635 A x f s) = (term609 A x f s).
Proof. exact (MK_COMB (@lem3750276 A x) (@lem3750275 A f s)). Qed.
Lemma lem3750278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3750279 {A : Type'} (x : A -> Prop) (f : type686 A) (s : A -> Prop) : (term644 A x f s) = (term611 A x f s).
Proof. exact (MK_COMB (@lem3750278) (@lem3750277 A x f s)). Qed.
Lemma lem3750280 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term636 A f s x) = (term602 A f s x).
Proof. exact (eq_refl (term636 A f s x)). Qed.
Lemma lem3750281 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : ((term635 A x f s) = (term636 A f s x)) = ((term609 A x f s) = (term602 A f s x)).
Proof. exact (MK_COMB (@lem3750279 A x f s) (@lem3750280 A f s x)). Qed.
Lemma lem3750282 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term609 A x f s) = (term602 A f s x).
Proof. exact (EQ_MP (@lem3750281 A f s x) (@lem3750264 A f s x)). Qed.
Lemma lem3750286 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750287 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3750286 (A -> Prop) P x). Qed.
Lemma lem3750288 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3750287 A f x). Qed.
Lemma lem3750289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750290 {A : Type'} (f : type686 A) (x : A -> Prop) : (term65 A x f) = (term618 A f x).
Proof. exact (MK_COMB (@lem3750289) (@lem3750288 A f x)). Qed.
Lemma lem3750298 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750299 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3750298 A P x). Qed.
Lemma lem3750300 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3750299 A s x). Qed.
Lemma lem3750301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3750302 {A : Type'} (s : A -> Prop) (x : A) : (term375 A x s) = (term376 A s x).
Proof. exact (MK_COMB (@lem3750301) (@lem3750300 A s x)). Qed.
Lemma lem3750304 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3750305 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3750304 A P x). Qed.
Lemma lem3750306 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem3750305 A x x'). Qed.
Lemma lem3750307 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term377 A s x' x) = (term378 A s x x').
Proof. exact (MK_COMB (@lem3750302 A s x') (@lem3750306 A x x')). Qed.
Lemma lem3750310 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term379 A s x) = (term380 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3750307 A s x x')). Qed.
Lemma lem3750311 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750312 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term343 A s x) = (term381 A s x).
Proof. exact (MK_COMB (@lem3750311 A) (@lem3750310 A s x)). Qed.
Lemma lem3750317 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term602 A f s x) = (term645 A f s x).
Proof. exact (MK_COMB (@lem3750290 A f x) (@lem3750312 A s x)). Qed.
Lemma lem3750320 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term609 A x f s) = (term645 A f s x).
Proof. exact (TRANS (@lem3750282 A f s x) (@lem3750317 A f s x)). Qed.
Lemma lem3750321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3750322 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term611 A x f s) = (term646 A f s x).
Proof. exact (MK_COMB (@lem3750321) (@lem3750320 A f s x)). Qed.
Lemma lem3750324 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3750325 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3750324 (A -> Prop) x). Qed.
Lemma lem3750326 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : ((term609 A x f s) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((term645 A f s x) = False).
Proof. exact (MK_COMB (@lem3750322 A f s x) (@lem3750325 A x)). Qed.
Lemma lem3750328 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3750329 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : ((term645 A f s x) = False) = (term647 A f s x).
Proof. exact (@lem3750328 (term645 A f s x)). Qed.
Lemma lem3750338 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : ((term609 A x f s) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term647 A f s x).
Proof. exact (TRANS (@lem3750326 A f s x) (@lem3750329 A f s x)). Qed.
Lemma lem3750339 {A : Type'} (f : type686 A) (s : A -> Prop) : (term613 A f s) = (term648 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3750338 A f s x)). Qed.
Lemma lem3750340 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3750341 {A : Type'} (f : type686 A) (s : A -> Prop) : (term614 A f s) = (term649 A f s).
Proof. exact (MK_COMB (@lem3750340 A) (@lem3750339 A f s)). Qed.
Lemma lem3750346 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750347 {A : Type'} (f : type686 A) (s : A -> Prop) : (term615 A f s) = (term650 A f s).
Proof. exact (MK_COMB (@lem3750346) (@lem3750341 A f s)). Qed.
Lemma lem3750348 {A : Type'} (f : type686 A) (s : A -> Prop) : (term617 A f s) = (term651 A f s).
Proof. exact (MK_COMB (@lem3750254 A s f) (@lem3750347 A f s)). Qed.
Lemma lem3750351 {A : Type'} (f : type686 A) (s : A -> Prop) : (term651 A f s) = (term617 A f s).
Proof. exact (SYM (@lem3750348 A f s)). Qed.
Lemma lem3750353 (p : Prop) : p = (term401 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3750354 {A : Type'} (f : type686 A) (s : A -> Prop) : (term651 A f s) = (term652 A f s).
Proof. exact (@lem3750353 (term651 A f s)). Qed.
Lemma lem3750355 {A : Type'} (f : type686 A) (s : A -> Prop) : (term652 A f s) = (term651 A f s).
Proof. exact (SYM (@lem3750354 A f s)). Qed.
Lemma lem3750356 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term653 A f s) : term653 A f s.
Proof. exact (h1). Qed.
Lemma lem3750359 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term652 A f s) : term652 A f s.
Proof. exact (h1). Qed.
Lemma lem3750360 {A : Type'} (f : type686 A) (s : A -> Prop) : term654 A f s.
Proof. exact (fun h0 : term652 A f s => @lem3750359 A f s h0). Qed.
Lemma lem3750361 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term654 A f s) : term654 A f s.
Proof. exact (h1). Qed.
Lemma lem3750362 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term652 A f s) : term652 A f s.
Proof. exact (h1). Qed.
Lemma lem3750363 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term652 A f s) (h2 : term654 A f s) : term652 A f s.
Proof. exact (@lem3750361 A f s h2 (@lem3750362 A f s h1)). Qed.
Lemma lem3750364 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term652 A f s) : term655 A f s.
Proof. exact (fun h0 : term654 A f s => @lem3750363 A f s h1 h0). Qed.
Lemma lem3750365 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term654 A f s) : term654 A f s.
Proof. exact (h1). Qed.
Lemma lem3750366 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term652 A f s) (h2 : term654 A f s) : term652 A f s.
Proof. exact (@lem3750364 A f s h1 (@lem3750365 A f s h2)). Qed.
Lemma lem3750367 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term654 A f s) : term654 A f s.
Proof. exact (fun h0 : term652 A f s => @lem3750366 A f s h0 h1). Qed.
Lemma lem3750368 {A : Type'} (f : type686 A) (s : A -> Prop) : term656 A f s.
Proof. exact (fun h0 : term654 A f s => @lem3750367 A f s h0). Qed.
Lemma lem3750371 {A : Type'} (f : type686 A) (s : A -> Prop) : term654 A f s.
Proof. exact (@lem3750368 A f s (@lem3750360 A f s)). Qed.
Lemma lem3750372 {A : Type'} (f : type686 A) (s : A -> Prop) : term654 A f s.
Proof. exact (@lem3750371 A f s). Qed.
Lemma lem3750382 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3750383 {A : Type'} (f : type686 A) (s : A -> Prop) : (term652 A f s) = (term657 A f s).
Proof. exact (@lem3750382 (term653 A f s)). Qed.
Lemma lem3750385 (t : Prop) : (term14 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3750386 {A : Type'} (f : type686 A) (s : A -> Prop) : (term657 A f s) = (term651 A f s).
Proof. exact (@lem3750385 (term651 A f s)). Qed.
Lemma lem3750389 {A : Type'} (f : type686 A) (s : A -> Prop) : (term652 A f s) = (term651 A f s).
Proof. exact (TRANS (@lem3750383 A f s) (@lem3750386 A f s)). Qed.
Lemma lem3750482 {A : Type'} (s : A -> Prop) : (term658 A s) = (term659 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3750389 A f s)). Qed.
Lemma lem3750483 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3750484 {A : Type'} (s : A -> Prop) : (term660 A s) = (term661 A s).
Proof. exact (MK_COMB (@lem3750483 A) (@lem3750482 A s)). Qed.
Lemma lem3750489 {A : Type'} : (term662 A) = (term663 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3750484 A s)). Qed.
Lemma lem3750490 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3750499 {A : Type'} : (term664 A) = (term665 A).
Proof. exact (MK_COMB (@lem3750490 A) (@lem3750489 A)). Qed.
Lemma lem3750504 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term378 A s x x') = (term378 A s x x').
Proof. exact (eq_refl (term378 A s x x')). Qed.
Lemma lem3750505 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term380 A s x) = (term380 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3750504 A s x x')). Qed.
Lemma lem3750506 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750507 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term381 A s x) = (term381 A s x).
Proof. exact (MK_COMB (@lem3750506 A) (@lem3750505 A s x)). Qed.
Lemma lem3750510 {A : Type'} (f : type686 A) (x : A -> Prop) : (term618 A f x) = (term618 A f x).
Proof. exact (eq_refl (term618 A f x)). Qed.
Lemma lem3750511 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term645 A f s x) = (term645 A f s x).
Proof. exact (MK_COMB (@lem3750510 A f x) (@lem3750507 A s x)). Qed.
Lemma lem3750512 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750513 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term647 A f s x) = (term647 A f s x).
Proof. exact (MK_COMB (@lem3750512) (@lem3750511 A f s x)). Qed.
Lemma lem3750514 {A : Type'} (f : type686 A) (s : A -> Prop) : (term648 A f s) = (term648 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3750513 A f s x)). Qed.
Lemma lem3750515 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3750516 {A : Type'} (f : type686 A) (s : A -> Prop) : (term649 A f s) = (term649 A f s).
Proof. exact (MK_COMB (@lem3750515 A) (@lem3750514 A f s)). Qed.
Lemma lem3750517 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750518 {A : Type'} (f : type686 A) (s : A -> Prop) : (term650 A f s) = (term650 A f s).
Proof. exact (MK_COMB (@lem3750517) (@lem3750516 A f s)). Qed.
Lemma lem3750523 {A : Type'} (s : A -> Prop) (f : type686 A) : (term630 A s f) = (term630 A s f).
Proof. exact (eq_refl (term630 A s f)). Qed.
Lemma lem3750528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term378 A s t x) = (term378 A s t x).
Proof. exact (eq_refl (term378 A s t x)). Qed.
Lemma lem3750529 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term380 A s t) = (term380 A s t).
Proof. exact (fun_ext (fun x : A => @lem3750528 A s t x)). Qed.
Lemma lem3750530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750531 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term381 A s t) = (term381 A s t).
Proof. exact (MK_COMB (@lem3750530 A) (@lem3750529 A s t)). Qed.
Lemma lem3750536 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((t x) = (u x)) = ((t x) = (u x)).
Proof. exact (eq_refl ((t x) = (u x))). Qed.
Lemma lem3750537 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term386 A t u) = (term386 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750536 A t u x)). Qed.
Lemma lem3750538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750539 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term387 A t u) = (term387 A t u).
Proof. exact (MK_COMB (@lem3750538 A) (@lem3750537 A t u)). Qed.
Lemma lem3750540 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750541 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term388 A t u) = (term388 A t u).
Proof. exact (MK_COMB (@lem3750540) (@lem3750539 A t u)). Qed.
Lemma lem3750546 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term378 A t u x) = (term378 A t u x).
Proof. exact (eq_refl (term378 A t u x)). Qed.
Lemma lem3750547 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term380 A t u) = (term380 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750546 A t u x)). Qed.
Lemma lem3750548 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750549 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term381 A t u) = (term381 A t u).
Proof. exact (MK_COMB (@lem3750548 A) (@lem3750547 A t u)). Qed.
Lemma lem3750550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750551 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term382 A t u) = (term382 A t u).
Proof. exact (MK_COMB (@lem3750550) (@lem3750549 A t u)). Qed.
Lemma lem3750552 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term389 A t u) = (term389 A t u).
Proof. exact (MK_COMB (@lem3750551 A t u) (@lem3750541 A t u)). Qed.
Lemma lem3750553 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750554 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term413 A t u) = (term413 A t u).
Proof. exact (MK_COMB (@lem3750553) (@lem3750552 A t u)). Qed.
Lemma lem3750557 {A : Type'} (f : type686 A) (u : A -> Prop) : (term619 A f u) = (term619 A f u).
Proof. exact (eq_refl (term619 A f u)). Qed.
Lemma lem3750558 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term620 A f t u) = (term620 A f t u).
Proof. exact (MK_COMB (@lem3750557 A f u) (@lem3750554 A t u)). Qed.
Lemma lem3750559 {A : Type'} (f : type686 A) (t : A -> Prop) : (term621 A f t) = (term621 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3750558 A f t u)). Qed.
Lemma lem3750560 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3750561 {A : Type'} (f : type686 A) (t : A -> Prop) : (term622 A f t) = (term622 A f t).
Proof. exact (MK_COMB (@lem3750560 A) (@lem3750559 A f t)). Qed.
Lemma lem3750564 {A : Type'} (f : type686 A) (t : A -> Prop) : (term618 A f t) = (term618 A f t).
Proof. exact (eq_refl (term618 A f t)). Qed.
Lemma lem3750565 {A : Type'} (f : type686 A) (t : A -> Prop) : (term623 A f t) = (term623 A f t).
Proof. exact (MK_COMB (@lem3750564 A f t) (@lem3750561 A f t)). Qed.
Lemma lem3750566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750567 {A : Type'} (f : type686 A) (t : A -> Prop) : (term624 A f t) = (term624 A f t).
Proof. exact (MK_COMB (@lem3750566) (@lem3750565 A f t)). Qed.
Lemma lem3750568 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term625 A f s t) = (term625 A f s t).
Proof. exact (MK_COMB (@lem3750567 A f t) (@lem3750531 A s t)). Qed.
Lemma lem3750569 {A : Type'} (f : type686 A) (s : A -> Prop) : (term626 A f s) = (term626 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3750568 A f s t)). Qed.
Lemma lem3750570 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3750571 {A : Type'} (f : type686 A) (s : A -> Prop) : (term627 A f s) = (term627 A f s).
Proof. exact (MK_COMB (@lem3750570 A) (@lem3750569 A f s)). Qed.
Lemma lem3750572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750573 {A : Type'} (f : type686 A) (s : A -> Prop) : (term628 A f s) = (term628 A f s).
Proof. exact (MK_COMB (@lem3750572) (@lem3750571 A f s)). Qed.
Lemma lem3750574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750575 {A : Type'} (f : type686 A) (s : A -> Prop) : (term629 A f s) = (term629 A f s).
Proof. exact (MK_COMB (@lem3750574) (@lem3750573 A f s)). Qed.
Lemma lem3750576 {A : Type'} (s : A -> Prop) (f : type686 A) : (term631 A s f) = (term631 A s f).
Proof. exact (MK_COMB (@lem3750575 A f s) (@lem3750523 A s f)). Qed.
Lemma lem3750577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3750578 {A : Type'} (s : A -> Prop) (f : type686 A) : (term632 A s f) = (term632 A s f).
Proof. exact (MK_COMB (@lem3750577) (@lem3750576 A s f)). Qed.
Lemma lem3750579 {A : Type'} (f : type686 A) (s : A -> Prop) : (term651 A f s) = (term651 A f s).
Proof. exact (MK_COMB (@lem3750578 A s f) (@lem3750518 A f s)). Qed.
Lemma lem3750580 {A : Type'} (s : A -> Prop) : (term659 A s) = (term659 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3750579 A f s)). Qed.
Lemma lem3750581 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3750582 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (MK_COMB (@lem3750581 A) (@lem3750580 A s)). Qed.
Lemma lem3750583 {A : Type'} : (term663 A) = (term663 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3750582 A s)). Qed.
Lemma lem3750584 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3750585 {A : Type'} : (term665 A) = (term665 A).
Proof. exact (MK_COMB (@lem3750584 A) (@lem3750583 A)). Qed.
Lemma lem3750664 {A : Type'} : (term664 A) = (term665 A).
Proof. exact (TRANS (@lem3750499 A) (@lem3750585 A)). Qed.
Lemma lem3750665 {A : Type'} : (term665 A) = (term664 A).
Proof. exact (SYM (@lem3750664 A)). Qed.
Lemma lem3750666 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term631 A s f) : term631 A s f.
Proof. exact (h1). Qed.
Lemma lem3750667 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term649 A f s) : term649 A f s.
Proof. exact (h1). Qed.
Lemma lem3750676 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term378 A t u x) = (term414 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3750677 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term380 A t u) = (term415 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750676 A t u x)). Qed.
Lemma lem3750678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3750679 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term381 A t u) = (term416 A t u).
Proof. exact (MK_COMB (@lem3750678 A) (@lem3750677 A t u)). Qed.
Lemma lem3750694 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term417 A t u x) = (term666 A t u x).
Proof. exact (@lem17930 (t x) (u x)). Qed.
Lemma lem3750695 {A : Type'} (P : A -> Prop) : (term419 A P) = (term420 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3750696 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term388 A t u) = (term421 A t u).
Proof. exact (@lem3750695 A (term386 A t u)). Qed.
Lemma lem3750697 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term422 A t u x) = ((t x) = (u x)).
Proof. exact (eq_refl (term422 A t u x)). Qed.
Lemma lem3750698 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750699 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term423 A t u x) = (term417 A t u x).
Proof. exact (MK_COMB (@lem3750698) (@lem3750697 A t u x)). Qed.
Lemma lem3750700 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term423 A t u x) = (term666 A t u x).
Proof. exact (TRANS (@lem3750699 A t u x) (@lem3750694 A t u x)). Qed.
Lemma lem3750701 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term424 A t u) = (term667 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750700 A t u x)). Qed.
Lemma lem3750702 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3750703 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term421 A t u) = (term668 A t u).
Proof. exact (MK_COMB (@lem3750702 A) (@lem3750701 A t u)). Qed.
Lemma lem3750704 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term388 A t u) = (term668 A t u).
Proof. exact (TRANS (@lem3750696 A t u) (@lem3750703 A t u)). Qed.
Lemma lem3750705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750706 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term382 A t u) = (term427 A t u).
Proof. exact (MK_COMB (@lem3750705) (@lem3750679 A t u)). Qed.
Lemma lem3750707 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term389 A t u) = (term669 A t u).
Proof. exact (MK_COMB (@lem3750706 A t u) (@lem3750704 A t u)). Qed.
Lemma lem3750708 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term670 A t u) = (term389 A t u).
Proof. exact (@lem16933 (term389 A t u)). Qed.
Lemma lem3750709 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term670 A t u) = (term669 A t u).
Proof. exact (TRANS (@lem3750708 A t u) (@lem3750707 A t u)). Qed.
Lemma lem3750711 {A : Type'} (f : type686 A) (u : A -> Prop) : (term618 A f u) = (term618 A f u).
Proof. exact (eq_refl (term618 A f u)). Qed.
Lemma lem3750712 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term671 A f t u) = (term672 A f t u).
Proof. exact (MK_COMB (@lem3750711 A f u) (@lem3750709 A t u)). Qed.
Lemma lem3750713 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term673 A f t u) = (term671 A f t u).
Proof. exact (@lem17362 (f u) (term413 A t u)). Qed.
Lemma lem3750714 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term673 A f t u) = (term672 A f t u).
Proof. exact (TRANS (@lem3750713 A f t u) (@lem3750712 A f t u)). Qed.
Lemma lem3750715 {A : Type'} (P : type686 A) : (term674 A P) = (term675 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3750716 {A : Type'} (f : type686 A) (t : A -> Prop) : (term676 A f t) = (term677 A f t).
Proof. exact (@lem3750715 A (term621 A f t)). Qed.
Lemma lem3750717 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term678 A f t u) = (term620 A f t u).
Proof. exact (eq_refl (term678 A f t u)). Qed.
Lemma lem3750718 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750719 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term679 A f t u) = (term673 A f t u).
Proof. exact (MK_COMB (@lem3750718) (@lem3750717 A f t u)). Qed.
Lemma lem3750720 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term679 A f t u) = (term672 A f t u).
Proof. exact (TRANS (@lem3750719 A f t u) (@lem3750714 A f t u)). Qed.
Lemma lem3750721 {A : Type'} (f : type686 A) (t : A -> Prop) : (term680 A f t) = (term681 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3750720 A f t u)). Qed.
Lemma lem3750722 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3750723 {A : Type'} (f : type686 A) (t : A -> Prop) : (term677 A f t) = (term682 A f t).
Proof. exact (MK_COMB (@lem3750722 A) (@lem3750721 A f t)). Qed.
Lemma lem3750724 {A : Type'} (f : type686 A) (t : A -> Prop) : (term676 A f t) = (term682 A f t).
Proof. exact (TRANS (@lem3750716 A f t) (@lem3750723 A f t)). Qed.
Lemma lem3750726 {A : Type'} (f : type686 A) (t : A -> Prop) : (term683 A f t) = (term683 A f t).
Proof. exact (eq_refl (term683 A f t)). Qed.
Lemma lem3750727 {A : Type'} (f : type686 A) (t : A -> Prop) : (term684 A f t) = (term685 A f t).
Proof. exact (MK_COMB (@lem3750726 A f t) (@lem3750724 A f t)). Qed.
Lemma lem3750728 {A : Type'} (f : type686 A) (t : A -> Prop) : (term686 A f t) = (term684 A f t).
Proof. exact (@lem17045 (f t) (term622 A f t)). Qed.
Lemma lem3750729 {A : Type'} (f : type686 A) (t : A -> Prop) : (term686 A f t) = (term685 A f t).
Proof. exact (TRANS (@lem3750728 A f t) (@lem3750727 A f t)). Qed.
Lemma lem3750736 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term520 A s t x) = (term439 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3750737 {A : Type'} (P : A -> Prop) : (term419 A P) = (term420 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3750738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term521 A s t) = (term522 A s t).
Proof. exact (@lem3750737 A (term380 A s t)). Qed.
Lemma lem3750739 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term523 A s t x) = (term378 A s t x).
Proof. exact (eq_refl (term523 A s t x)). Qed.
Lemma lem3750740 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750741 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term524 A s t x) = (term520 A s t x).
Proof. exact (MK_COMB (@lem3750740) (@lem3750739 A s t x)). Qed.
Lemma lem3750742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term524 A s t x) = (term439 A s t x).
Proof. exact (TRANS (@lem3750741 A s t x) (@lem3750736 A s t x)). Qed.
Lemma lem3750743 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term525 A s t) = (term436 A s t).
Proof. exact (fun_ext (fun x : A => @lem3750742 A s t x)). Qed.
Lemma lem3750744 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3750745 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term522 A s t) = (term450 A s t).
Proof. exact (MK_COMB (@lem3750744 A) (@lem3750743 A s t)). Qed.
Lemma lem3750746 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term521 A s t) = (term450 A s t).
Proof. exact (TRANS (@lem3750738 A s t) (@lem3750745 A s t)). Qed.
Lemma lem3750747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3750748 {A : Type'} (f : type686 A) (t : A -> Prop) : (term687 A f t) = (term688 A f t).
Proof. exact (MK_COMB (@lem3750747) (@lem3750729 A f t)). Qed.
Lemma lem3750749 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term689 A f s t) = (term690 A f s t).
Proof. exact (MK_COMB (@lem3750748 A f t) (@lem3750746 A s t)). Qed.
Lemma lem3750750 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term691 A f s t) = (term689 A f s t).
Proof. exact (@lem17045 (term623 A f t) (term381 A s t)). Qed.
Lemma lem3750751 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term691 A f s t) = (term690 A f s t).
Proof. exact (TRANS (@lem3750750 A f s t) (@lem3750749 A f s t)). Qed.
Lemma lem3750752 {A : Type'} (P : type686 A) : (term692 A P) = (term693 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3750753 {A : Type'} (f : type686 A) (s : A -> Prop) : (term628 A f s) = (term694 A f s).
Proof. exact (@lem3750752 A (term626 A f s)). Qed.
Lemma lem3750754 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term695 A f s t) = (term625 A f s t).
Proof. exact (eq_refl (term695 A f s t)). Qed.
Lemma lem3750755 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3750756 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term696 A f s t) = (term691 A f s t).
Proof. exact (MK_COMB (@lem3750755) (@lem3750754 A f s t)). Qed.
Lemma lem3750757 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term696 A f s t) = (term690 A f s t).
Proof. exact (TRANS (@lem3750756 A f s t) (@lem3750751 A f s t)). Qed.
Lemma lem3750758 {A : Type'} (f : type686 A) (s : A -> Prop) : (term697 A f s) = (term698 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3750757 A f s t)). Qed.
Lemma lem3750759 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3750760 {A : Type'} (f : type686 A) (s : A -> Prop) : (term694 A f s) = (term699 A f s).
Proof. exact (MK_COMB (@lem3750759 A) (@lem3750758 A f s)). Qed.
Lemma lem3750761 {A : Type'} (f : type686 A) (s : A -> Prop) : (term628 A f s) = (term699 A f s).
Proof. exact (TRANS (@lem3750753 A f s) (@lem3750760 A f s)). Qed.
Lemma lem3750766 {A : Type'} (s : A -> Prop) (f : type686 A) : (term630 A s f) = (term630 A s f).
Proof. exact (eq_refl (term630 A s f)). Qed.
Lemma lem3750767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3750768 {A : Type'} (f : type686 A) (s : A -> Prop) : (term629 A f s) = (term700 A f s).
Proof. exact (MK_COMB (@lem3750767) (@lem3750761 A f s)). Qed.
Lemma lem3750769 {A : Type'} (s : A -> Prop) (f : type686 A) : (term631 A s f) = (term701 A s f).
Proof. exact (MK_COMB (@lem3750768 A f s) (@lem3750766 A s f)). Qed.
Lemma lem3750956 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3750957 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (@lem3750956 A P Q). Qed.
Lemma lem3750958 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term702 A t u) = (term703 A t u).
Proof. exact (@lem3750957 A (term416 A t u) (term667 A t u)). Qed.
Lemma lem3750959 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term704 A t u x) = (term666 A t u x).
Proof. exact (eq_refl (term704 A t u x)). Qed.
Lemma lem3750960 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term705 A t u) = (term667 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750959 A t u x)). Qed.
Lemma lem3750961 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3750962 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term706 A t u) = (term668 A t u).
Proof. exact (MK_COMB (@lem3750961 A) (@lem3750960 A t u)). Qed.
Lemma lem3750963 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term427 A t u) = (term427 A t u).
Proof. exact (eq_refl (term427 A t u)). Qed.
Lemma lem3750964 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term702 A t u) = (term669 A t u).
Proof. exact (MK_COMB (@lem3750963 A t u) (@lem3750962 A t u)). Qed.
Lemma lem3750965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3750966 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term707 A t u) = (term708 A t u).
Proof. exact (MK_COMB (@lem3750965) (@lem3750964 A t u)). Qed.
Lemma lem3750967 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term704 A t u x) = (term666 A t u x).
Proof. exact (eq_refl (term704 A t u x)). Qed.
Lemma lem3750968 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term427 A t u) = (term427 A t u).
Proof. exact (eq_refl (term427 A t u)). Qed.
Lemma lem3750969 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term709 A t u x) = (term710 A t u x).
Proof. exact (MK_COMB (@lem3750968 A t u) (@lem3750967 A t u x)). Qed.
Lemma lem3750970 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term711 A t u) = (term712 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750969 A t u x)). Qed.
Lemma lem3750971 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3750972 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term703 A t u) = (term713 A t u).
Proof. exact (MK_COMB (@lem3750971 A) (@lem3750970 A t u)). Qed.
Lemma lem3750973 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((term702 A t u) = (term703 A t u)) = ((term669 A t u) = (term713 A t u)).
Proof. exact (MK_COMB (@lem3750966 A t u) (@lem3750972 A t u)). Qed.
Lemma lem3750974 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term669 A t u) = (term713 A t u).
Proof. exact (EQ_MP (@lem3750973 A t u) (@lem3750958 A t u)). Qed.
Lemma lem3750975 {A : Type'} (f : type686 A) (u : A -> Prop) : (term618 A f u) = (term618 A f u).
Proof. exact (eq_refl (term618 A f u)). Qed.
Lemma lem3750976 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term672 A f t u) = (term714 A f t u).
Proof. exact (MK_COMB (@lem3750975 A f u) (@lem3750974 A t u)). Qed.
Lemma lem3750978 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3750979 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (@lem3750978 A P Q). Qed.
Lemma lem3750980 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term715 A f t u) = (term716 A f t u).
Proof. exact (@lem3750979 A (f u) (term712 A t u)). Qed.
Lemma lem3750981 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term717 A t u x) = (term710 A t u x).
Proof. exact (eq_refl (term717 A t u x)). Qed.
Lemma lem3750982 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term718 A t u) = (term712 A t u).
Proof. exact (fun_ext (fun x : A => @lem3750981 A t u x)). Qed.
Lemma lem3750983 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3750984 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term719 A t u) = (term713 A t u).
Proof. exact (MK_COMB (@lem3750983 A) (@lem3750982 A t u)). Qed.
Lemma lem3750985 {A : Type'} (f : type686 A) (u : A -> Prop) : (term618 A f u) = (term618 A f u).
Proof. exact (eq_refl (term618 A f u)). Qed.
Lemma lem3750986 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term715 A f t u) = (term714 A f t u).
Proof. exact (MK_COMB (@lem3750985 A f u) (@lem3750984 A t u)). Qed.
Lemma lem3750987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3750988 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term720 A f t u) = (term721 A f t u).
Proof. exact (MK_COMB (@lem3750987) (@lem3750986 A f t u)). Qed.
Lemma lem3750989 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term717 A t u x) = (term710 A t u x).
Proof. exact (eq_refl (term717 A t u x)). Qed.
Lemma lem3750990 {A : Type'} (f : type686 A) (u : A -> Prop) : (term618 A f u) = (term618 A f u).
Proof. exact (eq_refl (term618 A f u)). Qed.
Lemma lem3750991 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) (x : A) : (term722 A f t u x) = (term723 A f t u x).
Proof. exact (MK_COMB (@lem3750990 A f u) (@lem3750989 A t u x)). Qed.
Lemma lem3750992 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term724 A f t u) = (term725 A f t u).
Proof. exact (fun_ext (fun x : A => @lem3750991 A f t u x)). Qed.
Lemma lem3750993 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3750994 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term716 A f t u) = (term726 A f t u).
Proof. exact (MK_COMB (@lem3750993 A) (@lem3750992 A f t u)). Qed.
Lemma lem3750995 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : ((term715 A f t u) = (term716 A f t u)) = ((term714 A f t u) = (term726 A f t u)).
Proof. exact (MK_COMB (@lem3750988 A f t u) (@lem3750994 A f t u)). Qed.
Lemma lem3750996 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term714 A f t u) = (term726 A f t u).
Proof. exact (EQ_MP (@lem3750995 A f t u) (@lem3750980 A f t u)). Qed.
Lemma lem3750997 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term672 A f t u) = (term726 A f t u).
Proof. exact (TRANS (@lem3750976 A f t u) (@lem3750996 A f t u)). Qed.
Lemma lem3750998 {A : Type'} (f : type686 A) (t : A -> Prop) : (term681 A f t) = (term727 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3750997 A f t u)). Qed.
Lemma lem3750999 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3751000 {A : Type'} (f : type686 A) (t : A -> Prop) : (term682 A f t) = (term728 A f t).
Proof. exact (MK_COMB (@lem3750999 A) (@lem3750998 A f t)). Qed.
Lemma lem3751001 {A : Type'} (f : type686 A) (t : A -> Prop) : (term683 A f t) = (term683 A f t).
Proof. exact (eq_refl (term683 A f t)). Qed.
Lemma lem3751002 {A : Type'} (f : type686 A) (t : A -> Prop) : (term685 A f t) = (term729 A f t).
Proof. exact (MK_COMB (@lem3751001 A f t) (@lem3751000 A f t)). Qed.
Lemma lem3751004 {A : Type'} (P : Prop) (Q : A -> Prop) : (term730 A P Q) = (term731 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3751005 {A : Type'} (P : Prop) (Q : type686 A) : (term732 A P Q) = (term733 A P Q).
Proof. exact (@lem3751004 (A -> Prop) P Q). Qed.
Lemma lem3751006 {A : Type'} (f : type686 A) (t : A -> Prop) : (term734 A f t) = (term735 A f t).
Proof. exact (@lem3751005 A (term736 A f t) (term727 A f t)). Qed.
Lemma lem3751007 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term737 A f t u) = (term726 A f t u).
Proof. exact (eq_refl (term737 A f t u)). Qed.
Lemma lem3751008 {A : Type'} (f : type686 A) (t : A -> Prop) : (term738 A f t) = (term727 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3751007 A f t u)). Qed.
Lemma lem3751009 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3751010 {A : Type'} (f : type686 A) (t : A -> Prop) : (term739 A f t) = (term728 A f t).
Proof. exact (MK_COMB (@lem3751009 A) (@lem3751008 A f t)). Qed.
Lemma lem3751011 {A : Type'} (f : type686 A) (t : A -> Prop) : (term683 A f t) = (term683 A f t).
Proof. exact (eq_refl (term683 A f t)). Qed.
Lemma lem3751012 {A : Type'} (f : type686 A) (t : A -> Prop) : (term734 A f t) = (term729 A f t).
Proof. exact (MK_COMB (@lem3751011 A f t) (@lem3751010 A f t)). Qed.
Lemma lem3751013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751014 {A : Type'} (f : type686 A) (t : A -> Prop) : (term740 A f t) = (term741 A f t).
Proof. exact (MK_COMB (@lem3751013) (@lem3751012 A f t)). Qed.
Lemma lem3751015 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term737 A f t u) = (term726 A f t u).
Proof. exact (eq_refl (term737 A f t u)). Qed.
Lemma lem3751016 {A : Type'} (f : type686 A) (t : A -> Prop) : (term683 A f t) = (term683 A f t).
Proof. exact (eq_refl (term683 A f t)). Qed.
Lemma lem3751017 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term742 A f t u) = (term743 A f t u).
Proof. exact (MK_COMB (@lem3751016 A f t) (@lem3751015 A f t u)). Qed.
Lemma lem3751018 {A : Type'} (f : type686 A) (t : A -> Prop) : (term744 A f t) = (term745 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3751017 A f t u)). Qed.
Lemma lem3751019 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3751020 {A : Type'} (f : type686 A) (t : A -> Prop) : (term735 A f t) = (term746 A f t).
Proof. exact (MK_COMB (@lem3751019 A) (@lem3751018 A f t)). Qed.
Lemma lem3751021 {A : Type'} (f : type686 A) (t : A -> Prop) : ((term734 A f t) = (term735 A f t)) = ((term729 A f t) = (term746 A f t)).
Proof. exact (MK_COMB (@lem3751014 A f t) (@lem3751020 A f t)). Qed.
Lemma lem3751022 {A : Type'} (f : type686 A) (t : A -> Prop) : (term729 A f t) = (term746 A f t).
Proof. exact (EQ_MP (@lem3751021 A f t) (@lem3751006 A f t)). Qed.
Lemma lem3751024 {A : Type'} (P : Prop) (Q : A -> Prop) : (term730 A P Q) = (term731 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3751025 {A : Type'} (P : Prop) (Q : A -> Prop) : (term730 A P Q) = (term731 A P Q).
Proof. exact (@lem3751024 A P Q). Qed.
Lemma lem3751026 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term747 A f t u) = (term748 A f t u).
Proof. exact (@lem3751025 A (term736 A f t) (term725 A f t u)). Qed.
Lemma lem3751027 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) (x : A) : (term749 A f t u x) = (term723 A f t u x).
Proof. exact (eq_refl (term749 A f t u x)). Qed.
Lemma lem3751028 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term750 A f t u) = (term725 A f t u).
Proof. exact (fun_ext (fun x : A => @lem3751027 A f t u x)). Qed.
Lemma lem3751029 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751030 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term751 A f t u) = (term726 A f t u).
Proof. exact (MK_COMB (@lem3751029 A) (@lem3751028 A f t u)). Qed.
Lemma lem3751031 {A : Type'} (f : type686 A) (t : A -> Prop) : (term683 A f t) = (term683 A f t).
Proof. exact (eq_refl (term683 A f t)). Qed.
Lemma lem3751032 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term747 A f t u) = (term743 A f t u).
Proof. exact (MK_COMB (@lem3751031 A f t) (@lem3751030 A f t u)). Qed.
Lemma lem3751033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751034 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term752 A f t u) = (term753 A f t u).
Proof. exact (MK_COMB (@lem3751033) (@lem3751032 A f t u)). Qed.
Lemma lem3751035 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) (x : A) : (term749 A f t u x) = (term723 A f t u x).
Proof. exact (eq_refl (term749 A f t u x)). Qed.
Lemma lem3751036 {A : Type'} (f : type686 A) (t : A -> Prop) : (term683 A f t) = (term683 A f t).
Proof. exact (eq_refl (term683 A f t)). Qed.
Lemma lem3751037 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) (x : A) : (term754 A f t u x) = (term755 A f t u x).
Proof. exact (MK_COMB (@lem3751036 A f t) (@lem3751035 A f t u x)). Qed.
Lemma lem3751038 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term756 A f t u) = (term757 A f t u).
Proof. exact (fun_ext (fun x : A => @lem3751037 A f t u x)). Qed.
Lemma lem3751039 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751040 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term748 A f t u) = (term758 A f t u).
Proof. exact (MK_COMB (@lem3751039 A) (@lem3751038 A f t u)). Qed.
Lemma lem3751041 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : ((term747 A f t u) = (term748 A f t u)) = ((term743 A f t u) = (term758 A f t u)).
Proof. exact (MK_COMB (@lem3751034 A f t u) (@lem3751040 A f t u)). Qed.
Lemma lem3751042 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term743 A f t u) = (term758 A f t u).
Proof. exact (EQ_MP (@lem3751041 A f t u) (@lem3751026 A f t u)). Qed.
Lemma lem3751043 {A : Type'} (f : type686 A) (t : A -> Prop) : (term745 A f t) = (term759 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3751042 A f t u)). Qed.
Lemma lem3751044 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3751045 {A : Type'} (f : type686 A) (t : A -> Prop) : (term746 A f t) = (term760 A f t).
Proof. exact (MK_COMB (@lem3751044 A) (@lem3751043 A f t)). Qed.
Lemma lem3751046 {A : Type'} (f : type686 A) (t : A -> Prop) : (term729 A f t) = (term760 A f t).
Proof. exact (TRANS (@lem3751022 A f t) (@lem3751045 A f t)). Qed.
Lemma lem3751047 {A : Type'} (f : type686 A) (t : A -> Prop) : (term685 A f t) = (term760 A f t).
Proof. exact (TRANS (@lem3751002 A f t) (@lem3751046 A f t)). Qed.
Lemma lem3751048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751049 {A : Type'} (f : type686 A) (t : A -> Prop) : (term688 A f t) = (term761 A f t).
Proof. exact (MK_COMB (@lem3751048) (@lem3751047 A f t)). Qed.
Lemma lem3751050 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term450 A s t) = (term450 A s t).
Proof. exact (eq_refl (term450 A s t)). Qed.
Lemma lem3751051 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term690 A f s t) = (term762 A f s t).
Proof. exact (MK_COMB (@lem3751049 A f t) (@lem3751050 A s t)). Qed.
Lemma lem3751055 {A : Type'} (P : A -> Prop) (Q : Prop) : (term556 A P Q) = (term557 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3751056 {A : Type'} (P : type686 A) (Q : Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem3751055 (A -> Prop) P Q). Qed.
Lemma lem3751057 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term765 A f s t) = (term766 A f s t).
Proof. exact (@lem3751056 A (term759 A f t) (term450 A s t)). Qed.
Lemma lem3751058 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term767 A f t u) = (term758 A f t u).
Proof. exact (eq_refl (term767 A f t u)). Qed.
Lemma lem3751059 {A : Type'} (f : type686 A) (t : A -> Prop) : (term768 A f t) = (term759 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3751058 A f t u)). Qed.
Lemma lem3751060 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3751061 {A : Type'} (f : type686 A) (t : A -> Prop) : (term769 A f t) = (term760 A f t).
Proof. exact (MK_COMB (@lem3751060 A) (@lem3751059 A f t)). Qed.
Lemma lem3751062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751063 {A : Type'} (f : type686 A) (t : A -> Prop) : (term770 A f t) = (term761 A f t).
Proof. exact (MK_COMB (@lem3751062) (@lem3751061 A f t)). Qed.
Lemma lem3751064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term450 A s t) = (term450 A s t).
Proof. exact (eq_refl (term450 A s t)). Qed.
Lemma lem3751065 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term765 A f s t) = (term762 A f s t).
Proof. exact (MK_COMB (@lem3751063 A f t) (@lem3751064 A s t)). Qed.
Lemma lem3751066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751067 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term771 A f s t) = (term772 A f s t).
Proof. exact (MK_COMB (@lem3751066) (@lem3751065 A f s t)). Qed.
Lemma lem3751068 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term767 A f t u) = (term758 A f t u).
Proof. exact (eq_refl (term767 A f t u)). Qed.
Lemma lem3751069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751070 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term773 A f t u) = (term774 A f t u).
Proof. exact (MK_COMB (@lem3751069) (@lem3751068 A f t u)). Qed.
Lemma lem3751071 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term450 A s t) = (term450 A s t).
Proof. exact (eq_refl (term450 A s t)). Qed.
Lemma lem3751072 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term775 A f u s t) = (term776 A f u s t).
Proof. exact (MK_COMB (@lem3751070 A f t u) (@lem3751071 A s t)). Qed.
Lemma lem3751073 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term777 A f s t) = (term778 A f s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3751072 A f u s t)). Qed.
Lemma lem3751074 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3751075 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term766 A f s t) = (term779 A f s t).
Proof. exact (MK_COMB (@lem3751074 A) (@lem3751073 A f s t)). Qed.
Lemma lem3751076 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : ((term765 A f s t) = (term766 A f s t)) = ((term762 A f s t) = (term779 A f s t)).
Proof. exact (MK_COMB (@lem3751067 A f s t) (@lem3751075 A f s t)). Qed.
Lemma lem3751077 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term762 A f s t) = (term779 A f s t).
Proof. exact (EQ_MP (@lem3751076 A f s t) (@lem3751057 A f s t)). Qed.
Lemma lem3751079 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term433 A P Q) = (term432 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3751080 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term433 A P Q) = (term432 A P Q).
Proof. exact (@lem3751079 A P Q). Qed.
Lemma lem3751081 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term780 A f u s t) = (term781 A f u s t).
Proof. exact (@lem3751080 A (term757 A f t u) (term436 A s t)). Qed.
Lemma lem3751082 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) (x : A) : (term782 A f t u x) = (term755 A f t u x).
Proof. exact (eq_refl (term782 A f t u x)). Qed.
Lemma lem3751083 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term783 A f t u) = (term757 A f t u).
Proof. exact (fun_ext (fun x : A => @lem3751082 A f t u x)). Qed.
Lemma lem3751084 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751085 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term784 A f t u) = (term758 A f t u).
Proof. exact (MK_COMB (@lem3751084 A) (@lem3751083 A f t u)). Qed.
Lemma lem3751086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751087 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term785 A f t u) = (term774 A f t u).
Proof. exact (MK_COMB (@lem3751086) (@lem3751085 A f t u)). Qed.
Lemma lem3751088 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term438 A s t x) = (term439 A s t x).
Proof. exact (eq_refl (term438 A s t x)). Qed.
Lemma lem3751089 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term448 A s t) = (term436 A s t).
Proof. exact (fun_ext (fun x : A => @lem3751088 A s t x)). Qed.
Lemma lem3751090 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term449 A s t) = (term450 A s t).
Proof. exact (MK_COMB (@lem3751090 A) (@lem3751089 A s t)). Qed.
Lemma lem3751092 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term780 A f u s t) = (term776 A f u s t).
Proof. exact (MK_COMB (@lem3751087 A f t u) (@lem3751091 A s t)). Qed.
Lemma lem3751093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751094 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term786 A f u s t) = (term787 A f u s t).
Proof. exact (MK_COMB (@lem3751093) (@lem3751092 A f u s t)). Qed.
Lemma lem3751095 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) (x : A) : (term782 A f t u x) = (term755 A f t u x).
Proof. exact (eq_refl (term782 A f t u x)). Qed.
Lemma lem3751096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751097 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) (x : A) : (term788 A f t u x) = (term789 A f t u x).
Proof. exact (MK_COMB (@lem3751096) (@lem3751095 A f t u x)). Qed.
Lemma lem3751098 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term438 A s t x) = (term439 A s t x).
Proof. exact (eq_refl (term438 A s t x)). Qed.
Lemma lem3751099 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) (x : A) : (term790 A f u s t x) = (term791 A f u s t x).
Proof. exact (MK_COMB (@lem3751097 A f t u x) (@lem3751098 A s t x)). Qed.
Lemma lem3751100 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term792 A f u s t) = (term793 A f u s t).
Proof. exact (fun_ext (fun x : A => @lem3751099 A f u s t x)). Qed.
Lemma lem3751101 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751102 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term781 A f u s t) = (term794 A f u s t).
Proof. exact (MK_COMB (@lem3751101 A) (@lem3751100 A f u s t)). Qed.
Lemma lem3751103 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : ((term780 A f u s t) = (term781 A f u s t)) = ((term776 A f u s t) = (term794 A f u s t)).
Proof. exact (MK_COMB (@lem3751094 A f u s t) (@lem3751102 A f u s t)). Qed.
Lemma lem3751104 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term776 A f u s t) = (term794 A f u s t).
Proof. exact (EQ_MP (@lem3751103 A f u s t) (@lem3751081 A f u s t)). Qed.
Lemma lem3751105 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term778 A f s t) = (term795 A f s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3751104 A f u s t)). Qed.
Lemma lem3751106 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3751107 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term779 A f s t) = (term796 A f s t).
Proof. exact (MK_COMB (@lem3751106 A) (@lem3751105 A f s t)). Qed.
Lemma lem3751108 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term762 A f s t) = (term796 A f s t).
Proof. exact (TRANS (@lem3751077 A f s t) (@lem3751107 A f s t)). Qed.
Lemma lem3751109 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term690 A f s t) = (term796 A f s t).
Proof. exact (TRANS (@lem3751051 A f s t) (@lem3751108 A f s t)). Qed.
Lemma lem3751110 {A : Type'} (f : type686 A) (s : A -> Prop) : (term698 A f s) = (term797 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3751109 A f s t)). Qed.
Lemma lem3751111 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751112 {A : Type'} (f : type686 A) (s : A -> Prop) : (term699 A f s) = (term798 A f s).
Proof. exact (MK_COMB (@lem3751111 A) (@lem3751110 A f s)). Qed.
Lemma lem3751114 {A B : Type'} (P : type1413 A B) : (term799 A B P) = (term800 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3751115 {A : Type'} (P : type639 A) : (term801 A P) = (term802 A P).
Proof. exact (@lem3751114 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem3751116 {A : Type'} (f : type686 A) (s : A -> Prop) : (term803 A f s) = (term804 A f s).
Proof. exact (@lem3751115 A (term805 A f s)). Qed.
Lemma lem3751117 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term806 A f s t) = (term795 A f s t).
Proof. exact (eq_refl (term806 A f s t)). Qed.
Lemma lem3751118 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem3751119 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term807 A f s t u) = (term808 A f s t u).
Proof. exact (MK_COMB (@lem3751117 A f s t) (@lem3751118 A u)). Qed.
Lemma lem3751120 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term808 A f s t u) = (term794 A f u s t).
Proof. exact (eq_refl (term808 A f s t u)). Qed.
Lemma lem3751121 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term807 A f s t u) = (term794 A f u s t).
Proof. exact (TRANS (@lem3751119 A f s t u) (@lem3751120 A f u s t)). Qed.
Lemma lem3751122 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term809 A f s t) = (term795 A f s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3751121 A f u s t)). Qed.
Lemma lem3751123 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3751124 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term810 A f s t) = (term796 A f s t).
Proof. exact (MK_COMB (@lem3751123 A) (@lem3751122 A f s t)). Qed.
Lemma lem3751125 {A : Type'} (f : type686 A) (s : A -> Prop) : (term811 A f s) = (term797 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3751124 A f s t)). Qed.
Lemma lem3751126 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751127 {A : Type'} (f : type686 A) (s : A -> Prop) : (term803 A f s) = (term798 A f s).
Proof. exact (MK_COMB (@lem3751126 A) (@lem3751125 A f s)). Qed.
Lemma lem3751128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751129 {A : Type'} (f : type686 A) (s : A -> Prop) : (term812 A f s) = (term813 A f s).
Proof. exact (MK_COMB (@lem3751128) (@lem3751127 A f s)). Qed.
Lemma lem3751130 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term806 A f s t) = (term795 A f s t).
Proof. exact (eq_refl (term806 A f s t)). Qed.
Lemma lem3751131 {A : Type'} (u : type672 A) (t : A -> Prop) : (u t) = (u t).
Proof. exact (eq_refl (u t)). Qed.
Lemma lem3751132 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type672 A) (t : A -> Prop) : (term814 A f s u t) = (term815 A f s u t).
Proof. exact (MK_COMB (@lem3751130 A f s t) (@lem3751131 A u t)). Qed.
Lemma lem3751133 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term815 A f s u t) = (term816 A f u s t).
Proof. exact (eq_refl (term815 A f s u t)). Qed.
Lemma lem3751134 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term814 A f s u t) = (term816 A f u s t).
Proof. exact (TRANS (@lem3751132 A f s u t) (@lem3751133 A f u s t)). Qed.
Lemma lem3751135 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term817 A f s u) = (term818 A f u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3751134 A f u s t)). Qed.
Lemma lem3751136 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751137 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term819 A f s u) = (term820 A f u s).
Proof. exact (MK_COMB (@lem3751136 A) (@lem3751135 A f u s)). Qed.
Lemma lem3751138 {A : Type'} (f : type686 A) (s : A -> Prop) : (term821 A f s) = (term822 A f s).
Proof. exact (fun_ext (fun u : type672 A => @lem3751137 A f u s)). Qed.
Lemma lem3751139 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3751140 {A : Type'} (f : type686 A) (s : A -> Prop) : (term804 A f s) = (term823 A f s).
Proof. exact (MK_COMB (@lem3751139 A) (@lem3751138 A f s)). Qed.
Lemma lem3751141 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term803 A f s) = (term804 A f s)) = ((term798 A f s) = (term823 A f s)).
Proof. exact (MK_COMB (@lem3751129 A f s) (@lem3751140 A f s)). Qed.
Lemma lem3751142 {A : Type'} (f : type686 A) (s : A -> Prop) : (term798 A f s) = (term823 A f s).
Proof. exact (EQ_MP (@lem3751141 A f s) (@lem3751116 A f s)). Qed.
Lemma lem3751144 {A B : Type'} (P : type1413 A B) : (term799 A B P) = (term800 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3751145 {A : Type'} (P : type672 A) : (term824 A P) = (term825 A P).
Proof. exact (@lem3751144 (A -> Prop) A P). Qed.
Lemma lem3751146 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term826 A f u s) = (term827 A f u s).
Proof. exact (@lem3751145 A (term828 A f u s)). Qed.
Lemma lem3751147 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term829 A f u s t) = (term830 A f u s t).
Proof. exact (eq_refl (term829 A f u s t)). Qed.
Lemma lem3751148 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3751149 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term831 A f u s t x) = (term832 A f u s t x).
Proof. exact (MK_COMB (@lem3751147 A f u s t) (@lem3751148 A x)). Qed.
Lemma lem3751150 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term832 A f u s t x) = (term833 A f u s t x).
Proof. exact (eq_refl (term832 A f u s t x)). Qed.
Lemma lem3751151 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term831 A f u s t x) = (term833 A f u s t x).
Proof. exact (TRANS (@lem3751149 A f u s t x) (@lem3751150 A f u s t x)). Qed.
Lemma lem3751152 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term834 A f u s t) = (term830 A f u s t).
Proof. exact (fun_ext (fun x : A => @lem3751151 A f u s t x)). Qed.
Lemma lem3751153 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751154 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term835 A f u s t) = (term816 A f u s t).
Proof. exact (MK_COMB (@lem3751153 A) (@lem3751152 A f u s t)). Qed.
Lemma lem3751155 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term836 A f u s) = (term818 A f u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3751154 A f u s t)). Qed.
Lemma lem3751156 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751157 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term826 A f u s) = (term820 A f u s).
Proof. exact (MK_COMB (@lem3751156 A) (@lem3751155 A f u s)). Qed.
Lemma lem3751158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751159 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term837 A f u s) = (term838 A f u s).
Proof. exact (MK_COMB (@lem3751158) (@lem3751157 A f u s)). Qed.
Lemma lem3751160 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term829 A f u s t) = (term830 A f u s t).
Proof. exact (eq_refl (term829 A f u s t)). Qed.
Lemma lem3751161 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem3751162 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term839 A f u s x t) = (term840 A f u s x t).
Proof. exact (MK_COMB (@lem3751160 A f u s t) (@lem3751161 A x t)). Qed.
Lemma lem3751163 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term840 A f u s x t) = (term841 A f u s x t).
Proof. exact (eq_refl (term840 A f u s x t)). Qed.
Lemma lem3751164 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term839 A f u s x t) = (term841 A f u s x t).
Proof. exact (TRANS (@lem3751162 A f u s x t) (@lem3751163 A f u s x t)). Qed.
Lemma lem3751165 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x : type684 A) : (term842 A f u s x) = (term843 A f u s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3751164 A f u s x t)). Qed.
Lemma lem3751166 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751167 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x : type684 A) : (term844 A f u s x) = (term845 A f u s x).
Proof. exact (MK_COMB (@lem3751166 A) (@lem3751165 A f u s x)). Qed.
Lemma lem3751168 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term846 A f u s) = (term847 A f u s).
Proof. exact (fun_ext (fun x : type684 A => @lem3751167 A f u s x)). Qed.
Lemma lem3751169 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3751170 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term827 A f u s) = (term848 A f u s).
Proof. exact (MK_COMB (@lem3751169 A) (@lem3751168 A f u s)). Qed.
Lemma lem3751171 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : ((term826 A f u s) = (term827 A f u s)) = ((term820 A f u s) = (term848 A f u s)).
Proof. exact (MK_COMB (@lem3751159 A f u s) (@lem3751170 A f u s)). Qed.
Lemma lem3751172 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term820 A f u s) = (term848 A f u s).
Proof. exact (EQ_MP (@lem3751171 A f u s) (@lem3751146 A f u s)). Qed.
Lemma lem3751173 {A : Type'} (f : type686 A) (s : A -> Prop) : (term822 A f s) = (term849 A f s).
Proof. exact (fun_ext (fun u : type672 A => @lem3751172 A f u s)). Qed.
Lemma lem3751174 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3751175 {A : Type'} (f : type686 A) (s : A -> Prop) : (term823 A f s) = (term850 A f s).
Proof. exact (MK_COMB (@lem3751174 A) (@lem3751173 A f s)). Qed.
Lemma lem3751176 {A : Type'} (f : type686 A) (s : A -> Prop) : (term798 A f s) = (term850 A f s).
Proof. exact (TRANS (@lem3751142 A f s) (@lem3751175 A f s)). Qed.
Lemma lem3751177 {A : Type'} (f : type686 A) (s : A -> Prop) : (term699 A f s) = (term850 A f s).
Proof. exact (TRANS (@lem3751112 A f s) (@lem3751176 A f s)). Qed.
Lemma lem3751178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751179 {A : Type'} (f : type686 A) (s : A -> Prop) : (term700 A f s) = (term851 A f s).
Proof. exact (MK_COMB (@lem3751178) (@lem3751177 A f s)). Qed.
Lemma lem3751180 {A : Type'} (s : A -> Prop) (f : type686 A) : (term630 A s f) = (term630 A s f).
Proof. exact (eq_refl (term630 A s f)). Qed.
Lemma lem3751181 {A : Type'} (s : A -> Prop) (f : type686 A) : (term701 A s f) = (term852 A s f).
Proof. exact (MK_COMB (@lem3751179 A f s) (@lem3751180 A s f)). Qed.
Lemma lem3751183 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3751184 {A : Type'} (P : type151 A) (Q : Prop) : (term853 A P Q) = (term854 A P Q).
Proof. exact (@lem3751183 (type672 A) P Q). Qed.
Lemma lem3751185 {A : Type'} (s : A -> Prop) (f : type686 A) : (term855 A s f) = (term856 A s f).
Proof. exact (@lem3751184 A (term849 A f s) (term630 A s f)). Qed.
Lemma lem3751186 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term857 A f s u) = (term848 A f u s).
Proof. exact (eq_refl (term857 A f s u)). Qed.
Lemma lem3751187 {A : Type'} (f : type686 A) (s : A -> Prop) : (term858 A f s) = (term849 A f s).
Proof. exact (fun_ext (fun u : type672 A => @lem3751186 A f u s)). Qed.
Lemma lem3751188 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3751189 {A : Type'} (f : type686 A) (s : A -> Prop) : (term859 A f s) = (term850 A f s).
Proof. exact (MK_COMB (@lem3751188 A) (@lem3751187 A f s)). Qed.
Lemma lem3751190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751191 {A : Type'} (f : type686 A) (s : A -> Prop) : (term860 A f s) = (term851 A f s).
Proof. exact (MK_COMB (@lem3751190) (@lem3751189 A f s)). Qed.
Lemma lem3751192 {A : Type'} (s : A -> Prop) (f : type686 A) : (term630 A s f) = (term630 A s f).
Proof. exact (eq_refl (term630 A s f)). Qed.
Lemma lem3751193 {A : Type'} (s : A -> Prop) (f : type686 A) : (term855 A s f) = (term852 A s f).
Proof. exact (MK_COMB (@lem3751191 A f s) (@lem3751192 A s f)). Qed.
Lemma lem3751194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751195 {A : Type'} (s : A -> Prop) (f : type686 A) : (term861 A s f) = (term862 A s f).
Proof. exact (MK_COMB (@lem3751194) (@lem3751193 A s f)). Qed.
Lemma lem3751196 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term857 A f s u) = (term848 A f u s).
Proof. exact (eq_refl (term857 A f s u)). Qed.
Lemma lem3751197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751198 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term863 A f s u) = (term864 A f u s).
Proof. exact (MK_COMB (@lem3751197) (@lem3751196 A f u s)). Qed.
Lemma lem3751199 {A : Type'} (s : A -> Prop) (f : type686 A) : (term630 A s f) = (term630 A s f).
Proof. exact (eq_refl (term630 A s f)). Qed.
Lemma lem3751200 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) : (term865 A u s f) = (term866 A u s f).
Proof. exact (MK_COMB (@lem3751198 A f u s) (@lem3751199 A s f)). Qed.
Lemma lem3751201 {A : Type'} (s : A -> Prop) (f : type686 A) : (term867 A s f) = (term868 A s f).
Proof. exact (fun_ext (fun u : type672 A => @lem3751200 A u s f)). Qed.
Lemma lem3751202 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3751203 {A : Type'} (s : A -> Prop) (f : type686 A) : (term856 A s f) = (term869 A s f).
Proof. exact (MK_COMB (@lem3751202 A) (@lem3751201 A s f)). Qed.
Lemma lem3751204 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term855 A s f) = (term856 A s f)) = ((term852 A s f) = (term869 A s f)).
Proof. exact (MK_COMB (@lem3751195 A s f) (@lem3751203 A s f)). Qed.
Lemma lem3751205 {A : Type'} (s : A -> Prop) (f : type686 A) : (term852 A s f) = (term869 A s f).
Proof. exact (EQ_MP (@lem3751204 A s f) (@lem3751185 A s f)). Qed.
Lemma lem3751207 {A : Type'} (P : A -> Prop) (Q : Prop) : (term492 A P Q) = (term493 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3751208 {A : Type'} (P : type162 A) (Q : Prop) : (term870 A P Q) = (term871 A P Q).
Proof. exact (@lem3751207 (type684 A) P Q). Qed.
Lemma lem3751209 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) : (term872 A u s f) = (term873 A u s f).
Proof. exact (@lem3751208 A (term847 A f u s) (term630 A s f)). Qed.
Lemma lem3751210 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x : type684 A) : (term874 A f u s x) = (term845 A f u s x).
Proof. exact (eq_refl (term874 A f u s x)). Qed.
Lemma lem3751211 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term875 A f u s) = (term847 A f u s).
Proof. exact (fun_ext (fun x : type684 A => @lem3751210 A f u s x)). Qed.
Lemma lem3751212 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3751213 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term876 A f u s) = (term848 A f u s).
Proof. exact (MK_COMB (@lem3751212 A) (@lem3751211 A f u s)). Qed.
Lemma lem3751214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751215 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term877 A f u s) = (term864 A f u s).
Proof. exact (MK_COMB (@lem3751214) (@lem3751213 A f u s)). Qed.
Lemma lem3751216 {A : Type'} (s : A -> Prop) (f : type686 A) : (term630 A s f) = (term630 A s f).
Proof. exact (eq_refl (term630 A s f)). Qed.
Lemma lem3751217 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) : (term872 A u s f) = (term866 A u s f).
Proof. exact (MK_COMB (@lem3751215 A f u s) (@lem3751216 A s f)). Qed.
Lemma lem3751218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751219 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) : (term878 A u s f) = (term879 A u s f).
Proof. exact (MK_COMB (@lem3751218) (@lem3751217 A u s f)). Qed.
Lemma lem3751220 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x : type684 A) : (term874 A f u s x) = (term845 A f u s x).
Proof. exact (eq_refl (term874 A f u s x)). Qed.
Lemma lem3751221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751222 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x : type684 A) : (term880 A f u s x) = (term881 A f u s x).
Proof. exact (MK_COMB (@lem3751221) (@lem3751220 A f u s x)). Qed.
Lemma lem3751223 {A : Type'} (s : A -> Prop) (f : type686 A) : (term630 A s f) = (term630 A s f).
Proof. exact (eq_refl (term630 A s f)). Qed.
Lemma lem3751224 {A : Type'} (u : type672 A) (x : type684 A) (s : A -> Prop) (f : type686 A) : (term882 A u x s f) = (term883 A u x s f).
Proof. exact (MK_COMB (@lem3751222 A f u s x) (@lem3751223 A s f)). Qed.
Lemma lem3751225 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) : (term884 A u s f) = (term885 A u s f).
Proof. exact (fun_ext (fun x : type684 A => @lem3751224 A u x s f)). Qed.
Lemma lem3751226 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3751227 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) : (term873 A u s f) = (term886 A u s f).
Proof. exact (MK_COMB (@lem3751226 A) (@lem3751225 A u s f)). Qed.
Lemma lem3751228 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) : ((term872 A u s f) = (term873 A u s f)) = ((term866 A u s f) = (term886 A u s f)).
Proof. exact (MK_COMB (@lem3751219 A u s f) (@lem3751227 A u s f)). Qed.
Lemma lem3751229 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) : (term866 A u s f) = (term886 A u s f).
Proof. exact (EQ_MP (@lem3751228 A u s f) (@lem3751209 A u s f)). Qed.
Lemma lem3751230 {A : Type'} (s : A -> Prop) (f : type686 A) : (term868 A s f) = (term887 A s f).
Proof. exact (fun_ext (fun u : type672 A => @lem3751229 A u s f)). Qed.
Lemma lem3751231 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3751232 {A : Type'} (s : A -> Prop) (f : type686 A) : (term869 A s f) = (term888 A s f).
Proof. exact (MK_COMB (@lem3751231 A) (@lem3751230 A s f)). Qed.
Lemma lem3751233 {A : Type'} (s : A -> Prop) (f : type686 A) : (term852 A s f) = (term888 A s f).
Proof. exact (TRANS (@lem3751205 A s f) (@lem3751232 A s f)). Qed.
Lemma lem3751235 {A : Type'} (s : A -> Prop) (f : type686 A) : (term701 A s f) = (term888 A s f).
Proof. exact (TRANS (@lem3751181 A s f) (@lem3751233 A s f)). Qed.
Lemma lem3751236 {A : Type'} (s : A -> Prop) (f : type686 A) : (term631 A s f) = (term888 A s f).
Proof. exact (TRANS (@lem3750769 A s f) (@lem3751235 A s f)). Qed.
Lemma lem3751237 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term631 A s f) : term888 A s f.
Proof. exact (EQ_MP (@lem3751236 A s f) (@lem3750666 A s f h1)). Qed.
Lemma lem3751245 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term520 A s x x') = (term439 A s x x').
Proof. exact (@lem17362 (s x') (x x')). Qed.
Lemma lem3751246 {A : Type'} (P : A -> Prop) : (term419 A P) = (term420 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3751247 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term521 A s x) = (term522 A s x).
Proof. exact (@lem3751246 A (term380 A s x)). Qed.
Lemma lem3751248 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term523 A s x x') = (term378 A s x x').
Proof. exact (eq_refl (term523 A s x x')). Qed.
Lemma lem3751249 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3751250 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term524 A s x x') = (term520 A s x x').
Proof. exact (MK_COMB (@lem3751249) (@lem3751248 A s x x')). Qed.
Lemma lem3751251 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term524 A s x x') = (term439 A s x x').
Proof. exact (TRANS (@lem3751250 A s x x') (@lem3751245 A s x x')). Qed.
Lemma lem3751252 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term525 A s x) = (term436 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3751251 A s x x')). Qed.
Lemma lem3751253 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751254 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term522 A s x) = (term450 A s x).
Proof. exact (MK_COMB (@lem3751253 A) (@lem3751252 A s x)). Qed.
Lemma lem3751255 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term521 A s x) = (term450 A s x).
Proof. exact (TRANS (@lem3751247 A s x) (@lem3751254 A s x)). Qed.
Lemma lem3751257 {A : Type'} (f : type686 A) (x : A -> Prop) : (term683 A f x) = (term683 A f x).
Proof. exact (eq_refl (term683 A f x)). Qed.
Lemma lem3751258 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term889 A f s x) = (term890 A f s x).
Proof. exact (MK_COMB (@lem3751257 A f x) (@lem3751255 A s x)). Qed.
Lemma lem3751259 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term647 A f s x) = (term889 A f s x).
Proof. exact (@lem17045 (f x) (term381 A s x)). Qed.
Lemma lem3751260 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term647 A f s x) = (term890 A f s x).
Proof. exact (TRANS (@lem3751259 A f s x) (@lem3751258 A f s x)). Qed.
Lemma lem3751261 {A : Type'} (f : type686 A) (s : A -> Prop) : (term648 A f s) = (term891 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3751260 A f s x)). Qed.
Lemma lem3751262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751263 {A : Type'} (f : type686 A) (s : A -> Prop) : (term649 A f s) = (term892 A f s).
Proof. exact (MK_COMB (@lem3751262 A) (@lem3751261 A f s)). Qed.
Lemma lem3751342 {A : Type'} (P : Prop) (Q : A -> Prop) : (term730 A P Q) = (term731 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3751343 {A : Type'} (P : Prop) (Q : A -> Prop) : (term730 A P Q) = (term731 A P Q).
Proof. exact (@lem3751342 A P Q). Qed.
Lemma lem3751344 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term893 A f s x) = (term894 A f s x).
Proof. exact (@lem3751343 A (term736 A f x) (term436 A s x)). Qed.
Lemma lem3751345 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term438 A s x x') = (term439 A s x x').
Proof. exact (eq_refl (term438 A s x x')). Qed.
Lemma lem3751346 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term448 A s x) = (term436 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3751345 A s x x')). Qed.
Lemma lem3751347 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751348 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term449 A s x) = (term450 A s x).
Proof. exact (MK_COMB (@lem3751347 A) (@lem3751346 A s x)). Qed.
Lemma lem3751349 {A : Type'} (f : type686 A) (x : A -> Prop) : (term683 A f x) = (term683 A f x).
Proof. exact (eq_refl (term683 A f x)). Qed.
Lemma lem3751350 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term893 A f s x) = (term890 A f s x).
Proof. exact (MK_COMB (@lem3751349 A f x) (@lem3751348 A s x)). Qed.
Lemma lem3751351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751352 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term895 A f s x) = (term896 A f s x).
Proof. exact (MK_COMB (@lem3751351) (@lem3751350 A f s x)). Qed.
Lemma lem3751353 {A : Type'} (s : A -> Prop) (x : A -> Prop) (x' : A) : (term438 A s x x') = (term439 A s x x').
Proof. exact (eq_refl (term438 A s x x')). Qed.
Lemma lem3751354 {A : Type'} (f : type686 A) (x : A -> Prop) : (term683 A f x) = (term683 A f x).
Proof. exact (eq_refl (term683 A f x)). Qed.
Lemma lem3751355 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) (x' : A) : (term897 A f s x x') = (term898 A f s x x').
Proof. exact (MK_COMB (@lem3751354 A f x) (@lem3751353 A s x x')). Qed.
Lemma lem3751356 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term899 A f s x) = (term900 A f s x).
Proof. exact (fun_ext (fun x' : A => @lem3751355 A f s x x')). Qed.
Lemma lem3751357 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751358 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term894 A f s x) = (term901 A f s x).
Proof. exact (MK_COMB (@lem3751357 A) (@lem3751356 A f s x)). Qed.
Lemma lem3751359 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : ((term893 A f s x) = (term894 A f s x)) = ((term890 A f s x) = (term901 A f s x)).
Proof. exact (MK_COMB (@lem3751352 A f s x) (@lem3751358 A f s x)). Qed.
Lemma lem3751360 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term890 A f s x) = (term901 A f s x).
Proof. exact (EQ_MP (@lem3751359 A f s x) (@lem3751344 A f s x)). Qed.
Lemma lem3751361 {A : Type'} (f : type686 A) (s : A -> Prop) : (term891 A f s) = (term902 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3751360 A f s x)). Qed.
Lemma lem3751362 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751363 {A : Type'} (f : type686 A) (s : A -> Prop) : (term892 A f s) = (term903 A f s).
Proof. exact (MK_COMB (@lem3751362 A) (@lem3751361 A f s)). Qed.
Lemma lem3751365 {A B : Type'} (P : type1413 A B) : (term799 A B P) = (term800 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3751366 {A : Type'} (P : type672 A) : (term824 A P) = (term825 A P).
Proof. exact (@lem3751365 (A -> Prop) A P). Qed.
Lemma lem3751367 {A : Type'} (f : type686 A) (s : A -> Prop) : (term904 A f s) = (term905 A f s).
Proof. exact (@lem3751366 A (term906 A f s)). Qed.
Lemma lem3751368 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term907 A f s x) = (term900 A f s x).
Proof. exact (eq_refl (term907 A f s x)). Qed.
Lemma lem3751369 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3751370 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) (x' : A) : (term908 A f s x x') = (term909 A f s x x').
Proof. exact (MK_COMB (@lem3751368 A f s x) (@lem3751369 A x')). Qed.
Lemma lem3751371 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) (x' : A) : (term909 A f s x x') = (term898 A f s x x').
Proof. exact (eq_refl (term909 A f s x x')). Qed.
Lemma lem3751372 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) (x' : A) : (term908 A f s x x') = (term898 A f s x x').
Proof. exact (TRANS (@lem3751370 A f s x x') (@lem3751371 A f s x x')). Qed.
Lemma lem3751373 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term910 A f s x) = (term900 A f s x).
Proof. exact (fun_ext (fun x' : A => @lem3751372 A f s x x')). Qed.
Lemma lem3751374 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3751375 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term911 A f s x) = (term901 A f s x).
Proof. exact (MK_COMB (@lem3751374 A) (@lem3751373 A f s x)). Qed.
Lemma lem3751376 {A : Type'} (f : type686 A) (s : A -> Prop) : (term912 A f s) = (term902 A f s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3751375 A f s x)). Qed.
Lemma lem3751377 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751378 {A : Type'} (f : type686 A) (s : A -> Prop) : (term904 A f s) = (term903 A f s).
Proof. exact (MK_COMB (@lem3751377 A) (@lem3751376 A f s)). Qed.
Lemma lem3751379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3751380 {A : Type'} (f : type686 A) (s : A -> Prop) : (term913 A f s) = (term914 A f s).
Proof. exact (MK_COMB (@lem3751379) (@lem3751378 A f s)). Qed.
Lemma lem3751381 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A -> Prop) : (term907 A f s x) = (term900 A f s x).
Proof. exact (eq_refl (term907 A f s x)). Qed.
Lemma lem3751382 {A : Type'} (x : type684 A) (x' : A -> Prop) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem3751383 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term915 A f s x x') = (term916 A f s x x').
Proof. exact (MK_COMB (@lem3751381 A f s x') (@lem3751382 A x x')). Qed.
Lemma lem3751384 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term916 A f s x x') = (term917 A f s x x').
Proof. exact (eq_refl (term916 A f s x x')). Qed.
Lemma lem3751385 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term915 A f s x x') = (term917 A f s x x').
Proof. exact (TRANS (@lem3751383 A f s x x') (@lem3751384 A f s x x')). Qed.
Lemma lem3751386 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) : (term918 A f s x) = (term919 A f s x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3751385 A f s x x')). Qed.
Lemma lem3751387 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751388 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) : (term920 A f s x) = (term921 A f s x).
Proof. exact (MK_COMB (@lem3751387 A) (@lem3751386 A f s x)). Qed.
Lemma lem3751389 {A : Type'} (f : type686 A) (s : A -> Prop) : (term922 A f s) = (term923 A f s).
Proof. exact (fun_ext (fun x : type684 A => @lem3751388 A f s x)). Qed.
Lemma lem3751390 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3751391 {A : Type'} (f : type686 A) (s : A -> Prop) : (term905 A f s) = (term924 A f s).
Proof. exact (MK_COMB (@lem3751390 A) (@lem3751389 A f s)). Qed.
Lemma lem3751392 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term904 A f s) = (term905 A f s)) = ((term903 A f s) = (term924 A f s)).
Proof. exact (MK_COMB (@lem3751380 A f s) (@lem3751391 A f s)). Qed.
Lemma lem3751393 {A : Type'} (f : type686 A) (s : A -> Prop) : (term903 A f s) = (term924 A f s).
Proof. exact (EQ_MP (@lem3751392 A f s) (@lem3751367 A f s)). Qed.
Lemma lem3751395 {A : Type'} (f : type686 A) (s : A -> Prop) : (term892 A f s) = (term924 A f s).
Proof. exact (TRANS (@lem3751363 A f s) (@lem3751393 A f s)). Qed.
Lemma lem3751396 {A : Type'} (f : type686 A) (s : A -> Prop) : (term649 A f s) = (term924 A f s).
Proof. exact (TRANS (@lem3751263 A f s) (@lem3751395 A f s)). Qed.
Lemma lem3751397 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term649 A f s) : term924 A f s.
Proof. exact (EQ_MP (@lem3751396 A f s) (@lem3750667 A f s h1)). Qed.
Lemma lem3751398 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term921 A f s x.
Proof. exact (h1). Qed.
Lemma lem3751399 {A : Type'} (u : type672 A) (s : A -> Prop) (f : type686 A) (h1 : term886 A u s f) : term886 A u s f.
Proof. exact (h1). Qed.
Lemma lem3751400 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : term883 A u x' s f.
Proof. exact (h1). Qed.
Lemma lem3751401 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3751402 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3751407 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751408 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3751407 (A -> Prop) A f x). Qed.
Lemma lem3751410 {A : Type'} (x : type684 A) (x' : A -> Prop) : (x x') = (@I ((A -> Prop) -> A) x x').
Proof. exact (@lem3751408 A x x'). Qed.
Lemma lem3751411 {A : Type'} (x : type684 A) (x' : A -> Prop) : (term925 A x x') = (term926 A x x').
Proof. exact (MK_COMB (@lem3751402 A x') (@lem3751410 A x x')). Qed.
Lemma lem3751413 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751414 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751413 A Prop f x). Qed.
Lemma lem3751415 {A : Type'} (x : type684 A) (x' : A -> Prop) : (term926 A x x') = (term927 A x x').
Proof. exact (@lem3751414 A x' (@I ((A -> Prop) -> A) x x')). Qed.
Lemma lem3751416 {A : Type'} (x : type684 A) (x' : A -> Prop) : (term925 A x x') = (term927 A x x').
Proof. exact (TRANS (@lem3751411 A x x') (@lem3751415 A x x')). Qed.
Lemma lem3751417 {A : Type'} (x : type684 A) (x' : A -> Prop) : (term928 A x x') = (term929 A x x').
Proof. exact (MK_COMB (@lem3751401) (@lem3751416 A x x')). Qed.
Lemma lem3751418 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3751423 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751424 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3751423 (A -> Prop) A f x). Qed.
Lemma lem3751426 {A : Type'} (x : type684 A) (x' : A -> Prop) : (x x') = (@I ((A -> Prop) -> A) x x').
Proof. exact (@lem3751424 A x x'). Qed.
Lemma lem3751427 {A : Type'} (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term930 A s x x') = (term931 A s x x').
Proof. exact (MK_COMB (@lem3751418 A s) (@lem3751426 A x x')). Qed.
Lemma lem3751429 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751430 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751429 A Prop f x). Qed.
Lemma lem3751431 {A : Type'} (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term931 A s x x') = (term932 A s x x').
Proof. exact (@lem3751430 A s (@I ((A -> Prop) -> A) x x')). Qed.
Lemma lem3751432 {A : Type'} (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term930 A s x x') = (term932 A s x x').
Proof. exact (TRANS (@lem3751427 A s x x') (@lem3751431 A s x x')). Qed.
Lemma lem3751433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751434 {A : Type'} (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term933 A s x x') = (term934 A s x x').
Proof. exact (MK_COMB (@lem3751433) (@lem3751432 A s x x')). Qed.
Lemma lem3751435 {A : Type'} (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term935 A s x x') = (term936 A s x x').
Proof. exact (MK_COMB (@lem3751434 A s x x') (@lem3751417 A x x')). Qed.
Lemma lem3751436 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3751441 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751443 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3751441 (A -> Prop) Prop f x). Qed.
Lemma lem3751444 {A : Type'} (f : type686 A) (x : A -> Prop) : (term736 A f x) = (term937 A f x).
Proof. exact (MK_COMB (@lem3751436) (@lem3751443 A f x)). Qed.
Lemma lem3751445 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751446 {A : Type'} (f : type686 A) (x : A -> Prop) : (term683 A f x) = (term938 A f x).
Proof. exact (MK_COMB (@lem3751445) (@lem3751444 A f x)). Qed.
Lemma lem3751447 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term917 A f s x x') = (term939 A f s x x').
Proof. exact (MK_COMB (@lem3751446 A f x') (@lem3751435 A s x x')). Qed.
Lemma lem3751448 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) : (term919 A f s x) = (term940 A f s x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3751447 A f s x x')). Qed.
Lemma lem3751449 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751450 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) : (term921 A f s x) = (term941 A f s x).
Proof. exact (MK_COMB (@lem3751449 A) (@lem3751448 A f s x)). Qed.
Lemma lem3751451 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term941 A f s x.
Proof. exact (EQ_MP (@lem3751450 A f s x) (@lem3751398 A f s x h1)). Qed.
Lemma lem3751456 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751457 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3751456 (type686 A) Prop f x). Qed.
Lemma lem3751459 {A : Type'} (f : type686 A) : (@FINITE (A -> Prop) f) = (@I (((A -> Prop) -> Prop) -> Prop) (@FINITE (A -> Prop)) f).
Proof. exact (@lem3751457 A (@FINITE (A -> Prop)) f). Qed.
Lemma lem3751464 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751465 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3751464 (A -> Prop) Prop f x). Qed.
Lemma lem3751467 {A : Type'} (f : type686 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> Prop) f s).
Proof. exact (@lem3751465 A f s). Qed.
Lemma lem3751468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751469 {A : Type'} (f : type686 A) (s : A -> Prop) : (term618 A f s) = (term942 A f s).
Proof. exact (MK_COMB (@lem3751468) (@lem3751467 A f s)). Qed.
Lemma lem3751470 {A : Type'} (s : A -> Prop) (f : type686 A) : (term630 A s f) = (term943 A s f).
Proof. exact (MK_COMB (@lem3751469 A f s) (@lem3751459 A f)). Qed.
Lemma lem3751471 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3751472 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3751477 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751478 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3751477 (A -> Prop) A f x). Qed.
Lemma lem3751480 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3751478 A x' t). Qed.
Lemma lem3751481 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term925 A x' t) = (term926 A x' t).
Proof. exact (MK_COMB (@lem3751472 A t) (@lem3751480 A x' t)). Qed.
Lemma lem3751483 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751484 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751483 A Prop f x). Qed.
Lemma lem3751485 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term926 A x' t) = (term927 A x' t).
Proof. exact (@lem3751484 A t (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3751486 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term925 A x' t) = (term927 A x' t).
Proof. exact (TRANS (@lem3751481 A x' t) (@lem3751485 A x' t)). Qed.
Lemma lem3751487 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term928 A x' t) = (term929 A x' t).
Proof. exact (MK_COMB (@lem3751471) (@lem3751486 A x' t)). Qed.
Lemma lem3751488 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3751493 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751494 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3751493 (A -> Prop) A f x). Qed.
Lemma lem3751496 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3751494 A x' t). Qed.
Lemma lem3751497 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term930 A s x' t) = (term931 A s x' t).
Proof. exact (MK_COMB (@lem3751488 A s) (@lem3751496 A x' t)). Qed.
Lemma lem3751499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751500 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751499 A Prop f x). Qed.
Lemma lem3751501 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term931 A s x' t) = (term932 A s x' t).
Proof. exact (@lem3751500 A s (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3751502 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term930 A s x' t) = (term932 A s x' t).
Proof. exact (TRANS (@lem3751497 A s x' t) (@lem3751501 A s x' t)). Qed.
Lemma lem3751503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751504 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term933 A s x' t) = (term934 A s x' t).
Proof. exact (MK_COMB (@lem3751503) (@lem3751502 A s x' t)). Qed.
Lemma lem3751505 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term935 A s x' t) = (term936 A s x' t).
Proof. exact (MK_COMB (@lem3751504 A s x' t) (@lem3751487 A x' t)). Qed.
Lemma lem3751506 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3751513 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751514 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3751513 (A -> Prop) A f x). Qed.
Lemma lem3751516 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3751514 A x' t). Qed.
Lemma lem3751517 {A : Type'} (u : type672 A) (t : A -> Prop) : (u t) = (u t).
Proof. exact (eq_refl (u t)). Qed.
Lemma lem3751518 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term944 A u x' t) = (term945 A u x' t).
Proof. exact (MK_COMB (@lem3751517 A u t) (@lem3751516 A x' t)). Qed.
Lemma lem3751520 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751521 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3751520 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3751522 {A : Type'} (u : type672 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> A -> Prop) u t).
Proof. exact (@lem3751521 A u t). Qed.
Lemma lem3751523 {A : Type'} (x' : type684 A) (t : A -> Prop) : (@I ((A -> Prop) -> A) x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (eq_refl (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3751524 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term945 A u x' t) = (term946 A u x' t).
Proof. exact (MK_COMB (@lem3751522 A u t) (@lem3751523 A x' t)). Qed.
Lemma lem3751526 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751527 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751526 A Prop f x). Qed.
Lemma lem3751528 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term946 A u x' t) = (term947 A u x' t).
Proof. exact (@lem3751527 A (@I ((A -> Prop) -> A -> Prop) u t) (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3751529 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term945 A u x' t) = (term947 A u x' t).
Proof. exact (TRANS (@lem3751524 A u x' t) (@lem3751528 A u x' t)). Qed.
Lemma lem3751530 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term944 A u x' t) = (term947 A u x' t).
Proof. exact (TRANS (@lem3751518 A u x' t) (@lem3751529 A u x' t)). Qed.
Lemma lem3751531 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term948 A u x' t) = (term949 A u x' t).
Proof. exact (MK_COMB (@lem3751506) (@lem3751530 A u x' t)). Qed.
Lemma lem3751532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3751533 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3751538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751539 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3751538 (A -> Prop) A f x). Qed.
Lemma lem3751541 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3751539 A x' t). Qed.
Lemma lem3751542 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term925 A x' t) = (term926 A x' t).
Proof. exact (MK_COMB (@lem3751533 A t) (@lem3751541 A x' t)). Qed.
Lemma lem3751544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751545 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751544 A Prop f x). Qed.
Lemma lem3751546 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term926 A x' t) = (term927 A x' t).
Proof. exact (@lem3751545 A t (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3751547 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term925 A x' t) = (term927 A x' t).
Proof. exact (TRANS (@lem3751542 A x' t) (@lem3751546 A x' t)). Qed.
Lemma lem3751548 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term928 A x' t) = (term929 A x' t).
Proof. exact (MK_COMB (@lem3751532) (@lem3751547 A x' t)). Qed.
Lemma lem3751549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751550 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term950 A x' t) = (term951 A x' t).
Proof. exact (MK_COMB (@lem3751549) (@lem3751548 A x' t)). Qed.
Lemma lem3751551 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term952 A u x' t) = (term953 A u x' t).
Proof. exact (MK_COMB (@lem3751550 A x' t) (@lem3751531 A u x' t)). Qed.
Lemma lem3751558 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751559 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3751558 (A -> Prop) A f x). Qed.
Lemma lem3751561 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3751559 A x' t). Qed.
Lemma lem3751562 {A : Type'} (u : type672 A) (t : A -> Prop) : (u t) = (u t).
Proof. exact (eq_refl (u t)). Qed.
Lemma lem3751563 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term944 A u x' t) = (term945 A u x' t).
Proof. exact (MK_COMB (@lem3751562 A u t) (@lem3751561 A x' t)). Qed.
Lemma lem3751565 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751566 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3751565 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3751567 {A : Type'} (u : type672 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> A -> Prop) u t).
Proof. exact (@lem3751566 A u t). Qed.
Lemma lem3751568 {A : Type'} (x' : type684 A) (t : A -> Prop) : (@I ((A -> Prop) -> A) x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (eq_refl (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3751569 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term945 A u x' t) = (term946 A u x' t).
Proof. exact (MK_COMB (@lem3751567 A u t) (@lem3751568 A x' t)). Qed.
Lemma lem3751571 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751572 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751571 A Prop f x). Qed.
Lemma lem3751573 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term946 A u x' t) = (term947 A u x' t).
Proof. exact (@lem3751572 A (@I ((A -> Prop) -> A -> Prop) u t) (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3751574 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term945 A u x' t) = (term947 A u x' t).
Proof. exact (TRANS (@lem3751569 A u x' t) (@lem3751573 A u x' t)). Qed.
Lemma lem3751575 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term944 A u x' t) = (term947 A u x' t).
Proof. exact (TRANS (@lem3751563 A u x' t) (@lem3751574 A u x' t)). Qed.
Lemma lem3751576 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3751581 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751582 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3751581 (A -> Prop) A f x). Qed.
Lemma lem3751584 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem3751582 A x' t). Qed.
Lemma lem3751585 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term925 A x' t) = (term926 A x' t).
Proof. exact (MK_COMB (@lem3751576 A t) (@lem3751584 A x' t)). Qed.
Lemma lem3751587 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751588 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751587 A Prop f x). Qed.
Lemma lem3751589 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term926 A x' t) = (term927 A x' t).
Proof. exact (@lem3751588 A t (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem3751590 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term925 A x' t) = (term927 A x' t).
Proof. exact (TRANS (@lem3751585 A x' t) (@lem3751589 A x' t)). Qed.
Lemma lem3751591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751592 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term954 A x' t) = (term955 A x' t).
Proof. exact (MK_COMB (@lem3751591) (@lem3751590 A x' t)). Qed.
Lemma lem3751593 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term956 A u x' t) = (term957 A u x' t).
Proof. exact (MK_COMB (@lem3751592 A x' t) (@lem3751575 A u x' t)). Qed.
Lemma lem3751594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751595 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term958 A u x' t) = (term959 A u x' t).
Proof. exact (MK_COMB (@lem3751594) (@lem3751593 A u x' t)). Qed.
Lemma lem3751596 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term960 A u x' t) = (term961 A u x' t).
Proof. exact (MK_COMB (@lem3751595 A u x' t) (@lem3751551 A u x' t)). Qed.
Lemma lem3751603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751604 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3751603 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3751605 {A : Type'} (u : type672 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> A -> Prop) u t).
Proof. exact (@lem3751604 A u t). Qed.
Lemma lem3751606 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3751607 {A : Type'} (u : type672 A) (t : A -> Prop) (x : A) : (u t x) = (@I ((A -> Prop) -> A -> Prop) u t x).
Proof. exact (MK_COMB (@lem3751605 A u t) (@lem3751606 A x)). Qed.
Lemma lem3751609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751610 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751609 A Prop f x). Qed.
Lemma lem3751611 {A : Type'} (u : type672 A) (t : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> Prop) u t x) = (term962 A u t x).
Proof. exact (@lem3751610 A (@I ((A -> Prop) -> A -> Prop) u t) x). Qed.
Lemma lem3751613 {A : Type'} (u : type672 A) (t : A -> Prop) (x : A) : (u t x) = (term962 A u t x).
Proof. exact (TRANS (@lem3751607 A u t x) (@lem3751611 A u t x)). Qed.
Lemma lem3751614 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3751619 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751620 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3751619 A Prop f x). Qed.
Lemma lem3751622 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3751620 A t x). Qed.
Lemma lem3751623 {A : Type'} (t : A -> Prop) (x : A) : (term567 A t x) = (term963 A t x).
Proof. exact (MK_COMB (@lem3751614) (@lem3751622 A t x)). Qed.
Lemma lem3751624 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751625 {A : Type'} (t : A -> Prop) (x : A) : (term964 A t x) = (term965 A t x).
Proof. exact (MK_COMB (@lem3751624) (@lem3751623 A t x)). Qed.
Lemma lem3751626 {A : Type'} (u : type672 A) (t : A -> Prop) (x : A) : (term966 A u t x) = (term967 A u t x).
Proof. exact (MK_COMB (@lem3751625 A t x) (@lem3751613 A u t x)). Qed.
Lemma lem3751627 {A : Type'} (u : type672 A) (t : A -> Prop) : (term968 A u t) = (term969 A u t).
Proof. exact (fun_ext (fun x : A => @lem3751626 A u t x)). Qed.
Lemma lem3751628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3751629 {A : Type'} (u : type672 A) (t : A -> Prop) : (term970 A u t) = (term971 A u t).
Proof. exact (MK_COMB (@lem3751628 A) (@lem3751627 A u t)). Qed.
Lemma lem3751630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751631 {A : Type'} (u : type672 A) (t : A -> Prop) : (term972 A u t) = (term973 A u t).
Proof. exact (MK_COMB (@lem3751630) (@lem3751629 A u t)). Qed.
Lemma lem3751632 {A : Type'} (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term974 A u x' t) = (term975 A u x' t).
Proof. exact (MK_COMB (@lem3751631 A u t) (@lem3751596 A u x' t)). Qed.
Lemma lem3751633 {A : Type'} (f : type686 A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3751638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751639 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3751638 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3751641 {A : Type'} (u : type672 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> A -> Prop) u t).
Proof. exact (@lem3751639 A u t). Qed.
Lemma lem3751642 {A : Type'} (f : type686 A) (u : type672 A) (t : A -> Prop) : (term976 A f u t) = (term977 A f u t).
Proof. exact (MK_COMB (@lem3751633 A f) (@lem3751641 A u t)). Qed.
Lemma lem3751644 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751645 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3751644 (A -> Prop) Prop f x). Qed.
Lemma lem3751646 {A : Type'} (f : type686 A) (u : type672 A) (t : A -> Prop) : (term977 A f u t) = (term978 A f u t).
Proof. exact (@lem3751645 A f (@I ((A -> Prop) -> A -> Prop) u t)). Qed.
Lemma lem3751647 {A : Type'} (f : type686 A) (u : type672 A) (t : A -> Prop) : (term976 A f u t) = (term978 A f u t).
Proof. exact (TRANS (@lem3751642 A f u t) (@lem3751646 A f u t)). Qed.
Lemma lem3751648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751649 {A : Type'} (f : type686 A) (u : type672 A) (t : A -> Prop) : (term979 A f u t) = (term980 A f u t).
Proof. exact (MK_COMB (@lem3751648) (@lem3751647 A f u t)). Qed.
Lemma lem3751650 {A : Type'} (f : type686 A) (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term981 A f u x' t) = (term982 A f u x' t).
Proof. exact (MK_COMB (@lem3751649 A f u t) (@lem3751632 A u x' t)). Qed.
Lemma lem3751651 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3751656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3751657 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3751656 (A -> Prop) Prop f x). Qed.
Lemma lem3751659 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3751657 A f t). Qed.
Lemma lem3751660 {A : Type'} (f : type686 A) (t : A -> Prop) : (term736 A f t) = (term937 A f t).
Proof. exact (MK_COMB (@lem3751651) (@lem3751659 A f t)). Qed.
Lemma lem3751661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751662 {A : Type'} (f : type686 A) (t : A -> Prop) : (term683 A f t) = (term938 A f t).
Proof. exact (MK_COMB (@lem3751661) (@lem3751660 A f t)). Qed.
Lemma lem3751663 {A : Type'} (f : type686 A) (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term983 A f u x' t) = (term984 A f u x' t).
Proof. exact (MK_COMB (@lem3751662 A f t) (@lem3751650 A f u x' t)). Qed.
Lemma lem3751664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3751665 {A : Type'} (f : type686 A) (u : type672 A) (x' : type684 A) (t : A -> Prop) : (term985 A f u x' t) = (term986 A f u x' t).
Proof. exact (MK_COMB (@lem3751664) (@lem3751663 A f u x' t)). Qed.
Lemma lem3751666 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term841 A f u s x' t) = (term987 A f u s x' t).
Proof. exact (MK_COMB (@lem3751665 A f u x' t) (@lem3751505 A s x' t)). Qed.
Lemma lem3751667 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x' : type684 A) : (term843 A f u s x') = (term988 A f u s x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3751666 A f u s x' t)). Qed.
Lemma lem3751668 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751669 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x' : type684 A) : (term845 A f u s x') = (term989 A f u s x').
Proof. exact (MK_COMB (@lem3751668 A) (@lem3751667 A f u s x')). Qed.
Lemma lem3751670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3751671 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (x' : type684 A) : (term881 A f u s x') = (term990 A f u s x').
Proof. exact (MK_COMB (@lem3751670) (@lem3751669 A f u s x')). Qed.
Lemma lem3751672 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) : (term883 A u x' s f) = (term991 A u x' s f).
Proof. exact (MK_COMB (@lem3751671 A f u s x') (@lem3751470 A s f)). Qed.
Lemma lem3751673 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : term991 A u x' s f.
Proof. exact (EQ_MP (@lem3751672 A u x' s f) (@lem3751400 A u x' s f h1)). Qed.
Lemma lem3751674 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : term943 A s f.
Proof. exact (proj2 (@lem3751673 A u x' s f h1)). Qed.
Lemma lem3751695 {A : Type'} (s : A -> Prop) (f : type686 A) (x : type684 A) (x' : A -> Prop) : (term939 A f s x x') = (term992 A s f x x').
Proof. exact (@lem19490 (term932 A s x x') (term937 A f x') (term929 A x x')). Qed.
Lemma lem3751696 {A : Type'} (s : A -> Prop) (f : type686 A) (x : type684 A) : (term940 A f s x) = (term993 A s f x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3751695 A s f x x')). Qed.
Lemma lem3751697 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3751699 {A : Type'} (s : A -> Prop) (f : type686 A) (x : type684 A) : (term941 A f s x) = (term994 A s f x).
Proof. exact (MK_COMB (@lem3751697 A) (@lem3751696 A s f x)). Qed.
Lemma lem3751700 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term994 A s f x.
Proof. exact (EQ_MP (@lem3751699 A s f x) (@lem3751451 A f s x h1)). Qed.
Lemma lem3751926 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term995 A s f x _43157.
Proof. exact (@lem3751700 A f s x h1 _43157). Qed.
Lemma lem3751927 {A : Type'} (s : A -> Prop) (f : type686 A) (x : type684 A) (_43157 : A -> Prop) : (term995 A s f x _43157) = (term992 A s f x _43157).
Proof. exact (eq_refl (term995 A s f x _43157)). Qed.
Lemma lem3751928 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term992 A s f x _43157.
Proof. exact (EQ_MP (@lem3751927 A s f x _43157) (@lem3751926 A _43157 f s x h1)). Qed.
Lemma lem3752092 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term996 A f s x _43157.
Proof. exact (proj1 (@lem3751928 A _43157 f s x h1)). Qed.
Lemma lem3752098 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term997 A f x _43157.
Proof. exact (proj2 (@lem3751928 A _43157 f s x h1)). Qed.
Lemma lem3752100 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : @I ((A -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem3751674 A u x' s f h1)). Qed.
Lemma lem3752101 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : term998 A f s.
Proof. exact (fun h0 : term937 A f s => @lem3752100 A u x' s f h1). Qed.
Lemma lem3752103 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3752104 {A : Type'} (f : type686 A) (s : A -> Prop) : (term998 A f s) = (@I ((A -> Prop) -> Prop) f s).
Proof. exact (@lem3752103 (@I ((A -> Prop) -> Prop) f s)). Qed.
Lemma lem3752105 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : @I ((A -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem3752104 A f s) (@lem3752101 A u x' s f h1)). Qed.
Lemma lem3752107 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : @I ((A -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem3751674 A u x' s f h1)). Qed.
Lemma lem3752108 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : term998 A f s.
Proof. exact (fun h0 : term937 A f s => @lem3752107 A u x' s f h1). Qed.
Lemma lem3752110 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3752111 {A : Type'} (f : type686 A) (s : A -> Prop) : (term998 A f s) = (@I ((A -> Prop) -> Prop) f s).
Proof. exact (@lem3752110 (@I ((A -> Prop) -> Prop) f s)). Qed.
Lemma lem3752112 {A : Type'} (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term883 A u x' s f) : @I ((A -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem3752111 A f s) (@lem3752108 A u x' s f h1)). Qed.
Lemma lem3752118 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3752119 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43157 : A -> Prop) : (term996 A f s x _43157) = (term999 A s x f _43157).
Proof. exact (@lem3752118 (term932 A s x _43157) (term937 A f _43157)). Qed.
Lemma lem3752125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3752126 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43157 : A -> Prop) : (term1000 A f s x _43157) = (term1001 A s x f _43157).
Proof. exact (MK_COMB (@lem3752125) (@lem3752119 A s x f _43157)). Qed.
Lemma lem3752132 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43157 : A -> Prop) : (term999 A s x f _43157) = (term999 A s x f _43157).
Proof. exact (eq_refl (term999 A s x f _43157)). Qed.
Lemma lem3752133 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43157 : A -> Prop) : ((term996 A f s x _43157) = (term999 A s x f _43157)) = ((term999 A s x f _43157) = (term999 A s x f _43157)).
Proof. exact (MK_COMB (@lem3752126 A s x f _43157) (@lem3752132 A s x f _43157)). Qed.
Lemma lem3752135 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3752136 (x : Prop) : (x = x) = True.
Proof. exact (@lem3752135 Prop x). Qed.
Lemma lem3752137 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43157 : A -> Prop) : ((term999 A s x f _43157) = (term999 A s x f _43157)) = True.
Proof. exact (@lem3752136 (term999 A s x f _43157)). Qed.
Lemma lem3752138 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43157 : A -> Prop) : ((term996 A f s x _43157) = (term999 A s x f _43157)) = True.
Proof. exact (TRANS (@lem3752133 A s x f _43157) (@lem3752137 A s x f _43157)). Qed.
Lemma lem3752139 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43157 : A -> Prop) : True = ((term996 A f s x _43157) = (term999 A s x f _43157)).
Proof. exact (SYM (@lem3752138 A s x f _43157)). Qed.
Lemma lem3752140 {A : Type'} (s : A -> Prop) (x : type684 A) (f : type686 A) (_43157 : A -> Prop) : (term996 A f s x _43157) = (term999 A s x f _43157).
Proof. exact (EQ_MP (@lem3752139 A s x f _43157) (@lem0)). Qed.
Lemma lem3752141 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term999 A s x f _43157.
Proof. exact (EQ_MP (@lem3752140 A s x f _43157) (@lem3752092 A _43157 f s x h1)). Qed.
Lemma lem3752143 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3752144 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (_43157 : A -> Prop) : (term999 A s x f _43157) = (term1002 A f s x _43157).
Proof. exact (@lem3752143 (term937 A f _43157) (term932 A s x _43157)). Qed.
Lemma lem3752146 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3752147 {A : Type'} (f : type686 A) (_43157 : A -> Prop) : (term1003 A f _43157) = (@I ((A -> Prop) -> Prop) f _43157).
Proof. exact (@lem3752146 (@I ((A -> Prop) -> Prop) f _43157)). Qed.
Lemma lem3752148 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3752149 {A : Type'} (f : type686 A) (_43157 : A -> Prop) : (term1004 A f _43157) = (term1005 A f _43157).
Proof. exact (MK_COMB (@lem3752148) (@lem3752147 A f _43157)). Qed.
Lemma lem3752150 {A : Type'} (s : A -> Prop) (x : type684 A) (_43157 : A -> Prop) : (term932 A s x _43157) = (term932 A s x _43157).
Proof. exact (eq_refl (term932 A s x _43157)). Qed.
Lemma lem3752151 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (_43157 : A -> Prop) : (term1002 A f s x _43157) = (term1006 A f s x _43157).
Proof. exact (MK_COMB (@lem3752149 A f _43157) (@lem3752150 A s x _43157)). Qed.
Lemma lem3752152 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (_43157 : A -> Prop) : (term999 A s x f _43157) = (term1006 A f s x _43157).
Proof. exact (TRANS (@lem3752144 A f s x _43157) (@lem3752151 A f s x _43157)). Qed.
Lemma lem3752155 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term1006 A f s x _43157.
Proof. exact (EQ_MP (@lem3752152 A f s x _43157) (@lem3752141 A _43157 f s x h1)). Qed.
Lemma lem3752156 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term1006 A f s x _43157.
Proof. exact (@lem3752155 A _43157 f s x h1). Qed.
Lemma lem3752157 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term1007 A f x s.
Proof. exact (@lem3752156 A s f s x h1). Qed.
Lemma lem3752160 {A : Type'} (x : type684 A) (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term883 A u x' s f) : term927 A x s.
Proof. exact (@lem3752157 A f s x h1 (@lem3752112 A u x' s f h2)). Qed.
Lemma lem3752161 {A : Type'} (x : type684 A) (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term883 A u x' s f) : term1008 A x s.
Proof. exact (fun h0 : term929 A x s => @lem3752160 A x u x' s f h1 h2). Qed.
Lemma lem3752163 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3752164 {A : Type'} (x : type684 A) (s : A -> Prop) : (term1008 A x s) = (term927 A x s).
Proof. exact (@lem3752163 (term927 A x s)). Qed.
Lemma lem3752165 {A : Type'} (x : type684 A) (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term883 A u x' s f) : term927 A x s.
Proof. exact (EQ_MP (@lem3752164 A x s) (@lem3752161 A x u x' s f h1 h2)). Qed.
Lemma lem3752167 (a : Prop) (b : Prop) : (term1009 a b) = (term1010 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3752168 {A : Type'} (f : type686 A) (x : type684 A) (_43157 : A -> Prop) : (term997 A f x _43157) = (term1011 A f x _43157).
Proof. exact (@lem3752167 (@I ((A -> Prop) -> Prop) f _43157) (term927 A x _43157)). Qed.
Lemma lem3752170 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3752171 {A : Type'} (f : type686 A) (x : type684 A) (_43157 : A -> Prop) : (term1011 A f x _43157) = (term1012 A f x _43157).
Proof. exact (@lem3752170 (term1013 A f x _43157)). Qed.
Lemma lem3752172 {A : Type'} (f : type686 A) (x : type684 A) (_43157 : A -> Prop) : (term997 A f x _43157) = (term1012 A f x _43157).
Proof. exact (TRANS (@lem3752168 A f x _43157) (@lem3752171 A f x _43157)). Qed.
Lemma lem3752174 {A : Type'} (x : type684 A) (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term883 A u x' s f) : term1013 A f x s.
Proof. exact (conj (@lem3752105 A u x' s f h2) (@lem3752165 A x u x' s f h1 h2)). Qed.
Lemma lem3752176 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term1012 A f x _43157.
Proof. exact (EQ_MP (@lem3752172 A f x _43157) (@lem3752098 A _43157 f s x h1)). Qed.
Lemma lem3752177 {A : Type'} (_43157 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term1012 A f x _43157.
Proof. exact (@lem3752176 A _43157 f s x h1). Qed.
Lemma lem3752178 {A : Type'} (f : type686 A) (s : A -> Prop) (x : type684 A) (h1 : term921 A f s x) : term1012 A f x s.
Proof. exact (@lem3752177 A s f s x h1). Qed.
Lemma lem3752181 {A : Type'} (x : type684 A) (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term883 A u x' s f) : False.
Proof. exact (@lem3752178 A f s x h1 (@lem3752174 A x u x' s f h1 h2)). Qed.
Lemma lem3752182 {A : Type'} (x : type684 A) (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term883 A u x' s f) : term577.
Proof. exact (fun h0 : ~ False => @lem3752181 A x u x' s f h1 h2). Qed.
Lemma lem3752184 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3752185 : term577 = False.
Proof. exact (@lem3752184 False). Qed.
Lemma lem3752186 {A : Type'} (x : type684 A) (u : type672 A) (x' : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term883 A u x' s f) : False.
Proof. exact (EQ_MP (@lem3752185) (@lem3752182 A x u x' s f h1 h2)). Qed.
Lemma lem3752187 {A : Type'} (x : type684 A) (u : type672 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term886 A u s f) : False.
Proof. exact (ex_elim (@lem3751399 A u s f h2) (fun x' : type684 A => fun h0 : term885 A u s f x' => @lem3752186 A x u x' s f h1 h0)). Qed.
Lemma lem3752188 {A : Type'} (x : type684 A) (s : A -> Prop) (f : type686 A) (h1 : term921 A f s x) (h2 : term631 A s f) : False.
Proof. exact (ex_elim (@lem3751237 A s f h2) (fun u : type672 A => fun h0 : term887 A s f u => @lem3752187 A x u s f h1 h0)). Qed.
Lemma lem3752189 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term649 A f s) (h2 : term631 A s f) : False.
Proof. exact (ex_elim (@lem3751397 A f s h1) (fun x : type684 A => fun h0 : term923 A f s x => @lem3752188 A x s f h0 h2)). Qed.
Lemma lem3752190 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term631 A s f) : term1014 A f s.
Proof. exact (fun h0 : term649 A f s => @lem3752189 A s f h0 h1). Qed.
Lemma lem3752191 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1014 A f s) = (term650 A f s).
Proof. exact (@lem69 (term649 A f s)). Qed.
Lemma lem3752192 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term631 A s f) : term650 A f s.
Proof. exact (EQ_MP (@lem3752191 A f s) (@lem3752190 A s f h1)). Qed.
Lemma lem3752193 {A : Type'} (f : type686 A) (s : A -> Prop) : term651 A f s.
Proof. exact (fun h0 : term631 A s f => @lem3752192 A s f h0). Qed.
Lemma lem3752198 {A : Type'} (s : A -> Prop) : term661 A s.
Proof. exact (fun f : type686 A => @lem3752193 A f s). Qed.
Lemma lem3752203 {A : Type'} : term665 A.
Proof. exact (fun s : A -> Prop => @lem3752198 A s). Qed.
Lemma lem3752204 {A : Type'} : term664 A.
Proof. exact (EQ_MP (@lem3750665 A) (@lem3752203 A)). Qed.
Lemma lem3752205 {A : Type'} (s : A -> Prop) : term1015 A s.
Proof. exact (@lem3752204 A s). Qed.
Lemma lem3752206 {A : Type'} (s : A -> Prop) : (term1015 A s) = (term660 A s).
Proof. exact (eq_refl (term1015 A s)). Qed.
Lemma lem3752207 {A : Type'} (s : A -> Prop) : term660 A s.
Proof. exact (EQ_MP (@lem3752206 A s) (@lem3752205 A s)). Qed.
Lemma lem3752208 {A : Type'} (s : A -> Prop) (f : type686 A) : term1016 A s f.
Proof. exact (@lem3752207 A s f). Qed.
Lemma lem3752209 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1016 A s f) = (term652 A f s).
Proof. exact (eq_refl (term1016 A s f)). Qed.
Lemma lem3752210 {A : Type'} (f : type686 A) (s : A -> Prop) : term652 A f s.
Proof. exact (EQ_MP (@lem3752209 A f s) (@lem3752208 A s f)). Qed.
Lemma lem3752212 {A : Type'} (f : type686 A) (s : A -> Prop) : term652 A f s.
Proof. exact (@lem3750372 A f s (@lem3752210 A f s)). Qed.
Lemma lem3752213 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term653 A f s) : False.
Proof. exact (@lem3752212 A f s (@lem3750356 A f s h1)). Qed.
Lemma lem3752214 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term653 A f s) : (term653 A f s) = False.
Proof. exact (prop_ext (fun h2 : term653 A f s => @lem3752213 A f s h1) (fun h2 : False => @lem3750356 A f s h1)). Qed.
Lemma lem3752215 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term653 A f s) : False.
Proof. exact (EQ_MP (@lem3752214 A f s h1) (@lem3750356 A f s h1)). Qed.
Lemma lem3752216 {A : Type'} (f : type686 A) (s : A -> Prop) : term652 A f s.
Proof. exact (fun h0 : term653 A f s => @lem3752215 A f s h0). Qed.
Lemma lem3752217 {A : Type'} (f : type686 A) (s : A -> Prop) : term651 A f s.
Proof. exact (EQ_MP (@lem3750355 A f s) (@lem3752216 A f s)). Qed.
Lemma lem3752218 {A : Type'} (f : type686 A) (s : A -> Prop) : term617 A f s.
Proof. exact (EQ_MP (@lem3750351 A f s) (@lem3752217 A f s)). Qed.
Lemma lem3752219 {A : Type'} (f : type686 A) (s : A -> Prop) : term616 A f s.
Proof. exact (EQ_MP (@lem3750089 A f s) (@lem3752218 A f s)). Qed.
Lemma lem3752220 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term341 A f s.
Proof. exact (@lem3752219 A f s (@lem3749912 A s f h1 h2 h3)). Qed.
Lemma lem3752222 (p : Prop) : p = (term401 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3752223 {A : Type'} (f : type686 A) (s : A -> Prop) : (term333 A f s) = (term1017 A f s).
Proof. exact (@lem3752222 (term333 A f s)). Qed.
Lemma lem3752224 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1017 A f s) = (term333 A f s).
Proof. exact (SYM (@lem3752223 A f s)). Qed.
Lemma lem3752225 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1018 A f s) : term1018 A f s.
Proof. exact (h1). Qed.
Lemma lem3752226 {A : Type'} : term1019 A.
Proof. exact (@lem3224151 A). Qed.
Lemma lem3752227 {A : Type'} : term1020 A.
Proof. exact (@lem3227973 A). Qed.
Lemma lem3752229 {A : Type'} : term1021 A.
Proof. exact (@lem3195125 A). Qed.
Lemma lem3752233 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1022 A f s) : term1022 A f s.
Proof. exact (h1). Qed.
Lemma lem3752234 {A : Type'} (f : type686 A) (s : A -> Prop) : term1023 A f s.
Proof. exact (fun h0 : term1022 A f s => @lem3752233 A f s h0). Qed.
Lemma lem3752235 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1023 A f s) : term1023 A f s.
Proof. exact (h1). Qed.
Lemma lem3752236 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1022 A f s) : term1022 A f s.
Proof. exact (h1). Qed.
Lemma lem3752237 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1022 A f s) (h2 : term1023 A f s) : term1022 A f s.
Proof. exact (@lem3752235 A f s h2 (@lem3752236 A f s h1)). Qed.
Lemma lem3752238 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1022 A f s) : term1024 A f s.
Proof. exact (fun h0 : term1023 A f s => @lem3752237 A f s h1 h0). Qed.
Lemma lem3752239 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1023 A f s) : term1023 A f s.
Proof. exact (h1). Qed.
Lemma lem3752240 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1022 A f s) (h2 : term1023 A f s) : term1022 A f s.
Proof. exact (@lem3752238 A f s h1 (@lem3752239 A f s h2)). Qed.
Lemma lem3752241 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1023 A f s) : term1023 A f s.
Proof. exact (fun h0 : term1022 A f s => @lem3752240 A f s h0 h1). Qed.
Lemma lem3752242 {A : Type'} (f : type686 A) (s : A -> Prop) : term1025 A f s.
Proof. exact (fun h0 : term1023 A f s => @lem3752241 A f s h0). Qed.
Lemma lem3752245 {A : Type'} (f : type686 A) (s : A -> Prop) : term1023 A f s.
Proof. exact (@lem3752242 A f s (@lem3752234 A f s)). Qed.
Lemma lem3752246 {A : Type'} (f : type686 A) (s : A -> Prop) : term1023 A f s.
Proof. exact (@lem3752245 A f s). Qed.
Lemma lem3752412 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3752413 {A : Type'} : (term1026 A) = (term1027 A).
Proof. exact (@lem3752412 (term1019 A)). Qed.
Lemma lem3752430 {A : Type'} : (term1028 A) = (term1028 A).
Proof. exact (eq_refl (term1028 A)). Qed.
Lemma lem3752431 {A : Type'} : (term1029 A) = (term1030 A).
Proof. exact (MK_COMB (@lem3752430 A) (@lem3752413 A)). Qed.
Lemma lem3752434 {A : Type'} : (term1031 A) = (term1031 A).
Proof. exact (eq_refl (term1031 A)). Qed.
Lemma lem3752435 {A : Type'} : (term1032 A) = (term1033 A).
Proof. exact (MK_COMB (@lem3752434 A) (@lem3752431 A)). Qed.
Lemma lem3752438 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1034 A f s) = (term1034 A f s).
Proof. exact (eq_refl (term1034 A f s)). Qed.
Lemma lem3752439 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1035 A f s) = (term1036 A f s).
Proof. exact (MK_COMB (@lem3752438 A f s) (@lem3752435 A)). Qed.
Lemma lem3752442 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1037 A f s) = (term1037 A f s).
Proof. exact (eq_refl (term1037 A f s)). Qed.
Lemma lem3752443 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1038 A f s) = (term1039 A f s).
Proof. exact (MK_COMB (@lem3752442 A f s) (@lem3752439 A f s)). Qed.
Lemma lem3752446 {A : Type'} (s : A -> Prop) (f : type686 A) : (term583 A s f) = (term583 A s f).
Proof. exact (eq_refl (term583 A s f)). Qed.
Lemma lem3752447 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1040 A f s) = (term1041 A f s).
Proof. exact (MK_COMB (@lem3752446 A s f) (@lem3752443 A f s)). Qed.
Lemma lem3752450 {A : Type'} (f : type686 A) : (term184 A f) = (term184 A f).
Proof. exact (eq_refl (term184 A f)). Qed.
Lemma lem3752451 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1022 A f s) = (term1042 A f s).
Proof. exact (MK_COMB (@lem3752450 A f) (@lem3752447 A f s)). Qed.
Lemma lem3752454 {A : Type'} (s : A -> Prop) : (term1043 A s) = (term1044 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3752451 A f s)). Qed.
Lemma lem3752455 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3752456 {A : Type'} (s : A -> Prop) : (term1045 A s) = (term1046 A s).
Proof. exact (MK_COMB (@lem3752455 A) (@lem3752454 A s)). Qed.
Lemma lem3752461 {A : Type'} : (term1047 A) = (term1048 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3752456 A s)). Qed.
Lemma lem3752462 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752471 {A : Type'} : (term1049 A) = (term1050 A).
Proof. exact (MK_COMB (@lem3752462 A) (@lem3752461 A)). Qed.
Lemma lem3752480 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term1051 A t s u) = (term1051 A t s u).
Proof. exact (eq_refl (term1051 A t s u)). Qed.
Lemma lem3752481 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1052 A t s) = (term1052 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752480 A t s u)). Qed.
Lemma lem3752482 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752483 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1053 A t s) = (term1053 A t s).
Proof. exact (MK_COMB (@lem3752482 A) (@lem3752481 A t s)). Qed.
Lemma lem3752484 {A : Type'} (s : A -> Prop) : (term1054 A s) = (term1054 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752483 A t s)). Qed.
Lemma lem3752485 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752486 {A : Type'} (s : A -> Prop) : (term1055 A s) = (term1055 A s).
Proof. exact (MK_COMB (@lem3752485 A) (@lem3752484 A s)). Qed.
Lemma lem3752487 {A : Type'} : (term1056 A) = (term1056 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3752486 A s)). Qed.
Lemma lem3752488 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752489 {A : Type'} : (term1019 A) = (term1019 A).
Proof. exact (MK_COMB (@lem3752488 A) (@lem3752487 A)). Qed.
Lemma lem3752490 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3752491 {A : Type'} : (term1027 A) = (term1027 A).
Proof. exact (MK_COMB (@lem3752490) (@lem3752489 A)). Qed.
Lemma lem3752500 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term1057 A t s u) = (term1057 A t s u).
Proof. exact (eq_refl (term1057 A t s u)). Qed.
Lemma lem3752501 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1058 A t s) = (term1058 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752500 A t s u)). Qed.
Lemma lem3752502 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752503 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1059 A t s) = (term1059 A t s).
Proof. exact (MK_COMB (@lem3752502 A) (@lem3752501 A t s)). Qed.
Lemma lem3752504 {A : Type'} (s : A -> Prop) : (term1060 A s) = (term1060 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752503 A t s)). Qed.
Lemma lem3752505 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752506 {A : Type'} (s : A -> Prop) : (term1061 A s) = (term1061 A s).
Proof. exact (MK_COMB (@lem3752505 A) (@lem3752504 A s)). Qed.
Lemma lem3752507 {A : Type'} : (term1062 A) = (term1062 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3752506 A s)). Qed.
Lemma lem3752508 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752509 {A : Type'} : (term1020 A) = (term1020 A).
Proof. exact (MK_COMB (@lem3752508 A) (@lem3752507 A)). Qed.
Lemma lem3752510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3752511 {A : Type'} : (term1028 A) = (term1028 A).
Proof. exact (MK_COMB (@lem3752510) (@lem3752509 A)). Qed.
Lemma lem3752512 {A : Type'} : (term1030 A) = (term1030 A).
Proof. exact (MK_COMB (@lem3752511 A) (@lem3752491 A)). Qed.
Lemma lem3752523 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@PSUBSET A s t) = (term345 A s t)) = ((@PSUBSET A s t) = (term345 A s t)).
Proof. exact (eq_refl ((@PSUBSET A s t) = (term345 A s t))). Qed.
Lemma lem3752524 {A : Type'} (s : A -> Prop) : (term1063 A s) = (term1063 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752523 A s t)). Qed.
Lemma lem3752525 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752526 {A : Type'} (s : A -> Prop) : (term1064 A s) = (term1064 A s).
Proof. exact (MK_COMB (@lem3752525 A) (@lem3752524 A s)). Qed.
Lemma lem3752527 {A : Type'} : (term1065 A) = (term1065 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3752526 A s)). Qed.
Lemma lem3752528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752529 {A : Type'} : (term1021 A) = (term1021 A).
Proof. exact (MK_COMB (@lem3752528 A) (@lem3752527 A)). Qed.
Lemma lem3752530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3752531 {A : Type'} : (term1031 A) = (term1031 A).
Proof. exact (MK_COMB (@lem3752530) (@lem3752529 A)). Qed.
Lemma lem3752532 {A : Type'} : (term1033 A) = (term1033 A).
Proof. exact (MK_COMB (@lem3752531 A) (@lem3752512 A)). Qed.
Lemma lem3752541 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term326 A f s t t') = (term326 A f s t t').
Proof. exact (eq_refl (term326 A f s t t')). Qed.
Lemma lem3752542 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term327 A f s t) = (term327 A f s t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3752541 A f s t t')). Qed.
Lemma lem3752543 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3752544 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term328 A f s t) = (term328 A f s t).
Proof. exact (MK_COMB (@lem3752543 A) (@lem3752542 A f s t)). Qed.
Lemma lem3752551 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term280 A f s t) = (term280 A f s t).
Proof. exact (eq_refl (term280 A f s t)). Qed.
Lemma lem3752552 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term331 A f s t) = (term331 A f s t).
Proof. exact (MK_COMB (@lem3752551 A f s t) (@lem3752544 A f s t)). Qed.
Lemma lem3752553 {A : Type'} (f : type686 A) (s : A -> Prop) : (term332 A f s) = (term332 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752552 A f s t)). Qed.
Lemma lem3752554 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752555 {A : Type'} (f : type686 A) (s : A -> Prop) : (term333 A f s) = (term333 A f s).
Proof. exact (MK_COMB (@lem3752554 A) (@lem3752553 A f s)). Qed.
Lemma lem3752556 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3752557 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1018 A f s) = (term1018 A f s).
Proof. exact (MK_COMB (@lem3752556) (@lem3752555 A f s)). Qed.
Lemma lem3752558 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3752559 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1034 A f s) = (term1034 A f s).
Proof. exact (MK_COMB (@lem3752558) (@lem3752557 A f s)). Qed.
Lemma lem3752560 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1036 A f s) = (term1036 A f s).
Proof. exact (MK_COMB (@lem3752559 A f s) (@lem3752532 A)). Qed.
Lemma lem3752561 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (@SUBSET A s t).
Proof. exact (eq_refl (@SUBSET A s t)). Qed.
Lemma lem3752568 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term584 A f t u) = (term584 A f t u).
Proof. exact (eq_refl (term584 A f t u)). Qed.
Lemma lem3752569 {A : Type'} (f : type686 A) (t : A -> Prop) : (term586 A f t) = (term586 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752568 A f t u)). Qed.
Lemma lem3752570 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752571 {A : Type'} (f : type686 A) (t : A -> Prop) : (term64 A f t) = (term64 A f t).
Proof. exact (MK_COMB (@lem3752570 A) (@lem3752569 A f t)). Qed.
Lemma lem3752574 {A : Type'} (t : A -> Prop) (f : type686 A) : (term65 A t f) = (term65 A t f).
Proof. exact (eq_refl (term65 A t f)). Qed.
Lemma lem3752575 {A : Type'} (f : type686 A) (t : A -> Prop) : (term67 A f t) = (term67 A f t).
Proof. exact (MK_COMB (@lem3752574 A t f) (@lem3752571 A f t)). Qed.
Lemma lem3752576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3752577 {A : Type'} (f : type686 A) (t : A -> Prop) : (term125 A f t) = (term125 A f t).
Proof. exact (MK_COMB (@lem3752576) (@lem3752575 A f t)). Qed.
Lemma lem3752578 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term139 A f s t) = (term139 A f s t).
Proof. exact (MK_COMB (@lem3752577 A f t) (@lem3752561 A s t)). Qed.
Lemma lem3752579 {A : Type'} (f : type686 A) (s : A -> Prop) : (term140 A f s) = (term140 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752578 A f s t)). Qed.
Lemma lem3752580 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3752581 {A : Type'} (f : type686 A) (s : A -> Prop) : (term141 A f s) = (term141 A f s).
Proof. exact (MK_COMB (@lem3752580 A) (@lem3752579 A f s)). Qed.
Lemma lem3752582 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3752583 {A : Type'} (f : type686 A) (s : A -> Prop) : (term143 A f s) = (term143 A f s).
Proof. exact (MK_COMB (@lem3752582) (@lem3752581 A f s)). Qed.
Lemma lem3752584 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3752585 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1037 A f s) = (term1037 A f s).
Proof. exact (MK_COMB (@lem3752584) (@lem3752583 A f s)). Qed.
Lemma lem3752586 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1039 A f s) = (term1039 A f s).
Proof. exact (MK_COMB (@lem3752585 A f s) (@lem3752560 A f s)). Qed.
Lemma lem3752589 {A : Type'} (s : A -> Prop) (f : type686 A) : (term583 A s f) = (term583 A s f).
Proof. exact (eq_refl (term583 A s f)). Qed.
Lemma lem3752590 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1041 A f s) = (term1041 A f s).
Proof. exact (MK_COMB (@lem3752589 A s f) (@lem3752586 A f s)). Qed.
Lemma lem3752593 {A : Type'} (f : type686 A) : (term184 A f) = (term184 A f).
Proof. exact (eq_refl (term184 A f)). Qed.
Lemma lem3752594 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1042 A f s) = (term1042 A f s).
Proof. exact (MK_COMB (@lem3752593 A f) (@lem3752590 A f s)). Qed.
Lemma lem3752595 {A : Type'} (s : A -> Prop) : (term1044 A s) = (term1044 A s).
Proof. exact (fun_ext (fun f : type686 A => @lem3752594 A f s)). Qed.
Lemma lem3752596 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3752597 {A : Type'} (s : A -> Prop) : (term1046 A s) = (term1046 A s).
Proof. exact (MK_COMB (@lem3752596 A) (@lem3752595 A s)). Qed.
Lemma lem3752598 {A : Type'} : (term1048 A) = (term1048 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3752597 A s)). Qed.
Lemma lem3752599 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752600 {A : Type'} : (term1050 A) = (term1050 A).
Proof. exact (MK_COMB (@lem3752599 A) (@lem3752598 A)). Qed.
Lemma lem3752723 {A : Type'} : (term1049 A) = (term1050 A).
Proof. exact (TRANS (@lem3752471 A) (@lem3752600 A)). Qed.
Lemma lem3752724 {A : Type'} : (term1050 A) = (term1049 A).
Proof. exact (SYM (@lem3752723 A)). Qed.
Lemma lem3752727 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term143 A f s) : term143 A f s.
Proof. exact (h1). Qed.
Lemma lem3752728 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1018 A f s) : term1018 A f s.
Proof. exact (h1). Qed.
Lemma lem3752729 {A : Type'} (h1 : term1021 A) : term1021 A.
Proof. exact (h1). Qed.
Lemma lem3752730 {A : Type'} (h1 : term1020 A) : term1020 A.
Proof. exact (h1). Qed.
Lemma lem3752748 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term1066 A t u) = (@PSUBSET A t u).
Proof. exact (@lem16933 (@PSUBSET A t u)). Qed.
Lemma lem3752750 {A : Type'} (u : A -> Prop) (f : type686 A) : (term65 A u f) = (term65 A u f).
Proof. exact (eq_refl (term65 A u f)). Qed.
Lemma lem3752751 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1067 A f t u) = (term1068 A f t u).
Proof. exact (MK_COMB (@lem3752750 A u f) (@lem3752748 A t u)). Qed.
Lemma lem3752752 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1069 A f t u) = (term1067 A f t u).
Proof. exact (@lem17362 (@IN (A -> Prop) u f) (term581 A t u)). Qed.
Lemma lem3752753 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1069 A f t u) = (term1068 A f t u).
Proof. exact (TRANS (@lem3752752 A f t u) (@lem3752751 A f t u)). Qed.
Lemma lem3752754 {A : Type'} (P : type686 A) : (term674 A P) = (term675 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3752755 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1070 A f t) = (term1071 A f t).
Proof. exact (@lem3752754 A (term586 A f t)). Qed.
Lemma lem3752756 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1072 A f t u) = (term584 A f t u).
Proof. exact (eq_refl (term1072 A f t u)). Qed.
Lemma lem3752757 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3752758 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1073 A f t u) = (term1069 A f t u).
Proof. exact (MK_COMB (@lem3752757) (@lem3752756 A f t u)). Qed.
Lemma lem3752759 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1073 A f t u) = (term1068 A f t u).
Proof. exact (TRANS (@lem3752758 A f t u) (@lem3752753 A f t u)). Qed.
Lemma lem3752760 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1074 A f t) = (term1075 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752759 A f t u)). Qed.
Lemma lem3752761 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3752762 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1071 A f t) = (term1076 A f t).
Proof. exact (MK_COMB (@lem3752761 A) (@lem3752760 A f t)). Qed.
Lemma lem3752763 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1070 A f t) = (term1076 A f t).
Proof. exact (TRANS (@lem3752755 A f t) (@lem3752762 A f t)). Qed.
Lemma lem3752765 {A : Type'} (t : A -> Prop) (f : type686 A) : (term1077 A t f) = (term1077 A t f).
Proof. exact (eq_refl (term1077 A t f)). Qed.
Lemma lem3752766 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1078 A f t) = (term1079 A f t).
Proof. exact (MK_COMB (@lem3752765 A t f) (@lem3752763 A f t)). Qed.
Lemma lem3752767 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1080 A f t) = (term1078 A f t).
Proof. exact (@lem17045 (@IN (A -> Prop) t f) (term64 A f t)). Qed.
Lemma lem3752768 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1080 A f t) = (term1079 A f t).
Proof. exact (TRANS (@lem3752767 A f t) (@lem3752766 A f t)). Qed.
Lemma lem3752769 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1081 A s t) = (term1081 A s t).
Proof. exact (eq_refl (term1081 A s t)). Qed.
Lemma lem3752770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3752771 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1082 A f t) = (term1083 A f t).
Proof. exact (MK_COMB (@lem3752770) (@lem3752768 A f t)). Qed.
Lemma lem3752772 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1084 A f s t) = (term1085 A f s t).
Proof. exact (MK_COMB (@lem3752771 A f t) (@lem3752769 A s t)). Qed.
Lemma lem3752773 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1086 A f s t) = (term1084 A f s t).
Proof. exact (@lem17045 (term67 A f t) (@SUBSET A s t)). Qed.
Lemma lem3752774 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1086 A f s t) = (term1085 A f s t).
Proof. exact (TRANS (@lem3752773 A f s t) (@lem3752772 A f s t)). Qed.
Lemma lem3752775 {A : Type'} (P : type686 A) : (term692 A P) = (term693 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3752776 {A : Type'} (f : type686 A) (s : A -> Prop) : (term143 A f s) = (term1087 A f s).
Proof. exact (@lem3752775 A (term140 A f s)). Qed.
Lemma lem3752777 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1088 A f s t) = (term139 A f s t).
Proof. exact (eq_refl (term1088 A f s t)). Qed.
Lemma lem3752778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3752779 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1089 A f s t) = (term1086 A f s t).
Proof. exact (MK_COMB (@lem3752778) (@lem3752777 A f s t)). Qed.
Lemma lem3752780 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1089 A f s t) = (term1085 A f s t).
Proof. exact (TRANS (@lem3752779 A f s t) (@lem3752774 A f s t)). Qed.
Lemma lem3752781 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1090 A f s) = (term1091 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752780 A f s t)). Qed.
Lemma lem3752782 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752783 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1087 A f s) = (term1092 A f s).
Proof. exact (MK_COMB (@lem3752782 A) (@lem3752781 A f s)). Qed.
Lemma lem3752784 {A : Type'} (f : type686 A) (s : A -> Prop) : (term143 A f s) = (term1092 A f s).
Proof. exact (TRANS (@lem3752776 A f s) (@lem3752783 A f s)). Qed.
Lemma lem3752883 {A : Type'} (P : Prop) (Q : A -> Prop) : (term730 A P Q) = (term731 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3752884 {A : Type'} (P : Prop) (Q : type686 A) : (term732 A P Q) = (term733 A P Q).
Proof. exact (@lem3752883 (A -> Prop) P Q). Qed.
Lemma lem3752885 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1093 A f t) = (term1094 A f t).
Proof. exact (@lem3752884 A (term1095 A t f) (term1075 A f t)). Qed.
Lemma lem3752886 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1096 A f t u) = (term1068 A f t u).
Proof. exact (eq_refl (term1096 A f t u)). Qed.
Lemma lem3752887 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1097 A f t) = (term1075 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752886 A f t u)). Qed.
Lemma lem3752888 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3752889 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1098 A f t) = (term1076 A f t).
Proof. exact (MK_COMB (@lem3752888 A) (@lem3752887 A f t)). Qed.
Lemma lem3752890 {A : Type'} (t : A -> Prop) (f : type686 A) : (term1077 A t f) = (term1077 A t f).
Proof. exact (eq_refl (term1077 A t f)). Qed.
Lemma lem3752891 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1093 A f t) = (term1079 A f t).
Proof. exact (MK_COMB (@lem3752890 A t f) (@lem3752889 A f t)). Qed.
Lemma lem3752892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3752893 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1099 A f t) = (term1100 A f t).
Proof. exact (MK_COMB (@lem3752892) (@lem3752891 A f t)). Qed.
Lemma lem3752894 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1096 A f t u) = (term1068 A f t u).
Proof. exact (eq_refl (term1096 A f t u)). Qed.
Lemma lem3752895 {A : Type'} (t : A -> Prop) (f : type686 A) : (term1077 A t f) = (term1077 A t f).
Proof. exact (eq_refl (term1077 A t f)). Qed.
Lemma lem3752896 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1101 A f t u) = (term1102 A f t u).
Proof. exact (MK_COMB (@lem3752895 A t f) (@lem3752894 A f t u)). Qed.
Lemma lem3752897 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1103 A f t) = (term1104 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752896 A f t u)). Qed.
Lemma lem3752898 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3752899 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1094 A f t) = (term1105 A f t).
Proof. exact (MK_COMB (@lem3752898 A) (@lem3752897 A f t)). Qed.
Lemma lem3752900 {A : Type'} (f : type686 A) (t : A -> Prop) : ((term1093 A f t) = (term1094 A f t)) = ((term1079 A f t) = (term1105 A f t)).
Proof. exact (MK_COMB (@lem3752893 A f t) (@lem3752899 A f t)). Qed.
Lemma lem3752901 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1079 A f t) = (term1105 A f t).
Proof. exact (EQ_MP (@lem3752900 A f t) (@lem3752885 A f t)). Qed.
Lemma lem3752902 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3752903 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1083 A f t) = (term1106 A f t).
Proof. exact (MK_COMB (@lem3752902) (@lem3752901 A f t)). Qed.
Lemma lem3752904 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1081 A s t) = (term1081 A s t).
Proof. exact (eq_refl (term1081 A s t)). Qed.
Lemma lem3752905 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1085 A f s t) = (term1107 A f s t).
Proof. exact (MK_COMB (@lem3752903 A f t) (@lem3752904 A s t)). Qed.
Lemma lem3752907 {A : Type'} (P : A -> Prop) (Q : Prop) : (term556 A P Q) = (term557 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3752908 {A : Type'} (P : type686 A) (Q : Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem3752907 (A -> Prop) P Q). Qed.
Lemma lem3752909 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1108 A f s t) = (term1109 A f s t).
Proof. exact (@lem3752908 A (term1104 A f t) (term1081 A s t)). Qed.
Lemma lem3752910 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1110 A f t u) = (term1102 A f t u).
Proof. exact (eq_refl (term1110 A f t u)). Qed.
Lemma lem3752911 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1111 A f t) = (term1104 A f t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752910 A f t u)). Qed.
Lemma lem3752912 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3752913 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1112 A f t) = (term1105 A f t).
Proof. exact (MK_COMB (@lem3752912 A) (@lem3752911 A f t)). Qed.
Lemma lem3752914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3752915 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1113 A f t) = (term1106 A f t).
Proof. exact (MK_COMB (@lem3752914) (@lem3752913 A f t)). Qed.
Lemma lem3752916 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1081 A s t) = (term1081 A s t).
Proof. exact (eq_refl (term1081 A s t)). Qed.
Lemma lem3752917 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1108 A f s t) = (term1107 A f s t).
Proof. exact (MK_COMB (@lem3752915 A f t) (@lem3752916 A s t)). Qed.
Lemma lem3752918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3752919 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1114 A f s t) = (term1115 A f s t).
Proof. exact (MK_COMB (@lem3752918) (@lem3752917 A f s t)). Qed.
Lemma lem3752920 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1110 A f t u) = (term1102 A f t u).
Proof. exact (eq_refl (term1110 A f t u)). Qed.
Lemma lem3752921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3752922 {A : Type'} (f : type686 A) (t : A -> Prop) (u : A -> Prop) : (term1116 A f t u) = (term1117 A f t u).
Proof. exact (MK_COMB (@lem3752921) (@lem3752920 A f t u)). Qed.
Lemma lem3752923 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1081 A s t) = (term1081 A s t).
Proof. exact (eq_refl (term1081 A s t)). Qed.
Lemma lem3752924 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term1118 A f u s t) = (term1119 A f u s t).
Proof. exact (MK_COMB (@lem3752922 A f t u) (@lem3752923 A s t)). Qed.
Lemma lem3752925 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1120 A f s t) = (term1121 A f s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752924 A f u s t)). Qed.
Lemma lem3752926 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3752927 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1109 A f s t) = (term1122 A f s t).
Proof. exact (MK_COMB (@lem3752926 A) (@lem3752925 A f s t)). Qed.
Lemma lem3752928 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : ((term1108 A f s t) = (term1109 A f s t)) = ((term1107 A f s t) = (term1122 A f s t)).
Proof. exact (MK_COMB (@lem3752919 A f s t) (@lem3752927 A f s t)). Qed.
Lemma lem3752929 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1107 A f s t) = (term1122 A f s t).
Proof. exact (EQ_MP (@lem3752928 A f s t) (@lem3752909 A f s t)). Qed.
Lemma lem3752930 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1085 A f s t) = (term1122 A f s t).
Proof. exact (TRANS (@lem3752905 A f s t) (@lem3752929 A f s t)). Qed.
Lemma lem3752931 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1091 A f s) = (term1123 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752930 A f s t)). Qed.
Lemma lem3752932 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752933 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1092 A f s) = (term1124 A f s).
Proof. exact (MK_COMB (@lem3752932 A) (@lem3752931 A f s)). Qed.
Lemma lem3752935 {A B : Type'} (P : type1413 A B) : (term799 A B P) = (term800 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3752936 {A : Type'} (P : type639 A) : (term801 A P) = (term802 A P).
Proof. exact (@lem3752935 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem3752937 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1125 A f s) = (term1126 A f s).
Proof. exact (@lem3752936 A (term1127 A f s)). Qed.
Lemma lem3752938 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1128 A f s t) = (term1121 A f s t).
Proof. exact (eq_refl (term1128 A f s t)). Qed.
Lemma lem3752939 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem3752940 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term1129 A f s t u) = (term1130 A f s t u).
Proof. exact (MK_COMB (@lem3752938 A f s t) (@lem3752939 A u)). Qed.
Lemma lem3752941 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term1130 A f s t u) = (term1119 A f u s t).
Proof. exact (eq_refl (term1130 A f s t u)). Qed.
Lemma lem3752942 {A : Type'} (f : type686 A) (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term1129 A f s t u) = (term1119 A f u s t).
Proof. exact (TRANS (@lem3752940 A f s t u) (@lem3752941 A f u s t)). Qed.
Lemma lem3752943 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1131 A f s t) = (term1121 A f s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3752942 A f u s t)). Qed.
Lemma lem3752944 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3752945 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1132 A f s t) = (term1122 A f s t).
Proof. exact (MK_COMB (@lem3752944 A) (@lem3752943 A f s t)). Qed.
Lemma lem3752946 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1133 A f s) = (term1123 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752945 A f s t)). Qed.
Lemma lem3752947 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752948 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1125 A f s) = (term1124 A f s).
Proof. exact (MK_COMB (@lem3752947 A) (@lem3752946 A f s)). Qed.
Lemma lem3752949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3752950 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1134 A f s) = (term1135 A f s).
Proof. exact (MK_COMB (@lem3752949) (@lem3752948 A f s)). Qed.
Lemma lem3752951 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1128 A f s t) = (term1121 A f s t).
Proof. exact (eq_refl (term1128 A f s t)). Qed.
Lemma lem3752952 {A : Type'} (u : type672 A) (t : A -> Prop) : (u t) = (u t).
Proof. exact (eq_refl (u t)). Qed.
Lemma lem3752953 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type672 A) (t : A -> Prop) : (term1136 A f s u t) = (term1137 A f s u t).
Proof. exact (MK_COMB (@lem3752951 A f s t) (@lem3752952 A u t)). Qed.
Lemma lem3752954 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term1137 A f s u t) = (term1138 A f u s t).
Proof. exact (eq_refl (term1137 A f s u t)). Qed.
Lemma lem3752955 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term1136 A f s u t) = (term1138 A f u s t).
Proof. exact (TRANS (@lem3752953 A f s u t) (@lem3752954 A f u s t)). Qed.
Lemma lem3752956 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term1139 A f s u) = (term1140 A f u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3752955 A f u s t)). Qed.
Lemma lem3752957 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752958 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term1141 A f s u) = (term1142 A f u s).
Proof. exact (MK_COMB (@lem3752957 A) (@lem3752956 A f u s)). Qed.
Lemma lem3752959 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1143 A f s) = (term1144 A f s).
Proof. exact (fun_ext (fun u : type672 A => @lem3752958 A f u s)). Qed.
Lemma lem3752960 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3752961 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1126 A f s) = (term1145 A f s).
Proof. exact (MK_COMB (@lem3752960 A) (@lem3752959 A f s)). Qed.
Lemma lem3752962 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term1125 A f s) = (term1126 A f s)) = ((term1124 A f s) = (term1145 A f s)).
Proof. exact (MK_COMB (@lem3752950 A f s) (@lem3752961 A f s)). Qed.
Lemma lem3752963 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1124 A f s) = (term1145 A f s).
Proof. exact (EQ_MP (@lem3752962 A f s) (@lem3752937 A f s)). Qed.
Lemma lem3752965 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1092 A f s) = (term1145 A f s).
Proof. exact (TRANS (@lem3752933 A f s) (@lem3752963 A f s)). Qed.
Lemma lem3752966 {A : Type'} (f : type686 A) (s : A -> Prop) : (term143 A f s) = (term1145 A f s).
Proof. exact (TRANS (@lem3752784 A f s) (@lem3752965 A f s)). Qed.
Lemma lem3752967 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term143 A f s) : term1145 A f s.
Proof. exact (EQ_MP (@lem3752966 A f s) (@lem3752727 A f s h1)). Qed.
Lemma lem3752979 {A : Type'} (f : type686 A) (s : A -> Prop) (t' : A -> Prop) : (term1146 A f s t') = (term1147 A f s t').
Proof. exact (@lem17045 (@IN (A -> Prop) t' f) (@SUBSET A s t')). Qed.
Lemma lem3752980 {A : Type'} (t : A -> Prop) (t' : A -> Prop) : (term581 A t t') = (term581 A t t').
Proof. exact (eq_refl (term581 A t t')). Qed.
Lemma lem3752981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3752982 {A : Type'} (f : type686 A) (s : A -> Prop) (t' : A -> Prop) : (term1148 A f s t') = (term1149 A f s t').
Proof. exact (MK_COMB (@lem3752981) (@lem3752979 A f s t')). Qed.
Lemma lem3752983 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term1150 A f s t t') = (term1151 A f s t t').
Proof. exact (MK_COMB (@lem3752982 A f s t') (@lem3752980 A t t')). Qed.
Lemma lem3752984 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term1152 A f s t t') = (term1150 A f s t t').
Proof. exact (@lem17045 (term168 A f s t') (@PSUBSET A t t')). Qed.
Lemma lem3752985 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term1152 A f s t t') = (term1151 A f s t t').
Proof. exact (TRANS (@lem3752984 A f s t t') (@lem3752983 A f s t t')). Qed.
Lemma lem3752986 {A : Type'} (P : type686 A) : (term692 A P) = (term693 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3752987 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1153 A f s t) = (term1154 A f s t).
Proof. exact (@lem3752986 A (term327 A f s t)). Qed.
Lemma lem3752988 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term1155 A f s t t') = (term326 A f s t t').
Proof. exact (eq_refl (term1155 A f s t t')). Qed.
Lemma lem3752989 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3752990 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term1156 A f s t t') = (term1152 A f s t t').
Proof. exact (MK_COMB (@lem3752989) (@lem3752988 A f s t t')). Qed.
Lemma lem3752991 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term1156 A f s t t') = (term1151 A f s t t').
Proof. exact (TRANS (@lem3752990 A f s t t') (@lem3752985 A f s t t')). Qed.
Lemma lem3752992 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1157 A f s t) = (term1158 A f s t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3752991 A f s t t')). Qed.
Lemma lem3752993 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3752994 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1154 A f s t) = (term1159 A f s t).
Proof. exact (MK_COMB (@lem3752993 A) (@lem3752992 A f s t)). Qed.
Lemma lem3752995 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1153 A f s t) = (term1159 A f s t).
Proof. exact (TRANS (@lem3752987 A f s t) (@lem3752994 A f s t)). Qed.
Lemma lem3752997 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term309 A f s t) = (term309 A f s t).
Proof. exact (eq_refl (term309 A f s t)). Qed.
Lemma lem3752998 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1160 A f s t) = (term1161 A f s t).
Proof. exact (MK_COMB (@lem3752997 A f s t) (@lem3752995 A f s t)). Qed.
Lemma lem3752999 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1162 A f s t) = (term1160 A f s t).
Proof. exact (@lem17362 (term168 A f s t) (term328 A f s t)). Qed.
Lemma lem3753000 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1162 A f s t) = (term1161 A f s t).
Proof. exact (TRANS (@lem3752999 A f s t) (@lem3752998 A f s t)). Qed.
Lemma lem3753001 {A : Type'} (P : type686 A) : (term674 A P) = (term675 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3753002 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1018 A f s) = (term1163 A f s).
Proof. exact (@lem3753001 A (term332 A f s)). Qed.
Lemma lem3753003 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1164 A f s t) = (term331 A f s t).
Proof. exact (eq_refl (term1164 A f s t)). Qed.
Lemma lem3753004 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3753005 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1165 A f s t) = (term1162 A f s t).
Proof. exact (MK_COMB (@lem3753004) (@lem3753003 A f s t)). Qed.
Lemma lem3753006 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1165 A f s t) = (term1161 A f s t).
Proof. exact (TRANS (@lem3753005 A f s t) (@lem3753000 A f s t)). Qed.
Lemma lem3753007 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1166 A f s) = (term1167 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753006 A f s t)). Qed.
Lemma lem3753008 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3753009 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1163 A f s) = (term1168 A f s).
Proof. exact (MK_COMB (@lem3753008 A) (@lem3753007 A f s)). Qed.
Lemma lem3753110 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1018 A f s) = (term1168 A f s).
Proof. exact (TRANS (@lem3753002 A f s) (@lem3753009 A f s)). Qed.
Lemma lem3753111 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1018 A f s) : term1168 A f s.
Proof. exact (EQ_MP (@lem3753110 A f s) (@lem3752728 A f s h1)). Qed.
Lemma lem3753119 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1169 A s t) = (s = t).
Proof. exact (@lem16933 (s = t)). Qed.
Lemma lem3753121 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1170 A s t) = (term1170 A s t).
Proof. exact (eq_refl (term1170 A s t)). Qed.
Lemma lem3753122 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1171 A s t) = (term1172 A s t).
Proof. exact (MK_COMB (@lem3753121 A s t) (@lem3753119 A s t)). Qed.
Lemma lem3753123 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1173 A s t) = (term1171 A s t).
Proof. exact (@lem17045 (@SUBSET A s t) (term360 A s t)). Qed.
Lemma lem3753124 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1173 A s t) = (term1172 A s t).
Proof. exact (TRANS (@lem3753123 A s t) (@lem3753122 A s t)). Qed.
Lemma lem3753130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1174 A s t) = (term1174 A s t).
Proof. exact (eq_refl (term1174 A s t)). Qed.
Lemma lem3753132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1175 A s t) = (term1175 A s t).
Proof. exact (eq_refl (term1175 A s t)). Qed.
Lemma lem3753133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1176 A s t) = (term1177 A s t).
Proof. exact (MK_COMB (@lem3753132 A s t) (@lem3753124 A s t)). Qed.
Lemma lem3753134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3753135 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1178 A s t) = (term1179 A s t).
Proof. exact (MK_COMB (@lem3753134) (@lem3753133 A s t)). Qed.
Lemma lem3753136 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1180 A s t) = (term1181 A s t).
Proof. exact (MK_COMB (@lem3753135 A s t) (@lem3753130 A s t)). Qed.
Lemma lem3753137 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@PSUBSET A s t) = (term345 A s t)) = (term1180 A s t).
Proof. exact (@lem17784 (@PSUBSET A s t) (term345 A s t)). Qed.
Lemma lem3753138 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@PSUBSET A s t) = (term345 A s t)) = (term1181 A s t).
Proof. exact (TRANS (@lem3753137 A s t) (@lem3753136 A s t)). Qed.
Lemma lem3753139 {A : Type'} (s : A -> Prop) : (term1063 A s) = (term1182 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753138 A s t)). Qed.
Lemma lem3753140 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753141 {A : Type'} (s : A -> Prop) : (term1064 A s) = (term1183 A s).
Proof. exact (MK_COMB (@lem3753140 A) (@lem3753139 A s)). Qed.
Lemma lem3753142 {A : Type'} : (term1065 A) = (term1184 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753141 A s)). Qed.
Lemma lem3753143 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753144 {A : Type'} : (term1021 A) = (term1185 A).
Proof. exact (MK_COMB (@lem3753143 A) (@lem3753142 A)). Qed.
Lemma lem3753150 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term533 A P Q) = (term534 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3753151 {A : Type'} (P : type686 A) (Q : type686 A) : (term1186 A P Q) = (term1187 A P Q).
Proof. exact (@lem3753150 (A -> Prop) P Q). Qed.
Lemma lem3753152 {A : Type'} (s : A -> Prop) : (term1188 A s) = (term1189 A s).
Proof. exact (@lem3753151 A (term1190 A s) (term1191 A s)). Qed.
Lemma lem3753153 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1192 A s t) = (term1177 A s t).
Proof. exact (eq_refl (term1192 A s t)). Qed.
Lemma lem3753154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3753155 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1193 A s t) = (term1179 A s t).
Proof. exact (MK_COMB (@lem3753154) (@lem3753153 A s t)). Qed.
Lemma lem3753156 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1194 A s t) = (term1174 A s t).
Proof. exact (eq_refl (term1194 A s t)). Qed.
Lemma lem3753157 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1195 A s t) = (term1181 A s t).
Proof. exact (MK_COMB (@lem3753155 A s t) (@lem3753156 A s t)). Qed.
Lemma lem3753158 {A : Type'} (s : A -> Prop) : (term1196 A s) = (term1182 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753157 A s t)). Qed.
Lemma lem3753159 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753160 {A : Type'} (s : A -> Prop) : (term1188 A s) = (term1183 A s).
Proof. exact (MK_COMB (@lem3753159 A) (@lem3753158 A s)). Qed.
Lemma lem3753161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3753162 {A : Type'} (s : A -> Prop) : (term1197 A s) = (term1198 A s).
Proof. exact (MK_COMB (@lem3753161) (@lem3753160 A s)). Qed.
Lemma lem3753163 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1192 A s t) = (term1177 A s t).
Proof. exact (eq_refl (term1192 A s t)). Qed.
Lemma lem3753164 {A : Type'} (s : A -> Prop) : (term1199 A s) = (term1190 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753163 A s t)). Qed.
Lemma lem3753165 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753166 {A : Type'} (s : A -> Prop) : (term1200 A s) = (term1201 A s).
Proof. exact (MK_COMB (@lem3753165 A) (@lem3753164 A s)). Qed.
Lemma lem3753167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3753168 {A : Type'} (s : A -> Prop) : (term1202 A s) = (term1203 A s).
Proof. exact (MK_COMB (@lem3753167) (@lem3753166 A s)). Qed.
Lemma lem3753169 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1194 A s t) = (term1174 A s t).
Proof. exact (eq_refl (term1194 A s t)). Qed.
Lemma lem3753170 {A : Type'} (s : A -> Prop) : (term1204 A s) = (term1191 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753169 A s t)). Qed.
Lemma lem3753171 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753172 {A : Type'} (s : A -> Prop) : (term1205 A s) = (term1206 A s).
Proof. exact (MK_COMB (@lem3753171 A) (@lem3753170 A s)). Qed.
Lemma lem3753173 {A : Type'} (s : A -> Prop) : (term1189 A s) = (term1207 A s).
Proof. exact (MK_COMB (@lem3753168 A s) (@lem3753172 A s)). Qed.
Lemma lem3753174 {A : Type'} (s : A -> Prop) : ((term1188 A s) = (term1189 A s)) = ((term1183 A s) = (term1207 A s)).
Proof. exact (MK_COMB (@lem3753162 A s) (@lem3753173 A s)). Qed.
Lemma lem3753175 {A : Type'} (s : A -> Prop) : (term1183 A s) = (term1207 A s).
Proof. exact (EQ_MP (@lem3753174 A s) (@lem3753152 A s)). Qed.
Lemma lem3753272 {A : Type'} : (term1184 A) = (term1208 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753175 A s)). Qed.
Lemma lem3753273 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753274 {A : Type'} : (term1185 A) = (term1209 A).
Proof. exact (MK_COMB (@lem3753273 A) (@lem3753272 A)). Qed.
Lemma lem3753276 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term533 A P Q) = (term534 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3753277 {A : Type'} (P : type686 A) (Q : type686 A) : (term1186 A P Q) = (term1187 A P Q).
Proof. exact (@lem3753276 (A -> Prop) P Q). Qed.
Lemma lem3753278 {A : Type'} : (term1210 A) = (term1211 A).
Proof. exact (@lem3753277 A (term1212 A) (term1213 A)). Qed.
Lemma lem3753279 {A : Type'} (s : A -> Prop) : (term1214 A s) = (term1201 A s).
Proof. exact (eq_refl (term1214 A s)). Qed.
Lemma lem3753280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3753281 {A : Type'} (s : A -> Prop) : (term1215 A s) = (term1203 A s).
Proof. exact (MK_COMB (@lem3753280) (@lem3753279 A s)). Qed.
Lemma lem3753282 {A : Type'} (s : A -> Prop) : (term1216 A s) = (term1206 A s).
Proof. exact (eq_refl (term1216 A s)). Qed.
Lemma lem3753283 {A : Type'} (s : A -> Prop) : (term1217 A s) = (term1207 A s).
Proof. exact (MK_COMB (@lem3753281 A s) (@lem3753282 A s)). Qed.
Lemma lem3753284 {A : Type'} : (term1218 A) = (term1208 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753283 A s)). Qed.
Lemma lem3753285 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753286 {A : Type'} : (term1210 A) = (term1209 A).
Proof. exact (MK_COMB (@lem3753285 A) (@lem3753284 A)). Qed.
Lemma lem3753287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3753288 {A : Type'} : (term1219 A) = (term1220 A).
Proof. exact (MK_COMB (@lem3753287) (@lem3753286 A)). Qed.
Lemma lem3753289 {A : Type'} (s : A -> Prop) : (term1214 A s) = (term1201 A s).
Proof. exact (eq_refl (term1214 A s)). Qed.
Lemma lem3753290 {A : Type'} : (term1221 A) = (term1212 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753289 A s)). Qed.
Lemma lem3753291 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753292 {A : Type'} : (term1222 A) = (term1223 A).
Proof. exact (MK_COMB (@lem3753291 A) (@lem3753290 A)). Qed.
Lemma lem3753293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3753294 {A : Type'} : (term1224 A) = (term1225 A).
Proof. exact (MK_COMB (@lem3753293) (@lem3753292 A)). Qed.
Lemma lem3753295 {A : Type'} (s : A -> Prop) : (term1216 A s) = (term1206 A s).
Proof. exact (eq_refl (term1216 A s)). Qed.
Lemma lem3753296 {A : Type'} : (term1226 A) = (term1213 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753295 A s)). Qed.
Lemma lem3753297 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753298 {A : Type'} : (term1227 A) = (term1228 A).
Proof. exact (MK_COMB (@lem3753297 A) (@lem3753296 A)). Qed.
Lemma lem3753299 {A : Type'} : (term1211 A) = (term1229 A).
Proof. exact (MK_COMB (@lem3753294 A) (@lem3753298 A)). Qed.
Lemma lem3753300 {A : Type'} : ((term1210 A) = (term1211 A)) = ((term1209 A) = (term1229 A)).
Proof. exact (MK_COMB (@lem3753288 A) (@lem3753299 A)). Qed.
Lemma lem3753301 {A : Type'} : (term1209 A) = (term1229 A).
Proof. exact (EQ_MP (@lem3753300 A) (@lem3753278 A)). Qed.
Lemma lem3753408 {A : Type'} : (term1185 A) = (term1229 A).
Proof. exact (TRANS (@lem3753274 A) (@lem3753301 A)). Qed.
Lemma lem3753409 {A : Type'} : (term1021 A) = (term1229 A).
Proof. exact (TRANS (@lem3753144 A) (@lem3753408 A)). Qed.
Lemma lem3753410 {A : Type'} (h1 : term1021 A) : term1229 A.
Proof. exact (EQ_MP (@lem3753409 A) (@lem3752729 A h1)). Qed.
Lemma lem3753417 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term1230 A s t u) = (term1231 A s t u).
Proof. exact (@lem17045 (@SUBSET A s t) (@PSUBSET A t u)). Qed.
Lemma lem3753418 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@PSUBSET A s u) = (@PSUBSET A s u).
Proof. exact (eq_refl (@PSUBSET A s u)). Qed.
Lemma lem3753419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3753420 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term1232 A s t u) = (term1233 A s t u).
Proof. exact (MK_COMB (@lem3753419) (@lem3753417 A s t u)). Qed.
Lemma lem3753421 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term1234 A t s u) = (term1235 A t s u).
Proof. exact (MK_COMB (@lem3753420 A s t u) (@lem3753418 A s u)). Qed.
Lemma lem3753422 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term1057 A t s u) = (term1234 A t s u).
Proof. exact (@lem17265 (term199 A s t u) (@PSUBSET A s u)). Qed.
Lemma lem3753423 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term1057 A t s u) = (term1235 A t s u).
Proof. exact (TRANS (@lem3753422 A t s u) (@lem3753421 A t s u)). Qed.
Lemma lem3753424 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1058 A t s) = (term1236 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3753423 A t s u)). Qed.
Lemma lem3753425 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753426 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1059 A t s) = (term1237 A t s).
Proof. exact (MK_COMB (@lem3753425 A) (@lem3753424 A t s)). Qed.
Lemma lem3753427 {A : Type'} (s : A -> Prop) : (term1060 A s) = (term1238 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753426 A t s)). Qed.
Lemma lem3753428 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753429 {A : Type'} (s : A -> Prop) : (term1061 A s) = (term1239 A s).
Proof. exact (MK_COMB (@lem3753428 A) (@lem3753427 A s)). Qed.
Lemma lem3753430 {A : Type'} : (term1062 A) = (term1240 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753429 A s)). Qed.
Lemma lem3753431 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753492 {A : Type'} : (term1020 A) = (term1241 A).
Proof. exact (MK_COMB (@lem3753431 A) (@lem3753430 A)). Qed.
Lemma lem3753493 {A : Type'} (h1 : term1020 A) : term1241 A.
Proof. exact (EQ_MP (@lem3753492 A) (@lem3752730 A h1)). Qed.
Lemma lem3753577 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1161 A f s t.
Proof. exact (h1). Qed.
Lemma lem3753578 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1142 A f u s.
Proof. exact (h1). Qed.
Lemma lem3753613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1174 A s t) = (term1174 A s t).
Proof. exact (eq_refl (term1174 A s t)). Qed.
Lemma lem3753614 {A : Type'} (s : A -> Prop) : (term1191 A s) = (term1191 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753613 A s t)). Qed.
Lemma lem3753615 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753616 {A : Type'} (s : A -> Prop) : (term1206 A s) = (term1206 A s).
Proof. exact (MK_COMB (@lem3753615 A) (@lem3753614 A s)). Qed.
Lemma lem3753617 {A : Type'} : (term1213 A) = (term1213 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753616 A s)). Qed.
Lemma lem3753618 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753619 {A : Type'} : (term1228 A) = (term1228 A).
Proof. exact (MK_COMB (@lem3753618 A) (@lem3753617 A)). Qed.
Lemma lem3753642 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1177 A s t) = (term1177 A s t).
Proof. exact (eq_refl (term1177 A s t)). Qed.
Lemma lem3753643 {A : Type'} (s : A -> Prop) : (term1190 A s) = (term1190 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753642 A s t)). Qed.
Lemma lem3753644 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753645 {A : Type'} (s : A -> Prop) : (term1201 A s) = (term1201 A s).
Proof. exact (MK_COMB (@lem3753644 A) (@lem3753643 A s)). Qed.
Lemma lem3753646 {A : Type'} : (term1212 A) = (term1212 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753645 A s)). Qed.
Lemma lem3753647 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753648 {A : Type'} : (term1223 A) = (term1223 A).
Proof. exact (MK_COMB (@lem3753647 A) (@lem3753646 A)). Qed.
Lemma lem3753649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3753650 {A : Type'} : (term1225 A) = (term1225 A).
Proof. exact (MK_COMB (@lem3753649) (@lem3753648 A)). Qed.
Lemma lem3753651 {A : Type'} : (term1229 A) = (term1229 A).
Proof. exact (MK_COMB (@lem3753650 A) (@lem3753619 A)). Qed.
Lemma lem3753652 {A : Type'} (h1 : term1021 A) : term1229 A.
Proof. exact (EQ_MP (@lem3753651 A) (@lem3753410 A h1)). Qed.
Lemma lem3753677 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term1235 A t s u) = (term1235 A t s u).
Proof. exact (eq_refl (term1235 A t s u)). Qed.
Lemma lem3753678 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1236 A t s) = (term1236 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3753677 A t s u)). Qed.
Lemma lem3753679 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753680 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1237 A t s) = (term1237 A t s).
Proof. exact (MK_COMB (@lem3753679 A) (@lem3753678 A t s)). Qed.
Lemma lem3753681 {A : Type'} (s : A -> Prop) : (term1238 A s) = (term1238 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753680 A t s)). Qed.
Lemma lem3753682 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753683 {A : Type'} (s : A -> Prop) : (term1239 A s) = (term1239 A s).
Proof. exact (MK_COMB (@lem3753682 A) (@lem3753681 A s)). Qed.
Lemma lem3753684 {A : Type'} : (term1240 A) = (term1240 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753683 A s)). Qed.
Lemma lem3753685 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753686 {A : Type'} : (term1241 A) = (term1241 A).
Proof. exact (MK_COMB (@lem3753685 A) (@lem3753684 A)). Qed.
Lemma lem3753687 {A : Type'} (h1 : term1020 A) : term1241 A.
Proof. exact (EQ_MP (@lem3753686 A) (@lem3753493 A h1)). Qed.
Lemma lem3753749 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term1151 A f s t t') = (term1151 A f s t t').
Proof. exact (eq_refl (term1151 A f s t t')). Qed.
Lemma lem3753750 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1158 A f s t) = (term1158 A f s t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3753749 A f s t t')). Qed.
Lemma lem3753751 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753752 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1159 A f s t) = (term1159 A f s t).
Proof. exact (MK_COMB (@lem3753751 A) (@lem3753750 A f s t)). Qed.
Lemma lem3753767 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term309 A f s t) = (term309 A f s t).
Proof. exact (eq_refl (term309 A f s t)). Qed.
Lemma lem3753768 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1161 A f s t) = (term1161 A f s t).
Proof. exact (MK_COMB (@lem3753767 A f s t) (@lem3753752 A f s t)). Qed.
Lemma lem3753769 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1161 A f s t.
Proof. exact (EQ_MP (@lem3753768 A f s t) (@lem3753577 A f s t h1)). Qed.
Lemma lem3753806 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term1138 A f u s t) = (term1138 A f u s t).
Proof. exact (eq_refl (term1138 A f u s t)). Qed.
Lemma lem3753807 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term1140 A f u s) = (term1140 A f u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753806 A f u s t)). Qed.
Lemma lem3753808 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753809 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term1142 A f u s) = (term1142 A f u s).
Proof. exact (MK_COMB (@lem3753808 A) (@lem3753807 A f u s)). Qed.
Lemma lem3753810 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1142 A f u s.
Proof. exact (EQ_MP (@lem3753809 A f u s) (@lem3753578 A f u s h1)). Qed.
Lemma lem3753811 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1159 A f s t.
Proof. exact (proj2 (@lem3753769 A f s t h1)). Qed.
Lemma lem3753812 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term168 A f s t.
Proof. exact (proj1 (@lem3753769 A f s t h1)). Qed.
Lemma lem3753815 {A : Type'} (h1 : term1021 A) : term1228 A.
Proof. exact (proj2 (@lem3753652 A h1)). Qed.
Lemma lem3753838 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term1235 A t s u) = (term1235 A t s u).
Proof. exact (eq_refl (term1235 A t s u)). Qed.
Lemma lem3753839 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1236 A t s) = (term1236 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3753838 A t s u)). Qed.
Lemma lem3753840 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753841 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1237 A t s) = (term1237 A t s).
Proof. exact (MK_COMB (@lem3753840 A) (@lem3753839 A t s)). Qed.
Lemma lem3753842 {A : Type'} (s : A -> Prop) : (term1238 A s) = (term1238 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753841 A t s)). Qed.
Lemma lem3753843 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753844 {A : Type'} (s : A -> Prop) : (term1239 A s) = (term1239 A s).
Proof. exact (MK_COMB (@lem3753843 A) (@lem3753842 A s)). Qed.
Lemma lem3753845 {A : Type'} : (term1240 A) = (term1240 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753844 A s)). Qed.
Lemma lem3753846 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753848 {A : Type'} : (term1241 A) = (term1241 A).
Proof. exact (MK_COMB (@lem3753846 A) (@lem3753845 A)). Qed.
Lemma lem3753849 {A : Type'} (h1 : term1020 A) : term1241 A.
Proof. exact (EQ_MP (@lem3753848 A) (@lem3753687 A h1)). Qed.
Lemma lem3753876 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1081 A s t) = (term1081 A s t).
Proof. exact (eq_refl (term1081 A s t)). Qed.
Lemma lem3753893 {A : Type'} (f : type686 A) (u : type672 A) (t : A -> Prop) : (term1242 A f u t) = (term1243 A f u t).
Proof. exact (@lem19490 (term1244 A u t f) (term1095 A t f) (term1245 A u t)). Qed.
Lemma lem3753894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3753895 {A : Type'} (f : type686 A) (u : type672 A) (t : A -> Prop) : (term1246 A f u t) = (term1247 A f u t).
Proof. exact (MK_COMB (@lem3753894) (@lem3753893 A f u t)). Qed.
Lemma lem3753896 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term1138 A f u s t) = (term1248 A f u s t).
Proof. exact (MK_COMB (@lem3753895 A f u t) (@lem3753876 A s t)). Qed.
Lemma lem3753903 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term1248 A f u s t) = (term1249 A f u s t).
Proof. exact (@lem19699 (term1250 A u t f) (term1251 A f u t) (term1081 A s t)). Qed.
Lemma lem3753904 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (t : A -> Prop) : (term1138 A f u s t) = (term1249 A f u s t).
Proof. exact (TRANS (@lem3753896 A f u s t) (@lem3753903 A f u s t)). Qed.
Lemma lem3753905 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term1140 A f u s) = (term1252 A f u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753904 A f u s t)). Qed.
Lemma lem3753906 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753908 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) : (term1142 A f u s) = (term1253 A f u s).
Proof. exact (MK_COMB (@lem3753906 A) (@lem3753905 A f u s)). Qed.
Lemma lem3753909 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1253 A f u s.
Proof. exact (EQ_MP (@lem3753908 A f u s) (@lem3753810 A f u s h1)). Qed.
Lemma lem3753923 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (t' : A -> Prop) : (term1151 A f s t t') = (term1151 A f s t t').
Proof. exact (eq_refl (term1151 A f s t t')). Qed.
Lemma lem3753924 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1158 A f s t) = (term1158 A f s t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3753923 A f s t t')). Qed.
Lemma lem3753925 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753927 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) : (term1159 A f s t) = (term1159 A f s t).
Proof. exact (MK_COMB (@lem3753925 A) (@lem3753924 A f s t)). Qed.
Lemma lem3753928 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1159 A f s t.
Proof. exact (EQ_MP (@lem3753927 A f s t) (@lem3753811 A f s t h1)). Qed.
Lemma lem3753976 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1174 A s t) = (term1254 A s t).
Proof. exact (@lem19490 (@SUBSET A s t) (term581 A s t) (term360 A s t)). Qed.
Lemma lem3753977 {A : Type'} (s : A -> Prop) : (term1191 A s) = (term1255 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3753976 A s t)). Qed.
Lemma lem3753978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753979 {A : Type'} (s : A -> Prop) : (term1206 A s) = (term1256 A s).
Proof. exact (MK_COMB (@lem3753978 A) (@lem3753977 A s)). Qed.
Lemma lem3753980 {A : Type'} : (term1213 A) = (term1257 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3753979 A s)). Qed.
Lemma lem3753981 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3753983 {A : Type'} : (term1228 A) = (term1258 A).
Proof. exact (MK_COMB (@lem3753981 A) (@lem3753980 A)). Qed.
Lemma lem3753984 {A : Type'} (h1 : term1021 A) : term1258 A.
Proof. exact (EQ_MP (@lem3753983 A) (@lem3753815 A h1)). Qed.
Lemma lem3753985 {A : Type'} (_43160 : A -> Prop) (h1 : term1020 A) : term1259 A _43160.
Proof. exact (@lem3753849 A h1 _43160). Qed.
Lemma lem3753986 {A : Type'} (_43160 : A -> Prop) : (term1259 A _43160) = (term1239 A _43160).
Proof. exact (eq_refl (term1259 A _43160)). Qed.
Lemma lem3753987 {A : Type'} (_43160 : A -> Prop) (h1 : term1020 A) : term1239 A _43160.
Proof. exact (EQ_MP (@lem3753986 A _43160) (@lem3753985 A _43160 h1)). Qed.
Lemma lem3753988 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (h1 : term1020 A) : term1260 A _43160 _43161.
Proof. exact (@lem3753987 A _43160 h1 _43161). Qed.
Lemma lem3753989 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) : (term1260 A _43160 _43161) = (term1237 A _43161 _43160).
Proof. exact (eq_refl (term1260 A _43160 _43161)). Qed.
Lemma lem3753990 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (h1 : term1020 A) : term1237 A _43161 _43160.
Proof. exact (EQ_MP (@lem3753989 A _43161 _43160) (@lem3753988 A _43160 _43161 h1)). Qed.
Lemma lem3753991 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) (h1 : term1020 A) : term1261 A _43161 _43160 _43162.
Proof. exact (@lem3753990 A _43161 _43160 h1 _43162). Qed.
Lemma lem3753992 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) : (term1261 A _43161 _43160 _43162) = (term1235 A _43161 _43160 _43162).
Proof. exact (eq_refl (term1261 A _43161 _43160 _43162)). Qed.
Lemma lem3753993 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) (h1 : term1020 A) : term1235 A _43161 _43160 _43162.
Proof. exact (EQ_MP (@lem3753992 A _43161 _43160 _43162) (@lem3753991 A _43161 _43160 _43162 h1)). Qed.
Lemma lem3754003 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1262 A f u s _43166.
Proof. exact (@lem3753909 A f u s h1 _43166). Qed.
Lemma lem3754004 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1262 A f u s _43166) = (term1249 A f u s _43166).
Proof. exact (eq_refl (term1262 A f u s _43166)). Qed.
Lemma lem3754005 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1249 A f u s _43166.
Proof. exact (EQ_MP (@lem3754004 A f u s _43166) (@lem3754003 A _43166 f u s h1)). Qed.
Lemma lem3754006 {A : Type'} (_43167 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1263 A f s t _43167.
Proof. exact (@lem3753928 A f s t h1 _43167). Qed.
Lemma lem3754007 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (_43167 : A -> Prop) : (term1263 A f s t _43167) = (term1151 A f s t _43167).
Proof. exact (eq_refl (term1263 A f s t _43167)). Qed.
Lemma lem3754008 {A : Type'} (_43167 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1151 A f s t _43167.
Proof. exact (EQ_MP (@lem3754007 A f s t _43167) (@lem3754006 A _43167 f s t h1)). Qed.
Lemma lem3754015 {A : Type'} (_43170 : A -> Prop) (h1 : term1021 A) : term1264 A _43170.
Proof. exact (@lem3753984 A h1 _43170). Qed.
Lemma lem3754016 {A : Type'} (_43170 : A -> Prop) : (term1264 A _43170) = (term1256 A _43170).
Proof. exact (eq_refl (term1264 A _43170)). Qed.
Lemma lem3754017 {A : Type'} (_43170 : A -> Prop) (h1 : term1021 A) : term1256 A _43170.
Proof. exact (EQ_MP (@lem3754016 A _43170) (@lem3754015 A _43170 h1)). Qed.
Lemma lem3754018 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) (h1 : term1021 A) : term1265 A _43170 _43171.
Proof. exact (@lem3754017 A _43170 h1 _43171). Qed.
Lemma lem3754019 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1265 A _43170 _43171) = (term1254 A _43170 _43171).
Proof. exact (eq_refl (term1265 A _43170 _43171)). Qed.
Lemma lem3754020 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) (h1 : term1021 A) : term1254 A _43170 _43171.
Proof. exact (EQ_MP (@lem3754019 A _43170 _43171) (@lem3754018 A _43170 _43171 h1)). Qed.
Lemma lem3754023 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1266 A f u s _43166.
Proof. exact (proj2 (@lem3754005 A _43166 f u s h1)). Qed.
Lemma lem3754024 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1267 A u f s _43166.
Proof. exact (proj1 (@lem3754005 A _43166 f u s h1)). Qed.
Lemma lem3754039 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) : (term1235 A _43161 _43160 _43162) = (term1268 A _43161 _43160 _43162).
Proof. exact (@lem3743391 (term1081 A _43160 _43161) (term581 A _43161 _43162) (@PSUBSET A _43160 _43162)). Qed.
Lemma lem3754040 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) (h1 : term1020 A) : term1268 A _43161 _43160 _43162.
Proof. exact (EQ_MP (@lem3754039 A _43161 _43160 _43162) (@lem3753993 A _43161 _43160 _43162 h1)). Qed.
Lemma lem3754063 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (_43167 : A -> Prop) : (term1151 A f s t _43167) = (term1269 A f s t _43167).
Proof. exact (@lem3743391 (term1095 A _43167 f) (term1081 A s _43167) (term581 A t _43167)). Qed.
Lemma lem3754064 {A : Type'} (_43167 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1269 A f s t _43167.
Proof. exact (EQ_MP (@lem3754063 A f s t _43167) (@lem3754008 A _43167 f s t h1)). Qed.
Lemma lem3754084 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) (h1 : term1021 A) : term1270 A _43170 _43171.
Proof. exact (proj1 (@lem3754020 A _43170 _43171 h1)). Qed.
Lemma lem3754101 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1267 A u f s _43166) = (term1271 A u f s _43166).
Proof. exact (@lem3743391 (term1095 A _43166 f) (term1244 A u _43166 f) (term1081 A s _43166)). Qed.
Lemma lem3754102 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1271 A u f s _43166.
Proof. exact (EQ_MP (@lem3754101 A u f s _43166) (@lem3754024 A _43166 f u s h1)). Qed.
Lemma lem3754113 {A : Type'} (f : type686 A) (u : type672 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1266 A f u s _43166) = (term1272 A f u s _43166).
Proof. exact (@lem3743391 (term1095 A _43166 f) (term1245 A u _43166) (term1081 A s _43166)). Qed.
Lemma lem3754114 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1272 A f u s _43166.
Proof. exact (EQ_MP (@lem3754113 A f u s _43166) (@lem3754023 A _43166 f u s h1)). Qed.
Lemma lem3754197 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @IN (A -> Prop) t f.
Proof. exact (proj1 (@lem3753812 A f s t h1)). Qed.
Lemma lem3754198 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1273 A t f.
Proof. exact (fun h0 : term1095 A t f => @lem3754197 A f s t h1). Qed.
Lemma lem3754200 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754201 {A : Type'} (t : A -> Prop) (f : type686 A) : (term1273 A t f) = (@IN (A -> Prop) t f).
Proof. exact (@lem3754200 (@IN (A -> Prop) t f)). Qed.
Lemma lem3754202 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @IN (A -> Prop) t f.
Proof. exact (EQ_MP (@lem3754201 A t f) (@lem3754198 A f s t h1)). Qed.
Lemma lem3754204 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @SUBSET A s t.
Proof. exact (proj2 (@lem3753812 A f s t h1)). Qed.
Lemma lem3754205 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1274 A s t.
Proof. exact (fun h0 : term1081 A s t => @lem3754204 A f s t h1). Qed.
Lemma lem3754207 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754208 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1274 A s t) = (@SUBSET A s t).
Proof. exact (@lem3754207 (@SUBSET A s t)). Qed.
Lemma lem3754209 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3754208 A s t) (@lem3754205 A f s t h1)). Qed.
Lemma lem3754215 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3754216 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1271 A u f s _43166) = (term1275 A u f s _43166).
Proof. exact (@lem3754215 (term1244 A u _43166 f) (term1095 A _43166 f) (term1081 A s _43166)). Qed.
Lemma lem3754232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3754233 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1276 A u f s _43166) = (term1277 A u f s _43166).
Proof. exact (MK_COMB (@lem3754232) (@lem3754216 A u f s _43166)). Qed.
Lemma lem3754249 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1275 A u f s _43166) = (term1275 A u f s _43166).
Proof. exact (eq_refl (term1275 A u f s _43166)). Qed.
Lemma lem3754250 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : ((term1271 A u f s _43166) = (term1275 A u f s _43166)) = ((term1275 A u f s _43166) = (term1275 A u f s _43166)).
Proof. exact (MK_COMB (@lem3754233 A u f s _43166) (@lem3754249 A u f s _43166)). Qed.
Lemma lem3754252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3754253 (x : Prop) : (x = x) = True.
Proof. exact (@lem3754252 Prop x). Qed.
Lemma lem3754254 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : ((term1275 A u f s _43166) = (term1275 A u f s _43166)) = True.
Proof. exact (@lem3754253 (term1275 A u f s _43166)). Qed.
Lemma lem3754255 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : ((term1271 A u f s _43166) = (term1275 A u f s _43166)) = True.
Proof. exact (TRANS (@lem3754250 A u f s _43166) (@lem3754254 A u f s _43166)). Qed.
Lemma lem3754256 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : True = ((term1271 A u f s _43166) = (term1275 A u f s _43166)).
Proof. exact (SYM (@lem3754255 A u f s _43166)). Qed.
Lemma lem3754257 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1271 A u f s _43166) = (term1275 A u f s _43166).
Proof. exact (EQ_MP (@lem3754256 A u f s _43166) (@lem0)). Qed.
Lemma lem3754258 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1275 A u f s _43166.
Proof. exact (EQ_MP (@lem3754257 A u f s _43166) (@lem3754102 A _43166 f u s h1)). Qed.
Lemma lem3754260 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3754261 {A : Type'} (s : A -> Prop) (u : type672 A) (_43166 : A -> Prop) (f : type686 A) : (term1275 A u f s _43166) = (term1278 A s u _43166 f).
Proof. exact (@lem3754260 (term1147 A f s _43166) (term1244 A u _43166 f)). Qed.
Lemma lem3754263 (a : Prop) (b : Prop) : (term1279 a b) = (term1280 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3754264 {A : Type'} (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1281 A f s _43166) = (term1282 A f s _43166).
Proof. exact (@lem3754263 (term1095 A _43166 f) (term1081 A s _43166)). Qed.
Lemma lem3754266 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3754267 {A : Type'} (_43166 : A -> Prop) (f : type686 A) : (term1283 A _43166 f) = (@IN (A -> Prop) _43166 f).
Proof. exact (@lem3754266 (@IN (A -> Prop) _43166 f)). Qed.
Lemma lem3754268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3754269 {A : Type'} (_43166 : A -> Prop) (f : type686 A) : (term1284 A _43166 f) = (term65 A _43166 f).
Proof. exact (MK_COMB (@lem3754268) (@lem3754267 A _43166 f)). Qed.
Lemma lem3754271 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3754272 {A : Type'} (s : A -> Prop) (_43166 : A -> Prop) : (term1285 A s _43166) = (@SUBSET A s _43166).
Proof. exact (@lem3754271 (@SUBSET A s _43166)). Qed.
Lemma lem3754273 {A : Type'} (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1282 A f s _43166) = (term168 A f s _43166).
Proof. exact (MK_COMB (@lem3754269 A _43166 f) (@lem3754272 A s _43166)). Qed.
Lemma lem3754274 {A : Type'} (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1281 A f s _43166) = (term168 A f s _43166).
Proof. exact (TRANS (@lem3754264 A f s _43166) (@lem3754273 A f s _43166)). Qed.
Lemma lem3754275 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3754276 {A : Type'} (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1286 A f s _43166) = (term280 A f s _43166).
Proof. exact (MK_COMB (@lem3754275) (@lem3754274 A f s _43166)). Qed.
Lemma lem3754277 {A : Type'} (u : type672 A) (_43166 : A -> Prop) (f : type686 A) : (term1244 A u _43166 f) = (term1244 A u _43166 f).
Proof. exact (eq_refl (term1244 A u _43166 f)). Qed.
Lemma lem3754278 {A : Type'} (s : A -> Prop) (u : type672 A) (_43166 : A -> Prop) (f : type686 A) : (term1278 A s u _43166 f) = (term1287 A s u _43166 f).
Proof. exact (MK_COMB (@lem3754276 A f s _43166) (@lem3754277 A u _43166 f)). Qed.
Lemma lem3754279 {A : Type'} (s : A -> Prop) (u : type672 A) (_43166 : A -> Prop) (f : type686 A) : (term1275 A u f s _43166) = (term1287 A s u _43166 f).
Proof. exact (TRANS (@lem3754261 A s u _43166 f) (@lem3754278 A s u _43166 f)). Qed.
Lemma lem3754281 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term168 A f s t.
Proof. exact (conj (@lem3754202 A f s t h1) (@lem3754209 A f s t h1)). Qed.
Lemma lem3754283 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1287 A s u _43166 f.
Proof. exact (EQ_MP (@lem3754279 A s u _43166 f) (@lem3754258 A _43166 f u s h1)). Qed.
Lemma lem3754284 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1287 A s u _43166 f.
Proof. exact (@lem3754283 A _43166 f u s h1). Qed.
Lemma lem3754285 {A : Type'} (t : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1287 A s u t f.
Proof. exact (@lem3754284 A t f u s h1). Qed.
Lemma lem3754288 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1244 A u t f.
Proof. exact (@lem3754285 A t f u s h1 (@lem3754281 A f s t h2)). Qed.
Lemma lem3754289 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1288 A u t f.
Proof. exact (fun h0 : term1289 A u t f => @lem3754288 A u f s t h1 h2). Qed.
Lemma lem3754291 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754292 {A : Type'} (u : type672 A) (t : A -> Prop) (f : type686 A) : (term1288 A u t f) = (term1244 A u t f).
Proof. exact (@lem3754291 (term1244 A u t f)). Qed.
Lemma lem3754293 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1244 A u t f.
Proof. exact (EQ_MP (@lem3754292 A u t f) (@lem3754289 A u f s t h1 h2)). Qed.
Lemma lem3754295 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @SUBSET A s t.
Proof. exact (proj2 (@lem3753812 A f s t h1)). Qed.
Lemma lem3754296 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1274 A s t.
Proof. exact (fun h0 : term1081 A s t => @lem3754295 A f s t h1). Qed.
Lemma lem3754298 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754299 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1274 A s t) = (@SUBSET A s t).
Proof. exact (@lem3754298 (@SUBSET A s t)). Qed.
Lemma lem3754300 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3754299 A s t) (@lem3754296 A f s t h1)). Qed.
Lemma lem3754302 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @IN (A -> Prop) t f.
Proof. exact (proj1 (@lem3753812 A f s t h1)). Qed.
Lemma lem3754303 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1273 A t f.
Proof. exact (fun h0 : term1095 A t f => @lem3754302 A f s t h1). Qed.
Lemma lem3754305 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754306 {A : Type'} (t : A -> Prop) (f : type686 A) : (term1273 A t f) = (@IN (A -> Prop) t f).
Proof. exact (@lem3754305 (@IN (A -> Prop) t f)). Qed.
Lemma lem3754307 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @IN (A -> Prop) t f.
Proof. exact (EQ_MP (@lem3754306 A t f) (@lem3754303 A f s t h1)). Qed.
Lemma lem3754309 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @SUBSET A s t.
Proof. exact (proj2 (@lem3753812 A f s t h1)). Qed.
Lemma lem3754310 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1274 A s t.
Proof. exact (fun h0 : term1081 A s t => @lem3754309 A f s t h1). Qed.
Lemma lem3754312 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754313 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1274 A s t) = (@SUBSET A s t).
Proof. exact (@lem3754312 (@SUBSET A s t)). Qed.
Lemma lem3754314 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3754313 A s t) (@lem3754310 A f s t h1)). Qed.
Lemma lem3754320 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3754321 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1272 A f u s _43166) = (term1290 A u f s _43166).
Proof. exact (@lem3754320 (term1245 A u _43166) (term1095 A _43166 f) (term1081 A s _43166)). Qed.
Lemma lem3754337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3754338 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1291 A f u s _43166) = (term1292 A u f s _43166).
Proof. exact (MK_COMB (@lem3754337) (@lem3754321 A u f s _43166)). Qed.
Lemma lem3754354 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1290 A u f s _43166) = (term1290 A u f s _43166).
Proof. exact (eq_refl (term1290 A u f s _43166)). Qed.
Lemma lem3754355 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : ((term1272 A f u s _43166) = (term1290 A u f s _43166)) = ((term1290 A u f s _43166) = (term1290 A u f s _43166)).
Proof. exact (MK_COMB (@lem3754338 A u f s _43166) (@lem3754354 A u f s _43166)). Qed.
Lemma lem3754357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3754358 (x : Prop) : (x = x) = True.
Proof. exact (@lem3754357 Prop x). Qed.
Lemma lem3754359 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : ((term1290 A u f s _43166) = (term1290 A u f s _43166)) = True.
Proof. exact (@lem3754358 (term1290 A u f s _43166)). Qed.
Lemma lem3754360 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : ((term1272 A f u s _43166) = (term1290 A u f s _43166)) = True.
Proof. exact (TRANS (@lem3754355 A u f s _43166) (@lem3754359 A u f s _43166)). Qed.
Lemma lem3754361 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : True = ((term1272 A f u s _43166) = (term1290 A u f s _43166)).
Proof. exact (SYM (@lem3754360 A u f s _43166)). Qed.
Lemma lem3754362 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1272 A f u s _43166) = (term1290 A u f s _43166).
Proof. exact (EQ_MP (@lem3754361 A u f s _43166) (@lem0)). Qed.
Lemma lem3754363 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1290 A u f s _43166.
Proof. exact (EQ_MP (@lem3754362 A u f s _43166) (@lem3754114 A _43166 f u s h1)). Qed.
Lemma lem3754365 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3754366 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type672 A) (_43166 : A -> Prop) : (term1290 A u f s _43166) = (term1293 A f s u _43166).
Proof. exact (@lem3754365 (term1147 A f s _43166) (term1245 A u _43166)). Qed.
Lemma lem3754368 (a : Prop) (b : Prop) : (term1279 a b) = (term1280 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3754369 {A : Type'} (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1281 A f s _43166) = (term1282 A f s _43166).
Proof. exact (@lem3754368 (term1095 A _43166 f) (term1081 A s _43166)). Qed.
Lemma lem3754371 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3754372 {A : Type'} (_43166 : A -> Prop) (f : type686 A) : (term1283 A _43166 f) = (@IN (A -> Prop) _43166 f).
Proof. exact (@lem3754371 (@IN (A -> Prop) _43166 f)). Qed.
Lemma lem3754373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3754374 {A : Type'} (_43166 : A -> Prop) (f : type686 A) : (term1284 A _43166 f) = (term65 A _43166 f).
Proof. exact (MK_COMB (@lem3754373) (@lem3754372 A _43166 f)). Qed.
Lemma lem3754376 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3754377 {A : Type'} (s : A -> Prop) (_43166 : A -> Prop) : (term1285 A s _43166) = (@SUBSET A s _43166).
Proof. exact (@lem3754376 (@SUBSET A s _43166)). Qed.
Lemma lem3754378 {A : Type'} (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1282 A f s _43166) = (term168 A f s _43166).
Proof. exact (MK_COMB (@lem3754374 A _43166 f) (@lem3754377 A s _43166)). Qed.
Lemma lem3754379 {A : Type'} (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1281 A f s _43166) = (term168 A f s _43166).
Proof. exact (TRANS (@lem3754369 A f s _43166) (@lem3754378 A f s _43166)). Qed.
Lemma lem3754380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3754381 {A : Type'} (f : type686 A) (s : A -> Prop) (_43166 : A -> Prop) : (term1286 A f s _43166) = (term280 A f s _43166).
Proof. exact (MK_COMB (@lem3754380) (@lem3754379 A f s _43166)). Qed.
Lemma lem3754382 {A : Type'} (u : type672 A) (_43166 : A -> Prop) : (term1245 A u _43166) = (term1245 A u _43166).
Proof. exact (eq_refl (term1245 A u _43166)). Qed.
Lemma lem3754383 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type672 A) (_43166 : A -> Prop) : (term1293 A f s u _43166) = (term1294 A f s u _43166).
Proof. exact (MK_COMB (@lem3754381 A f s _43166) (@lem3754382 A u _43166)). Qed.
Lemma lem3754384 {A : Type'} (f : type686 A) (s : A -> Prop) (u : type672 A) (_43166 : A -> Prop) : (term1290 A u f s _43166) = (term1294 A f s u _43166).
Proof. exact (TRANS (@lem3754366 A f s u _43166) (@lem3754383 A f s u _43166)). Qed.
Lemma lem3754386 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term168 A f s t.
Proof. exact (conj (@lem3754307 A f s t h1) (@lem3754314 A f s t h1)). Qed.
Lemma lem3754388 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1294 A f s u _43166.
Proof. exact (EQ_MP (@lem3754384 A f s u _43166) (@lem3754363 A _43166 f u s h1)). Qed.
Lemma lem3754389 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1294 A f s u _43166.
Proof. exact (@lem3754388 A _43166 f u s h1). Qed.
Lemma lem3754390 {A : Type'} (t : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1294 A f s u t.
Proof. exact (@lem3754389 A t f u s h1). Qed.
Lemma lem3754393 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1245 A u t.
Proof. exact (@lem3754390 A t f u s h1 (@lem3754386 A f s t h2)). Qed.
Lemma lem3754394 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1295 A u t.
Proof. exact (fun h0 : term1296 A u t => @lem3754393 A u f s t h1 h2). Qed.
Lemma lem3754396 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754397 {A : Type'} (u : type672 A) (t : A -> Prop) : (term1295 A u t) = (term1245 A u t).
Proof. exact (@lem3754396 (term1245 A u t)). Qed.
Lemma lem3754398 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1245 A u t.
Proof. exact (EQ_MP (@lem3754397 A u t) (@lem3754394 A u f s t h1 h2)). Qed.
Lemma lem3754404 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3754405 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) : (term1268 A _43161 _43160 _43162) = (term1297 A _43161 _43160 _43162).
Proof. exact (@lem3754404 (term581 A _43161 _43162) (term1081 A _43160 _43161) (@PSUBSET A _43160 _43162)). Qed.
Lemma lem3754419 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3754420 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1298 A _43161 _43160 _43162) = (term1299 A _43162 _43160 _43161).
Proof. exact (@lem3754419 (@PSUBSET A _43160 _43162) (term1081 A _43160 _43161)). Qed.
Lemma lem3754426 {A : Type'} (_43161 : A -> Prop) (_43162 : A -> Prop) : (term1300 A _43161 _43162) = (term1300 A _43161 _43162).
Proof. exact (eq_refl (term1300 A _43161 _43162)). Qed.
Lemma lem3754427 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1297 A _43161 _43160 _43162) = (term1301 A _43162 _43160 _43161).
Proof. exact (MK_COMB (@lem3754426 A _43161 _43162) (@lem3754420 A _43162 _43160 _43161)). Qed.
Lemma lem3754431 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3754432 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1301 A _43162 _43160 _43161) = (term1302 A _43162 _43160 _43161).
Proof. exact (@lem3754431 (@PSUBSET A _43160 _43162) (term581 A _43161 _43162) (term1081 A _43160 _43161)). Qed.
Lemma lem3754448 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1297 A _43161 _43160 _43162) = (term1302 A _43162 _43160 _43161).
Proof. exact (TRANS (@lem3754427 A _43162 _43160 _43161) (@lem3754432 A _43162 _43160 _43161)). Qed.
Lemma lem3754449 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1268 A _43161 _43160 _43162) = (term1302 A _43162 _43160 _43161).
Proof. exact (TRANS (@lem3754405 A _43161 _43160 _43162) (@lem3754448 A _43162 _43160 _43161)). Qed.
Lemma lem3754450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3754451 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1303 A _43161 _43160 _43162) = (term1304 A _43162 _43160 _43161).
Proof. exact (MK_COMB (@lem3754450) (@lem3754449 A _43162 _43160 _43161)). Qed.
Lemma lem3754465 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3754466 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1231 A _43160 _43161 _43162) = (term1305 A _43162 _43160 _43161).
Proof. exact (@lem3754465 (term581 A _43161 _43162) (term1081 A _43160 _43161)). Qed.
Lemma lem3754472 {A : Type'} (_43160 : A -> Prop) (_43162 : A -> Prop) : (term1175 A _43160 _43162) = (term1175 A _43160 _43162).
Proof. exact (eq_refl (term1175 A _43160 _43162)). Qed.
Lemma lem3754473 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1306 A _43160 _43161 _43162) = (term1302 A _43162 _43160 _43161).
Proof. exact (MK_COMB (@lem3754472 A _43160 _43162) (@lem3754466 A _43162 _43160 _43161)). Qed.
Lemma lem3754484 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : ((term1268 A _43161 _43160 _43162) = (term1306 A _43160 _43161 _43162)) = ((term1302 A _43162 _43160 _43161) = (term1302 A _43162 _43160 _43161)).
Proof. exact (MK_COMB (@lem3754451 A _43162 _43160 _43161) (@lem3754473 A _43162 _43160 _43161)). Qed.
Lemma lem3754486 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3754487 (x : Prop) : (x = x) = True.
Proof. exact (@lem3754486 Prop x). Qed.
Lemma lem3754488 {A : Type'} (_43162 : A -> Prop) (_43160 : A -> Prop) (_43161 : A -> Prop) : ((term1302 A _43162 _43160 _43161) = (term1302 A _43162 _43160 _43161)) = True.
Proof. exact (@lem3754487 (term1302 A _43162 _43160 _43161)). Qed.
Lemma lem3754489 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (_43162 : A -> Prop) : ((term1268 A _43161 _43160 _43162) = (term1306 A _43160 _43161 _43162)) = True.
Proof. exact (TRANS (@lem3754484 A _43162 _43160 _43161) (@lem3754488 A _43162 _43160 _43161)). Qed.
Lemma lem3754490 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (_43162 : A -> Prop) : True = ((term1268 A _43161 _43160 _43162) = (term1306 A _43160 _43161 _43162)).
Proof. exact (SYM (@lem3754489 A _43160 _43161 _43162)). Qed.
Lemma lem3754491 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (_43162 : A -> Prop) : (term1268 A _43161 _43160 _43162) = (term1306 A _43160 _43161 _43162).
Proof. exact (EQ_MP (@lem3754490 A _43160 _43161 _43162) (@lem0)). Qed.
Lemma lem3754492 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (_43162 : A -> Prop) (h1 : term1020 A) : term1306 A _43160 _43161 _43162.
Proof. exact (EQ_MP (@lem3754491 A _43160 _43161 _43162) (@lem3754040 A _43161 _43160 _43162 h1)). Qed.
Lemma lem3754494 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3754495 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) : (term1306 A _43160 _43161 _43162) = (term1307 A _43161 _43160 _43162).
Proof. exact (@lem3754494 (term1231 A _43160 _43161 _43162) (@PSUBSET A _43160 _43162)). Qed.
Lemma lem3754497 (a : Prop) (b : Prop) : (term1279 a b) = (term1280 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3754498 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (_43162 : A -> Prop) : (term1308 A _43160 _43161 _43162) = (term1309 A _43160 _43161 _43162).
Proof. exact (@lem3754497 (term1081 A _43160 _43161) (term581 A _43161 _43162)). Qed.
Lemma lem3754500 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3754501 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1285 A _43160 _43161) = (@SUBSET A _43160 _43161).
Proof. exact (@lem3754500 (@SUBSET A _43160 _43161)). Qed.
Lemma lem3754502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3754503 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) : (term1310 A _43160 _43161) = (term227 A _43160 _43161).
Proof. exact (MK_COMB (@lem3754502) (@lem3754501 A _43160 _43161)). Qed.
Lemma lem3754505 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3754506 {A : Type'} (_43161 : A -> Prop) (_43162 : A -> Prop) : (term1066 A _43161 _43162) = (@PSUBSET A _43161 _43162).
Proof. exact (@lem3754505 (@PSUBSET A _43161 _43162)). Qed.
Lemma lem3754507 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (_43162 : A -> Prop) : (term1309 A _43160 _43161 _43162) = (term199 A _43160 _43161 _43162).
Proof. exact (MK_COMB (@lem3754503 A _43160 _43161) (@lem3754506 A _43161 _43162)). Qed.
Lemma lem3754508 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (_43162 : A -> Prop) : (term1308 A _43160 _43161 _43162) = (term199 A _43160 _43161 _43162).
Proof. exact (TRANS (@lem3754498 A _43160 _43161 _43162) (@lem3754507 A _43160 _43161 _43162)). Qed.
Lemma lem3754509 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3754510 {A : Type'} (_43160 : A -> Prop) (_43161 : A -> Prop) (_43162 : A -> Prop) : (term1311 A _43160 _43161 _43162) = (term1312 A _43160 _43161 _43162).
Proof. exact (MK_COMB (@lem3754509) (@lem3754508 A _43160 _43161 _43162)). Qed.
Lemma lem3754511 {A : Type'} (_43160 : A -> Prop) (_43162 : A -> Prop) : (@PSUBSET A _43160 _43162) = (@PSUBSET A _43160 _43162).
Proof. exact (eq_refl (@PSUBSET A _43160 _43162)). Qed.
Lemma lem3754512 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) : (term1307 A _43161 _43160 _43162) = (term1057 A _43161 _43160 _43162).
Proof. exact (MK_COMB (@lem3754510 A _43160 _43161 _43162) (@lem3754511 A _43160 _43162)). Qed.
Lemma lem3754513 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) : (term1306 A _43160 _43161 _43162) = (term1057 A _43161 _43160 _43162).
Proof. exact (TRANS (@lem3754495 A _43161 _43160 _43162) (@lem3754512 A _43161 _43160 _43162)). Qed.
Lemma lem3754515 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1313 A s u t.
Proof. exact (conj (@lem3754300 A f s t h2) (@lem3754398 A u f s t h1 h2)). Qed.
Lemma lem3754517 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) (h1 : term1020 A) : term1057 A _43161 _43160 _43162.
Proof. exact (EQ_MP (@lem3754513 A _43161 _43160 _43162) (@lem3754492 A _43160 _43161 _43162 h1)). Qed.
Lemma lem3754518 {A : Type'} (_43161 : A -> Prop) (_43160 : A -> Prop) (_43162 : A -> Prop) (h1 : term1020 A) : term1057 A _43161 _43160 _43162.
Proof. exact (@lem3754517 A _43161 _43160 _43162 h1). Qed.
Lemma lem3754519 {A : Type'} (s : A -> Prop) (u : type672 A) (t : A -> Prop) (h1 : term1020 A) : term1314 A s u t.
Proof. exact (@lem3754518 A t s (u t) h1). Qed.
Lemma lem3754522 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1142 A f u s) (h3 : term1161 A f s t) : term1315 A s u t.
Proof. exact (@lem3754519 A s u t h1 (@lem3754515 A u f s t h2 h3)). Qed.
Lemma lem3754523 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1142 A f u s) (h3 : term1161 A f s t) : term1316 A s u t.
Proof. exact (fun h0 : term1317 A s u t => @lem3754522 A u f s t h1 h2 h3). Qed.
Lemma lem3754525 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754526 {A : Type'} (s : A -> Prop) (u : type672 A) (t : A -> Prop) : (term1316 A s u t) = (term1315 A s u t).
Proof. exact (@lem3754525 (term1315 A s u t)). Qed.
Lemma lem3754527 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1142 A f u s) (h3 : term1161 A f s t) : term1315 A s u t.
Proof. exact (EQ_MP (@lem3754526 A s u t) (@lem3754523 A u f s t h1 h2 h3)). Qed.
Lemma lem3754533 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3754534 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1270 A _43170 _43171) = (term1318 A _43170 _43171).
Proof. exact (@lem3754533 (@SUBSET A _43170 _43171) (term581 A _43170 _43171)). Qed.
Lemma lem3754540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3754541 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1319 A _43170 _43171) = (term1320 A _43170 _43171).
Proof. exact (MK_COMB (@lem3754540) (@lem3754534 A _43170 _43171)). Qed.
Lemma lem3754547 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1318 A _43170 _43171) = (term1318 A _43170 _43171).
Proof. exact (eq_refl (term1318 A _43170 _43171)). Qed.
Lemma lem3754548 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : ((term1270 A _43170 _43171) = (term1318 A _43170 _43171)) = ((term1318 A _43170 _43171) = (term1318 A _43170 _43171)).
Proof. exact (MK_COMB (@lem3754541 A _43170 _43171) (@lem3754547 A _43170 _43171)). Qed.
Lemma lem3754550 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3754551 (x : Prop) : (x = x) = True.
Proof. exact (@lem3754550 Prop x). Qed.
Lemma lem3754552 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : ((term1318 A _43170 _43171) = (term1318 A _43170 _43171)) = True.
Proof. exact (@lem3754551 (term1318 A _43170 _43171)). Qed.
Lemma lem3754553 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : ((term1270 A _43170 _43171) = (term1318 A _43170 _43171)) = True.
Proof. exact (TRANS (@lem3754548 A _43170 _43171) (@lem3754552 A _43170 _43171)). Qed.
Lemma lem3754554 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : True = ((term1270 A _43170 _43171) = (term1318 A _43170 _43171)).
Proof. exact (SYM (@lem3754553 A _43170 _43171)). Qed.
Lemma lem3754555 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1270 A _43170 _43171) = (term1318 A _43170 _43171).
Proof. exact (EQ_MP (@lem3754554 A _43170 _43171) (@lem0)). Qed.
Lemma lem3754556 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) (h1 : term1021 A) : term1318 A _43170 _43171.
Proof. exact (EQ_MP (@lem3754555 A _43170 _43171) (@lem3754084 A _43170 _43171 h1)). Qed.
Lemma lem3754558 (b : Prop) (a : Prop) : (a \/ b) = (term572 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3754559 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1318 A _43170 _43171) = (term1321 A _43170 _43171).
Proof. exact (@lem3754558 (term581 A _43170 _43171) (@SUBSET A _43170 _43171)). Qed.
Lemma lem3754561 (a : Prop) : (term14 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3754562 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1066 A _43170 _43171) = (@PSUBSET A _43170 _43171).
Proof. exact (@lem3754561 (@PSUBSET A _43170 _43171)). Qed.
Lemma lem3754563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3754564 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1322 A _43170 _43171) = (term1323 A _43170 _43171).
Proof. exact (MK_COMB (@lem3754563) (@lem3754562 A _43170 _43171)). Qed.
Lemma lem3754565 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (@SUBSET A _43170 _43171) = (@SUBSET A _43170 _43171).
Proof. exact (eq_refl (@SUBSET A _43170 _43171)). Qed.
Lemma lem3754566 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1321 A _43170 _43171) = (term1324 A _43170 _43171).
Proof. exact (MK_COMB (@lem3754564 A _43170 _43171) (@lem3754565 A _43170 _43171)). Qed.
Lemma lem3754567 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) : (term1318 A _43170 _43171) = (term1324 A _43170 _43171).
Proof. exact (TRANS (@lem3754559 A _43170 _43171) (@lem3754566 A _43170 _43171)). Qed.
Lemma lem3754570 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) (h1 : term1021 A) : term1324 A _43170 _43171.
Proof. exact (EQ_MP (@lem3754567 A _43170 _43171) (@lem3754556 A _43170 _43171 h1)). Qed.
Lemma lem3754571 {A : Type'} (_43170 : A -> Prop) (_43171 : A -> Prop) (h1 : term1021 A) : term1324 A _43170 _43171.
Proof. exact (@lem3754570 A _43170 _43171 h1). Qed.
Lemma lem3754572 {A : Type'} (s : A -> Prop) (u : type672 A) (t : A -> Prop) (h1 : term1021 A) : term1325 A s u t.
Proof. exact (@lem3754571 A s (u t) h1). Qed.
Lemma lem3754575 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : term1326 A s u t.
Proof. exact (@lem3754572 A s u t h2 (@lem3754527 A u f s t h1 h3 h4)). Qed.
Lemma lem3754576 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : term1327 A s u t.
Proof. exact (fun h0 : term1328 A s u t => @lem3754575 A u f s t h1 h2 h3 h4). Qed.
Lemma lem3754578 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754579 {A : Type'} (s : A -> Prop) (u : type672 A) (t : A -> Prop) : (term1327 A s u t) = (term1326 A s u t).
Proof. exact (@lem3754578 (term1326 A s u t)). Qed.
Lemma lem3754580 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : term1326 A s u t.
Proof. exact (EQ_MP (@lem3754579 A s u t) (@lem3754576 A u f s t h1 h2 h3 h4)). Qed.
Lemma lem3754582 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @IN (A -> Prop) t f.
Proof. exact (proj1 (@lem3753812 A f s t h1)). Qed.
Lemma lem3754583 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1273 A t f.
Proof. exact (fun h0 : term1095 A t f => @lem3754582 A f s t h1). Qed.
Lemma lem3754585 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754586 {A : Type'} (t : A -> Prop) (f : type686 A) : (term1273 A t f) = (@IN (A -> Prop) t f).
Proof. exact (@lem3754585 (@IN (A -> Prop) t f)). Qed.
Lemma lem3754587 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @IN (A -> Prop) t f.
Proof. exact (EQ_MP (@lem3754586 A t f) (@lem3754583 A f s t h1)). Qed.
Lemma lem3754589 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @SUBSET A s t.
Proof. exact (proj2 (@lem3753812 A f s t h1)). Qed.
Lemma lem3754590 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1274 A s t.
Proof. exact (fun h0 : term1081 A s t => @lem3754589 A f s t h1). Qed.
Lemma lem3754592 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754593 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1274 A s t) = (@SUBSET A s t).
Proof. exact (@lem3754592 (@SUBSET A s t)). Qed.
Lemma lem3754594 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3754593 A s t) (@lem3754590 A f s t h1)). Qed.
Lemma lem3754595 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term168 A f s t.
Proof. exact (conj (@lem3754587 A f s t h1) (@lem3754594 A f s t h1)). Qed.
Lemma lem3754597 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1294 A f s u _43166.
Proof. exact (EQ_MP (@lem3754384 A f s u _43166) (@lem3754363 A _43166 f u s h1)). Qed.
Lemma lem3754598 {A : Type'} (_43166 : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1294 A f s u _43166.
Proof. exact (@lem3754597 A _43166 f u s h1). Qed.
Lemma lem3754599 {A : Type'} (t : A -> Prop) (f : type686 A) (u : type672 A) (s : A -> Prop) (h1 : term1142 A f u s) : term1294 A f s u t.
Proof. exact (@lem3754598 A t f u s h1). Qed.
Lemma lem3754602 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1245 A u t.
Proof. exact (@lem3754599 A t f u s h1 (@lem3754595 A f s t h2)). Qed.
Lemma lem3754603 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1295 A u t.
Proof. exact (fun h0 : term1296 A u t => @lem3754602 A u f s t h1 h2). Qed.
Lemma lem3754605 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754606 {A : Type'} (u : type672 A) (t : A -> Prop) : (term1295 A u t) = (term1245 A u t).
Proof. exact (@lem3754605 (term1245 A u t)). Qed.
Lemma lem3754607 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1142 A f u s) (h2 : term1161 A f s t) : term1245 A u t.
Proof. exact (EQ_MP (@lem3754606 A u t) (@lem3754603 A u f s t h1 h2)). Qed.
Lemma lem3754609 (a : Prop) (b : Prop) : (term1009 a b) = (term1010 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3754610 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_43167 : A -> Prop) : (term1329 A s t _43167) = (term1330 A s t _43167).
Proof. exact (@lem3754609 (@SUBSET A s _43167) (@PSUBSET A t _43167)). Qed.
Lemma lem3754611 {A : Type'} (_43167 : A -> Prop) (f : type686 A) : (term1077 A _43167 f) = (term1077 A _43167 f).
Proof. exact (eq_refl (term1077 A _43167 f)). Qed.
Lemma lem3754612 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (_43167 : A -> Prop) : (term1269 A f s t _43167) = (term1331 A f s t _43167).
Proof. exact (MK_COMB (@lem3754611 A _43167 f) (@lem3754610 A s t _43167)). Qed.
Lemma lem3754614 (a : Prop) (b : Prop) : (term1009 a b) = (term1010 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3754615 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (_43167 : A -> Prop) : (term1331 A f s t _43167) = (term1332 A f s t _43167).
Proof. exact (@lem3754614 (@IN (A -> Prop) _43167 f) (term1333 A s t _43167)). Qed.
Lemma lem3754616 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (_43167 : A -> Prop) : (term1269 A f s t _43167) = (term1332 A f s t _43167).
Proof. exact (TRANS (@lem3754612 A f s t _43167) (@lem3754615 A f s t _43167)). Qed.
Lemma lem3754618 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3754619 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (_43167 : A -> Prop) : (term1332 A f s t _43167) = (term1334 A f s t _43167).
Proof. exact (@lem3754618 (term1335 A f s t _43167)). Qed.
Lemma lem3754620 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (_43167 : A -> Prop) : (term1269 A f s t _43167) = (term1334 A f s t _43167).
Proof. exact (TRANS (@lem3754616 A f s t _43167) (@lem3754619 A f s t _43167)). Qed.
Lemma lem3754622 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : term1336 A s u t.
Proof. exact (conj (@lem3754580 A u f s t h1 h2 h3 h4) (@lem3754607 A u f s t h3 h4)). Qed.
Lemma lem3754623 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : term1337 A f s u t.
Proof. exact (conj (@lem3754293 A u f s t h3 h4) (@lem3754622 A u f s t h1 h2 h3 h4)). Qed.
Lemma lem3754625 {A : Type'} (_43167 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1334 A f s t _43167.
Proof. exact (EQ_MP (@lem3754620 A f s t _43167) (@lem3754064 A _43167 f s t h1)). Qed.
Lemma lem3754626 {A : Type'} (_43167 : A -> Prop) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1334 A f s t _43167.
Proof. exact (@lem3754625 A _43167 f s t h1). Qed.
Lemma lem3754627 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1161 A f s t) : term1338 A f s u t.
Proof. exact (@lem3754626 A (u t) f s t h1). Qed.
Lemma lem3754630 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : False.
Proof. exact (@lem3754627 A u f s t h4 (@lem3754623 A u f s t h1 h2 h3 h4)). Qed.
Lemma lem3754631 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : term577.
Proof. exact (fun h0 : ~ False => @lem3754630 A u f s t h1 h2 h3 h4). Qed.
Lemma lem3754633 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3754634 : term577 = False.
Proof. exact (@lem3754633 False). Qed.
Lemma lem3754635 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : False.
Proof. exact (EQ_MP (@lem3754634) (@lem3754631 A u f s t h1 h2 h3 h4)). Qed.
Lemma lem3754636 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : (term1142 A f u s) = False.
Proof. exact (prop_ext (fun h5 : term1142 A f u s => @lem3754635 A u f s t h1 h2 h3 h4) (fun h5 : False => @lem3753810 A f u s h3)). Qed.
Lemma lem3754637 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : False.
Proof. exact (EQ_MP (@lem3754636 A u f s t h1 h2 h3 h4) (@lem3753810 A f u s h3)). Qed.
Lemma lem3754638 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : (term1161 A f s t) = False.
Proof. exact (prop_ext (fun h5 : term1161 A f s t => @lem3754637 A u f s t h1 h2 h3 h4) (fun h5 : False => @lem3753769 A f s t h4)). Qed.
Lemma lem3754639 {A : Type'} (u : type672 A) (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1142 A f u s) (h4 : term1161 A f s t) : False.
Proof. exact (EQ_MP (@lem3754638 A u f s t h1 h2 h3 h4) (@lem3753769 A f s t h4)). Qed.
Lemma lem3754640 {A : Type'} (f : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term143 A f s) (h4 : term1161 A f s t) : False.
Proof. exact (ex_elim (@lem3752967 A f s h3) (fun u : type672 A => fun h0 : term1144 A f s u => @lem3754639 A u f s t h1 h2 h0 h4)). Qed.
Lemma lem3754641 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1018 A f s) (h4 : term143 A f s) : False.
Proof. exact (ex_elim (@lem3753111 A f s h3) (fun t : A -> Prop => fun h0 : term1167 A f s t => @lem3754640 A f s t h1 h2 h4 h0)). Qed.
Lemma lem3754642 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1018 A f s) (h4 : term143 A f s) : term1026 A.
Proof. exact (fun h0 : term1019 A => @lem3754641 A f s h1 h2 h3 h4). Qed.
Lemma lem3754643 {A : Type'} : (term1026 A) = (term1027 A).
Proof. exact (@lem69 (term1019 A)). Qed.
Lemma lem3754644 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1020 A) (h2 : term1021 A) (h3 : term1018 A f s) (h4 : term143 A f s) : term1027 A.
Proof. exact (EQ_MP (@lem3754643 A) (@lem3754642 A f s h1 h2 h3 h4)). Qed.
Lemma lem3754645 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1021 A) (h2 : term1018 A f s) (h3 : term143 A f s) : term1030 A.
Proof. exact (fun h0 : term1020 A => @lem3754644 A f s h0 h1 h2 h3). Qed.
Lemma lem3754646 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term1018 A f s) (h2 : term143 A f s) : term1033 A.
Proof. exact (fun h0 : term1021 A => @lem3754645 A f s h0 h1 h2). Qed.
Lemma lem3754647 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term143 A f s) : term1036 A f s.
Proof. exact (fun h0 : term1018 A f s => @lem3754646 A f s h0 h1). Qed.
Lemma lem3754648 {A : Type'} (f : type686 A) (s : A -> Prop) : term1039 A f s.
Proof. exact (fun h0 : term143 A f s => @lem3754647 A f s h0). Qed.
Lemma lem3754649 {A : Type'} (f : type686 A) (s : A -> Prop) : term1041 A f s.
Proof. exact (fun h0 : @IN (A -> Prop) s f => @lem3754648 A f s). Qed.
Lemma lem3754650 {A : Type'} (f : type686 A) (s : A -> Prop) : term1042 A f s.
Proof. exact (fun h0 : @FINITE (A -> Prop) f => @lem3754649 A f s). Qed.
Lemma lem3754655 {A : Type'} (s : A -> Prop) : term1046 A s.
Proof. exact (fun f : type686 A => @lem3754650 A f s). Qed.
Lemma lem3754660 {A : Type'} : term1050 A.
Proof. exact (fun s : A -> Prop => @lem3754655 A s). Qed.
Lemma lem3754661 {A : Type'} : term1049 A.
Proof. exact (EQ_MP (@lem3752724 A) (@lem3754660 A)). Qed.
Lemma lem3754662 {A : Type'} (s : A -> Prop) : term1339 A s.
Proof. exact (@lem3754661 A s). Qed.
Lemma lem3754663 {A : Type'} (s : A -> Prop) : (term1339 A s) = (term1045 A s).
Proof. exact (eq_refl (term1339 A s)). Qed.
Lemma lem3754664 {A : Type'} (s : A -> Prop) : term1045 A s.
Proof. exact (EQ_MP (@lem3754663 A s) (@lem3754662 A s)). Qed.
Lemma lem3754665 {A : Type'} (s : A -> Prop) (f : type686 A) : term1340 A s f.
Proof. exact (@lem3754664 A s f). Qed.
Lemma lem3754666 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1340 A s f) = (term1022 A f s).
Proof. exact (eq_refl (term1340 A s f)). Qed.
Lemma lem3754667 {A : Type'} (f : type686 A) (s : A -> Prop) : term1022 A f s.
Proof. exact (EQ_MP (@lem3754666 A f s) (@lem3754665 A s f)). Qed.
Lemma lem3754669 {A : Type'} (f : type686 A) (s : A -> Prop) : term1022 A f s.
Proof. exact (@lem3752246 A f s (@lem3754667 A f s)). Qed.
Lemma lem3754670 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : term1040 A f s.
Proof. exact (@lem3754669 A f s (@lem3744244 A f h1)). Qed.
Lemma lem3754671 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : @IN (A -> Prop) s f) : term1038 A f s.
Proof. exact (@lem3754670 A s f h1 (@lem3744249 A s f h2)). Qed.
Lemma lem3754672 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term1035 A f s.
Proof. exact (@lem3754671 A s f h1 h3 (@lem3744332 A f s h2)). Qed.
Lemma lem3754673 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term1018 A f s) (h3 : term143 A f s) (h4 : @IN (A -> Prop) s f) : term1032 A.
Proof. exact (@lem3754672 A s f h1 h3 h4 (@lem3752225 A f s h2)). Qed.
Lemma lem3754674 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term1018 A f s) (h3 : term143 A f s) (h4 : @IN (A -> Prop) s f) : term1029 A.
Proof. exact (@lem3754673 A s f h1 h2 h3 h4 (@lem3752229 A)). Qed.
Lemma lem3754675 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term1018 A f s) (h3 : term143 A f s) (h4 : @IN (A -> Prop) s f) : term1026 A.
Proof. exact (@lem3754674 A s f h1 h2 h3 h4 (@lem3752227 A)). Qed.
Lemma lem3754676 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term1018 A f s) (h3 : term143 A f s) (h4 : @IN (A -> Prop) s f) : False.
Proof. exact (@lem3754675 A s f h1 h2 h3 h4 (@lem3752226 A)). Qed.
Lemma lem3754677 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term1018 A f s) (h3 : term143 A f s) (h4 : @IN (A -> Prop) s f) : (term1018 A f s) = False.
Proof. exact (prop_ext (fun h5 : term1018 A f s => @lem3754676 A s f h1 h2 h3 h4) (fun h5 : False => @lem3752225 A f s h2)). Qed.
Lemma lem3754678 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term1018 A f s) (h3 : term143 A f s) (h4 : @IN (A -> Prop) s f) : False.
Proof. exact (EQ_MP (@lem3754677 A s f h1 h2 h3 h4) (@lem3752225 A f s h2)). Qed.
Lemma lem3754679 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term1017 A f s.
Proof. exact (fun h0 : term1018 A f s => @lem3754678 A s f h1 h0 h2 h3). Qed.
Lemma lem3754680 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term333 A f s.
Proof. exact (EQ_MP (@lem3752224 A f s) (@lem3754679 A s f h1 h2 h3)). Qed.
Lemma lem3754681 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term335 A f s.
Proof. exact (conj (@lem3749900 A s) (@lem3754680 A s f h1 h2 h3)). Qed.
Lemma lem3754682 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term337 A f s.
Proof. exact (conj (@lem3746202 A s) (@lem3754681 A s f h1 h2 h3)). Qed.
Lemma lem3754683 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term342 A f s.
Proof. exact (conj (@lem3754682 A s f h1 h2 h3) (@lem3752220 A s f h1 h2 h3)). Qed.
Lemma lem3754684 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : term160 A f s.
Proof. exact (EQ_MP (@lem3746122 A s f h1) (@lem3754683 A s f h1 h2 h3)). Qed.
Lemma lem3754685 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : term143 A f s) (h3 : @IN (A -> Prop) s f) : False.
Proof. exact (@lem3754684 A s f h1 h2 h3 (@lem3743418 A f s)). Qed.
Lemma lem3754686 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : @IN (A -> Prop) s f) : term1341 A f s.
Proof. exact (fun h0 : term143 A f s => @lem3754685 A s f h1 h0 h2). Qed.
Lemma lem3754687 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1341 A f s) = (term142 A f s).
Proof. exact (@lem69 (term143 A f s)). Qed.
Lemma lem3754688 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : @IN (A -> Prop) s f) : term142 A f s.
Proof. exact (EQ_MP (@lem3754687 A f s) (@lem3754686 A s f h1 h2)). Qed.
Lemma lem3754689 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : @IN (A -> Prop) s f) : term141 A f s.
Proof. exact (EQ_MP (@lem3744331 A f s) (@lem3754688 A s f h1 h2)). Qed.
Lemma lem3754690 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) (h2 : @IN (A -> Prop) s f) : term121 A f s.
Proof. exact (EQ_MP (@lem3744327 A f s) (@lem3754689 A s f h1 h2)). Qed.
Lemma lem3754691 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : @FINITE (A -> Prop) f) : term1342 A f s.
Proof. exact (fun h0 : @IN (A -> Prop) s f => @lem3754690 A s f h1 h0). Qed.
Lemma lem3754696 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : term1343 A f.
Proof. exact (fun s : A -> Prop => @lem3754691 A s f h1). Qed.
Lemma lem3754697 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : term86 A f.
Proof. exact (@lem3744248 A f (@lem3754696 A f h1)). Qed.
Lemma lem3754698 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (@FINITE (A -> Prop) f) = (term86 A f).
Proof. exact (prop_ext (fun h2 : @FINITE (A -> Prop) f => @lem3754697 A f h1) (fun h2 : term86 A f => @lem3744244 A f h1)). Qed.
Lemma lem3754699 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : term86 A f.
Proof. exact (EQ_MP (@lem3754698 A f h1) (@lem3744244 A f h1)). Qed.
Lemma lem3754700 {A : Type'} (f : type686 A) : term91 A f.
Proof. exact (fun h0 : @FINITE (A -> Prop) f => @lem3754699 A f h0). Qed.
Lemma lem3754705 {A : Type'} : term95 A.
Proof. exact (fun f : type686 A => @lem3754700 A f). Qed.
Lemma lem3754706 {A : Type'} : term94 A.
Proof. exact (EQ_MP (@lem3744243 A) (@lem3754705 A)). Qed.
