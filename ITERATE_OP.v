Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_OP_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import MONOIDAL_AC_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
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
Require Import thm82_spec.
Lemma lem6007454 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6007455 {A : Type'} (P : type686 A) (h1 : term0 A) : term1 A P.
Proof. exact (@lem6007454 A h1 P). Qed.
Lemma lem6007456 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6007457 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem6007456 A P) (@lem6007455 A P h1)). Qed.
Lemma lem6007458 {A : Type'} (P : type686 A) (h1 : term3 A P) : term3 A P.
Proof. exact (h1). Qed.
Lemma lem6007459 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem6007457 A P h1 (@lem6007458 A P h2)). Qed.
Lemma lem6007460 {A : Type'} (P : type686 A) (h1 : term3 A P) : term5 A P.
Proof. exact (fun h0 : term0 A => @lem6007459 A P h0 h1). Qed.
Lemma lem6007461 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6007462 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem6007460 A P h2 (@lem6007461 A h1)). Qed.
Lemma lem6007463 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (fun h0 : term3 A P => @lem6007462 A P h1 h0). Qed.
Lemma lem6007464 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : type686 A => @lem6007463 A P h1). Qed.
Lemma lem6007465 {A : Type'} : term6 A.
Proof. exact (fun h0 : term0 A => @lem6007464 A h0). Qed.
Lemma lem6007466 {A : Type'} : term0 A.
Proof. exact (@lem6007465 A (@lem3558722 A)). Qed.
Lemma lem6007467 {A : Type'} (P : type686 A) : term1 A P.
Proof. exact (@lem6007466 A P). Qed.
Lemma lem6007468 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6007470 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (h1). Qed.
Lemma lem6007472 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (EQ_MP (@lem6007468 A P) (@lem6007467 A P)). Qed.
Lemma lem6007473 {_122572 : Type'} (P : type686 _122572) : term2 _122572 P.
Proof. exact (@lem6007472 _122572 P). Qed.
Lemma lem6007474 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : term7 _122572 _122573 f op g.
Proof. exact (@lem6007473 _122572 (term8 _122572 _122573 f op g)). Qed.
Lemma lem6007475 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term9 _122572 _122573 f op g) = ((term10 _122572 _122573 op f g) = (term11 _122572 _122573 f op g)).
Proof. exact (eq_refl (term9 _122572 _122573 f op g)). Qed.
Lemma lem6007476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6007477 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term12 _122572 _122573 f op g) = (term13 _122572 _122573 f op g).
Proof. exact (MK_COMB (@lem6007476) (@lem6007475 _122572 _122573 f op g)). Qed.
Lemma lem6007478 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term14 _122572 _122573 f op g s) = ((term15 _122572 _122573 s op f g) = (term16 _122572 _122573 f op s g)).
Proof. exact (eq_refl (term14 _122572 _122573 f op g s)). Qed.
Lemma lem6007479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6007480 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term17 _122572 _122573 f op g s) = (term18 _122572 _122573 f op s g).
Proof. exact (MK_COMB (@lem6007479) (@lem6007478 _122572 _122573 f op s g)). Qed.
Lemma lem6007481 {_122572 : Type'} (x : _122572) (s : _122572 -> Prop) : (term19 _122572 x s) = (term19 _122572 x s).
Proof. exact (eq_refl (term19 _122572 x s)). Qed.
Lemma lem6007482 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) : (term20 _122572 _122573 f op g x s) = (term21 _122572 _122573 f op g x s).
Proof. exact (MK_COMB (@lem6007480 _122572 _122573 f op s g) (@lem6007481 _122572 x s)). Qed.
Lemma lem6007483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6007484 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) : (term22 _122572 _122573 f op g x s) = (term23 _122572 _122573 f op g x s).
Proof. exact (MK_COMB (@lem6007483) (@lem6007482 _122572 _122573 f op g x s)). Qed.
Lemma lem6007485 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term24 _122572 _122573 f op g x s) = ((term25 _122572 _122573 x s op f g) = (term26 _122572 _122573 f op x s g)).
Proof. exact (eq_refl (term24 _122572 _122573 f op g x s)). Qed.
Lemma lem6007486 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term27 _122572 _122573 f op g x s) = (term28 _122572 _122573 f op x s g).
Proof. exact (MK_COMB (@lem6007484 _122572 _122573 f op g x s) (@lem6007485 _122572 _122573 f op x s g)). Qed.
Lemma lem6007487 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (g : _122572 -> _122573) : (term29 _122572 _122573 f op g x) = (term30 _122572 _122573 f op x g).
Proof. exact (fun_ext (fun s : _122572 -> Prop => @lem6007486 _122572 _122573 f op x s g)). Qed.
Lemma lem6007488 {_122572 : Type'} : (@all (_122572 -> Prop)) = (@all (_122572 -> Prop)).
Proof. exact (eq_refl (@all (_122572 -> Prop))). Qed.
Lemma lem6007489 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (g : _122572 -> _122573) : (term31 _122572 _122573 f op g x) = (term32 _122572 _122573 f op x g).
Proof. exact (MK_COMB (@lem6007488 _122572) (@lem6007487 _122572 _122573 f op x g)). Qed.
Lemma lem6007490 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term33 _122572 _122573 f op g) = (term34 _122572 _122573 f op g).
Proof. exact (fun_ext (fun x : _122572 => @lem6007489 _122572 _122573 f op x g)). Qed.
Lemma lem6007491 {_122572 : Type'} : (@all _122572) = (@all _122572).
Proof. exact (eq_refl (@all _122572)). Qed.
Lemma lem6007492 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term35 _122572 _122573 f op g) = (term36 _122572 _122573 f op g).
Proof. exact (MK_COMB (@lem6007491 _122572) (@lem6007490 _122572 _122573 f op g)). Qed.
Lemma lem6007493 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term37 _122572 _122573 f op g) = (term38 _122572 _122573 f op g).
Proof. exact (MK_COMB (@lem6007477 _122572 _122573 f op g) (@lem6007492 _122572 _122573 f op g)). Qed.
Lemma lem6007494 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6007495 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term39 _122572 _122573 f op g) = (term40 _122572 _122573 f op g).
Proof. exact (MK_COMB (@lem6007494) (@lem6007493 _122572 _122573 f op g)). Qed.
Lemma lem6007496 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term14 _122572 _122573 f op g s) = ((term15 _122572 _122573 s op f g) = (term16 _122572 _122573 f op s g)).
Proof. exact (eq_refl (term14 _122572 _122573 f op g s)). Qed.
Lemma lem6007497 {_122572 : Type'} (s : _122572 -> Prop) : (term41 _122572 s) = (term41 _122572 s).
Proof. exact (eq_refl (term41 _122572 s)). Qed.
Lemma lem6007498 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term42 _122572 _122573 f op g s) = (term43 _122572 _122573 f op s g).
Proof. exact (MK_COMB (@lem6007497 _122572 s) (@lem6007496 _122572 _122573 f op s g)). Qed.
Lemma lem6007499 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term44 _122572 _122573 f op g) = (term45 _122572 _122573 f op g).
Proof. exact (fun_ext (fun s : _122572 -> Prop => @lem6007498 _122572 _122573 f op s g)). Qed.
Lemma lem6007500 {_122572 : Type'} : (@all (_122572 -> Prop)) = (@all (_122572 -> Prop)).
Proof. exact (eq_refl (@all (_122572 -> Prop))). Qed.
Lemma lem6007501 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term46 _122572 _122573 f op g) = (term47 _122572 _122573 f op g).
Proof. exact (MK_COMB (@lem6007500 _122572) (@lem6007499 _122572 _122573 f op g)). Qed.
Lemma lem6007502 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : (term7 _122572 _122573 f op g) = (term48 _122572 _122573 f op g).
Proof. exact (MK_COMB (@lem6007495 _122572 _122573 f op g) (@lem6007501 _122572 _122573 f op g)). Qed.
Lemma lem6007503 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) : term48 _122572 _122573 f op g.
Proof. exact (EQ_MP (@lem6007502 _122572 _122573 f op g) (@lem6007474 _122572 _122573 f op g)). Qed.
Lemma lem6007504 {_119721 : Type'} (op : type1400 _119721) : term49 _119721 op.
Proof. exact (@lem5715484 _119721 op). Qed.
Lemma lem6007505 {_119721 : Type'} (op : type1400 _119721) : (term49 _119721 op) = (term50 _119721 op).
Proof. exact (eq_refl (term49 _119721 op)). Qed.
Lemma lem6007506 {_119721 : Type'} (op : type1400 _119721) : term50 _119721 op.
Proof. exact (EQ_MP (@lem6007505 _119721 op) (@lem6007504 _119721 op)). Qed.
Lemma lem6007507 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : @monoidal _119721 op.
Proof. exact (h1). Qed.
Lemma lem6007508 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : term51 _119721 op.
Proof. exact (@lem6007506 _119721 op (@lem6007507 _119721 op h1)). Qed.
Lemma lem6007509 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : term52 _119721 op.
Proof. exact (proj2 (@lem6007508 _119721 op h1)). Qed.
Lemma lem6007510 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : term53 _119721 op.
Proof. exact (proj2 (@lem6007509 _119721 op h1)). Qed.
Lemma lem6007511 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : term54 _119721 op.
Proof. exact (proj2 (@lem6007510 _119721 op h1)). Qed.
Lemma lem6007512 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : term55 _119721 op.
Proof. exact (proj2 (@lem6007511 _119721 op h1)). Qed.
Lemma lem6007513 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term56 _119721 op a.
Proof. exact (@lem6007512 _119721 op h1 a). Qed.
Lemma lem6007514 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term56 _119721 op a) = (term57 _119721 op a).
Proof. exact (eq_refl (term56 _119721 op a)). Qed.
Lemma lem6007515 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term57 _119721 op a.
Proof. exact (EQ_MP (@lem6007514 _119721 op a) (@lem6007513 _119721 a op h1)). Qed.
Lemma lem6007516 {_119721 : Type'} (a : _119721) (b : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term58 _119721 op a b.
Proof. exact (@lem6007515 _119721 a op h1 b). Qed.
Lemma lem6007517 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term58 _119721 op a b) = (term59 _119721 b op a).
Proof. exact (eq_refl (term58 _119721 op a b)). Qed.
Lemma lem6007518 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term59 _119721 b op a.
Proof. exact (EQ_MP (@lem6007517 _119721 b op a) (@lem6007516 _119721 a b op h1)). Qed.
Lemma lem6007519 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term60 _119721 b op a c.
Proof. exact (@lem6007518 _119721 b a op h1 c). Qed.
Lemma lem6007520 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term60 _119721 b op a c) = ((term61 _119721 a op b c) = (term61 _119721 b op a c)).
Proof. exact (eq_refl (term60 _119721 b op a c)). Qed.
Lemma lem6007521 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : (term61 _119721 a op b c) = (term61 _119721 b op a c).
Proof. exact (EQ_MP (@lem6007520 _119721 b op a c) (@lem6007519 _119721 b a c op h1)). Qed.
Lemma lem6007527 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : term62 _119721 op.
Proof. exact (proj1 (@lem6007511 _119721 op h1)). Qed.
Lemma lem6007528 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term63 _119721 op a.
Proof. exact (@lem6007527 _119721 op h1 a). Qed.
Lemma lem6007529 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term63 _119721 op a) = (term64 _119721 a op).
Proof. exact (eq_refl (term63 _119721 op a)). Qed.
Lemma lem6007530 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term64 _119721 a op.
Proof. exact (EQ_MP (@lem6007529 _119721 a op) (@lem6007528 _119721 a op h1)). Qed.
Lemma lem6007531 {_119721 : Type'} (a : _119721) (b : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term65 _119721 a op b.
Proof. exact (@lem6007530 _119721 a op h1 b). Qed.
Lemma lem6007532 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term65 _119721 a op b) = (term66 _119721 a op b).
Proof. exact (eq_refl (term65 _119721 a op b)). Qed.
Lemma lem6007533 {_119721 : Type'} (a : _119721) (b : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term66 _119721 a op b.
Proof. exact (EQ_MP (@lem6007532 _119721 a op b) (@lem6007531 _119721 a b op h1)). Qed.
Lemma lem6007534 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term67 _119721 a op b c.
Proof. exact (@lem6007533 _119721 a b op h1 c). Qed.
Lemma lem6007535 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term67 _119721 a op b c) = ((term68 _119721 op a b c) = (term61 _119721 a op b c)).
Proof. exact (eq_refl (term67 _119721 a op b c)). Qed.
Lemma lem6007536 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : (term68 _119721 op a b c) = (term61 _119721 a op b c).
Proof. exact (EQ_MP (@lem6007535 _119721 a op b c) (@lem6007534 _119721 a b c op h1)). Qed.
Lemma lem6007542 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : term69 _119721 op.
Proof. exact (proj1 (@lem6007510 _119721 op h1)). Qed.
Lemma lem6007543 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term70 _119721 op a.
Proof. exact (@lem6007542 _119721 op h1 a). Qed.
Lemma lem6007544 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term70 _119721 op a) = (term71 _119721 op a).
Proof. exact (eq_refl (term70 _119721 op a)). Qed.
Lemma lem6007545 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term71 _119721 op a.
Proof. exact (EQ_MP (@lem6007544 _119721 op a) (@lem6007543 _119721 a op h1)). Qed.
Lemma lem6007546 {_119721 : Type'} (a : _119721) (b : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term72 _119721 op a b.
Proof. exact (@lem6007545 _119721 a op h1 b). Qed.
Lemma lem6007547 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term72 _119721 op a b) = ((op a b) = (op b a)).
Proof. exact (eq_refl (term72 _119721 op a b)). Qed.
Lemma lem6007548 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : (op a b) = (op b a).
Proof. exact (EQ_MP (@lem6007547 _119721 op b a) (@lem6007546 _119721 a b op h1)). Qed.
Lemma lem6007554 {_119721 : Type'} (op : type1400 _119721) (h1 : @monoidal _119721 op) : term73 _119721 op.
Proof. exact (proj1 (@lem6007509 _119721 op h1)). Qed.
Lemma lem6007555 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : term74 _119721 op a.
Proof. exact (@lem6007554 _119721 op h1 a). Qed.
Lemma lem6007556 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term74 _119721 op a) = ((term75 _119721 a op) = a).
Proof. exact (eq_refl (term74 _119721 op a)). Qed.
Lemma lem6007557 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : @monoidal _119721 op) : (term75 _119721 a op) = a.
Proof. exact (EQ_MP (@lem6007556 _119721 op a) (@lem6007555 _119721 a op h1)). Qed.
Lemma lem6007572 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term76 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6007573 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term76 _120477 _120519 _120521 op) = (term77 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term76 _120477 _120519 _120521 op)). Qed.
Lemma lem6007574 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term77 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6007573 _120477 _120519 _120521 op) (@lem6007572 _120477 _120519 _120521 op)). Qed.
Lemma lem6007575 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6007576 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term78 _120477 _120519 _120521 op.
Proof. exact (@lem6007574 _120477 _120519 _120521 op (@lem6007575 _120519 op h1)). Qed.
Lemma lem6007577 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term79 _120519 _120521 op.
Proof. exact (proj2 (@lem6007576 Prop _120519 _120521 op h1)). Qed.
Lemma lem6007578 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term80 _120519 _120521 op f.
Proof. exact (@lem6007577 _120519 _120521 op h1 f). Qed.
Lemma lem6007579 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term80 _120519 _120521 op f) = (term81 _120519 _120521 op f).
Proof. exact (eq_refl (term80 _120519 _120521 op f)). Qed.
Lemma lem6007580 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term81 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem6007579 _120519 _120521 op f) (@lem6007578 _120519 _120521 f op h1)). Qed.
Lemma lem6007581 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term82 _120519 _120521 op f x.
Proof. exact (@lem6007580 _120519 _120521 f op h1 x). Qed.
Lemma lem6007582 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term82 _120519 _120521 op f x) = (term83 _120519 _120521 x op f).
Proof. exact (eq_refl (term82 _120519 _120521 op f x)). Qed.
Lemma lem6007583 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term83 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem6007582 _120519 _120521 x op f) (@lem6007581 _120519 _120521 f x op h1)). Qed.
Lemma lem6007584 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term84 _120519 _120521 x op f s.
Proof. exact (@lem6007583 _120519 _120521 x f op h1 s). Qed.
Lemma lem6007585 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term84 _120519 _120521 x op f s) = (term85 _120519 _120521 x op s f).
Proof. exact (eq_refl (term84 _120519 _120521 x op f s)). Qed.
Lemma lem6007586 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term85 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6007585 _120519 _120521 x op s f) (@lem6007584 _120519 _120521 x f s op h1)). Qed.
Lemma lem6007587 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem6007588 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term86 _120519 _120521 op x s f) = (term87 _120519 _120521 x op s f).
Proof. exact (@lem6007586 _120519 _120521 x s f op h2 (@lem6007587 _120521 s h1)). Qed.
Lemma lem6007589 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term88 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6007588 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem6007590 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term89 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem6007589 _120519 _120521 x op f s h0). Qed.
Lemma lem6007592 (p : Prop) (q : Prop) (r : Prop) : (term90 p q r) = (term91 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6007597 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term89 _120519 _120521 x op s f) = (term92 _120519 _120521 x op s f).
Proof. exact (@lem6007592 (@FINITE _120521 s) (@monoidal _120519 op) ((term86 _120519 _120521 op x s f) = (term87 _120519 _120521 x op s f))). Qed.
Lemma lem6007599 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term93 _120477 _120519 op.
Proof. exact (proj1 (@lem6007576 _120477 _120519 Prop op h1)). Qed.
Lemma lem6007600 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term94 _120477 _120519 op f.
Proof. exact (@lem6007599 _120477 _120519 op h1 f). Qed.
Lemma lem6007601 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term94 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term94 _120477 _120519 op f)). Qed.
Lemma lem6007602 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem6007601 _120477 _120519 f op) (@lem6007600 _120477 _120519 f op h1)). Qed.
Lemma lem6007608 {_122573 : Type'} (op : type1400 _122573) : (@monoidal _122573 op) = ((@monoidal _122573 op) = True).
Proof. exact (@lem7 (@monoidal _122573 op)). Qed.
Lemma lem6007709 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term95 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6007602 _120477 _120519 f op h0). Qed.
Lemma lem6007710 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) : term95 _122572 _122573 f op.
Proof. exact (@lem6007709 _122572 _122573 f op). Qed.
Lemma lem6007711 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) : term96 _122572 _122573 f g op.
Proof. exact (@lem6007710 _122572 _122573 (term97 _122572 _122573 op f g) op). Qed.
Lemma lem6007713 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6007724 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6007713 _122573 op h1)). Qed.
Lemma lem6007725 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6007724 _122573 op h1) (@lem0)). Qed.
Lemma lem6007726 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term10 _122572 _122573 op f g) = (@neutral _122573 op).
Proof. exact (@lem6007711 _122572 _122573 f g op (@lem6007725 _122573 op h1)). Qed.
Lemma lem6007757 {_122573 : Type'} : (@eq _122573) = (@eq _122573).
Proof. exact (eq_refl (@eq _122573)). Qed.
Lemma lem6007758 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term98 _122572 _122573 op f g) = (term99 _122573 op).
Proof. exact (MK_COMB (@lem6007757 _122573) (@lem6007726 _122572 _122573 f g op h1)). Qed.
Lemma lem6007842 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term95 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6007602 _120477 _120519 f op h0). Qed.
Lemma lem6007843 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) : term95 _122572 _122573 f op.
Proof. exact (@lem6007842 _122572 _122573 f op). Qed.
Lemma lem6007845 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6007856 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6007845 _122573 op h1)). Qed.
Lemma lem6007857 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6007856 _122573 op h1) (@lem0)). Qed.
Lemma lem6007858 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@iterate _122573 _122572 op (@EMPTY _122572) f) = (@neutral _122573 op).
Proof. exact (@lem6007843 _122572 _122573 f op (@lem6007857 _122573 op h1)). Qed.
Lemma lem6007889 {_122573 : Type'} (op : type1400 _122573) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6007890 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term100 _122572 _122573 op f) = (term101 _122573 op).
Proof. exact (MK_COMB (@lem6007889 _122573 op) (@lem6007858 _122572 _122573 f op h1)). Qed.
Lemma lem6007942 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term95 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6007602 _120477 _120519 f op h0). Qed.
Lemma lem6007943 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) : term95 _122572 _122573 f op.
Proof. exact (@lem6007942 _122572 _122573 f op). Qed.
Lemma lem6007944 {_122572 _122573 : Type'} (g : _122572 -> _122573) (op : type1400 _122573) : term95 _122572 _122573 g op.
Proof. exact (@lem6007943 _122572 _122573 g op). Qed.
Lemma lem6007946 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6007957 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6007946 _122573 op h1)). Qed.
Lemma lem6007958 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6007957 _122573 op h1) (@lem0)). Qed.
Lemma lem6007959 {_122572 _122573 : Type'} (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@iterate _122573 _122572 op (@EMPTY _122572) g) = (@neutral _122573 op).
Proof. exact (@lem6007944 _122572 _122573 g op (@lem6007958 _122573 op h1)). Qed.
Lemma lem6007990 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term11 _122572 _122573 f op g) = (term102 _122573 op).
Proof. exact (MK_COMB (@lem6007890 _122572 _122573 f op h1) (@lem6007959 _122572 _122573 g op h1)). Qed.
Lemma lem6008000 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : term103 _119721 op a.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007557 _119721 a op h0). Qed.
Lemma lem6008001 {_122573 : Type'} (op : type1400 _122573) (a : _122573) : term103 _122573 op a.
Proof. exact (@lem6008000 _122573 op a). Qed.
Lemma lem6008002 {_122573 : Type'} (op : type1400 _122573) : term104 _122573 op.
Proof. exact (@lem6008001 _122573 op (@neutral _122573 op)). Qed.
Lemma lem6008004 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6008015 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6008004 _122573 op h1)). Qed.
Lemma lem6008016 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6008015 _122573 op h1) (@lem0)). Qed.
Lemma lem6008017 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term102 _122573 op) = (@neutral _122573 op).
Proof. exact (@lem6008002 _122573 op (@lem6008016 _122573 op h1)). Qed.
Lemma lem6008048 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term11 _122572 _122573 f op g) = (@neutral _122573 op).
Proof. exact (TRANS (@lem6007990 _122572 _122573 f g op h1) (@lem6008017 _122573 op h1)). Qed.
Lemma lem6008049 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : ((term10 _122572 _122573 op f g) = (term11 _122572 _122573 f op g)) = ((@neutral _122573 op) = (@neutral _122573 op)).
Proof. exact (MK_COMB (@lem6007758 _122572 _122573 f g op h1) (@lem6008048 _122572 _122573 f g op h1)). Qed.
Lemma lem6008051 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6008052 {_122573 : Type'} (x : _122573) : (x = x) = True.
Proof. exact (@lem6008051 _122573 x). Qed.
Lemma lem6008053 {_122573 : Type'} (op : type1400 _122573) : ((@neutral _122573 op) = (@neutral _122573 op)) = True.
Proof. exact (@lem6008052 _122573 (@neutral _122573 op)). Qed.
Lemma lem6008064 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : ((term10 _122572 _122573 op f g) = (term11 _122572 _122573 f op g)) = True.
Proof. exact (TRANS (@lem6008049 _122572 _122573 f g op h1) (@lem6008053 _122573 op)). Qed.
Lemma lem6008065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6008066 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term13 _122572 _122573 f op g) = (and True).
Proof. exact (MK_COMB (@lem6008065) (@lem6008064 _122572 _122573 f g op h1)). Qed.
Lemma lem6008182 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term105 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6008183 (p : Prop) (q : Prop) (p' : Prop) : term106 p q p'.
Proof. exact (fun q' : Prop => @lem6008182 p q p' q'). Qed.
Lemma lem6008184 (p : Prop) (q : Prop) : term107 p q.
Proof. exact (fun p' : Prop => @lem6008183 p q p'). Qed.
Lemma lem6008185 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) : term108 _122572 _122573 f op x s g.
Proof. exact (@lem6008184 (term21 _122572 _122573 f op g x s) ((term25 _122572 _122573 x s op f g) = (term26 _122572 _122573 f op x s g))). Qed.
Lemma lem6008186 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (p' : Prop) : term109 _122572 _122573 f op x s g p'.
Proof. exact (@lem6008185 _122572 _122573 f op x s g p'). Qed.
Lemma lem6008187 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (p' : Prop) : (term109 _122572 _122573 f op x s g p') = (term110 _122572 _122573 f op x s g p').
Proof. exact (eq_refl (term109 _122572 _122573 f op x s g p')). Qed.
Lemma lem6008188 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (p' : Prop) : term110 _122572 _122573 f op x s g p'.
Proof. exact (EQ_MP (@lem6008187 _122572 _122573 f op x s g p') (@lem6008186 _122572 _122573 f op x s g p')). Qed.
Lemma lem6008189 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (p' : Prop) (q' : Prop) : term111 _122572 _122573 f op x s g p' q'.
Proof. exact (@lem6008188 _122572 _122573 f op x s g p' q'). Qed.
Lemma lem6008190 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (p' : Prop) (q' : Prop) : (term111 _122572 _122573 f op x s g p' q') = (term112 _122572 _122573 f op x s g p' q').
Proof. exact (eq_refl (term111 _122572 _122573 f op x s g p' q')). Qed.
Lemma lem6008191 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (p' : Prop) (q' : Prop) : term112 _122572 _122573 f op x s g p' q'.
Proof. exact (EQ_MP (@lem6008190 _122572 _122573 f op x s g p' q') (@lem6008189 _122572 _122573 f op x s g p' q')). Qed.
Lemma lem6008760 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) : (term21 _122572 _122573 f op g x s) = (term21 _122572 _122573 f op g x s).
Proof. exact (eq_refl (term21 _122572 _122573 f op g x s)). Qed.
Lemma lem6008761 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (q' : Prop) : term113 _122572 _122573 f op g x s q'.
Proof. exact (@lem6008191 _122572 _122573 f op x s g (term21 _122572 _122573 f op g x s) q'). Qed.
Lemma lem6008762 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (q' : Prop) : term114 _122572 _122573 f op g x s q'.
Proof. exact (@lem6008761 _122572 _122573 f op g x s q' (@lem6008760 _122572 _122573 f op g x s)). Qed.
Lemma lem6008763 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term21 _122572 _122573 f op g x s.
Proof. exact (h1). Qed.
Lemma lem6008764 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term19 _122572 x s.
Proof. exact (proj2 (@lem6008763 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6008765 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : @FINITE _122572 s.
Proof. exact (proj2 (@lem6008764 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6008766 {_122572 : Type'} (s : _122572 -> Prop) : (@FINITE _122572 s) = ((@FINITE _122572 s) = True).
Proof. exact (@lem7 (@FINITE _122572 s)). Qed.
Lemma lem6008768 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term115 _122572 x s.
Proof. exact (proj1 (@lem6008764 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6008769 {_122572 : Type'} (x : _122572) (s : _122572 -> Prop) : term116 _122572 x s.
Proof. exact (@lem82 (@IN _122572 x s)). Qed.
Lemma lem6008805 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term92 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6007597 _120519 _120521 x op s f) (@lem6007590 _120519 _120521 x op s f)). Qed.
Lemma lem6008806 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : term117 _122572 _122573 x op s f.
Proof. exact (@lem6008805 _122573 _122572 x op s f). Qed.
Lemma lem6008807 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : term118 _122572 _122573 x s op f g.
Proof. exact (@lem6008806 _122572 _122573 x op s (term97 _122572 _122573 op f g)). Qed.
Lemma lem6008843 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (@FINITE _122572 s) = True.
Proof. exact (EQ_MP (@lem6008766 _122572 s) (@lem6008765 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6008854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6008855 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term119 _122572 s) = (and True).
Proof. exact (MK_COMB (@lem6008854) (@lem6008843 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6008887 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6008898 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term120 _122572 _122573 s op) = (True /\ True).
Proof. exact (MK_COMB (@lem6008855 _122572 _122573 f op g x s h2) (@lem6008887 _122573 op h1)). Qed.
Lemma lem6008900 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6008901 : (True /\ True) = True.
Proof. exact (@lem6008900 True). Qed.
Lemma lem6008912 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term120 _122572 _122573 s op) = True.
Proof. exact (TRANS (@lem6008898 _122572 _122573 f op g x s h1 h2) (@lem6008901)). Qed.
Lemma lem6008913 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : True = (term120 _122572 _122573 s op).
Proof. exact (SYM (@lem6008912 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6008914 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : term120 _122572 _122573 s op.
Proof. exact (EQ_MP (@lem6008913 _122572 _122573 f op g x s h1 h2) (@lem0)). Qed.
Lemma lem6008915 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term25 _122572 _122573 x s op f g) = (term121 _122572 _122573 x s op f g).
Proof. exact (@lem6008807 _122572 _122573 x s op f g (@lem6008914 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6009068 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term122 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6009069 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term123 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6009068 _2963 g t e g' t' e'). Qed.
Lemma lem6009070 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term124 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6009069 _2963 g t e g' t'). Qed.
Lemma lem6009071 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term125 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6009070 _2963 g t e g'). Qed.
Lemma lem6009072 {_122573 : Type'} (g : Prop) (t : _122573) (e : _122573) : term125 _122573 g t e.
Proof. exact (@lem6009071 _122573 g t e). Qed.
Lemma lem6009073 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : term126 _122572 _122573 x s op f g.
Proof. exact (@lem6009072 _122573 (@IN _122572 x s) (term15 _122572 _122573 s op f g) (term127 _122572 _122573 x s op f g)). Qed.
Lemma lem6009074 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) : term128 _122572 _122573 x s op f g g'.
Proof. exact (@lem6009073 _122572 _122573 x s op f g g'). Qed.
Lemma lem6009075 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) : (term128 _122572 _122573 x s op f g g') = (term129 _122572 _122573 x s op f g g').
Proof. exact (eq_refl (term128 _122572 _122573 x s op f g g')). Qed.
Lemma lem6009076 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) : term129 _122572 _122573 x s op f g g'.
Proof. exact (EQ_MP (@lem6009075 _122572 _122573 x s op f g g') (@lem6009074 _122572 _122573 x s op f g g')). Qed.
Lemma lem6009077 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) : term130 _122572 _122573 x s op f g g' t'.
Proof. exact (@lem6009076 _122572 _122573 x s op f g g' t'). Qed.
Lemma lem6009078 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) : (term130 _122572 _122573 x s op f g g' t') = (term131 _122572 _122573 x s op f g g' t').
Proof. exact (eq_refl (term130 _122572 _122573 x s op f g g' t')). Qed.
Lemma lem6009079 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) : term131 _122572 _122573 x s op f g g' t'.
Proof. exact (EQ_MP (@lem6009078 _122572 _122573 x s op f g g' t') (@lem6009077 _122572 _122573 x s op f g g' t')). Qed.
Lemma lem6009080 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : term132 _122572 _122573 x s op f g g' t' e'.
Proof. exact (@lem6009079 _122572 _122573 x s op f g g' t' e'). Qed.
Lemma lem6009081 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : (term132 _122572 _122573 x s op f g g' t' e') = (term133 _122572 _122573 x s op f g g' t' e').
Proof. exact (eq_refl (term132 _122572 _122573 x s op f g g' t' e')). Qed.
Lemma lem6009082 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : term133 _122572 _122573 x s op f g g' t' e'.
Proof. exact (EQ_MP (@lem6009081 _122572 _122573 x s op f g g' t' e') (@lem6009080 _122572 _122573 x s op f g g' t' e')). Qed.
Lemma lem6009084 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (@IN _122572 x s) = False.
Proof. exact (@lem6008769 _122572 x s (@lem6008768 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6009095 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (t' : _122573) (e' : _122573) : term134 _122572 _122573 x s op f g t' e'.
Proof. exact (@lem6009082 _122572 _122573 x s op f g False t' e'). Qed.
Lemma lem6009096 {_122572 _122573 : Type'} (t' : _122573) (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term135 _122572 _122573 x s op f g t' e'.
Proof. exact (@lem6009095 _122572 _122573 x s op f g t' e' (@lem6009084 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6009101 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term15 _122572 _122573 s op f g) = (term16 _122572 _122573 f op s g).
Proof. exact (proj1 (@lem6008763 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6009102 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term15 _122572 _122573 s op f g) = (term16 _122572 _122573 f op s g).
Proof. exact (@lem6009101 _122572 _122573 f op g x s h1). Qed.
Lemma lem6009275 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term136 _122572 _122573 f op s g.
Proof. exact (fun h0 : False => @lem6009102 _122572 _122573 f op g x s h1). Qed.
Lemma lem6009276 {_122572 _122573 : Type'} (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term137 _122572 _122573 x f op s g e'.
Proof. exact (@lem6009096 _122572 _122573 (term16 _122572 _122573 f op s g) e' f op g x s h1). Qed.
Lemma lem6009277 {_122572 _122573 : Type'} (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term138 _122572 _122573 x f op s g e'.
Proof. exact (@lem6009276 _122572 _122573 e' f op g x s h1 (@lem6009275 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6009288 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : term139 _119721 op b a.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007548 _119721 b a op h0). Qed.
Lemma lem6009289 {_122573 : Type'} (op : type1400 _122573) (b : _122573) (a : _122573) : term139 _122573 op b a.
Proof. exact (@lem6009288 _122573 op b a). Qed.
Lemma lem6009290 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) : term140 _122572 _122573 s op f g x.
Proof. exact (@lem6009289 _122573 op (term15 _122572 _122573 s op f g) (term141 _122572 _122573 op f g x)). Qed.
Lemma lem6009292 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6009303 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6009292 _122573 op h1)). Qed.
Lemma lem6009304 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6009303 _122573 op h1) (@lem0)). Qed.
Lemma lem6009305 {_122572 _122573 : Type'} (s : _122572 -> Prop) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term127 _122572 _122573 x s op f g) = (term142 _122572 _122573 s op f g x).
Proof. exact (@lem6009290 _122572 _122573 s op f g x (@lem6009304 _122573 op h1)). Qed.
Lemma lem6009339 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term15 _122572 _122573 s op f g) = (term16 _122572 _122573 f op s g).
Proof. exact (proj1 (@lem6008763 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6009340 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term15 _122572 _122573 s op f g) = (term16 _122572 _122573 f op s g).
Proof. exact (@lem6009339 _122572 _122573 f op g x s h1). Qed.
Lemma lem6009513 {_122573 : Type'} (op : type1400 _122573) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6009514 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term143 _122572 _122573 s op f g) = (term144 _122572 _122573 f op s g).
Proof. exact (MK_COMB (@lem6009513 _122573 op) (@lem6009340 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6009708 {A B : Type'} (f : A -> B) (y : A) : (term145 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6009709 {_122572 _122573 : Type'} (f : _122572 -> _122573) (y : _122572) : (term145 _122572 _122573 f y) = (f y).
Proof. exact (@lem6009708 _122572 _122573 f y). Qed.
Lemma lem6009710 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) : (term146 _122572 _122573 op f g x) = (term141 _122572 _122573 op f g x).
Proof. exact (@lem6009709 _122572 _122573 (term97 _122572 _122573 op f g) x). Qed.
Lemma lem6009711 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) : (term141 _122572 _122573 op f g x) = (term147 _122572 _122573 op f g x).
Proof. exact (eq_refl (term141 _122572 _122573 op f g x)). Qed.
Lemma lem6009712 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : (term148 _122572 _122573 op f g) = (term97 _122572 _122573 op f g).
Proof. exact (fun_ext (fun x : _122572 => @lem6009711 _122572 _122573 op f g x)). Qed.
Lemma lem6009713 {_122572 : Type'} (x : _122572) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6009714 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) : (term146 _122572 _122573 op f g x) = (term141 _122572 _122573 op f g x).
Proof. exact (MK_COMB (@lem6009712 _122572 _122573 op f g) (@lem6009713 _122572 x)). Qed.
Lemma lem6009715 {_122573 : Type'} : (@eq _122573) = (@eq _122573).
Proof. exact (eq_refl (@eq _122573)). Qed.
Lemma lem6009716 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) : (term149 _122572 _122573 op f g x) = (term150 _122572 _122573 op f g x).
Proof. exact (MK_COMB (@lem6009715 _122573) (@lem6009714 _122572 _122573 op f g x)). Qed.
Lemma lem6009717 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) : (term141 _122572 _122573 op f g x) = (term147 _122572 _122573 op f g x).
Proof. exact (eq_refl (term141 _122572 _122573 op f g x)). Qed.
Lemma lem6009718 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) : ((term146 _122572 _122573 op f g x) = (term141 _122572 _122573 op f g x)) = ((term141 _122572 _122573 op f g x) = (term147 _122572 _122573 op f g x)).
Proof. exact (MK_COMB (@lem6009716 _122572 _122573 op f g x) (@lem6009717 _122572 _122573 op f g x)). Qed.
Lemma lem6009719 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) : (term141 _122572 _122573 op f g x) = (term147 _122572 _122573 op f g x).
Proof. exact (EQ_MP (@lem6009718 _122572 _122573 op f g x) (@lem6009710 _122572 _122573 op f g x)). Qed.
Lemma lem6009812 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term142 _122572 _122573 s op f g x) = (term151 _122572 _122573 s op f g x).
Proof. exact (MK_COMB (@lem6009514 _122572 _122573 f op g x s h1) (@lem6009719 _122572 _122573 op f g x)). Qed.
Lemma lem6009814 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : term152 _119721 b op a c.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007521 _119721 b a c op h0). Qed.
Lemma lem6009815 {_122573 : Type'} (b : _122573) (op : type1400 _122573) (a : _122573) (c : _122573) : term152 _122573 b op a c.
Proof. exact (@lem6009814 _122573 b op a c). Qed.
Lemma lem6009816 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (x : _122572) : term153 _122572 _122573 f op s g x.
Proof. exact (@lem6009815 _122573 (f x) op (term16 _122572 _122573 f op s g) (g x)). Qed.
Lemma lem6009818 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6009829 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6009818 _122573 op h1)). Qed.
Lemma lem6009830 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6009829 _122573 op h1) (@lem0)). Qed.
Lemma lem6009831 {_122572 _122573 : Type'} (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (x : _122572) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term151 _122572 _122573 s op f g x) = (term154 _122572 _122573 f op s g x).
Proof. exact (@lem6009816 _122572 _122573 f op s g x (@lem6009830 _122573 op h1)). Qed.
Lemma lem6009899 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : term155 _119721 a op b c.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007536 _119721 a b c op h0). Qed.
Lemma lem6009900 {_122573 : Type'} (a : _122573) (op : type1400 _122573) (b : _122573) (c : _122573) : term155 _122573 a op b c.
Proof. exact (@lem6009899 _122573 a op b c). Qed.
Lemma lem6009901 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (x : _122572) : term156 _122572 _122573 f op s g x.
Proof. exact (@lem6009900 _122573 (@iterate _122573 _122572 op s f) op (@iterate _122573 _122572 op s g) (g x)). Qed.
Lemma lem6009903 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6009914 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6009903 _122573 op h1)). Qed.
Lemma lem6009915 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6009914 _122573 op h1) (@lem0)). Qed.
Lemma lem6009916 {_122572 _122573 : Type'} (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (x : _122572) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term157 _122572 _122573 f op s g x) = (term158 _122572 _122573 f op s g x).
Proof. exact (@lem6009901 _122572 _122573 f op s g x (@lem6009915 _122573 op h1)). Qed.
Lemma lem6010026 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : term139 _119721 op b a.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007548 _119721 b a op h0). Qed.
Lemma lem6010027 {_122573 : Type'} (op : type1400 _122573) (b : _122573) (a : _122573) : term139 _122573 op b a.
Proof. exact (@lem6010026 _122573 op b a). Qed.
Lemma lem6010028 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term159 _122572 _122573 x op s g.
Proof. exact (@lem6010027 _122573 op (g x) (@iterate _122573 _122572 op s g)). Qed.
Lemma lem6010030 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6010041 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6010030 _122573 op h1)). Qed.
Lemma lem6010042 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6010041 _122573 op h1) (@lem0)). Qed.
Lemma lem6010043 {_122572 _122573 : Type'} (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term160 _122572 _122573 op s g x) = (term161 _122572 _122573 x op s g).
Proof. exact (@lem6010028 _122572 _122573 x op s g (@lem6010042 _122573 op h1)). Qed.
Lemma lem6010176 {_122572 _122573 : Type'} (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : (term162 _122572 _122573 op s f) = (term162 _122572 _122573 op s f).
Proof. exact (eq_refl (term162 _122572 _122573 op s f)). Qed.
Lemma lem6010177 {_122572 _122573 : Type'} (f : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term158 _122572 _122573 f op s g x) = (term163 _122572 _122573 f x op s g).
Proof. exact (MK_COMB (@lem6010176 _122572 _122573 op s f) (@lem6010043 _122572 _122573 x s g op h1)). Qed.
Lemma lem6010179 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : term152 _119721 b op a c.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007521 _119721 b a c op h0). Qed.
Lemma lem6010180 {_122573 : Type'} (b : _122573) (op : type1400 _122573) (a : _122573) (c : _122573) : term152 _122573 b op a c.
Proof. exact (@lem6010179 _122573 b op a c). Qed.
Lemma lem6010181 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term164 _122572 _122573 x f op s g.
Proof. exact (@lem6010180 _122573 (g x) op (@iterate _122573 _122572 op s f) (@iterate _122573 _122572 op s g)). Qed.
Lemma lem6010183 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6010194 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6010183 _122573 op h1)). Qed.
Lemma lem6010195 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6010194 _122573 op h1) (@lem0)). Qed.
Lemma lem6010196 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term163 _122572 _122573 f x op s g) = (term165 _122572 _122573 x f op s g).
Proof. exact (@lem6010181 _122572 _122573 x f op s g (@lem6010195 _122573 op h1)). Qed.
Lemma lem6010433 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term158 _122572 _122573 f op s g x) = (term165 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6010177 _122572 _122573 f x s g op h1) (@lem6010196 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6010434 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term157 _122572 _122573 f op s g x) = (term165 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6009916 _122572 _122573 f s g x op h1) (@lem6010433 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6010435 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (x : _122572) : (term166 _122572 _122573 op f x) = (term166 _122572 _122573 op f x).
Proof. exact (eq_refl (term166 _122572 _122573 op f x)). Qed.
Lemma lem6010436 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term154 _122572 _122573 f op s g x) = (term167 _122572 _122573 x f op s g).
Proof. exact (MK_COMB (@lem6010435 _122572 _122573 op f x) (@lem6010434 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6010737 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term151 _122572 _122573 s op f g x) = (term167 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6009831 _122572 _122573 f s g x op h1) (@lem6010436 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6010738 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term142 _122572 _122573 s op f g x) = (term167 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6009812 _122572 _122573 f op g x s h2) (@lem6010737 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6010739 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term127 _122572 _122573 x s op f g) = (term167 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6009305 _122572 _122573 s f g x op h1) (@lem6010738 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6010740 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : term168 _122572 _122573 x f op s g.
Proof. exact (fun h0 : ~ False => @lem6010739 _122572 _122573 f op g x s h1 h2). Qed.
Lemma lem6010741 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term169 _122572 _122573 x f op s g.
Proof. exact (@lem6009277 _122572 _122573 (term167 _122572 _122573 x f op s g) f op g x s h1). Qed.
Lemma lem6010742 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term121 _122572 _122573 x s op f g) = (term170 _122572 _122573 x f op s g).
Proof. exact (@lem6010741 _122572 _122573 f op g x s h2 (@lem6010740 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6010744 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6010745 {_122573 : Type'} (t1 : _122573) (t2 : _122573) : (@COND _122573 False t1 t2) = t2.
Proof. exact (@lem6010744 _122573 t1 t2). Qed.
Lemma lem6010746 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term170 _122572 _122573 x f op s g) = (term167 _122572 _122573 x f op s g).
Proof. exact (@lem6010745 _122573 (term16 _122572 _122573 f op s g) (term167 _122572 _122573 x f op s g)). Qed.
Lemma lem6011047 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term121 _122572 _122573 x s op f g) = (term167 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6010742 _122572 _122573 f op g x s h1 h2) (@lem6010746 _122572 _122573 x f op s g)). Qed.
Lemma lem6011048 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term25 _122572 _122573 x s op f g) = (term167 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6008915 _122572 _122573 f op g x s h1 h2) (@lem6011047 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6011049 {_122573 : Type'} : (@eq _122573) = (@eq _122573).
Proof. exact (eq_refl (@eq _122573)). Qed.
Lemma lem6011050 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term171 _122572 _122573 x s op f g) = (term172 _122572 _122573 x f op s g).
Proof. exact (MK_COMB (@lem6011049 _122573) (@lem6011048 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6011404 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term92 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6007597 _120519 _120521 x op s f) (@lem6007590 _120519 _120521 x op s f)). Qed.
Lemma lem6011405 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : term117 _122572 _122573 x op s f.
Proof. exact (@lem6011404 _122573 _122572 x op s f). Qed.
Lemma lem6011441 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (@FINITE _122572 s) = True.
Proof. exact (EQ_MP (@lem6008766 _122572 s) (@lem6008765 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6011452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6011453 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term119 _122572 s) = (and True).
Proof. exact (MK_COMB (@lem6011452) (@lem6011441 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6011485 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6011496 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term120 _122572 _122573 s op) = (True /\ True).
Proof. exact (MK_COMB (@lem6011453 _122572 _122573 f op g x s h2) (@lem6011485 _122573 op h1)). Qed.
Lemma lem6011498 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6011499 : (True /\ True) = True.
Proof. exact (@lem6011498 True). Qed.
Lemma lem6011510 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term120 _122572 _122573 s op) = True.
Proof. exact (TRANS (@lem6011496 _122572 _122573 f op g x s h1 h2) (@lem6011499)). Qed.
Lemma lem6011511 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : True = (term120 _122572 _122573 s op).
Proof. exact (SYM (@lem6011510 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6011512 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : term120 _122572 _122573 s op.
Proof. exact (EQ_MP (@lem6011511 _122572 _122573 f op g x s h1 h2) (@lem0)). Qed.
Lemma lem6011513 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term173 _122572 _122573 op x s f) = (term174 _122572 _122573 x op s f).
Proof. exact (@lem6011405 _122572 _122573 x op s f (@lem6011512 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6011666 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term122 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6011667 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term123 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6011666 _2963 g t e g' t' e'). Qed.
Lemma lem6011668 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term124 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6011667 _2963 g t e g' t'). Qed.
Lemma lem6011669 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term125 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6011668 _2963 g t e g'). Qed.
Lemma lem6011670 {_122573 : Type'} (g : Prop) (t : _122573) (e : _122573) : term125 _122573 g t e.
Proof. exact (@lem6011669 _122573 g t e). Qed.
Lemma lem6011671 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : term175 _122572 _122573 x op s f.
Proof. exact (@lem6011670 _122573 (@IN _122572 x s) (@iterate _122573 _122572 op s f) (term161 _122572 _122573 x op s f)). Qed.
Lemma lem6011672 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) : term176 _122572 _122573 x op s f g'.
Proof. exact (@lem6011671 _122572 _122573 x op s f g'). Qed.
Lemma lem6011673 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) : (term176 _122572 _122573 x op s f g') = (term177 _122572 _122573 x op s f g').
Proof. exact (eq_refl (term176 _122572 _122573 x op s f g')). Qed.
Lemma lem6011674 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) : term177 _122572 _122573 x op s f g'.
Proof. exact (EQ_MP (@lem6011673 _122572 _122573 x op s f g') (@lem6011672 _122572 _122573 x op s f g')). Qed.
Lemma lem6011675 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) (t' : _122573) : term178 _122572 _122573 x op s f g' t'.
Proof. exact (@lem6011674 _122572 _122573 x op s f g' t'). Qed.
Lemma lem6011676 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) (t' : _122573) : (term178 _122572 _122573 x op s f g' t') = (term179 _122572 _122573 x op s f g' t').
Proof. exact (eq_refl (term178 _122572 _122573 x op s f g' t')). Qed.
Lemma lem6011677 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) (t' : _122573) : term179 _122572 _122573 x op s f g' t'.
Proof. exact (EQ_MP (@lem6011676 _122572 _122573 x op s f g' t') (@lem6011675 _122572 _122573 x op s f g' t')). Qed.
Lemma lem6011678 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : term180 _122572 _122573 x op s f g' t' e'.
Proof. exact (@lem6011677 _122572 _122573 x op s f g' t' e'). Qed.
Lemma lem6011679 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : (term180 _122572 _122573 x op s f g' t' e') = (term181 _122572 _122573 x op s f g' t' e').
Proof. exact (eq_refl (term180 _122572 _122573 x op s f g' t' e')). Qed.
Lemma lem6011680 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : term181 _122572 _122573 x op s f g' t' e'.
Proof. exact (EQ_MP (@lem6011679 _122572 _122573 x op s f g' t' e') (@lem6011678 _122572 _122573 x op s f g' t' e')). Qed.
Lemma lem6011682 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (@IN _122572 x s) = False.
Proof. exact (@lem6008769 _122572 x s (@lem6008768 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6011693 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) (t' : _122573) (e' : _122573) : term182 _122572 _122573 x op s f t' e'.
Proof. exact (@lem6011680 _122572 _122573 x op s f False t' e'). Qed.
Lemma lem6011694 {_122572 _122573 : Type'} (t' : _122573) (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term183 _122572 _122573 x op s f t' e'.
Proof. exact (@lem6011693 _122572 _122573 x op s f t' e' (@lem6011682 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6011768 {_122572 _122573 : Type'} (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : (@iterate _122573 _122572 op s f) = (@iterate _122573 _122572 op s f).
Proof. exact (eq_refl (@iterate _122573 _122572 op s f)). Qed.
Lemma lem6011769 {_122572 _122573 : Type'} (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : term184 _122572 _122573 op s f.
Proof. exact (fun h0 : False => @lem6011768 _122572 _122573 op s f). Qed.
Lemma lem6011770 {_122572 _122573 : Type'} (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term185 _122572 _122573 x op s f e'.
Proof. exact (@lem6011694 _122572 _122573 (@iterate _122573 _122572 op s f) e' f op g x s h1). Qed.
Lemma lem6011771 {_122572 _122573 : Type'} (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term186 _122572 _122573 x op s f e'.
Proof. exact (@lem6011770 _122572 _122573 e' f op g x s h1 (@lem6011769 _122572 _122573 op s f)). Qed.
Lemma lem6011909 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : (term161 _122572 _122573 x op s f) = (term161 _122572 _122573 x op s f).
Proof. exact (eq_refl (term161 _122572 _122573 x op s f)). Qed.
Lemma lem6011910 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : term187 _122572 _122573 x op s f.
Proof. exact (fun h0 : ~ False => @lem6011909 _122572 _122573 x op s f). Qed.
Lemma lem6011911 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term188 _122572 _122573 x op s f.
Proof. exact (@lem6011771 _122572 _122573 (term161 _122572 _122573 x op s f) f op g x s h1). Qed.
Lemma lem6011912 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term174 _122572 _122573 x op s f) = (term189 _122572 _122573 x op s f).
Proof. exact (@lem6011911 _122572 _122573 f op g x s h1 (@lem6011910 _122572 _122573 x op s f)). Qed.
Lemma lem6011914 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6011915 {_122573 : Type'} (t1 : _122573) (t2 : _122573) : (@COND _122573 False t1 t2) = t2.
Proof. exact (@lem6011914 _122573 t1 t2). Qed.
Lemma lem6011916 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : (term189 _122572 _122573 x op s f) = (term161 _122572 _122573 x op s f).
Proof. exact (@lem6011915 _122573 (@iterate _122573 _122572 op s f) (term161 _122572 _122573 x op s f)). Qed.
Lemma lem6012049 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term174 _122572 _122573 x op s f) = (term161 _122572 _122573 x op s f).
Proof. exact (TRANS (@lem6011912 _122572 _122573 f op g x s h1) (@lem6011916 _122572 _122573 x op s f)). Qed.
Lemma lem6012050 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term173 _122572 _122573 op x s f) = (term161 _122572 _122573 x op s f).
Proof. exact (TRANS (@lem6011513 _122572 _122573 f op g x s h1 h2) (@lem6012049 _122572 _122573 f op g x s h2)). Qed.
Lemma lem6012051 {_122573 : Type'} (op : type1400 _122573) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6012052 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term190 _122572 _122573 op x s f) = (term191 _122572 _122573 x op s f).
Proof. exact (MK_COMB (@lem6012051 _122573 op) (@lem6012050 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6012206 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term92 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6007597 _120519 _120521 x op s f) (@lem6007590 _120519 _120521 x op s f)). Qed.
Lemma lem6012207 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (f : _122572 -> _122573) : term117 _122572 _122573 x op s f.
Proof. exact (@lem6012206 _122573 _122572 x op s f). Qed.
Lemma lem6012208 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term117 _122572 _122573 x op s g.
Proof. exact (@lem6012207 _122572 _122573 x op s g). Qed.
Lemma lem6012244 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (@FINITE _122572 s) = True.
Proof. exact (EQ_MP (@lem6008766 _122572 s) (@lem6008765 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6012255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6012256 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term119 _122572 s) = (and True).
Proof. exact (MK_COMB (@lem6012255) (@lem6012244 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6012288 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6012299 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term120 _122572 _122573 s op) = (True /\ True).
Proof. exact (MK_COMB (@lem6012256 _122572 _122573 f op g x s h2) (@lem6012288 _122573 op h1)). Qed.
Lemma lem6012301 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6012302 : (True /\ True) = True.
Proof. exact (@lem6012301 True). Qed.
Lemma lem6012313 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term120 _122572 _122573 s op) = True.
Proof. exact (TRANS (@lem6012299 _122572 _122573 f op g x s h1 h2) (@lem6012302)). Qed.
Lemma lem6012314 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : True = (term120 _122572 _122573 s op).
Proof. exact (SYM (@lem6012313 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6012315 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : term120 _122572 _122573 s op.
Proof. exact (EQ_MP (@lem6012314 _122572 _122573 f op g x s h1 h2) (@lem0)). Qed.
Lemma lem6012316 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term173 _122572 _122573 op x s g) = (term174 _122572 _122573 x op s g).
Proof. exact (@lem6012208 _122572 _122573 x op s g (@lem6012315 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6012469 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term122 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6012470 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term123 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6012469 _2963 g t e g' t' e'). Qed.
Lemma lem6012471 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term124 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6012470 _2963 g t e g' t'). Qed.
Lemma lem6012472 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term125 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6012471 _2963 g t e g'). Qed.
Lemma lem6012473 {_122573 : Type'} (g : Prop) (t : _122573) (e : _122573) : term125 _122573 g t e.
Proof. exact (@lem6012472 _122573 g t e). Qed.
Lemma lem6012474 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term175 _122572 _122573 x op s g.
Proof. exact (@lem6012473 _122573 (@IN _122572 x s) (@iterate _122573 _122572 op s g) (term161 _122572 _122573 x op s g)). Qed.
Lemma lem6012475 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) : term176 _122572 _122573 x op s g g'.
Proof. exact (@lem6012474 _122572 _122573 x op s g g'). Qed.
Lemma lem6012476 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) : (term176 _122572 _122573 x op s g g') = (term177 _122572 _122573 x op s g g').
Proof. exact (eq_refl (term176 _122572 _122573 x op s g g')). Qed.
Lemma lem6012477 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) : term177 _122572 _122573 x op s g g'.
Proof. exact (EQ_MP (@lem6012476 _122572 _122573 x op s g g') (@lem6012475 _122572 _122573 x op s g g')). Qed.
Lemma lem6012478 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) : term178 _122572 _122573 x op s g g' t'.
Proof. exact (@lem6012477 _122572 _122573 x op s g g' t'). Qed.
Lemma lem6012479 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) : (term178 _122572 _122573 x op s g g' t') = (term179 _122572 _122573 x op s g g' t').
Proof. exact (eq_refl (term178 _122572 _122573 x op s g g' t')). Qed.
Lemma lem6012480 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) : term179 _122572 _122573 x op s g g' t'.
Proof. exact (EQ_MP (@lem6012479 _122572 _122573 x op s g g' t') (@lem6012478 _122572 _122573 x op s g g' t')). Qed.
Lemma lem6012481 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : term180 _122572 _122573 x op s g g' t' e'.
Proof. exact (@lem6012480 _122572 _122573 x op s g g' t' e'). Qed.
Lemma lem6012482 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : (term180 _122572 _122573 x op s g g' t' e') = (term181 _122572 _122573 x op s g g' t' e').
Proof. exact (eq_refl (term180 _122572 _122573 x op s g g' t' e')). Qed.
Lemma lem6012483 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (g' : Prop) (t' : _122573) (e' : _122573) : term181 _122572 _122573 x op s g g' t' e'.
Proof. exact (EQ_MP (@lem6012482 _122572 _122573 x op s g g' t' e') (@lem6012481 _122572 _122573 x op s g g' t' e')). Qed.
Lemma lem6012485 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (@IN _122572 x s) = False.
Proof. exact (@lem6008769 _122572 x s (@lem6008768 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6012496 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (t' : _122573) (e' : _122573) : term182 _122572 _122573 x op s g t' e'.
Proof. exact (@lem6012483 _122572 _122573 x op s g False t' e'). Qed.
Lemma lem6012497 {_122572 _122573 : Type'} (t' : _122573) (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term183 _122572 _122573 x op s g t' e'.
Proof. exact (@lem6012496 _122572 _122573 x op s g t' e' (@lem6012485 _122572 _122573 f op g x s h1)). Qed.
Lemma lem6012571 {_122572 _122573 : Type'} (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (@iterate _122573 _122572 op s g) = (@iterate _122573 _122572 op s g).
Proof. exact (eq_refl (@iterate _122573 _122572 op s g)). Qed.
Lemma lem6012572 {_122572 _122573 : Type'} (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term184 _122572 _122573 op s g.
Proof. exact (fun h0 : False => @lem6012571 _122572 _122573 op s g). Qed.
Lemma lem6012573 {_122572 _122573 : Type'} (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term185 _122572 _122573 x op s g e'.
Proof. exact (@lem6012497 _122572 _122573 (@iterate _122573 _122572 op s g) e' f op g x s h1). Qed.
Lemma lem6012574 {_122572 _122573 : Type'} (e' : _122573) (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term186 _122572 _122573 x op s g e'.
Proof. exact (@lem6012573 _122572 _122573 e' f op g x s h1 (@lem6012572 _122572 _122573 op s g)). Qed.
Lemma lem6012712 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term161 _122572 _122573 x op s g) = (term161 _122572 _122573 x op s g).
Proof. exact (eq_refl (term161 _122572 _122573 x op s g)). Qed.
Lemma lem6012713 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term187 _122572 _122573 x op s g.
Proof. exact (fun h0 : ~ False => @lem6012712 _122572 _122573 x op s g). Qed.
Lemma lem6012714 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : term188 _122572 _122573 x op s g.
Proof. exact (@lem6012574 _122572 _122573 (term161 _122572 _122573 x op s g) f op g x s h1). Qed.
Lemma lem6012715 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term174 _122572 _122573 x op s g) = (term189 _122572 _122573 x op s g).
Proof. exact (@lem6012714 _122572 _122573 f op g x s h1 (@lem6012713 _122572 _122573 x op s g)). Qed.
Lemma lem6012717 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6012718 {_122573 : Type'} (t1 : _122573) (t2 : _122573) : (@COND _122573 False t1 t2) = t2.
Proof. exact (@lem6012717 _122573 t1 t2). Qed.
Lemma lem6012719 {_122572 _122573 : Type'} (x : _122572) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : (term189 _122572 _122573 x op s g) = (term161 _122572 _122573 x op s g).
Proof. exact (@lem6012718 _122573 (@iterate _122573 _122572 op s g) (term161 _122572 _122573 x op s g)). Qed.
Lemma lem6012852 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : term21 _122572 _122573 f op g x s) : (term174 _122572 _122573 x op s g) = (term161 _122572 _122573 x op s g).
Proof. exact (TRANS (@lem6012715 _122572 _122573 f op g x s h1) (@lem6012719 _122572 _122573 x op s g)). Qed.
Lemma lem6012853 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term173 _122572 _122573 op x s g) = (term161 _122572 _122573 x op s g).
Proof. exact (TRANS (@lem6012316 _122572 _122573 f op g x s h1 h2) (@lem6012852 _122572 _122573 f op g x s h2)). Qed.
Lemma lem6012854 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term26 _122572 _122573 f op x s g) = (term192 _122572 _122573 f x op s g).
Proof. exact (MK_COMB (@lem6012052 _122572 _122573 f op g x s h1 h2) (@lem6012853 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6012856 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : term152 _119721 b op a c.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007521 _119721 b a c op h0). Qed.
Lemma lem6012857 {_122573 : Type'} (b : _122573) (op : type1400 _122573) (a : _122573) (c : _122573) : term152 _122573 b op a c.
Proof. exact (@lem6012856 _122573 b op a c). Qed.
Lemma lem6012858 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term193 _122572 _122573 x f op s g.
Proof. exact (@lem6012857 _122573 (g x) op (term161 _122572 _122573 x op s f) (@iterate _122573 _122572 op s g)). Qed.
Lemma lem6012860 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6012871 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6012860 _122573 op h1)). Qed.
Lemma lem6012872 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6012871 _122573 op h1) (@lem0)). Qed.
Lemma lem6012873 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term192 _122572 _122573 f x op s g) = (term194 _122572 _122573 x f op s g).
Proof. exact (@lem6012858 _122572 _122573 x f op s g (@lem6012872 _122573 op h1)). Qed.
Lemma lem6012941 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : term155 _119721 a op b c.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007536 _119721 a b c op h0). Qed.
Lemma lem6012942 {_122573 : Type'} (a : _122573) (op : type1400 _122573) (b : _122573) (c : _122573) : term155 _122573 a op b c.
Proof. exact (@lem6012941 _122573 a op b c). Qed.
Lemma lem6012943 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term195 _122572 _122573 x f op s g.
Proof. exact (@lem6012942 _122573 (f x) op (@iterate _122573 _122572 op s f) (@iterate _122573 _122572 op s g)). Qed.
Lemma lem6012945 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6012956 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6012945 _122573 op h1)). Qed.
Lemma lem6012957 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6012956 _122573 op h1) (@lem0)). Qed.
Lemma lem6012958 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term196 _122572 _122573 x f op s g) = (term197 _122572 _122573 x f op s g).
Proof. exact (@lem6012943 _122572 _122573 x f op s g (@lem6012957 _122573 op h1)). Qed.
Lemma lem6013195 {_122572 _122573 : Type'} (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) : (term166 _122572 _122573 op g x) = (term166 _122572 _122573 op g x).
Proof. exact (eq_refl (term166 _122572 _122573 op g x)). Qed.
Lemma lem6013196 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term194 _122572 _122573 x f op s g) = (term198 _122572 _122573 x f op s g).
Proof. exact (MK_COMB (@lem6013195 _122572 _122573 op g x) (@lem6012958 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6013198 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : term152 _119721 b op a c.
Proof. exact (fun h0 : @monoidal _119721 op => @lem6007521 _119721 b a c op h0). Qed.
Lemma lem6013199 {_122573 : Type'} (b : _122573) (op : type1400 _122573) (a : _122573) (c : _122573) : term152 _122573 b op a c.
Proof. exact (@lem6013198 _122573 b op a c). Qed.
Lemma lem6013200 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : term199 _122572 _122573 x f op s g.
Proof. exact (@lem6013199 _122573 (f x) op (g x) (term16 _122572 _122573 f op s g)). Qed.
Lemma lem6013202 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : (@monoidal _122573 op) = True.
Proof. exact (EQ_MP (@lem6007608 _122573 op) (@lem6007470 _122573 op h1)). Qed.
Lemma lem6013213 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (@monoidal _122573 op).
Proof. exact (SYM (@lem6013202 _122573 op h1)). Qed.
Lemma lem6013214 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (EQ_MP (@lem6013213 _122573 op h1) (@lem0)). Qed.
Lemma lem6013215 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term198 _122572 _122573 x f op s g) = (term167 _122572 _122573 x f op s g).
Proof. exact (@lem6013200 _122572 _122573 x f op s g (@lem6013214 _122573 op h1)). Qed.
Lemma lem6013516 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term194 _122572 _122573 x f op s g) = (term167 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6013196 _122572 _122573 x f s g op h1) (@lem6013215 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6013517 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term192 _122572 _122573 f x op s g) = (term167 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6012873 _122572 _122573 x f s g op h1) (@lem6013516 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6013518 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : (term26 _122572 _122573 f op x s g) = (term167 _122572 _122573 x f op s g).
Proof. exact (TRANS (@lem6012854 _122572 _122573 f op g x s h1 h2) (@lem6013517 _122572 _122573 x f s g op h1)). Qed.
Lemma lem6013519 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : ((term25 _122572 _122573 x s op f g) = (term26 _122572 _122573 f op x s g)) = ((term167 _122572 _122573 x f op s g) = (term167 _122572 _122573 x f op s g)).
Proof. exact (MK_COMB (@lem6011050 _122572 _122573 f op g x s h1 h2) (@lem6013518 _122572 _122573 f op g x s h1 h2)). Qed.
Lemma lem6013521 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6013522 {_122573 : Type'} (x : _122573) : (x = x) = True.
Proof. exact (@lem6013521 _122573 x). Qed.
Lemma lem6013523 {_122572 _122573 : Type'} (x : _122572) (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) : ((term167 _122572 _122573 x f op s g) = (term167 _122572 _122573 x f op s g)) = True.
Proof. exact (@lem6013522 _122573 (term167 _122572 _122573 x f op s g)). Qed.
Lemma lem6013534 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (h1 : @monoidal _122573 op) (h2 : term21 _122572 _122573 f op g x s) : ((term25 _122572 _122573 x s op f g) = (term26 _122572 _122573 f op x s g)) = True.
Proof. exact (TRANS (@lem6013519 _122572 _122573 f op g x s h1 h2) (@lem6013523 _122572 _122573 x f op s g)). Qed.
Lemma lem6013535 {_122572 _122573 : Type'} (f : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term200 _122572 _122573 f op x s g.
Proof. exact (fun h0 : term21 _122572 _122573 f op g x s => @lem6013534 _122572 _122573 f op g x s h1 h0). Qed.
Lemma lem6013536 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) : term201 _122572 _122573 f op g x s.
Proof. exact (@lem6008762 _122572 _122573 f op g x s True). Qed.
Lemma lem6013537 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term28 _122572 _122573 f op x s g) = (term202 _122572 _122573 f op g x s).
Proof. exact (@lem6013536 _122572 _122573 f op g x s (@lem6013535 _122572 _122573 f x s g op h1)). Qed.
Lemma lem6013539 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6013540 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (g : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) : (term202 _122572 _122573 f op g x s) = True.
Proof. exact (@lem6013539 (term21 _122572 _122573 f op g x s)). Qed.
Lemma lem6013551 {_122572 _122573 : Type'} (f : _122572 -> _122573) (x : _122572) (s : _122572 -> Prop) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term28 _122572 _122573 f op x s g) = True.
Proof. exact (TRANS (@lem6013537 _122572 _122573 f g x s op h1) (@lem6013540 _122572 _122573 f op g x s)). Qed.
Lemma lem6013552 {_122572 _122573 : Type'} (f : _122572 -> _122573) (x : _122572) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term30 _122572 _122573 f op x g) = (term203 _122572).
Proof. exact (fun_ext (fun s : _122572 -> Prop => @lem6013551 _122572 _122573 f x s g op h1)). Qed.
Lemma lem6013573 {_122572 : Type'} : (@all (_122572 -> Prop)) = (@all (_122572 -> Prop)).
Proof. exact (eq_refl (@all (_122572 -> Prop))). Qed.
Lemma lem6013574 {_122572 _122573 : Type'} (f : _122572 -> _122573) (x : _122572) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term32 _122572 _122573 f op x g) = (term204 _122572).
Proof. exact (MK_COMB (@lem6013573 _122572) (@lem6013552 _122572 _122573 f x g op h1)). Qed.
Lemma lem6013576 {A : Type'} (t : Prop) : (term205 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6013577 {_122572 : Type'} (t : Prop) : (term206 _122572 t) = t.
Proof. exact (@lem6013576 (_122572 -> Prop) t). Qed.
Lemma lem6013578 {_122572 : Type'} : (term204 _122572) = True.
Proof. exact (@lem6013577 _122572 True). Qed.
Lemma lem6013589 {_122572 _122573 : Type'} (f : _122572 -> _122573) (x : _122572) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term32 _122572 _122573 f op x g) = True.
Proof. exact (TRANS (@lem6013574 _122572 _122573 f x g op h1) (@lem6013578 _122572)). Qed.
Lemma lem6013590 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term34 _122572 _122573 f op g) = (term207 _122572).
Proof. exact (fun_ext (fun x : _122572 => @lem6013589 _122572 _122573 f x g op h1)). Qed.
Lemma lem6013611 {_122572 : Type'} : (@all _122572) = (@all _122572).
Proof. exact (eq_refl (@all _122572)). Qed.
Lemma lem6013612 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term36 _122572 _122573 f op g) = (term208 _122572).
Proof. exact (MK_COMB (@lem6013611 _122572) (@lem6013590 _122572 _122573 f g op h1)). Qed.
Lemma lem6013614 {A : Type'} (t : Prop) : (term205 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6013615 {_122572 : Type'} (t : Prop) : (term205 _122572 t) = t.
Proof. exact (@lem6013614 _122572 t). Qed.
Lemma lem6013616 {_122572 : Type'} : (term208 _122572) = True.
Proof. exact (@lem6013615 _122572 True). Qed.
Lemma lem6013627 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term36 _122572 _122573 f op g) = True.
Proof. exact (TRANS (@lem6013612 _122572 _122573 f g op h1) (@lem6013616 _122572)). Qed.
Lemma lem6013628 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term38 _122572 _122573 f op g) = (True /\ True).
Proof. exact (MK_COMB (@lem6008066 _122572 _122573 f g op h1) (@lem6013627 _122572 _122573 f g op h1)). Qed.
Lemma lem6013630 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6013631 : (True /\ True) = True.
Proof. exact (@lem6013630 True). Qed.
Lemma lem6013642 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : (term38 _122572 _122573 f op g) = True.
Proof. exact (TRANS (@lem6013628 _122572 _122573 f g op h1) (@lem6013631)). Qed.
Lemma lem6013643 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : True = (term38 _122572 _122573 f op g).
Proof. exact (SYM (@lem6013642 _122572 _122573 f g op h1)). Qed.
Lemma lem6013644 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term38 _122572 _122573 f op g.
Proof. exact (EQ_MP (@lem6013643 _122572 _122573 f g op h1) (@lem0)). Qed.
Lemma lem6013645 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term47 _122572 _122573 f op g.
Proof. exact (@lem6007503 _122572 _122573 f op g (@lem6013644 _122572 _122573 f g op h1)). Qed.
Lemma lem6013650 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term209 _122572 _122573 f op.
Proof. exact (fun g : _122572 -> _122573 => @lem6013645 _122572 _122573 f g op h1). Qed.
Lemma lem6013655 {_122572 _122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : term210 _122572 _122573 op.
Proof. exact (fun f : _122572 -> _122573 => @lem6013650 _122572 _122573 f op h1). Qed.
Lemma lem6013656 {_122572 _122573 : Type'} (op : type1400 _122573) : term211 _122572 _122573 op.
Proof. exact (fun h0 : @monoidal _122573 op => @lem6013655 _122572 _122573 op h0). Qed.
Lemma lem6013661 {_122572 _122573 : Type'} : term212 _122572 _122573.
Proof. exact (fun op : type1400 _122573 => @lem6013656 _122572 _122573 op). Qed.
